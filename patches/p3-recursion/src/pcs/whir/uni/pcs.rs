use alloc::vec::Vec;
use core::marker::PhantomData;

use p3_challenger::{
    CanObserve, CanSample, CanSampleUniformBits, FieldChallenger, GrindingChallenger,
};
use p3_commit::{CommitmentOpening, Mmcs, MultilinearPcs, OpenedValues};
use p3_dft::TwoAdicSubgroupDft;
use p3_field::coset::TwoAdicMultiplicativeCoset;
use p3_field::{ExtensionField, PrimeCharacteristicRing, PrimeField64, TwoAdicField};
use p3_matrix::Matrix;
use p3_matrix::dense::RowMajorMatrix;
use p3_maybe_rayon::prelude::*;
use p3_multilinear_util::point::Point;
use p3_sumcheck::layout::{Layout, Table};
use p3_sumcheck::{
    OpeningBatch, OpeningProtocol, OpeningRequest, PrescribedPointPcs, TableShape, TableSpec,
};
use p3_util::log2_strict_usize;
use p3_whir::parameters::{ProtocolParameters, WhirConfig, WhirConfigError};
use p3_whir::pcs::WhirProverData;
use p3_whir::pcs::proof::{PcsProof, WhirProof, WhirRoundProof};
use p3_whir::pcs::prover::WhirProver;
use serde::{Deserialize, Serialize};

use crate::input_contract::whir::{WhirContextParams, validate_whir_pcs_context};
use crate::pcs::whir::params::WhirVerifierParamsError;
use crate::pcs::whir::uni::bridge::univariate_eq_point;
use crate::pcs::whir::uni::plan::{
    PaddedArity, StackedPlan, checked_stacked_num_variables, initial_layout_folding, padded_arity,
};
use crate::pcs::whir::uni::{SharedMmcs, WhirRatePolicy};

type CommitResult<F, EF, MT, L> =
    Result<(<MT as Mmcs<F>>::Commitment, WhirUniProverData<F, EF, MT, L>), WhirConfigError>;

pub struct WhirUniProverData<F, EF, MT, L>
where
    F: TwoAdicField,
    EF: ExtensionField<F>,
    MT: Mmcs<F>,
    L: Layout<F, EF>,
{
    pub domains: Vec<TwoAdicMultiplicativeCoset<F>>,
    pub coeffs: Vec<RowMajorMatrix<F>>,
    pub plan: StackedPlan,
    pub stacked_num_variables: usize,
    pub whir: WhirProverData<F, EF, SharedMmcs<MT>, L>,
}

#[derive(Debug)]
pub enum WhirUniPcsError {
    Whir {
        round: usize,
        source: p3_whir::pcs::verifier::errors::VerifierError,
    },
    OpeningValueMismatch {
        round: usize,
        batch: usize,
        column: usize,
    },
    RoundCountMismatch {
        expected: usize,
        actual: usize,
    },
    ShapeMismatch {
        round: usize,
    },
}

#[derive(Clone, Serialize, Deserialize)]
#[serde(bound(
    serialize = "F: Serialize, EF: Serialize, MT::Commitment: Serialize, MT::MultiProof: Serialize",
    deserialize = "F: Deserialize<'de>, EF: Deserialize<'de>, MT::Commitment: Deserialize<'de>, MT::MultiProof: Deserialize<'de>"
))]
pub struct WhirUniProof<F: Send + Sync + Clone, EF, MT: Mmcs<F>> {
    pub rounds: Vec<PcsProof<F, EF, MT>>,
}

pub(crate) struct RoundSchedule<EF> {
    pub(crate) protocol: OpeningProtocol,
    pub(crate) points: Vec<Point<EF>>,
    pub(crate) scales: Vec<Vec<EF>>,
    pub(crate) stacked_num_variables: usize,
}

pub(crate) fn round_schedule<F, EF>(
    shapes: &[(usize, usize)],
    points_per_matrix: &[Vec<EF>],
    folding: usize,
) -> RoundSchedule<EF>
where
    F: TwoAdicField,
    EF: ExtensionField<F>,
{
    assert_eq!(shapes.len(), points_per_matrix.len());

    let stacked_num_variables = checked_stacked_num_variables(
        shapes
            .iter()
            .map(|&(log_height, width)| (padded_arity(log_height, folding), width)),
    )
    .expect("native WHIR stacked geometry must fit in usize");

    let specs: Vec<TableSpec> = shapes
        .iter()
        .zip(points_per_matrix)
        .map(|(&(log_height, width), points)| {
            let schedule: Vec<OpeningRequest> = points
                .iter()
                .map(|_| OpeningBatch::new((0..width).collect(), Vec::new()))
                .collect();
            TableSpec::new(TableShape::new(log_height, width), schedule)
        })
        .collect();
    let protocol = OpeningProtocol::new(specs).pad_to_min_num_variables(folding);

    let mut points = Vec::new();
    let mut scales = Vec::with_capacity(shapes.len());
    for (&(log_height, _width), zetas) in shapes.iter().zip(points_per_matrix) {
        let arity = padded_arity(log_height, folding).get();
        let mut row = Vec::with_capacity(zetas.len());
        for &zeta in zetas {
            let (point, scale) = univariate_eq_point(zeta, arity);
            points.push(point);
            row.push(scale);
        }
        scales.push(row);
    }

    RoundSchedule {
        protocol,
        points,
        scales,
        stacked_num_variables,
    }
}

pub(crate) const FORK_SEED_LEN: usize = 8;

const FORK_TAG: u32 = 0x5748_5246;

pub(crate) fn fork_tag<F: PrimeCharacteristicRing>(round: usize) -> [F; 2] {
    [F::from_u32(FORK_TAG), F::from_usize(round)]
}

pub(crate) fn sample_fork_seed<F, Ch: CanSample<F>>(challenger: &mut Ch) -> [F; FORK_SEED_LEN] {
    challenger.sample_array()
}

pub(crate) fn fork_transcript<F, Ch>(fresh: &Ch, round: usize, seed: &[F]) -> Ch
where
    F: PrimeCharacteristicRing + Clone,
    Ch: CanObserve<F> + Clone,
{
    let mut challenger = fresh.clone();
    challenger.observe_slice(&fork_tag::<F>(round));
    challenger.observe_slice(seed);
    challenger
}

#[derive(Clone, Debug)]
pub struct WhirUniPcs<EF, F, Dft, MT, Challenger, L> {
    pub protocol_params: ProtocolParameters,
    folding: usize,
    rate_policy: WhirRatePolicy,
    pub dft: Dft,
    pub mmcs: MT,
    pub challenger_proto: Challenger,
    pub log_max_lde_height: usize,
    _marker: PhantomData<(EF, F, L)>,
}

impl<EF, F, Dft, MT, Challenger, L> WhirUniPcs<EF, F, Dft, MT, Challenger, L>
where
    F: TwoAdicField + PrimeField64 + Ord,
    EF: ExtensionField<F> + TwoAdicField,
    Dft: TwoAdicSubgroupDft<F> + Clone + Sync,
    MT: Mmcs<F> + Clone,
    MT::ProverData<RowMajorMatrix<F>>: Clone,
    Challenger: FieldChallenger<F>
        + GrindingChallenger<Witness = F>
        + CanSampleUniformBits<F>
        + CanObserve<MT::Commitment>
        + Clone,
    L: Layout<F, EF> + Clone,
{
    pub fn new(
        protocol_params: ProtocolParameters,
        dft: Dft,
        mmcs: MT,
        challenger_proto: Challenger,
        log_max_lde_height: usize,
    ) -> Self {
        let folding = initial_layout_folding(&protocol_params.folding_factor)
            .expect("WhirUniPcs requires a positive native folding strategy");
        Self {
            protocol_params,
            folding,
            rate_policy: WhirRatePolicy::Native,
            dft,
            mmcs,
            challenger_proto,
            log_max_lde_height,
            _marker: PhantomData,
        }
    }

    pub const fn folding(&self) -> usize {
        self.folding
    }

    pub fn with_rate_policy(
        mut self,
        policy: WhirRatePolicy,
    ) -> Result<Self, WhirVerifierParamsError> {
        policy.validate(&self.protocol_params)?;
        self.rate_policy = policy;
        Ok(self)
    }

    pub const fn rate_policy(&self) -> WhirRatePolicy {
        self.rate_policy
    }

    fn try_whir_config(
        &self,
        arity: usize,
    ) -> Result<WhirConfig<EF, F, Challenger>, WhirVerifierParamsError> {
        let protocol = self.rate_policy.resolve(arity, &self.protocol_params)?;
        Ok(WhirConfig::new(arity, protocol)?)
    }

    pub fn whir_config(&self, stacked_num_variables: usize) -> WhirConfig<EF, F, Challenger> {
        self.try_whir_config(stacked_num_variables)
            .expect("WHIR parameters are valid for the committed arity")
    }

    pub fn table_shapes(&self, coeffs: &[RowMajorMatrix<F>]) -> Vec<(PaddedArity, usize)> {
        coeffs
            .iter()
            .map(|m| {
                (
                    padded_arity(log2_strict_usize(m.height()), self.folding),
                    m.width(),
                )
            })
            .collect()
    }

    pub fn commit_coefficient_matrices(
        &self,
        domains: Vec<TwoAdicMultiplicativeCoset<F>>,
        coeffs: Vec<RowMajorMatrix<F>>,
    ) -> CommitResult<F, EF, MT, L> {
        let shapes = self.table_shapes(&coeffs);
        let plan = StackedPlan::new_with_strategy(&shapes, L::strategy());
        let stacked_num_variables = plan.num_variables;

        let tables: Vec<Table<F>> = coeffs.iter().map(|m| Table::new(m.transpose())).collect();
        let witness = L::new_witness(tables, self.folding);
        debug_assert_eq!(witness.num_variables(), stacked_num_variables);

        let prover = WhirProver::<EF, F, Dft, SharedMmcs<MT>, Challenger, L>::new(
            self.whir_config(stacked_num_variables),
            self.dft.clone(),
            SharedMmcs(self.mmcs.clone()),
        );

        let mut sink = self.challenger_proto.clone();
        let (commitment, whir) =
            <WhirProver<EF, F, Dft, SharedMmcs<MT>, Challenger, L> as MultilinearPcs<
                EF,
                Challenger,
            >>::commit(&prover, witness, &mut sink)?;

        Ok((
            commitment,
            WhirUniProverData {
                domains,
                coeffs,
                plan,
                stacked_num_variables,
                whir,
            },
        ))
    }

    fn evaluations_on_domain(
        &self,
        prover_data: &WhirUniProverData<F, EF, MT, L>,
        idx: usize,
        domain: TwoAdicMultiplicativeCoset<F>,
    ) -> RowMajorMatrix<F> {
        let coeffs = &prover_data.coeffs[idx];
        let width = coeffs.width();
        assert!(
            domain.size() >= coeffs.height(),
            "requested domain is smaller than the committed matrix"
        );
        let mut values = coeffs.values.clone();
        values.resize(domain.size() * width, F::ZERO);
        self.dft
            .coset_dft_batch(RowMajorMatrix::new(values, width), domain.shift())
            .to_row_major_matrix()
    }

    fn quotient_coefficient_matrices(
        &self,
        evaluations: impl IntoIterator<Item = (TwoAdicMultiplicativeCoset<F>, RowMajorMatrix<F>)>,
        _num_chunks: usize,
    ) -> Vec<RowMajorMatrix<F>> {
        evaluations
            .into_iter()
            .map(|(domain, evals)| {
                debug_assert_eq!(evals.height(), domain.size());
                self.dft.coset_idft_batch(evals, domain.shift())
            })
            .collect()
    }

    fn commit_quotient_coefficient_matrices(
        &self,
        coeffs: Vec<RowMajorMatrix<F>>,
    ) -> CommitResult<F, EF, MT, L> {
        let domains = coeffs
            .iter()
            .map(|m| {
                TwoAdicMultiplicativeCoset::new(F::ONE, log2_strict_usize(m.height()))
                    .expect("chunk height is within the field's two-adicity")
            })
            .collect();
        self.commit_coefficient_matrices(domains, coeffs)
    }

    #[allow(clippy::type_complexity)]
    fn open_rounds(
        &self,
        rounds: Vec<(&WhirUniProverData<F, EF, MT, L>, Vec<Vec<EF>>)>,
        challenger: &mut Challenger,
    ) -> Result<(OpenedValues<EF>, WhirUniProof<F, EF, MT>), WhirConfigError>
    where
        MT: Sync,
        MT::ProverData<RowMajorMatrix<F>>: Send + Sync,
        MT::Commitment: Send,
        MT::MultiProof: Send,
        Challenger: Sync,
        L: Sync,
    {
        let seed = sample_fork_seed::<F, _>(challenger);
        let results: Vec<_> = rounds
            .into_par_iter()
            .enumerate()
            .map(|(round, (data, points_per_matrix))| {
                let mut fork = fork_transcript(&self.challenger_proto, round, &seed);
                self.open_round(data, &points_per_matrix, &mut fork)
            })
            .collect();
        let (opened, proofs): (Vec<_>, Vec<_>) = results
            .into_iter()
            .collect::<Result<Vec<_>, _>>()?
            .into_iter()
            .unzip();
        Ok((opened, WhirUniProof { rounds: proofs }))
    }

    #[allow(clippy::type_complexity)]
    fn open_round(
        &self,
        data: &WhirUniProverData<F, EF, MT, L>,
        points_per_matrix: &[Vec<EF>],
        challenger: &mut Challenger,
    ) -> Result<(Vec<Vec<Vec<EF>>>, PcsProof<F, EF, MT>), WhirConfigError> {
        let shapes: Vec<(usize, usize)> = data
            .coeffs
            .iter()
            .map(|m| (log2_strict_usize(m.height()), m.width()))
            .collect();
        let schedule = round_schedule::<F, EF>(&shapes, points_per_matrix, self.folding);
        debug_assert_eq!(schedule.stacked_num_variables, data.stacked_num_variables);

        let prover = WhirProver::<EF, F, Dft, SharedMmcs<MT>, Challenger, L>::new(
            self.whir_config(data.stacked_num_variables),
            self.dft.clone(),
            SharedMmcs(self.mmcs.clone()),
        );
        if tracing::enabled!(tracing::Level::DEBUG) {
            let security = prover.prescribed_security(&schedule.protocol);
            let native = WhirProver::<EF, F, Dft, SharedMmcs<MT>, Challenger, L>::new(
                WhirConfig::new(data.stacked_num_variables, self.protocol_params.clone())
                    .expect("native rate baseline is valid for the committed arity"),
                self.dft.clone(),
                SharedMmcs(self.mmcs.clone()),
            )
            .prescribed_security(&schedule.protocol);
            tracing::debug!(
                stacked_num_variables = data.stacked_num_variables,
                rate_policy = ?self.rate_policy,
                opening_security_bits = security.as_ref().map(|s| s.error().bits()),
                native_rate_security_bits = native.as_ref().map(|s| s.error().bits()),
                log2_max_candidates = security.as_ref().map(|s| s.log2_max_candidates),
                native_log2_max_candidates = native.as_ref().map(|s| s.log2_max_candidates),
                "WHIR prescribed-opening security",
            );
        }
        let proof = prover.open_at(
            data.whir.clone(),
            &schedule.protocol,
            &schedule.points,
            challenger,
        )?;

        let mut batches = proof.evals.iter();
        let round_values = schedule
            .scales
            .iter()
            .map(|scales| {
                scales
                    .iter()
                    .map(|&scale| {
                        batches
                            .next()
                            .expect("WHIR returned every scheduled opening")
                            .current()
                            .iter()
                            .map(|&value| value * scale)
                            .collect()
                    })
                    .collect()
            })
            .collect();
        debug_assert_eq!(batches.len(), 0);
        let WhirProof {
            initial_ood_answers,
            initial_sumcheck,
            rounds,
            final_poly,
            final_pow_witness,
            final_openings,
            final_sumcheck,
        } = proof.whir;
        let rounds = rounds
            .into_iter()
            .map(|round| WhirRoundProof {
                commitment: round.commitment,
                ood_answers: round.ood_answers,
                pow_witness: round.pow_witness,
                openings: round.openings,
                sumcheck: round.sumcheck,
            })
            .collect();
        Ok((
            round_values,
            PcsProof {
                whir: WhirProof {
                    initial_ood_answers,
                    initial_sumcheck,
                    rounds,
                    final_poly,
                    final_pow_witness,
                    final_openings,
                    final_sumcheck,
                },
                evals: proof.evals,
            },
        ))
    }

    #[allow(clippy::type_complexity)]
    fn verify_rounds(
        &self,
        commitments: Vec<(
            MT::Commitment,
            Vec<(TwoAdicMultiplicativeCoset<F>, Vec<(EF, Vec<EF>)>)>,
        )>,
        proof: &WhirUniProof<F, EF, MT>,
        challenger: &mut Challenger,
    ) -> Result<(), WhirUniPcsError> {
        if proof.rounds.len() != commitments.len() {
            return Err(WhirUniPcsError::RoundCountMismatch {
                expected: commitments.len(),
                actual: proof.rounds.len(),
            });
        }

        for (round, ((_commitment, matrices), round_proof)) in
            commitments.iter().zip(&proof.rounds).enumerate()
        {
            let mut shapes = Vec::with_capacity(matrices.len());
            let mut context_shapes = Vec::with_capacity(matrices.len());
            for (domain, openings) in matrices {
                let width = openings
                    .first()
                    .map(|(_, values)| values.len())
                    .ok_or(WhirUniPcsError::ShapeMismatch { round })?;
                if openings.iter().any(|(_, values)| values.len() != width) {
                    return Err(WhirUniPcsError::ShapeMismatch { round });
                }
                shapes.push((domain.log_size(), width));
                context_shapes.push((domain.log_size(), width, openings.len()));
            }
            let stacked_num_variables = checked_stacked_num_variables(
                shapes
                    .iter()
                    .map(|&(log_height, width)| (padded_arity(log_height, self.folding), width)),
            )
            .map_err(|_| WhirUniPcsError::ShapeMismatch { round })?;
            let config = self
                .try_whir_config(stacked_num_variables)
                .map_err(|_| WhirUniPcsError::ShapeMismatch { round })?;
            validate_whir_pcs_context::<F, EF, MT>(
                round_proof,
                &WhirContextParams::from_native(&config),
                &context_shapes,
            )
            .map_err(|_| WhirUniPcsError::ShapeMismatch { round })?;
        }

        let seed = sample_fork_seed::<F, _>(challenger);
        for (round, ((commitment, matrices), round_proof)) in
            commitments.into_iter().zip(&proof.rounds).enumerate()
        {
            let mut shapes = Vec::with_capacity(matrices.len());
            let mut points_per_matrix = Vec::with_capacity(matrices.len());
            for (domain, openings) in &matrices {
                let width = openings
                    .first()
                    .map(|(_, values)| values.len())
                    .ok_or(WhirUniPcsError::ShapeMismatch { round })?;
                if openings.iter().any(|(_, values)| values.len() != width) {
                    return Err(WhirUniPcsError::ShapeMismatch { round });
                }
                shapes.push((domain.log_size(), width));
                points_per_matrix.push(openings.iter().map(|&(z, _)| z).collect::<Vec<EF>>());
            }

            let stacked_num_variables = checked_stacked_num_variables(
                shapes
                    .iter()
                    .map(|&(log_height, width)| (padded_arity(log_height, self.folding), width)),
            )
            .map_err(|_| WhirUniPcsError::ShapeMismatch { round })?;
            let config = self
                .try_whir_config(stacked_num_variables)
                .map_err(|_| WhirUniPcsError::ShapeMismatch { round })?;
            let schedule = round_schedule::<F, EF>(&shapes, &points_per_matrix, self.folding);
            let prover = WhirProver::<EF, F, Dft, MT, Challenger, L>::new(
                config,
                self.dft.clone(),
                self.mmcs.clone(),
            );
            let mut fork = fork_transcript(&self.challenger_proto, round, &seed);
            let evals = prover
                .verify_at(
                    &commitment,
                    round_proof,
                    &schedule.protocol,
                    &schedule.points,
                    &mut fork,
                )
                .map_err(|source| WhirUniPcsError::Whir { round, source })?;

            let mut batch = 0usize;
            for (m, (_domain, openings)) in matrices.iter().enumerate() {
                for (p, (_zeta, claimed)) in openings.iter().enumerate() {
                    let scale = schedule.scales[m][p];
                    let bound = evals
                        .get(batch)
                        .ok_or(WhirUniPcsError::ShapeMismatch { round })?;
                    if bound.current().len() != claimed.len() {
                        return Err(WhirUniPcsError::ShapeMismatch { round });
                    }
                    for (column, (&bound_value, &claimed_value)) in
                        bound.current().iter().zip(claimed).enumerate()
                    {
                        if bound_value * scale != claimed_value {
                            return Err(WhirUniPcsError::OpeningValueMismatch {
                                round,
                                batch,
                                column,
                            });
                        }
                    }
                    batch += 1;
                }
            }
        }

        Ok(())
    }
}

impl<EF, F, Dft, MT, Challenger, L> p3_commit::Pcs<EF, Challenger>
    for WhirUniPcs<EF, F, Dft, MT, Challenger, L>
where
    F: TwoAdicField + PrimeField64 + Ord,
    EF: ExtensionField<F> + TwoAdicField,
    Dft: TwoAdicSubgroupDft<F> + Clone + Sync,
    MT: Mmcs<F> + Clone + Sync,
    MT::ProverData<RowMajorMatrix<F>>: Clone + Send + Sync,
    MT::Commitment: Serialize + for<'de> Deserialize<'de> + Send,
    MT::MultiProof: Serialize + for<'de> Deserialize<'de> + Send,
    Challenger: FieldChallenger<F>
        + GrindingChallenger<Witness = F>
        + CanSampleUniformBits<F>
        + CanObserve<MT::Commitment>
        + Clone
        + Sync,
    L: Layout<F, EF> + Clone + Sync,
{
    type Domain = TwoAdicMultiplicativeCoset<F>;
    type Commitment = MT::Commitment;
    type ProverData = WhirUniProverData<F, EF, MT, L>;
    type Proof = WhirUniProof<F, EF, MT>;
    type Error = WhirUniPcsError;
    type ProverError = WhirConfigError;

    fn natural_domain_for_degree(&self, degree: usize) -> Self::Domain {
        TwoAdicMultiplicativeCoset::new(F::ONE, log2_strict_usize(degree))
            .expect("degree is within the field's two-adicity")
    }

    fn commit(
        &self,
        evaluations: impl IntoIterator<Item = (Self::Domain, RowMajorMatrix<F>)>,
    ) -> Result<(Self::Commitment, Self::ProverData), Self::ProverError> {
        let mut domains = Vec::new();
        let mut coeffs = Vec::new();
        for (domain, mat) in evaluations {
            debug_assert_eq!(mat.height(), domain.size());
            coeffs.push(self.dft.coset_idft_batch(mat, domain.shift()));
            domains.push(domain);
        }
        self.commit_coefficient_matrices(domains, coeffs)
    }

    fn open(
        &self,
        commitment_data_with_opening_points: Vec<
            p3_commit::OpeningRequest<'_, Self::ProverData, EF>,
        >,
        fiat_shamir_challenger: &mut Challenger,
    ) -> Result<(p3_commit::OpenedValues<EF>, Self::Proof), Self::ProverError> {
        let rounds = commitment_data_with_opening_points
            .into_iter()
            .map(|request| (request.prover_data, request.points))
            .collect();
        self.open_rounds(rounds, fiat_shamir_challenger)
    }

    fn verify(
        &self,
        commitments_with_opening_points: Vec<CommitmentOpening<EF, Self::Commitment, Self::Domain>>,
        proof: &Self::Proof,
        fiat_shamir_challenger: &mut Challenger,
    ) -> Result<(), Self::Error> {
        let rounds = commitments_with_opening_points
            .into_iter()
            .map(|claim| {
                (
                    claim.commitment,
                    claim
                        .matrices
                        .into_iter()
                        .map(|matrix| {
                            (
                                matrix.domain,
                                matrix
                                    .points
                                    .into_iter()
                                    .map(|point| (point.point, point.values))
                                    .collect(),
                            )
                        })
                        .collect(),
                )
            })
            .collect();
        self.verify_rounds(rounds, proof, fiat_shamir_challenger)
    }
}

impl<EF, F, Dft, MT, Challenger, L> p3_commit::UnivariateStarkPcs<EF, Challenger>
    for WhirUniPcs<EF, F, Dft, MT, Challenger, L>
where
    F: TwoAdicField + PrimeField64 + Ord,
    EF: ExtensionField<F> + TwoAdicField,
    Dft: TwoAdicSubgroupDft<F> + Clone + Sync,
    MT: Mmcs<F> + Clone + Sync,
    MT::ProverData<RowMajorMatrix<F>>: Clone + Send + Sync,
    MT::Commitment: Serialize + for<'de> Deserialize<'de> + Send,
    MT::MultiProof: Serialize + for<'de> Deserialize<'de> + Send,
    Challenger: FieldChallenger<F>
        + GrindingChallenger<Witness = F>
        + CanSampleUniformBits<F>
        + CanObserve<MT::Commitment>
        + Clone
        + Sync,
    L: Layout<F, EF> + Clone + Sync,
{
    type EvaluationsOnDomain<'a> = RowMajorMatrix<F>;

    const ZK: bool = false;

    fn log_max_trace_height(&self) -> usize {
        self.log_max_lde_height
    }

    fn log_min_trace_height(&self) -> usize {
        0
    }

    fn get_evaluations_on_domain<'a>(
        &self,
        prover_data: &'a Self::ProverData,
        idx: usize,
        domain: Self::Domain,
    ) -> Self::EvaluationsOnDomain<'a> {
        self.evaluations_on_domain(prover_data, idx, domain)
    }

    fn get_quotient_ldes(
        &self,
        evaluations: impl IntoIterator<Item = (Self::Domain, RowMajorMatrix<F>)>,
        num_chunks: usize,
    ) -> Result<Vec<RowMajorMatrix<F>>, Self::ProverError> {
        Ok(self.quotient_coefficient_matrices(evaluations, num_chunks))
    }

    fn commit_ldes(
        &self,
        ldes: Vec<RowMajorMatrix<F>>,
    ) -> Result<(Self::Commitment, Self::ProverData), Self::ProverError> {
        self.commit_quotient_coefficient_matrices(ldes)
    }
}
