use alloc::format;
use alloc::string::ToString;
use alloc::vec::Vec;

use p3_commit::Mmcs;
use p3_field::{BasedVectorSpace, ExtensionField, Field, TwoAdicField};
use p3_merkle_tree::{MerkleCap, PrunedMerklePaths};
use p3_sumcheck::SumcheckData;
use p3_whir::parameters::WhirConfig;
use p3_whir::pcs::proof::{PcsProof, QueryOpenings};

use super::{FriOpeningLayout, MerkleCapShape};
use crate::PermConfig;
use crate::pcs::whir::params::WhirVerifierParams;
use crate::pcs::whir::uni::WhirUniVerifierParams;
use crate::pcs::whir::uni::pcs::WhirUniProof;
use crate::traits::CheckedRecursive;
use crate::verifier::{InputResourceUsage, VerificationError, VerifierLimits};

#[derive(Clone, PartialEq, Eq)]
pub struct SumcheckShape {
    pub(crate) polynomial_evaluations: usize,
    pub(crate) pow_witnesses: usize,
}

#[derive(Clone, PartialEq, Eq)]
pub enum QueryOpeningsShape {
    Base { rows: Vec<usize> },
    Extension { rows: Vec<usize> },
}

#[derive(Clone, PartialEq, Eq)]
pub struct WhirStepShape<C> {
    pub(crate) commitment: Option<C>,
    pub(crate) ood_answers: usize,
    pub(crate) openings: QueryOpeningsShape,
    pub(crate) sumcheck: SumcheckShape,
}

#[derive(Clone, PartialEq, Eq)]
pub struct WhirShape<C> {
    pub(crate) initial_ood_answers: usize,
    pub(crate) initial_sumcheck: SumcheckShape,
    pub(crate) rounds: Vec<WhirStepShape<C>>,
    pub(crate) final_poly: Option<usize>,
    pub(crate) final_openings: QueryOpeningsShape,
    pub(crate) final_sumcheck: Option<SumcheckShape>,
}

#[derive(Clone, PartialEq, Eq)]
pub struct OpeningBatchShape {
    pub(crate) current: usize,
    pub(crate) next: usize,
}

#[derive(Clone, PartialEq, Eq)]
pub struct WhirPcsRoundShape<C> {
    pub(crate) evals: Vec<OpeningBatchShape>,
    pub(crate) whir: WhirShape<C>,
}

#[derive(Clone, PartialEq, Eq)]
pub struct WhirUniShape<C> {
    pub(crate) rounds: Vec<WhirPcsRoundShape<C>>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct WhirContextShape {
    pub(crate) stacked_num_variables: usize,
    pub(crate) opening_batches: usize,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct WhirRoundContext {
    pub(crate) ood_samples: usize,
    pub(crate) num_queries: usize,
    pub(crate) folding_pow_bits: usize,
    pub(crate) folding_factor: usize,
    pub(crate) domain_size: usize,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct WhirContextParams {
    pub(crate) num_variables: usize,
    pub(crate) commitment_ood_samples: usize,
    pub(crate) starting_folding_factor: usize,
    pub(crate) starting_folding_pow_bits: usize,
    pub(crate) rounds: Vec<WhirRoundContext>,
    pub(crate) final_poly_num_variables: usize,
    pub(crate) final_queries: usize,
    pub(crate) final_sumcheck_rounds: usize,
    pub(crate) final_folding_factor: usize,
    pub(crate) final_folding_pow_bits: usize,
    pub(crate) final_domain_size: usize,
}

#[derive(Clone, PartialEq, Eq)]
pub struct ValidatedWhirContext<F> {
    pub(crate) layout: super::stark_layout::NativeStarkLayout<'static>,
    pub(crate) permutation: PermConfig,
    pub(crate) canonical: Vec<WhirContextParams>,
    pub(crate) verifier_params: Vec<WhirVerifierParams<F>>,
    pub(crate) outside_cap_roots: Vec<usize>,
    pub(crate) shape: WhirUniShape<MerkleCapShape>,
    pub(crate) _field: core::marker::PhantomData<F>,
}

impl<F> ValidatedWhirContext<F> {
    pub(crate) const fn layout(&self) -> &super::stark_layout::NativeStarkLayout<'static> {
        &self.layout
    }

    pub(crate) const fn permutation(&self) -> PermConfig {
        self.permutation
    }

    pub(crate) fn canonical(&self) -> &[WhirContextParams] {
        &self.canonical
    }

    pub(crate) fn verifier_params(&self) -> &[WhirVerifierParams<F>] {
        &self.verifier_params
    }
}

pub trait CheckedWhirOpening<F, EF, C>: CheckedRecursive<EF>
where
    F: Field,
    EF: ExtensionField<F>,
    C: CheckedRecursive<EF>,
{
    fn check_whir_resources(
        input: &Self::Input,
        limits: &VerifierLimits,
    ) -> Result<InputResourceUsage, VerificationError>;

    fn validate_whir_context(
        input: &Self::Input,
        params: &WhirUniVerifierParams<F>,
        layout: FriOpeningLayout<'_>,
        caps: &[&C::Input],
    ) -> Result<ValidatedWhirContext<F>, VerificationError>;

    fn validate_whir_replacement(
        input: &Self::Input,
        expected: &ValidatedWhirContext<F>,
        layout: FriOpeningLayout<'_>,
        caps: &[&C::Input],
    ) -> Result<(), VerificationError>;
}

pub(crate) trait WhirResourceProof {
    fn compressed_frontier_hashes(&self) -> usize;
}

impl<F, const DIGEST_ELEMS: usize> WhirResourceProof for PrunedMerklePaths<F, DIGEST_ELEMS> {
    fn compressed_frontier_hashes(&self) -> usize {
        self.sibling_hashes.len()
    }
}

fn checked_product(
    left: usize,
    right: usize,
    component: &'static str,
) -> Result<usize, VerificationError> {
    left.checked_mul(right)
        .ok_or(VerificationError::ResourceArithmeticOverflow { component })
}

fn add_sumcheck_resources<F: Field, EF: Field>(
    usage: &mut InputResourceUsage,
    limits: &VerifierLimits,
    data: &SumcheckData<F, EF>,
) -> Result<(), VerificationError> {
    let evaluations = checked_product(data.polynomial_evaluations().len(), 2, "scalar elements")?;
    usage.add_scalar_elements(limits, evaluations)?;
    usage.add_scalar_elements(limits, data.pow_witnesses.len())
}

fn add_query_resources<F, EF, P>(
    usage: &mut InputResourceUsage,
    limits: &VerifierLimits,
    openings: &QueryOpenings<F, EF, P>,
) -> Result<(), VerificationError>
where
    P: WhirResourceProof,
{
    match openings {
        QueryOpenings::Base(opening) => {
            usage.add_query_round(limits, opening.rows.len())?;
            usage.add_metadata_entries(limits, opening.rows.len())?;
            for row in &opening.rows {
                usage.check_matrix_width(limits, row.len())?;
                usage.add_scalar_elements(limits, row.len())?;
            }
            usage.add_compressed_frontier_hashes(limits, opening.proof.compressed_frontier_hashes())
        }
        QueryOpenings::Extension(opening) => {
            usage.add_query_round(limits, opening.rows.len())?;
            usage.add_metadata_entries(limits, opening.rows.len())?;
            for row in &opening.rows {
                usage.check_matrix_width(limits, row.len())?;
                usage.add_scalar_elements(limits, row.len())?;
            }
            usage.add_compressed_frontier_hashes(limits, opening.proof.compressed_frontier_hashes())
        }
    }
}

pub(crate) fn check_whir_resource_limits<F, EF, MT, const DIGEST_ELEMS: usize>(
    input: &WhirUniProof<F, EF, MT>,
    limits: &VerifierLimits,
) -> Result<InputResourceUsage, VerificationError>
where
    F: Field,
    EF: ExtensionField<F> + BasedVectorSpace<F>,
    MT: Mmcs<F, Commitment = MerkleCap<F, [F; DIGEST_ELEMS]>>,
    MT::MultiProof: WhirResourceProof,
{
    let mut usage = InputResourceUsage::default();
    usage.add_rounds(limits, input.rounds.len())?;
    for argument in &input.rounds {
        usage.add_metadata_entries(limits, argument.evals.len())?;
        let opening_width_sum = argument.evals.iter().try_fold(0usize, |sum, batch| {
            InputResourceUsage::checked_add(
                "WHIR opening batch widths",
                sum,
                batch.current().len().max(batch.next().len()),
            )
        })?;
        usage.max_whir_opening_width_sum = usage.max_whir_opening_width_sum.max(opening_width_sum);
        for batch in &argument.evals {
            usage.check_matrix_width(limits, batch.current().len())?;
            usage.check_matrix_width(limits, batch.next().len())?;
            usage.add_scalar_elements(limits, batch.current().len())?;
            usage.add_scalar_elements(limits, batch.next().len())?;
        }

        let proof = &argument.whir;
        usage.check_matrix_width(limits, proof.initial_ood_answers.len())?;
        usage.add_scalar_elements(limits, proof.initial_ood_answers.len())?;
        add_sumcheck_resources(&mut usage, limits, &proof.initial_sumcheck)?;
        usage.add_rounds(limits, proof.rounds.len())?;
        for round in &proof.rounds {
            if let Some(cap) = &round.commitment {
                let roots = cap.num_roots();
                usage.add_cap_roots(limits, roots)?;
                let packed = checked_product(
                    roots,
                    crate::pcs::whir::uni::targets::packed_digest_len(DIGEST_ELEMS, EF::DIMENSION),
                    "scalar elements",
                )?;
                usage.add_scalar_elements(limits, packed)?;
            }
            usage.check_matrix_width(limits, round.ood_answers.len())?;
            usage.add_scalar_elements(limits, round.ood_answers.len())?;
            usage.add_scalar_elements(limits, 1)?;
            add_query_resources(&mut usage, limits, &round.openings)?;
            add_sumcheck_resources(&mut usage, limits, &round.sumcheck)?;
        }

        if let Some(final_poly) = &proof.final_poly {
            usage.add_final_poly_evaluations(limits, final_poly.num_evals())?;
            usage.add_scalar_elements(limits, final_poly.num_evals())?;
        }
        usage.add_scalar_elements(limits, 1)?;
        add_query_resources(&mut usage, limits, &proof.final_openings)?;
        if let Some(final_sumcheck) = &proof.final_sumcheck {
            add_sumcheck_resources(&mut usage, limits, final_sumcheck)?;
        }
    }
    usage.check(limits)?;
    Ok(usage)
}

impl WhirContextParams {
    pub(crate) fn from_recursive<F: Field>(params: &WhirVerifierParams<F>) -> Self {
        Self {
            num_variables: params.num_variables(),
            commitment_ood_samples: params.commitment_ood_samples(),
            starting_folding_factor: params.round_folding_factor(0),
            starting_folding_pow_bits: params.starting_folding_pow_bits(),
            rounds: params
                .round_params()
                .iter()
                .map(|round| WhirRoundContext {
                    ood_samples: round.ood_samples(),
                    num_queries: round.num_queries(),
                    folding_pow_bits: round.folding_pow_bits(),
                    folding_factor: round.folding_factor(),
                    domain_size: round.domain_size(),
                })
                .collect(),
            final_poly_num_variables: params.final_poly_num_variables(),
            final_queries: params.final_queries(),
            final_sumcheck_rounds: params.final_sumcheck_rounds(),
            final_folding_factor: params.final_folding_factor(),
            final_folding_pow_bits: params.final_folding_pow_bits(),
            final_domain_size: params.final_domain_size(),
        }
    }
}

impl WhirContextParams {
    pub(crate) fn from_native<EF, F, Ch>(config: &WhirConfig<EF, F, Ch>) -> Self
    where
        F: TwoAdicField,
        EF: ExtensionField<F> + TwoAdicField,
        Ch: p3_challenger::FieldChallenger<F> + p3_challenger::GrindingChallenger<Witness = F>,
    {
        let final_config = config.final_round_config();
        Self {
            num_variables: config.num_variables(),
            commitment_ood_samples: config.commitment_ood_samples(),
            starting_folding_factor: config.round_folding_factor(0),
            starting_folding_pow_bits: config.starting_folding_pow_bits(),
            rounds: config
                .round_parameters()
                .iter()
                .map(|round| WhirRoundContext {
                    ood_samples: round.ood_samples,
                    num_queries: round.num_queries,
                    folding_pow_bits: round.folding_pow_bits,
                    folding_factor: round.folding_factor,
                    domain_size: round.domain_size,
                })
                .collect(),
            final_poly_num_variables: final_config.num_variables,
            final_queries: config.terminal().num_queries,
            final_sumcheck_rounds: config.final_sumcheck_rounds(),
            final_folding_factor: final_config.folding_factor,
            final_folding_pow_bits: config.final_folding_pow_bits(),
            final_domain_size: final_config.domain_size,
        }
    }
}

fn checked_pow2(log: usize, what: &'static str) -> Result<usize, VerificationError> {
    let shift = u32::try_from(log).map_err(|_| {
        VerificationError::InvalidProofShape(format!(
            "WHIR {what} exponent {log} does not fit in u32"
        ))
    })?;
    1usize.checked_shl(shift).ok_or_else(|| {
        VerificationError::InvalidProofShape(format!(
            "WHIR {what} exponent {log} exceeds the usize word width"
        ))
    })
}

fn validate_sumcheck<F, EF>(
    sumcheck: &p3_sumcheck::SumcheckData<F, EF>,
    expected_rounds: usize,
    pow_bits: usize,
    label: &str,
) -> Result<(), VerificationError> {
    if sumcheck.polynomial_evaluations.len() != expected_rounds {
        return Err(VerificationError::InvalidProofShape(format!(
            "WHIR {label} sumcheck expects {expected_rounds} rounds, got {}",
            sumcheck.polynomial_evaluations.len()
        )));
    }
    if pow_bits > 0 && sumcheck.pow_witnesses.len() != expected_rounds {
        return Err(VerificationError::InvalidProofShape(format!(
            "WHIR {label} sumcheck expects {expected_rounds} PoW witnesses, got {}",
            sumcheck.pow_witnesses.len()
        )));
    }
    Ok(())
}

fn validate_query_rows<T>(
    rows: &[Vec<T>],
    expected_queries: usize,
    expected_width: usize,
    label: &str,
) -> Result<(), VerificationError> {
    if rows.len() != expected_queries {
        return Err(VerificationError::InvalidProofShape(format!(
            "WHIR {label} expects {expected_queries} query rows, got {}",
            rows.len()
        )));
    }
    if let Some((query, row)) = rows
        .iter()
        .enumerate()
        .find(|(_, row)| row.len() != expected_width)
    {
        return Err(VerificationError::InvalidProofShape(format!(
            "WHIR {label} query {query} expects width {expected_width}, got {}",
            row.len()
        )));
    }
    Ok(())
}

fn validate_query_openings<F, EF, P>(
    openings: &QueryOpenings<F, EF, P>,
    expected_extension: bool,
    expected_queries: usize,
    expected_width: usize,
    label: &str,
) -> Result<(), VerificationError> {
    let is_extension = matches!(openings, QueryOpenings::Extension(_));
    if is_extension != expected_extension {
        return Err(VerificationError::InvalidProofShape(format!(
            "WHIR {label} query field variant disagrees with its round"
        )));
    }
    match openings {
        QueryOpenings::Base(opening) => {
            validate_query_rows(&opening.rows, expected_queries, expected_width, label)
        }
        QueryOpenings::Extension(opening) => {
            validate_query_rows(&opening.rows, expected_queries, expected_width, label)
        }
    }
}

pub(crate) fn validate_whir_pcs_context<F, EF, MT>(
    proof: &PcsProof<F, EF, MT>,
    params: &WhirContextParams,
    matrix_shapes: &[(usize, usize, usize)],
) -> Result<WhirContextShape, VerificationError>
where
    F: Field,
    EF: ExtensionField<F> + BasedVectorSpace<F>,
    MT: Mmcs<F>,
{
    validate_whir_pcs_context_iter::<F, EF, MT, _>(proof, params, matrix_shapes.iter().copied())
}

pub(crate) fn validate_whir_pcs_context_iter<F, EF, MT, I>(
    proof: &PcsProof<F, EF, MT>,
    params: &WhirContextParams,
    matrix_shapes: I,
) -> Result<WhirContextShape, VerificationError>
where
    F: Field,
    EF: ExtensionField<F> + BasedVectorSpace<F>,
    MT: Mmcs<F>,
    I: Iterator<Item = (usize, usize, usize)> + Clone,
{
    if matrix_shapes.clone().next().is_none() {
        return Err(VerificationError::InvalidProofShape(
            "WHIR commitment must contain at least one matrix".into(),
        ));
    }
    if matrix_shapes
        .clone()
        .any(|(_, width, points)| width == 0 || points == 0)
    {
        return Err(VerificationError::InvalidProofShape(
            "WHIR matrices require positive widths and point counts".into(),
        ));
    }
    let expected_batches = matrix_shapes
        .clone()
        .try_fold(0usize, |sum, (_, _, points)| {
            sum.checked_add(points).ok_or_else(|| {
                VerificationError::InvalidProofShape(
                    "WHIR opening batch count overflows usize".into(),
                )
            })
        })?;
    if proof.evals.len() != expected_batches {
        return Err(VerificationError::InvalidProofShape(
            "WHIR opening batch count disagrees with the statement layout".into(),
        ));
    }
    let batch_widths = matrix_shapes
        .clone()
        .flat_map(|(_, width, points)| core::iter::repeat_n(width, points));
    for (batch, (width, eval)) in batch_widths.zip(proof.evals.iter()).enumerate() {
        if eval.current().len() != width || !eval.next().is_empty() {
            return Err(VerificationError::InvalidProofShape(format!(
                "WHIR opening batch {batch} has an invalid current/next width"
            )));
        }
    }

    let shapes = matrix_shapes.map(|(log_height, width, _)| {
        (
            crate::pcs::whir::uni::plan::padded_arity(log_height, params.starting_folding_factor),
            width,
        )
    });
    let stacked_num_variables = crate::pcs::whir::uni::plan::checked_stacked_num_variables(shapes)
        .map_err(|error| VerificationError::InvalidProofShape(error.to_string()))?;
    if stacked_num_variables != params.num_variables {
        return Err(VerificationError::InvalidProofShape(format!(
            "WHIR stacked arity {stacked_num_variables} disagrees with canonical {}",
            params.num_variables
        )));
    }
    if proof.whir.rounds.len() != params.rounds.len() {
        return Err(VerificationError::InvalidProofShape(format!(
            "WHIR intermediate round count expects {}, got {}",
            params.rounds.len(),
            proof.whir.rounds.len()
        )));
    }
    if proof.whir.initial_ood_answers.len() != params.commitment_ood_samples {
        return Err(VerificationError::InvalidProofShape(
            "WHIR initial OOD answer count disagrees with canonical parameters".into(),
        ));
    }
    validate_sumcheck(
        &proof.whir.initial_sumcheck,
        params.starting_folding_factor,
        params.starting_folding_pow_bits,
        "initial",
    )?;

    for (round, (step, expected)) in proof
        .whir
        .rounds
        .iter()
        .zip(params.rounds.iter())
        .enumerate()
    {
        let _cap = step.commitment.as_ref().ok_or_else(|| {
            VerificationError::InvalidProofShape(format!(
                "WHIR intermediate round {round} is missing its commitment"
            ))
        })?;
        if step.ood_answers.len() != expected.ood_samples {
            return Err(VerificationError::InvalidProofShape(format!(
                "WHIR intermediate round {round} OOD count disagrees with canonical parameters"
            )));
        }
        let width = checked_pow2(expected.folding_factor, "intermediate leaf")?;
        let expected_queries = expected
            .num_queries
            .min(expected.domain_size >> expected.folding_factor);
        validate_query_openings(
            &step.openings,
            round != 0,
            expected_queries,
            width,
            "intermediate",
        )?;
        validate_sumcheck(
            &step.sumcheck,
            params
                .rounds
                .get(round + 1)
                .map_or(params.final_folding_factor, |next| next.folding_factor),
            expected.folding_pow_bits,
            "intermediate",
        )?;
    }

    let final_poly = proof.whir.final_poly.as_ref().ok_or_else(|| {
        VerificationError::InvalidProofShape("WHIR proof is missing its final polynomial".into())
    })?;
    let expected_final_poly = checked_pow2(params.final_poly_num_variables, "final polynomial")?;
    if final_poly.num_evals() != expected_final_poly {
        return Err(VerificationError::InvalidProofShape(
            "WHIR final polynomial length disagrees with canonical parameters".into(),
        ));
    }
    let final_width = checked_pow2(params.final_folding_factor, "final leaf")?;
    let final_queries = params
        .final_queries
        .min(params.final_domain_size >> params.final_folding_factor);
    validate_query_openings(
        &proof.whir.final_openings,
        !params.rounds.is_empty(),
        final_queries,
        final_width,
        "final",
    )?;
    match (&proof.whir.final_sumcheck, params.final_sumcheck_rounds) {
        (Some(_), 0) => {}
        (Some(sumcheck), rounds) => {
            validate_sumcheck(sumcheck, rounds, params.final_folding_pow_bits, "final")?;
        }
        (None, 0) => {}
        (None, _) => {
            return Err(VerificationError::InvalidProofShape(
                "WHIR final sumcheck is required by canonical parameters".into(),
            ));
        }
    }

    Ok(WhirContextShape {
        stacked_num_variables,
        opening_batches: proof.evals.len(),
    })
}

fn sumcheck_shape<F, EF>(input: &SumcheckData<F, EF>) -> SumcheckShape {
    SumcheckShape {
        polynomial_evaluations: input.polynomial_evaluations().len(),
        pow_witnesses: input.pow_witnesses.len(),
    }
}

fn query_shape<F, EF, P>(input: &QueryOpenings<F, EF, P>) -> QueryOpeningsShape {
    match input {
        QueryOpenings::Base(opening) => QueryOpeningsShape::Base {
            rows: opening.rows.iter().map(Vec::len).collect(),
        },
        QueryOpenings::Extension(opening) => QueryOpeningsShape::Extension {
            rows: opening.rows.iter().map(Vec::len).collect(),
        },
    }
}


pub(crate) fn validate_whir_uni_input<F, EF, MT, const DIGEST_ELEMS: usize>(
    input: &WhirUniProof<F, EF, MT>,
) -> Result<(), VerificationError>
where
    F: Field,
    EF: ExtensionField<F> + BasedVectorSpace<F>,
    MT: Mmcs<F, Commitment = MerkleCap<F, [F; DIGEST_ELEMS]>>,
{
    for round in &input.rounds {
        for batch in &round.evals {
            if !batch.next().is_empty() {
                return Err(VerificationError::InvalidProofShape(
                    "WHIR uni openings use no next group".into(),
                ));
            }
        }
        for step in &round.whir.rounds {
            let commitment = step.commitment.as_ref().ok_or_else(|| {
                VerificationError::InvalidProofShape(
                    "WHIR proof missing intermediate round commitment".into(),
                )
            })?;
            let roots = commitment.num_roots();
            if roots == 0 || !roots.is_power_of_two() {
                return Err(VerificationError::InvalidProofShape(
                    "WHIR commitment cap must have a non-empty power-of-two root count".into(),
                ));
            }
        }
        if round.whir.final_poly.is_none() {
            return Err(VerificationError::InvalidProofShape(
                "WHIR proof missing final polynomial".into(),
            ));
        }
    }
    Ok(())
}

pub(crate) fn capture_whir_uni_shape<F, EF, MT, const DIGEST_ELEMS: usize>(
    input: &WhirUniProof<F, EF, MT>,
) -> Result<WhirUniShape<MerkleCapShape>, VerificationError>
where
    F: Field,
    EF: ExtensionField<F> + BasedVectorSpace<F>,
    MT: Mmcs<F, Commitment = MerkleCap<F, [F; DIGEST_ELEMS]>>,
{
    validate_whir_uni_input::<F, EF, MT, DIGEST_ELEMS>(input)?;

    let rounds = input
        .rounds
        .iter()
        .map(|round| {
            let evals = round
                .evals
                .iter()
                .map(|batch| {
                    if !batch.next().is_empty() {
                        return Err(VerificationError::InvalidProofShape(
                            "WHIR uni openings use no next group".into(),
                        ));
                    }
                    Ok(OpeningBatchShape {
                        current: batch.current().len(),
                        next: batch.next().len(),
                    })
                })
                .collect::<Result<Vec<_>, _>>()?;

            let whir = &round.whir;
            let rounds = whir
                .rounds
                .iter()
                .map(|step| {
                    let commitment = step.commitment.as_ref().ok_or_else(|| {
                        VerificationError::InvalidProofShape(
                            "WHIR proof missing intermediate round commitment".into(),
                        )
                    })?;
                    Ok(WhirStepShape {
                        commitment: Some(MerkleCapShape {
                            roots: commitment.num_roots(),
                        }),
                        ood_answers: step.ood_answers.len(),
                        openings: query_shape(&step.openings),
                        sumcheck: sumcheck_shape(&step.sumcheck),
                    })
                })
                .collect::<Result<Vec<_>, VerificationError>>()?;
            let final_poly = whir.final_poly.as_ref().ok_or_else(|| {
                VerificationError::InvalidProofShape("WHIR proof missing final polynomial".into())
            })?;

            Ok(WhirPcsRoundShape {
                evals,
                whir: WhirShape {
                    initial_ood_answers: whir.initial_ood_answers.len(),
                    initial_sumcheck: sumcheck_shape(&whir.initial_sumcheck),
                    rounds,
                    final_poly: Some(final_poly.num_evals()),
                    final_openings: query_shape(&whir.final_openings),
                    final_sumcheck: whir.final_sumcheck.as_ref().map(sumcheck_shape),
                },
            })
        })
        .collect::<Result<Vec<_>, VerificationError>>()?;

    Ok(WhirUniShape { rounds })
}
