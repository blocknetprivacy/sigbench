use alloc::string::ToString;
use alloc::vec::Vec;
use alloc::{format, vec};

use p3_circuit::{CircuitBuilder, CircuitBuilderError, NonPrimitiveOpId};
use p3_field::coset::TwoAdicMultiplicativeCoset;
use p3_field::{ExtensionField, PrimeField64, TwoAdicField};
use p3_sumcheck::OpeningEvals;
use p3_sumcheck::layout::{LayoutStrategy, Verifier};
use p3_sumcheck::strategy::VariableOrder;

use crate::Target;
use crate::input_contract::whir::WhirContextParams;
use crate::pcs::whir::gadgets::{ConstraintWeightData, eval_powers_combination};
use crate::pcs::whir::params::WhirTranscriptShape;
use crate::pcs::whir::targets::QueryOpeningTargets;
use crate::pcs::whir::uni::bridge::univariate_eq_point_circuit;
use crate::pcs::whir::uni::pcs::{FORK_SEED_LEN, fork_tag, round_schedule};
use crate::pcs::whir::uni::plan::{
    PaddedArity, StackedPlan, canonical_layout_strategy, checked_stacked_num_variables,
    padded_arity,
};
use crate::pcs::whir::uni::recursive_pcs::{DummyChallenger, WhirUniVerifierParams};
use crate::pcs::whir::uni::targets::WhirRoundTargets;
use crate::traits::{ComsWithOpeningsTargets, RecursiveChallenger};
use crate::transcript::{SeedTap, domain_separator_seed};
use crate::verifier::{ObservableCommitment, VerificationError};

pub struct MatrixOpenings<'a> {
    pub log_height: usize,
    pub points: &'a [(Target, Vec<Target>)],
}

#[derive(Clone, Debug)]
pub struct RoundTranscriptSeeds<F> {
    pub virtual_claims: Vec<Vec<F>>,
    pub opening_claims: Vec<Vec<F>>,
    pub whir: Vec<F>,
    pub batching: Vec<F>,
}

pub fn round_transcript_seeds<BF, EF>(
    matrices: &[MatrixOpenings<'_>],
    num_virtual_claims: usize,
    folding: usize,
    whir_shape: &WhirTranscriptShape,
) -> RoundTranscriptSeeds<BF>
where
    BF: PrimeField64 + TwoAdicField,
    EF: ExtensionField<BF>,
{
    round_transcript_seeds_with_strategy::<BF, EF>(
        matrices,
        num_virtual_claims,
        folding,
        whir_shape,
        canonical_layout_strategy(VariableOrder::Prefix),
    )
}

fn round_transcript_seeds_with_strategy<BF, EF>(
    matrices: &[MatrixOpenings<'_>],
    num_virtual_claims: usize,
    folding: usize,
    whir_shape: &WhirTranscriptShape,
    strategy: LayoutStrategy,
) -> RoundTranscriptSeeds<BF>
where
    BF: PrimeField64 + TwoAdicField,
    EF: ExtensionField<BF>,
{
    let shapes: Vec<(usize, usize)> = matrices
        .iter()
        .map(|m| {
            let width = m.points.first().map_or(0, |(_, values)| values.len());
            (m.log_height, width)
        })
        .collect();
    let dummy_points: Vec<Vec<EF>> = matrices
        .iter()
        .map(|m| vec![EF::ONE; m.points.len()])
        .collect();
    let schedule = round_schedule::<BF, EF>(&shapes, &dummy_points, folding);
    let mut layout = Verifier::<BF, EF>::new(&schedule.protocol.table_shapes(), strategy);

    let virtual_claims = (0..num_virtual_claims)
        .map(|_| {
            let mut tap = SeedTap::<BF>::new();
            layout.add_virtual_eval(EF::ZERO, &mut tap);
            tap.seed()
        })
        .collect();
    let opening_claims = schedule
        .protocol
        .iter_openings()
        .zip(&schedule.points)
        .map(|((table_idx, batch), point)| {
            let evals = OpeningEvals::new(
                vec![EF::ZERO; batch.current().len()],
                vec![EF::ZERO; batch.next().len()],
            );
            let mut tap = SeedTap::<BF>::new();
            layout
                .add_claim_at(table_idx, batch, point, &evals, &mut tap)
                .expect("dummy evaluations match the batch they were shaped from");
            tap.seed()
        })
        .collect();
    let mut tap = SeedTap::<BF>::new();
    let _ = layout.batching_challenge(&mut tap);
    let batching = tap.seed();
    let whir = domain_separator_seed(
        &whir_shape
            .for_claims(schedule.protocol.num_openings())
            .domain_separator::<BF, EF>(),
    );

    RoundTranscriptSeeds {
        virtual_claims,
        opening_claims,
        whir,
        batching,
    }
}

pub struct RoundClaims {
    pub constraint: ConstraintWeightData,
    pub claimed_eval: Target,
    pub stacked_num_variables: usize,
}

fn checked_target_pow2(log: usize, label: &str) -> Result<usize, VerificationError> {
    let shift = u32::try_from(log).map_err(|_| {
        VerificationError::InvalidProofShape(format!(
            "WHIR {label} exponent {log} does not fit in u32"
        ))
    })?;
    1usize.checked_shl(shift).ok_or_else(|| {
        VerificationError::InvalidProofShape(format!(
            "WHIR {label} exponent {log} exceeds the usize word width"
        ))
    })
}

fn validate_target_sumcheck(
    rounds: usize,
    pow_bits: usize,
    actual_rounds: usize,
    actual_pow: usize,
    label: &str,
) -> Result<(), VerificationError> {
    if actual_rounds != rounds {
        return Err(VerificationError::InvalidProofShape(format!(
            "WHIR {label} sumcheck expects {rounds} rounds, got {actual_rounds}"
        )));
    }
    if pow_bits > 0 && actual_pow != rounds {
        return Err(VerificationError::InvalidProofShape(format!(
            "WHIR {label} sumcheck expects {rounds} PoW witnesses, got {actual_pow}"
        )));
    }
    Ok(())
}

fn validate_target_query(
    opening: &QueryOpeningTargets,
    extension: bool,
    queries: usize,
    width: usize,
    label: &str,
) -> Result<(), VerificationError> {
    let actual_extension = matches!(opening, QueryOpeningTargets::Extension { .. });
    if actual_extension != extension {
        return Err(VerificationError::InvalidProofShape(format!(
            "WHIR {label} query field variant disagrees with its round"
        )));
    }
    if opening.leaf_values().len() != width {
        return Err(VerificationError::InvalidProofShape(format!(
            "WHIR {label} query leaf expects width {width}, got {}",
            opening.leaf_values().len()
        )));
    }
    if queries == 0 {
        return Err(VerificationError::InvalidProofShape(format!(
            "WHIR {label} query count must be positive"
        )));
    }
    Ok(())
}

fn validate_target_round_shape(
    round: &WhirRoundTargets,
    vp: &WhirContextParams,
    matrices: &[MatrixOpenings<'_>],
    evals: &[Vec<Target>],
) -> Result<(), VerificationError> {
    if matrices.is_empty() || matrices.iter().any(|m| m.points.is_empty()) {
        return Err(VerificationError::InvalidProofShape(
            "WHIR commitment must have nonempty matrices and points".into(),
        ));
    }
    let expected_batches = matrices.iter().try_fold(0usize, |sum, matrix| {
        sum.checked_add(matrix.points.len()).ok_or_else(|| {
            VerificationError::InvalidProofShape("WHIR opening batch count overflows usize".into())
        })
    })?;
    if evals.len() != expected_batches {
        return Err(VerificationError::InvalidProofShape(format!(
            "WHIR opening batch count expects {expected_batches}, got {}",
            evals.len()
        )));
    }
    let expected_widths = matrices
        .iter()
        .flat_map(|matrix| matrix.points.iter().map(|(_, values)| values.len()));
    for (batch, (expected, actual)) in expected_widths.zip(evals).enumerate() {
        if expected == 0 || actual.len() != expected {
            return Err(VerificationError::InvalidProofShape(format!(
                "WHIR opening batch {batch} expects positive width {expected}, got {}",
                actual.len()
            )));
        }
    }
    if round.whir.rounds.len() != vp.rounds.len() {
        return Err(VerificationError::InvalidProofShape(format!(
            "WHIR intermediate round count expects {}, got {}",
            vp.rounds.len(),
            round.whir.rounds.len()
        )));
    }
    if round.whir.initial_ood_answers.len() != vp.commitment_ood_samples {
        return Err(VerificationError::InvalidProofShape(
            "WHIR initial OOD answer count disagrees with canonical parameters".into(),
        ));
    }
    validate_target_sumcheck(
        vp.starting_folding_factor,
        vp.starting_folding_pow_bits,
        round.whir.initial_sumcheck.round_polys.len(),
        round.whir.initial_sumcheck.pow_witnesses.len(),
        "initial",
    )?;
    for (round_idx, (proof_round, params)) in round.whir.rounds.iter().zip(&vp.rounds).enumerate() {
        if proof_round.commitment_cap.is_empty() {
            return Err(VerificationError::InvalidProofShape(format!(
                "WHIR intermediate round {round_idx} has an empty commitment cap"
            )));
        }
        if proof_round.ood_answers.len() != params.ood_samples {
            return Err(VerificationError::InvalidProofShape(format!(
                "WHIR intermediate round {round_idx} OOD count disagrees with canonical parameters"
            )));
        }
        let expected_queries = params
            .num_queries
            .min(params.domain_size >> params.folding_factor);
        if proof_round.queries.len() != expected_queries {
            return Err(VerificationError::InvalidProofShape(format!(
                "WHIR intermediate round {round_idx} query count disagrees with canonical parameters"
            )));
        }
        let width = checked_target_pow2(params.folding_factor, "intermediate leaf")?;
        for query in &proof_round.queries {
            validate_target_query(
                query,
                round_idx != 0,
                expected_queries,
                width,
                "intermediate",
            )?;
        }
        validate_target_sumcheck(
            vp.rounds
                .get(round_idx + 1)
                .map_or(vp.final_folding_factor, |next| next.folding_factor),
            params.folding_pow_bits,
            proof_round.sumcheck.round_polys.len(),
            proof_round.sumcheck.pow_witnesses.len(),
            "intermediate",
        )?;
    }
    let expected_poly = checked_target_pow2(vp.final_poly_num_variables, "final polynomial")?;
    if round.whir.final_poly.len() != expected_poly {
        return Err(VerificationError::InvalidProofShape(
            "WHIR final polynomial length disagrees with canonical parameters".into(),
        ));
    }
    let expected_final_queries = vp
        .final_queries
        .min(vp.final_domain_size >> vp.final_folding_factor);
    if round.whir.final_queries.len() != expected_final_queries {
        return Err(VerificationError::InvalidProofShape(
            "WHIR final query count disagrees with canonical parameters".into(),
        ));
    }
    let final_width = checked_target_pow2(vp.final_folding_factor, "final leaf")?;
    for query in &round.whir.final_queries {
        validate_target_query(
            query,
            !vp.rounds.is_empty(),
            expected_final_queries,
            final_width,
            "final",
        )?;
    }
    match (&round.whir.final_sumcheck, vp.final_sumcheck_rounds) {
        (Some(_), 0) => {}
        (Some(sumcheck), rounds) => validate_target_sumcheck(
            rounds,
            vp.final_folding_pow_bits,
            sumcheck.round_polys.len(),
            sumcheck.pow_witnesses.len(),
            "final",
        )?,
        (None, 0) => {}
        (None, _) => {
            return Err(VerificationError::InvalidProofShape(
                "WHIR final sumcheck is required by canonical parameters".into(),
            ));
        }
    }
    Ok(())
}

pub fn build_round_claims<BF, EF, Ch>(
    circuit: &mut CircuitBuilder<EF>,
    challenger: &mut Ch,
    matrices: &[MatrixOpenings<'_>],
    round_evals: &[Vec<Target>],
    initial_ood_answers: &[Target],
    folding: usize,
    seeds: &RoundTranscriptSeeds<BF>,
) -> Result<RoundClaims, CircuitBuilderError>
where
    BF: PrimeField64,
    EF: ExtensionField<BF>,
    Ch: RecursiveChallenger<BF, EF>,
{
    build_round_claims_with_strategy::<BF, EF, Ch>(
        circuit,
        challenger,
        matrices,
        round_evals,
        initial_ood_answers,
        folding,
        seeds,
        canonical_layout_strategy(VariableOrder::Prefix),
    )
}

#[allow(clippy::too_many_arguments)]
fn build_round_claims_with_strategy<BF, EF, Ch>(
    circuit: &mut CircuitBuilder<EF>,
    challenger: &mut Ch,
    matrices: &[MatrixOpenings<'_>],
    round_evals: &[Vec<Target>],
    initial_ood_answers: &[Target],
    folding: usize,
    seeds: &RoundTranscriptSeeds<BF>,
    strategy: LayoutStrategy,
) -> Result<RoundClaims, CircuitBuilderError>
where
    BF: PrimeField64,
    EF: ExtensionField<BF>,
    Ch: RecursiveChallenger<BF, EF>,
{
    let shapes: Vec<(PaddedArity, usize)> = matrices
        .iter()
        .map(|m| {
            let width = m.points.first().map_or(0, |(_, values)| values.len());
            (padded_arity(m.log_height, folding), width)
        })
        .collect();
    let plan = StackedPlan::new_with_strategy(&shapes, strategy);

    let mut batch = 0usize;
    let mut local_points: Vec<Vec<Vec<Target>>> = Vec::with_capacity(matrices.len());
    for (matrix_idx, m) in matrices.iter().enumerate() {
        let width = shapes[matrix_idx].1;
        let arity = padded_arity(m.log_height, folding).get();
        let mut per_point = Vec::with_capacity(m.points.len());
        for (zeta, claimed) in m.points {
            assert_eq!(
                claimed.len(),
                width,
                "ragged opening width for matrix {matrix_idx}: a point claims {} columns, \
                 but the matrix's declared width (from its first point) is {width}; every \
                 point of one matrix must open the same columns, since `StackedPlan` \
                 allocates exactly one selector per column",
                claimed.len(),
            );
            let (x, scale) = univariate_eq_point_circuit(circuit, *zeta, arity);
            let bound = &round_evals[batch];
            assert_eq!(bound.len(), claimed.len(), "opening width mismatch");
            for (&b, &c) in bound.iter().zip(claimed) {
                let rescaled = circuit.mul(b, scale);
                circuit.connect(rescaled, c);
            }
            per_point.push(x);
            batch += 1;
        }
        local_points.push(per_point);
    }

    assert_eq!(seeds.virtual_claims.len(), initial_ood_answers.len());
    assert_eq!(seeds.opening_claims.len(), round_evals.len());
    let mut ood_points: Vec<Vec<Target>> = Vec::with_capacity(initial_ood_answers.len());
    for (&answer, seed) in initial_ood_answers.iter().zip(&seeds.virtual_claims) {
        challenger.observe_seed(circuit, seed);
        let univariate = challenger.sample_ext(circuit);
        ood_points.push(crate::pcs::whir::gadgets::expand_from_univariate(
            circuit,
            univariate,
            plan.num_variables,
        ));
        challenger.observe_ext(circuit, answer);
    }

    for (batch_values, seed) in round_evals.iter().zip(&seeds.opening_claims) {
        challenger.observe_seed(circuit, seed);
        challenger.observe_ext_slice(circuit, batch_values);
    }

    challenger.observe_seed(circuit, &seeds.whir);
    challenger.observe_seed(circuit, &seeds.batching);
    let alpha = challenger.sample_ext(circuit);

    let zero = circuit.define_const(EF::ZERO);
    let one = circuit.define_const(EF::ONE);
    let mut ordered_values: Vec<Target> = Vec::new();
    let mut eq_points: Vec<Vec<Target>> = Vec::new();
    for placement in &plan.placements {
        let m = placement.table_idx;
        let first_batch = round_evals_offset(matrices, m);
        for (point_idx, local) in local_points[m].iter().enumerate() {
            let batch_of_matrix = first_batch + point_idx;
            for (col, selector) in placement.selectors.iter().enumerate() {
                ordered_values.push(round_evals[batch_of_matrix][col]);
                eq_points.push(selector.lift_with_strategy(local, zero, one, strategy));
            }
        }
    }
    for (&answer, point) in initial_ood_answers.iter().zip(ood_points) {
        ordered_values.push(answer);
        eq_points.push(point);
    }

    let claimed_eval = eval_powers_combination(circuit, &ordered_values, alpha);

    Ok(RoundClaims {
        constraint: ConstraintWeightData {
            num_variables: plan.num_variables,
            eq_points,
            sel_scalars: Vec::new(),
            gamma: alpha,
            initial_power: 0,
        },
        claimed_eval,
        stacked_num_variables: plan.num_variables,
    })
}

fn round_evals_offset(matrices: &[MatrixOpenings<'_>], m: usize) -> usize {
    matrices[..m].iter().map(|x| x.points.len()).sum()
}

fn stacked_num_variables(
    matrices: &[MatrixOpenings<'_>],
    folding: usize,
) -> Result<usize, VerificationError> {
    let shapes: Vec<(PaddedArity, usize)> = matrices
        .iter()
        .map(|m| {
            let width = m.points.first().map_or(0, |(_, values)| values.len());
            (padded_arity(m.log_height, folding), width)
        })
        .collect();
    checked_stacked_num_variables(shapes.iter().copied())
        .map_err(|error| VerificationError::InvalidProofShape(error.to_string()))
}

pub fn verify_whir_uni_circuit<BF, EF, Ch, Comm>(
    circuit: &mut CircuitBuilder<EF>,
    challenger: &mut Ch,
    params: &WhirUniVerifierParams<BF>,
    commitments_with_opening_points: &ComsWithOpeningsTargets<Comm, TwoAdicMultiplicativeCoset<BF>>,
    rounds: &[WhirRoundTargets],
) -> Result<Vec<NonPrimitiveOpId>, VerificationError>
where
    BF: PrimeField64 + TwoAdicField,
    EF: ExtensionField<BF> + TwoAdicField,
    Ch: RecursiveChallenger<BF, EF>,
    Comm: ObservableCommitment,
{
    if rounds.len() != commitments_with_opening_points.len() {
        return Err(VerificationError::InvalidProofShape(format!(
            "WHIR proof carries {} arguments for {} commitments",
            rounds.len(),
            commitments_with_opening_points.len()
        )));
    }

    let mut verified_params = Vec::with_capacity(rounds.len());
    for ((_commitment, matrices), round) in commitments_with_opening_points.iter().zip(rounds) {
        let openings: Vec<MatrixOpenings<'_>> = matrices
            .iter()
            .map(|(domain, points)| MatrixOpenings {
                log_height: domain.log_size(),
                points: points.as_slice(),
            })
            .collect();

        let stacked_num_variables = stacked_num_variables(&openings, params.folding())?;
        let vp = params.round_params::<EF, DummyChallenger<BF>>(stacked_num_variables)?;

        let context_params = WhirContextParams::from_recursive(&vp);
        validate_target_round_shape(round, &context_params, &openings, &round.evals)?;
        verified_params.push(vp);
    }

    let strategy = canonical_layout_strategy(params.variable_order());
    let fork_seed: Vec<Target> = (0..FORK_SEED_LEN)
        .map(|_| challenger.sample(circuit))
        .collect();
    let mut mmcs_checks = Vec::new();
    for (round_idx, (((commitment, matrices), round), vp)) in commitments_with_opening_points
        .iter()
        .zip(rounds)
        .zip(&verified_params)
        .enumerate()
    {
        let openings: Vec<MatrixOpenings<'_>> = matrices
            .iter()
            .map(|(domain, points)| MatrixOpenings {
                log_height: domain.log_size(),
                points: points.as_slice(),
            })
            .collect();
        let stacked_num_variables = stacked_num_variables(&openings, params.folding())?;

        let seeds = round_transcript_seeds_with_strategy::<BF, EF>(
            &openings,
            round.whir.initial_ood_answers.len(),
            params.folding(),
            vp.transcript_shape(),
            strategy,
        );

        challenger.clear(circuit);
        challenger.observe_seed(circuit, &fork_tag::<BF>(round_idx));
        challenger.observe_slice(circuit, &fork_seed);

        #[cfg(test)]
        crate::pcs::whir::uni::acceptance_probe::target_challenger();
        let claims = build_round_claims_with_strategy::<BF, EF, Ch>(
            circuit,
            challenger,
            &openings,
            &round.evals,
            &round.whir.initial_ood_answers,
            params.folding(),
            &seeds,
            strategy,
        )
        .map_err(|e| VerificationError::InvalidProofShape(format!("{e:?}")))?;
        debug_assert_eq!(claims.stacked_num_variables, stacked_num_variables);

        let lifted = commitment.to_observation_targets();
        let cap: Vec<Vec<Target>> = crate::pcs::fri::commitment_cap_rows_from_lifted::<BF, EF>(
            circuit,
            params.permutation_config(),
            &lifted,
        );

        let round_checks = crate::pcs::whir::verifier::verify_whir_circuit_deferred::<BF, EF, Ch>(
            circuit,
            challenger,
            vp,
            &round.whir,
            &cap,
            claims.constraint,
            claims.claimed_eval,
        )
        .map_err(|e| VerificationError::InvalidProofShape(format!("{e:?}")))?;
        mmcs_checks.extend(round_checks);
    }

    crate::pcs::whir::verifier::verify_deferred_whir_mmcs::<BF, EF>(circuit, mmcs_checks)
        .map_err(|e| VerificationError::InvalidProofShape(format!("{e:?}")))
}
