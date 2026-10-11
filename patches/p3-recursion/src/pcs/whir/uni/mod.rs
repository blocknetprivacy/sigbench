pub mod bridge;
pub mod circuit;
pub mod pcs;
pub mod plan;
mod prover_mmcs;
mod rate;
pub mod recursion_data;
pub mod recursive_pcs;
pub mod targets;

use alloc::format;
use alloc::string::ToString;
use alloc::vec::Vec;

pub use bridge::{univariate_eq_point, univariate_eq_point_circuit};
pub use circuit::{MatrixOpenings, RoundClaims, build_round_claims};
use p3_challenger::{CanObserve, CanSampleUniformBits, FieldChallenger, GrindingChallenger};
use p3_commit::{Mmcs, PolynomialSpace};
use p3_field::{Algebra, PrimeCharacteristicRing, PrimeField64, TwoAdicField};
use p3_sumcheck::layout::Verifier;
use p3_sumcheck::strategy::Basis;
pub use p3_sumcheck::strategy::VariableOrder;
use p3_sumcheck::verify_final_sumcheck_rounds;
use p3_uni_stark::{StarkGenericConfig, SymbolicExpression, SymbolicExpressionExt, Val};
use p3_util::log2_strict_usize;
use p3_whir::parameters::{ProtocolParameters, WhirConfig};
use p3_whir::transcript::{WhirShape, WhirVerifierTranscript};
pub use pcs::{WhirUniPcs, WhirUniPcsError, WhirUniProof, WhirUniProverData};
pub use plan::{StackedPlacement, StackedPlan, StackedSelector, padded_arity};
pub use prover_mmcs::SharedMmcs;
pub use rate::WhirRatePolicy;
pub use recursion_data::{
    WhirRoundPaths, restore_whir_recursion_paths, restore_whir_recursion_paths_with_rate_policy,
    whir_round_paths_op_count,
};
pub use recursive_pcs::WhirUniVerifierParams;
pub use targets::{WhirRoundTargets, WhirUniProofTargets, packed_digest_len};

use crate::VerificationError;
use crate::input_contract::whir::{WhirContextParams, validate_whir_pcs_context};
use crate::pcs::whir::uni::plan::{canonical_layout_strategy, checked_stacked_num_variables};

#[derive(Clone, Debug)]
pub struct WhirQueryIndices {
    pub stacked_num_variables: usize,
    pub rounds: Vec<Vec<usize>>,
    pub final_queries: Vec<usize>,
}

pub fn replay_whir_query_indices<SC, MT>(
    transcript: crate::generation::OpeningTranscript<SC>,
    fresh_challenger: &SC::Challenger,
    opening_proof: &WhirUniProof<Val<SC>, SC::Challenge, MT>,
    protocol_params: &ProtocolParameters,
    folding: usize,
    variable_order: VariableOrder,
) -> Result<Vec<WhirQueryIndices>, VerificationError>
where
    SC: StarkGenericConfig,
    Val<SC>: TwoAdicField + PrimeField64,
    SC::Challenge: TwoAdicField,
    SC::Challenger: FieldChallenger<Val<SC>>
        + GrindingChallenger<Witness = Val<SC>>
        + CanSampleUniformBits<Val<SC>>
        + CanObserve<MT::Commitment>
        + Clone,
    SymbolicExpressionExt<Val<SC>, SC::Challenge>: Algebra<SymbolicExpression<Val<SC>>>,
    MT: Mmcs<Val<SC>>,
{
    replay_whir_query_indices_with_rate_policy::<SC, MT>(
        transcript,
        fresh_challenger,
        opening_proof,
        protocol_params,
        folding,
        variable_order,
        WhirRatePolicy::Native,
    )
}

pub fn replay_whir_query_indices_with_rate_policy<SC, MT>(
    transcript: crate::generation::OpeningTranscript<SC>,
    fresh_challenger: &SC::Challenger,
    opening_proof: &WhirUniProof<Val<SC>, SC::Challenge, MT>,
    protocol_params: &ProtocolParameters,
    folding: usize,
    variable_order: VariableOrder,
    rate_policy: WhirRatePolicy,
) -> Result<Vec<WhirQueryIndices>, VerificationError>
where
    SC: StarkGenericConfig,
    Val<SC>: TwoAdicField + PrimeField64,
    SC::Challenge: TwoAdicField,
    SC::Challenger: FieldChallenger<Val<SC>>
        + GrindingChallenger<Witness = Val<SC>>
        + CanSampleUniformBits<Val<SC>>
        + CanObserve<MT::Commitment>
        + Clone,
    SymbolicExpressionExt<Val<SC>, SC::Challenge>: Algebra<SymbolicExpression<Val<SC>>>,
    MT: Mmcs<Val<SC>>,
{
    type F<SC> = Val<SC>;
    type EF<SC> = <SC as StarkGenericConfig>::Challenge;

    let strategy = canonical_layout_strategy(variable_order);

    if transcript.commitments_with_opening_points.len() != opening_proof.rounds.len() {
        return Err(VerificationError::InvalidProofShape(format!(
            "WHIR commitment count mismatch: transcript expects {}, proof carries {}",
            transcript.commitments_with_opening_points.len(),
            opening_proof.rounds.len()
        )));
    }

    for ((_commitment, matrices), round_proof) in transcript
        .commitments_with_opening_points
        .iter()
        .zip(&opening_proof.rounds)
    {
        let mut shapes = Vec::with_capacity(matrices.len());
        for (domain, openings) in matrices {
            let width = openings
                .first()
                .map(|(_, values)| values.len())
                .ok_or_else(|| {
                    VerificationError::InvalidProofShape("WHIR commitment has no openings".into())
                })?;
            if openings.iter().any(|(_, values)| values.len() != width) {
                return Err(VerificationError::InvalidProofShape(
                    "WHIR opening width mismatch within one commitment".into(),
                ));
            }
            shapes.push((log2_strict_usize(domain.size()), width, openings.len()));
        }
        let stacked_num_variables = checked_stacked_num_variables(
            shapes
                .iter()
                .map(|&(log_height, width, _)| (padded_arity(log_height, folding), width)),
        )
        .map_err(|error| VerificationError::InvalidProofShape(error.to_string()))?;
        let config = WhirConfig::<EF<SC>, F<SC>, SC::Challenger>::new(
            stacked_num_variables,
            rate_policy
                .resolve(stacked_num_variables, protocol_params)
                .map_err(|error| VerificationError::InvalidProofShape(error.to_string()))?,
        )
        .map_err(|error| {
            VerificationError::InvalidProofShape(format!("invalid WHIR config: {error:?}"))
        })?;
        validate_whir_pcs_context::<F<SC>, EF<SC>, MT>(
            round_proof,
            &WhirContextParams::from_native(&config),
            &shapes,
        )?;
    }

    #[cfg(test)]
    acceptance_probe::query_replay();
    let mut parent = transcript.challenger;
    let seed = pcs::sample_fork_seed::<F<SC>, _>(&mut parent);

    let mut out = Vec::with_capacity(opening_proof.rounds.len());
    for (round, ((_commitment, matrices), round_proof)) in transcript
        .commitments_with_opening_points
        .iter()
        .zip(&opening_proof.rounds)
        .enumerate()
    {
        let mut challenger = pcs::fork_transcript(fresh_challenger, round, &seed);
        let mut shapes = Vec::with_capacity(matrices.len());
        let mut points_per_matrix = Vec::with_capacity(matrices.len());
        for (domain, openings) in matrices {
            let width = openings
                .first()
                .map(|(_, values)| values.len())
                .ok_or_else(|| {
                    VerificationError::InvalidProofShape("WHIR commitment has no openings".into())
                })?;
            if openings.iter().any(|(_, values)| values.len() != width) {
                return Err(VerificationError::InvalidProofShape(
                    "WHIR opening width mismatch within one commitment".into(),
                ));
            }
            shapes.push((log2_strict_usize(domain.size()), width));
            points_per_matrix.push(openings.iter().map(|&(z, _)| z).collect::<Vec<_>>());
        }
        let schedule = pcs::round_schedule::<F<SC>, EF<SC>>(&shapes, &points_per_matrix, folding);

        let whir_config = WhirConfig::<EF<SC>, F<SC>, SC::Challenger>::new(
            schedule.stacked_num_variables,
            rate_policy
                .resolve(schedule.stacked_num_variables, protocol_params)
                .map_err(|error| VerificationError::InvalidProofShape(error.to_string()))?,
        )
        .map_err(|e| VerificationError::InvalidProofShape(format!("invalid WHIR config: {e:?}")))?;

        if round_proof.whir.initial_ood_answers.len() != whir_config.commitment_ood_samples() {
            return Err(VerificationError::InvalidProofShape(format!(
                "WHIR initial OOD answer count mismatch: expected {}, got {}",
                whir_config.commitment_ood_samples(),
                round_proof.whir.initial_ood_answers.len()
            )));
        }
        let mut layout_verifier =
            Verifier::<F<SC>, EF<SC>>::new(&schedule.protocol.table_shapes(), strategy);
        for &eval in &round_proof.whir.initial_ood_answers {
            layout_verifier.add_virtual_eval(eval, &mut challenger);
        }
        if schedule.protocol.num_openings() != round_proof.evals.len() {
            return Err(VerificationError::InvalidProofShape(format!(
                "WHIR opening batch count mismatch: expected {}, got {}",
                schedule.protocol.num_openings(),
                round_proof.evals.len()
            )));
        }
        for (((table_idx, batch), point), evals) in schedule
            .protocol
            .iter_openings()
            .zip(&schedule.points)
            .zip(&round_proof.evals)
        {
            if !batch.has_same_shape(evals) {
                return Err(VerificationError::InvalidProofShape(format!(
                    "WHIR opening batch shape mismatch at table {table_idx}"
                )));
            }
            layout_verifier
                .add_claim_at(table_idx, batch, point, evals, &mut challenger)
                .map_err(|e| {
                    VerificationError::InvalidProofShape(format!(
                        "WHIR opening claim replay failed: {e:?}"
                    ))
                })?;
        }
        let n_rounds = whir_config.n_rounds();
        if round_proof.whir.rounds.len() != n_rounds {
            return Err(VerificationError::InvalidProofShape(format!(
                "WHIR round count mismatch: expected {n_rounds}, got {}",
                round_proof.whir.rounds.len()
            )));
        }
        let final_poly = round_proof.whir.final_poly.as_ref().ok_or_else(|| {
            VerificationError::InvalidProofShape("WHIR proof missing final polynomial".into())
        })?;
        let shape = WhirShape::new(&whir_config, schedule.protocol.num_openings());
        let mut whir_transcript =
            WhirVerifierTranscript::<SC::Challenger, F<SC>, EF<SC>>::new(&mut challenger, shape);
        let replayed = replay_whir_rounds::<SC, MT>(
            &mut whir_transcript,
            &whir_config,
            &layout_verifier,
            &round_proof.whir,
            final_poly.as_slice(),
        );
        let (rounds_indices, final_queries) = match replayed {
            Ok(indices) => {
                whir_transcript.finish();
                indices
            }
            Err(error) => {
                whir_transcript.abort();
                return Err(error);
            }
        };

        out.push(WhirQueryIndices {
            stacked_num_variables: schedule.stacked_num_variables,
            rounds: rounds_indices,
            final_queries,
        });
    }

    Ok(out)
}

type ReplayedWhirIndices = (Vec<Vec<usize>>, Vec<usize>);

fn replay_whir_rounds<SC, MT>(
    transcript: &mut WhirVerifierTranscript<'_, SC::Challenger, Val<SC>, SC::Challenge>,
    whir_config: &WhirConfig<SC::Challenge, Val<SC>, SC::Challenger>,
    layout_verifier: &Verifier<Val<SC>, SC::Challenge>,
    proof: &p3_whir::pcs::proof::WhirProof<Val<SC>, SC::Challenge, MT>,
    final_poly: &[SC::Challenge],
) -> Result<ReplayedWhirIndices, VerificationError>
where
    SC: StarkGenericConfig,
    Val<SC>: TwoAdicField + PrimeField64,
    SC::Challenge: TwoAdicField,
    SC::Challenger: FieldChallenger<Val<SC>>
        + GrindingChallenger<Witness = Val<SC>>
        + CanSampleUniformBits<Val<SC>>
        + CanObserve<MT::Commitment>,
    MT: Mmcs<Val<SC>>,
{
    let invalid = |what: &str, e: &dyn core::fmt::Debug| {
        VerificationError::InvalidProofShape(format!("WHIR {what} replay failed: {e:?}"))
    };

    let mut claimed_eval = SC::Challenge::ZERO;
    let _ = transcript
        .delegate_initial_fold(|challenger| {
            let _alpha = layout_verifier.batching_challenge(challenger);
            proof.initial_sumcheck.verify_rounds(
                challenger,
                &mut claimed_eval,
                whir_config.round_folding_factor(0),
                whir_config.starting_folding_pow_bits(),
                Basis::Evaluation,
            )
        })
        .map_err(|e| invalid("initial sumcheck", &e))?;

    let n_rounds = whir_config.n_rounds();
    let mut rounds_indices = Vec::with_capacity(n_rounds);
    for round_index in 0..n_rounds {
        let round_params = &whir_config.round_parameters()[round_index];
        let whir_round = &proof.rounds[round_index];

        let commitment = whir_round.commitment.clone().ok_or_else(|| {
            VerificationError::InvalidProofShape(format!(
                "WHIR round {round_index} is missing its commitment"
            ))
        })?;
        if whir_round.ood_answers.len() != round_params.ood_samples {
            return Err(VerificationError::InvalidProofShape(format!(
                "WHIR round {round_index} OOD answer count mismatch: expected {}, got {}",
                round_params.ood_samples,
                whir_round.ood_answers.len()
            )));
        }
        transcript.commitment(commitment);
        for &eval in &whir_round.ood_answers {
            let _ood_point = transcript.ood_point();
            transcript.ood_answer(eval);
        }

        transcript
            .query_pow(round_index, whir_round.pow_witness)
            .map_err(|e| invalid("round PoW", &e))?;
        rounds_indices.push(transcript.query_indices(round_index));

        let _gamma = transcript.round_batching();

        let _ = transcript
            .delegate_round_fold(|challenger| {
                whir_round.sumcheck.verify_rounds(
                    challenger,
                    &mut claimed_eval,
                    whir_config.round_folding_factor(round_index + 1),
                    round_params.folding_pow_bits,
                    Basis::Evaluation,
                )
            })
            .map_err(|e| invalid("round sumcheck", &e))?;
    }

    transcript
        .final_poly(final_poly)
        .map_err(|e| invalid("final polynomial", &e))?;
    transcript
        .query_pow(n_rounds, proof.final_pow_witness)
        .map_err(|e| invalid("final PoW", &e))?;
    let final_queries = transcript.query_indices(n_rounds);
    transcript
        .delegate_final_fold(|challenger| {
            verify_final_sumcheck_rounds(
                proof.final_sumcheck.as_ref(),
                challenger,
                &mut claimed_eval,
                whir_config.final_sumcheck_rounds(),
                whir_config.final_folding_pow_bits(),
                Basis::Evaluation,
            )
        })
        .transpose()
        .map_err(|e| invalid("final sumcheck", &e))?;

    Ok((rounds_indices, final_queries))
}
