use alloc::string::ToString;
use alloc::vec::Vec;

use p3_challenger::{CanObserve, CanSampleUniformBits, FieldChallenger, GrindingChallenger};
use p3_field::{Algebra, PackedValue, PrimeField64, TwoAdicField};
use p3_matrix::Dimensions;
use p3_merkle_tree::MerkleTreeMmcs;
use p3_symmetric::{CryptographicHasher, MerkleCap, PseudoCompressionFunction};
use p3_uni_stark::{StarkGenericConfig, SymbolicExpression, SymbolicExpressionExt, Val};
use p3_whir::parameters::{ProtocolParameters, WhirConfig};
use serde::{Deserialize, Serialize};

use super::WhirUniProof;
use crate::generation::OpeningTranscript;
use crate::pcs::restore_whir_query_paths;
use crate::pcs::whir::uni::{
    VariableOrder, WhirRatePolicy, replay_whir_query_indices_with_rate_policy,
};
use crate::verifier::VerificationError;

pub struct WhirRoundPaths<F, const DIGEST_ELEMS: usize> {
    pub rounds: Vec<Vec<Vec<[F; DIGEST_ELEMS]>>>,
    pub final_paths: Vec<Vec<[F; DIGEST_ELEMS]>>,
}

pub fn whir_round_paths_op_count<F, const DIGEST_ELEMS: usize>(
    paths: &WhirRoundPaths<F, DIGEST_ELEMS>,
) -> usize {
    paths
        .rounds
        .iter()
        .flatten()
        .map(Vec::len)
        .chain(paths.final_paths.iter().map(Vec::len))
        .sum()
}

#[expect(clippy::type_complexity)]
pub fn restore_whir_recursion_paths<SC, P, PW, H, C, const N: usize, const DIGEST_ELEMS: usize>(
    mmcs: &MerkleTreeMmcs<P, PW, H, C, N, DIGEST_ELEMS>,
    transcript: OpeningTranscript<SC>,
    fresh_challenger: &SC::Challenger,
    opening_proof: &WhirUniProof<
        Val<SC>,
        SC::Challenge,
        MerkleTreeMmcs<P, PW, H, C, N, DIGEST_ELEMS>,
    >,
    protocol_params: &ProtocolParameters,
    folding: usize,
    variable_order: VariableOrder,
) -> Result<Vec<WhirRoundPaths<Val<SC>, DIGEST_ELEMS>>, VerificationError>
where
    SC: StarkGenericConfig,
    Val<SC>: TwoAdicField + PrimeField64,
    SC::Challenge: TwoAdicField,
    SC::Challenger: FieldChallenger<Val<SC>>
        + GrindingChallenger<Witness = Val<SC>>
        + CanSampleUniformBits<Val<SC>>
        + CanObserve<MerkleCap<Val<SC>, [Val<SC>; DIGEST_ELEMS]>>
        + Clone,
    SymbolicExpressionExt<Val<SC>, SC::Challenge>: Algebra<SymbolicExpression<Val<SC>>>,
    P: PackedValue<Value = Val<SC>>,
    PW: PackedValue<Value = Val<SC>>,
    H: CryptographicHasher<Val<SC>, [Val<SC>; DIGEST_ELEMS]>
        + CryptographicHasher<P, [PW; DIGEST_ELEMS]>
        + Sync,
    C: PseudoCompressionFunction<[Val<SC>; DIGEST_ELEMS], N>
        + PseudoCompressionFunction<[PW; DIGEST_ELEMS], N>
        + Sync,
    [Val<SC>; DIGEST_ELEMS]: Serialize + for<'de> Deserialize<'de>,
{
    restore_whir_recursion_paths_with_rate_policy::<SC, P, PW, H, C, N, DIGEST_ELEMS>(
        mmcs,
        transcript,
        fresh_challenger,
        opening_proof,
        protocol_params,
        folding,
        variable_order,
        WhirRatePolicy::Native,
    )
}

#[expect(clippy::type_complexity, clippy::too_many_arguments)]
pub fn restore_whir_recursion_paths_with_rate_policy<
    SC,
    P,
    PW,
    H,
    C,
    const N: usize,
    const DIGEST_ELEMS: usize,
>(
    mmcs: &MerkleTreeMmcs<P, PW, H, C, N, DIGEST_ELEMS>,
    transcript: OpeningTranscript<SC>,
    fresh_challenger: &SC::Challenger,
    opening_proof: &WhirUniProof<
        Val<SC>,
        SC::Challenge,
        MerkleTreeMmcs<P, PW, H, C, N, DIGEST_ELEMS>,
    >,
    protocol_params: &ProtocolParameters,
    folding: usize,
    variable_order: VariableOrder,
    rate_policy: WhirRatePolicy,
) -> Result<Vec<WhirRoundPaths<Val<SC>, DIGEST_ELEMS>>, VerificationError>
where
    SC: StarkGenericConfig,
    Val<SC>: TwoAdicField + PrimeField64,
    SC::Challenge: TwoAdicField,
    SC::Challenger: FieldChallenger<Val<SC>>
        + GrindingChallenger<Witness = Val<SC>>
        + CanSampleUniformBits<Val<SC>>
        + CanObserve<MerkleCap<Val<SC>, [Val<SC>; DIGEST_ELEMS]>>
        + Clone,
    SymbolicExpressionExt<Val<SC>, SC::Challenge>: Algebra<SymbolicExpression<Val<SC>>>,
    P: PackedValue<Value = Val<SC>>,
    PW: PackedValue<Value = Val<SC>>,
    H: CryptographicHasher<Val<SC>, [Val<SC>; DIGEST_ELEMS]>
        + CryptographicHasher<P, [PW; DIGEST_ELEMS]>
        + Sync,
    C: PseudoCompressionFunction<[Val<SC>; DIGEST_ELEMS], N>
        + PseudoCompressionFunction<[PW; DIGEST_ELEMS], N>
        + Sync,
    [Val<SC>; DIGEST_ELEMS]: Serialize + for<'de> Deserialize<'de>,
{
    let indices = replay_whir_query_indices_with_rate_policy::<
        SC,
        MerkleTreeMmcs<P, PW, H, C, N, DIGEST_ELEMS>,
    >(
        transcript,
        fresh_challenger,
        opening_proof,
        protocol_params,
        folding,
        variable_order,
        rate_policy,
    )?;
    #[cfg(test)]
    crate::pcs::whir::uni::acceptance_probe::restoration();

    let mut out = Vec::with_capacity(opening_proof.rounds.len());
    for (round_idx, round) in opening_proof.rounds.iter().enumerate() {
        let cfg = WhirConfig::<SC::Challenge, Val<SC>, SC::Challenger>::new(
            indices[round_idx].stacked_num_variables,
            rate_policy
                .resolve(indices[round_idx].stacked_num_variables, protocol_params)
                .map_err(|error| VerificationError::InvalidProofShape(error.to_string()))?,
        )
        .map_err(|e| VerificationError::InvalidProofShape(alloc::format!("{e:?}")))?;

        let mut rounds = Vec::new();
        for (i, rp) in cfg.round_parameters().iter().enumerate() {
            let dims = [Dimensions {
                height: rp.domain_size >> rp.folding_factor,
                width: 1 << rp.folding_factor,
            }];
            rounds.push(
                restore_whir_query_paths::<P, PW, SC::Challenge, H, C, N, DIGEST_ELEMS>(
                    mmcs,
                    &round.whir.rounds[i].openings,
                    &dims,
                    &indices[round_idx].rounds[i],
                )
                .map_err(|e| VerificationError::InvalidProofShape(alloc::format!("{e:?}")))?,
            );
        }

        let final_cfg = cfg.final_round_config();
        let final_dims = [Dimensions {
            height: final_cfg.domain_size >> final_cfg.folding_factor,
            width: 1 << final_cfg.folding_factor,
        }];
        let final_paths = restore_whir_query_paths::<P, PW, SC::Challenge, H, C, N, DIGEST_ELEMS>(
            mmcs,
            &round.whir.final_openings,
            &final_dims,
            &indices[round_idx].final_queries,
        )
        .map_err(|e| VerificationError::InvalidProofShape(alloc::format!("{e:?}")))?;

        out.push(WhirRoundPaths {
            rounds,
            final_paths,
        });
    }
    Ok(out)
}
