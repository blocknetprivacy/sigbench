use alloc::format;
use alloc::string::String;
use alloc::vec::Vec;

use p3_air::{SymbolicExpression, SymbolicExpressionExt};
use p3_batch_stark::BatchProof;
use p3_circuit::ops::NpoTypeId;
use p3_circuit::{Circuit, CircuitError};
use p3_circuit_prover::batch_stark_prover::ProvingMaybeSend;
use p3_circuit_prover::config::StarkField;
use p3_circuit_prover::field_params::ExtractBinomialW;
use p3_circuit_prover::{BatchStarkProof, ConstraintProfile, TablePacking};
use p3_commit::Pcs;
use p3_field::{Algebra, BasedVectorSpace, ExtensionField, PrimeField64};
use p3_lookup::logup::LogUpGadget;
use p3_uni_stark::{StarkGenericConfig, Val};
use tracing::instrument;

use crate::prepared::prover::prepare_prover;
use crate::recursion::{
    BatchOnly, PcsRecursionBackend, ProveNextLayerParams, RecursionInput, RecursionOutput,
    build_next_layer_circuit, prove_aggregation_layer, prove_next_layer,
};
use crate::traits::RecursiveAir;
use crate::verifier::VerificationError;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MerkleArity {
    Two,
    Four,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct HashProfile {
    pub arity: MerkleArity,
    pub cap_height: usize,
}

impl Default for HashProfile {
    fn default() -> Self {
        Self {
            arity: MerkleArity::Two,
            cap_height: 0,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum TranscriptKind {
    #[default]
    BaseDuplex,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RecursionLayerProfile {
    pub table_packing: TablePacking,
    pub hash: HashProfile,
    pub transcript: TranscriptKind,
    pub constraint_profile: ConstraintProfile,
}

#[derive(Debug, Clone)]
pub struct FixedPointError {
    pub iterations: usize,
    pub last_growth: Vec<(String, usize, usize)>,
}

pub fn solve_fixed_point<SC, A, B, const D: usize>(
    seed: RecursionLayerProfile,
    prev: &RecursionInput<'_, SC, A>,
    config: &SC,
    backend: &B,
    max_iterations: usize,
) -> Result<RecursionLayerProfile, VerificationError>
where
    SC: StarkGenericConfig + Send + Sync + Clone + 'static,
    A: RecursiveAir<Val<SC>, SC::Challenge, LogUpGadget>,
    B: PcsRecursionBackend<SC, A, D>,
    Val<SC>: PrimeField64 + StarkField,
    SC::Challenge: BasedVectorSpace<Val<SC>>
        + From<Val<SC>>
        + ExtensionField<Val<SC>>
        + ExtractBinomialW<Val<SC>>,
    SymbolicExpressionExt<Val<SC>, SC::Challenge>:
        Algebra<SymbolicExpression<Val<SC>>> + Algebra<SC::Challenge>,
{
    let (circuit, _verifier_result) =
        build_next_layer_circuit::<SC, A, B, D>(prev, config, backend)?;

    let mut table_packing = seed.table_packing.with_strict_heights();
    let mut last_growth: Vec<(String, usize, usize)> = Vec::new();

    for iteration in 0..max_iterations {
        let params = ProveNextLayerParams {
            table_packing: table_packing.clone(),
            constraint_profile: seed.constraint_profile,
        };

        match prepare_prover::<SC, A, B, D>(&circuit, config, backend, &params) {
            Ok(_) => {
                tracing::info!(
                    iteration,
                    growth_events = last_growth.len(),
                    "solve_fixed_point converged"
                );
                return Ok(RecursionLayerProfile {
                    table_packing,
                    hash: seed.hash,
                    transcript: seed.transcript,
                    constraint_profile: seed.constraint_profile,
                });
            }
            Err(VerificationError::Circuit(CircuitError::ProfileOverflow {
                table,
                needed,
                allowed,
            })) => {
                tracing::info!(
                    iteration,
                    table = %table,
                    allowed,
                    needed,
                    "solve_fixed_point: table overflowed its configured height, bumping"
                );
                last_growth.push((table.clone(), allowed, needed));
                table_packing = bump_table_height(table_packing, &table, needed);
            }
            Err(other) => return Err(other),
        }
    }

    Err(VerificationError::InvalidProofShape(format!(
        "solve_fixed_point did not converge: {:?}",
        FixedPointError {
            iterations: max_iterations,
            last_growth,
        }
    )))
}

fn bump_table_height(packing: TablePacking, table: &str, needed: usize) -> TablePacking {
    match table {
        "ALU" => packing.with_alu_min_height(needed),
        "PUBLIC" => packing.with_public_min_height(needed),
        "CONST" => packing.with_const_min_height(needed),
        other => packing.with_npo_min_height(NpoTypeId::new(other), needed),
    }
}

impl RecursionLayerProfile {
    pub fn check_proof_shape<SC: StarkGenericConfig>(
        &self,
        proof: &BatchStarkProof<SC>,
    ) -> Result<(), VerificationError> {
        if proof.table_packing != self.table_packing {
            return Err(VerificationError::InvalidProofShape(format!(
                "proof's table_packing {:?} does not match this RecursionLayerProfile's table_packing {:?}",
                proof.table_packing, self.table_packing
            )));
        }
        Ok(())
    }
}

pub fn build_layer_circuit<SC, A, B, const D: usize>(
    profile: &RecursionLayerProfile,
    prev: &RecursionInput<'_, SC, A>,
    config: &SC,
    backend: &B,
) -> Result<(Circuit<SC::Challenge>, B::VerifierResult), VerificationError>
where
    SC: StarkGenericConfig + Send + Sync + Clone + 'static,
    A: RecursiveAir<Val<SC>, SC::Challenge, LogUpGadget>,
    B: PcsRecursionBackend<SC, A, D>,
    Val<SC>: PrimeField64 + StarkField,
    SC::Challenge: BasedVectorSpace<Val<SC>>
        + From<Val<SC>>
        + ExtensionField<Val<SC>>
        + ExtractBinomialW<Val<SC>>,
    SymbolicExpressionExt<Val<SC>, SC::Challenge>:
        Algebra<SymbolicExpression<Val<SC>>> + Algebra<SC::Challenge>,
{
    let _ = profile;
    build_next_layer_circuit::<SC, A, B, D>(prev, config, backend)
}

pub fn prove_layer<SC, A, B, const D: usize>(
    profile: &RecursionLayerProfile,
    prev: &RecursionInput<'_, SC, A>,
    verification_circuit: &Circuit<SC::Challenge>,
    verifier_result: &B::VerifierResult,
    config: &SC,
    backend: &B,
) -> Result<RecursionOutput<SC>, VerificationError>
where
    BatchProof<SC>: ProvingMaybeSend,
    p3_uni_stark::PcsProverError<SC>: Send,
    SC::Challenger: p3_challenger::GrindingChallenger<Witness = p3_uni_stark::Val<SC>>,
    SC: StarkGenericConfig + Send + Sync + Clone + 'static,
    A: RecursiveAir<Val<SC>, SC::Challenge, LogUpGadget>,
    B: PcsRecursionBackend<SC, A, D>,
    Val<SC>: PrimeField64 + StarkField,
    SC::Challenge: BasedVectorSpace<Val<SC>>
        + From<Val<SC>>
        + ExtensionField<Val<SC>>
        + ExtractBinomialW<Val<SC>>,
    SymbolicExpressionExt<Val<SC>, SC::Challenge>:
        Algebra<SymbolicExpression<Val<SC>>> + Algebra<SC::Challenge>,
    <SC::Pcs as Pcs<SC::Challenge, SC::Challenger>>::Domain: Send + Sync,
    SC::Pcs: Sync,
    <SC::Pcs as Pcs<SC::Challenge, SC::Challenger>>::ProverData: Sync,
    <SC::Pcs as Pcs<SC::Challenge, SC::Challenger>>::Commitment: Sync,
{
    let params = ProveNextLayerParams {
        table_packing: profile.table_packing.clone(),
        constraint_profile: profile.constraint_profile,
    };

    let output = prove_next_layer::<SC, A, B, D>(
        prev,
        verification_circuit,
        verifier_result,
        config,
        backend,
        &params,
    )?;

    profile.check_proof_shape(&output.0)?;

    Ok(output)
}

#[instrument(skip_all)]
#[allow(clippy::too_many_arguments)]
pub fn prove_aggregation_layer_with_profile<SC, A1, A2, B, const D: usize>(
    profile: &RecursionLayerProfile,
    left: &RecursionInput<'_, SC, A1>,
    right: &RecursionInput<'_, SC, A2>,
    left_result: &<B as PcsRecursionBackend<SC, A1, D>>::VerifierResult,
    right_result: &<B as PcsRecursionBackend<SC, A2, D>>::VerifierResult,
    verification_circuit: &Circuit<SC::Challenge>,
    config: &SC,
    backend: &B,
) -> Result<RecursionOutput<SC>, VerificationError>
where
    BatchProof<SC>: ProvingMaybeSend,
    p3_uni_stark::PcsProverError<SC>: Send,
    SC::Challenger: p3_challenger::GrindingChallenger<Witness = p3_uni_stark::Val<SC>>,
    SC: StarkGenericConfig + Send + Sync + Clone + 'static,
    A1: RecursiveAir<Val<SC>, SC::Challenge, LogUpGadget>,
    A2: RecursiveAir<Val<SC>, SC::Challenge, LogUpGadget>,
    B: PcsRecursionBackend<SC, A1, D> + PcsRecursionBackend<SC, A2, D>,
    Val<SC>: PrimeField64 + StarkField,
    SC::Challenge: BasedVectorSpace<Val<SC>>
        + From<Val<SC>>
        + ExtensionField<Val<SC>>
        + ExtractBinomialW<Val<SC>>,
    SymbolicExpressionExt<Val<SC>, SC::Challenge>:
        Algebra<SymbolicExpression<Val<SC>>> + Algebra<SC::Challenge>,
    <SC::Pcs as Pcs<SC::Challenge, SC::Challenger>>::Domain: Send + Sync,
    SC::Pcs: Sync,
    <SC::Pcs as Pcs<SC::Challenge, SC::Challenger>>::ProverData: Sync,
    <SC::Pcs as Pcs<SC::Challenge, SC::Challenger>>::Commitment: Sync,
{
    let params = ProveNextLayerParams {
        table_packing: profile.table_packing.clone(),
        constraint_profile: profile.constraint_profile,
    };

    let output = prove_aggregation_layer::<SC, A1, A2, B, D>(
        left,
        right,
        left_result,
        right_result,
        verification_circuit,
        config,
        backend,
        &params,
    )?;

    profile.check_proof_shape(&output.0)?;

    Ok(output)
}

#[instrument(skip_all)]
#[allow(clippy::too_many_arguments)]
pub fn prove_aggregation_layer_cross_with_profile<InSC, OutSC, A1, A2, B, const D: usize>(
    profile: &RecursionLayerProfile,
    left: &RecursionInput<'_, InSC, A1>,
    right: &RecursionInput<'_, InSC, A2>,
    left_result: &<B as PcsRecursionBackend<InSC, A1, D>>::VerifierResult,
    right_result: &<B as PcsRecursionBackend<InSC, A2, D>>::VerifierResult,
    verification_circuit: &Circuit<InSC::Challenge>,
    input_config: &InSC,
    output_config: &OutSC,
    backend: &B,
) -> Result<RecursionOutput<OutSC>, VerificationError>
where
    BatchProof<OutSC>: ProvingMaybeSend,
    p3_uni_stark::PcsProverError<OutSC>: Send,
    OutSC::Challenger: p3_challenger::GrindingChallenger<Witness = p3_uni_stark::Val<OutSC>>,
    InSC: StarkGenericConfig + Send + Sync + Clone + 'static,
    OutSC: StarkGenericConfig<Challenge = InSC::Challenge> + Send + Sync + Clone + 'static,
    A1: RecursiveAir<Val<InSC>, InSC::Challenge, LogUpGadget>,
    A2: RecursiveAir<Val<InSC>, InSC::Challenge, LogUpGadget>,
    B: PcsRecursionBackend<InSC, A1, D>
        + PcsRecursionBackend<InSC, A2, D>
        + PcsRecursionBackend<OutSC, BatchOnly, D>,
    Val<InSC>: PrimeField64,
    InSC::Challenge: BasedVectorSpace<Val<InSC>> + From<Val<InSC>>,
    Val<OutSC>: PrimeField64 + StarkField,
    OutSC::Challenge: BasedVectorSpace<Val<OutSC>>
        + From<Val<OutSC>>
        + ExtensionField<Val<OutSC>>
        + ExtractBinomialW<Val<OutSC>>,
    SymbolicExpressionExt<Val<OutSC>, OutSC::Challenge>:
        Algebra<SymbolicExpression<Val<OutSC>>> + Algebra<OutSC::Challenge>,
    <OutSC::Pcs as Pcs<OutSC::Challenge, OutSC::Challenger>>::Domain: Send + Sync,
    OutSC::Pcs: Sync,
    <OutSC::Pcs as Pcs<OutSC::Challenge, OutSC::Challenger>>::ProverData: Sync,
    <OutSC::Pcs as Pcs<OutSC::Challenge, OutSC::Challenger>>::Commitment: Sync,
{
    let params = ProveNextLayerParams {
        table_packing: profile.table_packing.clone(),
        constraint_profile: profile.constraint_profile,
    };

    let output = crate::recursion::prove_aggregation_layer_cross::<InSC, OutSC, A1, A2, B, D>(
        left,
        right,
        left_result,
        right_result,
        verification_circuit,
        input_config,
        output_config,
        backend,
        &params,
    )?;

    profile.check_proof_shape(&output.0)?;

    Ok(output)
}
