use alloc::boxed::Box;
use alloc::format;
use alloc::string::ToString;

use p3_batch_stark::CommonData;
use p3_batch_stark::common::GlobalPreprocessed;
use p3_circuit_prover::batch_stark_prover::{
    BatchStarkProof, CircuitVerifier, TableProver, lookups_for_circuit_table_air,
};
use p3_circuit_prover::field_params::ExtractBinomialW;
use p3_field::{Algebra, ExtensionField, PrimeField64};
use p3_lookup::logup::LogUpGadget;
use p3_uni_stark::{StarkGenericConfig, SymbolicExpression, SymbolicExpressionExt, Val};

use crate::generation::{
    OpeningTranscript, replay_batch_stark_transcript, replay_uni_stark_transcript,
};
use crate::recursion::RecursionInput;
use crate::traits::RecursiveAir;
use crate::verifier::{
    ReconstructedBatchTables, VerificationError, reconstruct_batch_tables, trusted_batch_tables,
};

pub fn replay_recursion_input_transcript<SC, A>(
    config: &SC,
    prev: &RecursionInput<'_, SC, A>,
    non_primitive_provers: &[Box<dyn TableProver<SC>>],
) -> Result<OpeningTranscript<SC>, VerificationError>
where
    SC::Challenger: p3_challenger::GrindingChallenger<Witness = p3_uni_stark::Val<SC>>,
    SC: StarkGenericConfig + 'static,
    A: RecursiveAir<Val<SC>, SC::Challenge, LogUpGadget>,
    Val<SC>: PrimeField64,
    SC::Challenge: ExtensionField<Val<SC>> + ExtractBinomialW<Val<SC>>,
    SymbolicExpressionExt<Val<SC>, SC::Challenge>:
        Algebra<SymbolicExpression<Val<SC>>> + Algebra<SC::Challenge>,
{
    #[cfg(test)]
    crate::pcs::whir::uni::acceptance_probe::transcript_replay();
    match prev {
        RecursionInput::UniStark {
            proof,
            air,
            public_inputs,
            preprocessed_commit,
        } => replay_uni_stark_transcript(
            config,
            *air,
            proof,
            public_inputs,
            preprocessed_commit.as_ref(),
        )
        .map_err(|e| VerificationError::InvalidProofShape(e.to_string())),
        RecursionInput::BatchStark {
            proof, common_data, ..
        } => match proof.ext_degree {
            1 => replay_batch_layer_transcript::<SC, 1>(
                config,
                proof,
                common_data,
                non_primitive_provers,
            ),
            2 => replay_batch_layer_transcript::<SC, 2>(
                config,
                proof,
                common_data,
                non_primitive_provers,
            ),
            4 => replay_batch_layer_transcript::<SC, 4>(
                config,
                proof,
                common_data,
                non_primitive_provers,
            ),
            5 => replay_batch_layer_transcript::<SC, 5>(
                config,
                proof,
                common_data,
                non_primitive_provers,
            ),
            d => Err(VerificationError::InvalidProofShape(format!(
                "unsupported batch proof ext_degree {d}"
            ))),
        },
    }
}

pub fn replay_batch_layer_transcript<SC, const D: usize>(
    config: &SC,
    proof: &BatchStarkProof<SC>,
    common_data: &CommonData<SC>,
    non_primitive_provers: &[Box<dyn TableProver<SC>>],
) -> Result<OpeningTranscript<SC>, VerificationError>
where
    SC::Challenger: p3_challenger::GrindingChallenger<Witness = p3_uni_stark::Val<SC>>,
    SC: StarkGenericConfig + 'static,
    Val<SC>: PrimeField64,
    SC::Challenge: ExtensionField<Val<SC>> + ExtractBinomialW<Val<SC>>,
    SymbolicExpressionExt<Val<SC>, SC::Challenge>:
        Algebra<SymbolicExpression<Val<SC>>> + Algebra<SC::Challenge>,
{
    let ReconstructedBatchTables {
        airs,
        trace_lens,
        public_values,
    } = reconstruct_batch_tables::<SC, D>(config, proof, non_primitive_provers)?;

    let lookups = airs
        .iter()
        .zip(&trace_lens)
        .map(|(air, &trace_len)| {
            lookups_for_circuit_table_air::<SC, D>(&air.to_table_air(), trace_len, config.is_zk())
        })
        .collect();
    let effective_common = CommonData::new(
        common_data
            .preprocessed
            .as_ref()
            .map(|g| GlobalPreprocessed {
                commitment: g.commitment.clone(),
                instances: g.instances.clone(),
                matrix_to_instance: g.matrix_to_instance.clone(),
            }),
        lookups,
    );

    let (transcript, _) = replay_batch_stark_transcript(
        &airs,
        config,
        &proof.proof,
        &public_values,
        &effective_common,
        &LogUpGadget::new(),
    )
    .map_err(|e| VerificationError::InvalidProofShape(e.to_string()))?;

    Ok(transcript)
}

pub fn replay_trusted_batch_layer_transcript<SC, const D: usize>(
    verifier: &CircuitVerifier<SC>,
    proof: &BatchStarkProof<SC>,
    statement: &[Val<SC>],
) -> Result<OpeningTranscript<SC>, VerificationError>
where
    SC::Challenger: p3_challenger::GrindingChallenger<Witness = p3_uni_stark::Val<SC>>,
    SC: StarkGenericConfig + 'static,
    Val<SC>: PrimeField64 + p3_circuit_prover::config::StarkField,
    SC::Challenge: ExtensionField<Val<SC>> + ExtractBinomialW<Val<SC>>,
    SymbolicExpressionExt<Val<SC>, SC::Challenge>:
        Algebra<SymbolicExpression<Val<SC>>> + Algebra<SC::Challenge>,
{
    verifier
        .verify(proof, statement)
        .map_err(|error| VerificationError::InvalidProofShape(error.to_string()))?;
    let ReconstructedBatchTables {
        airs,
        trace_lens: _,
        public_values,
    } = trusted_batch_tables::<SC, D>(verifier, statement)?;
    let (transcript, _) = replay_batch_stark_transcript(
        &airs,
        verifier.config(),
        &proof.proof,
        &public_values,
        verifier.common_data(),
        &LogUpGadget::new(),
    )
    .map_err(|error| VerificationError::InvalidProofShape(error.to_string()))?;
    Ok(transcript)
}
