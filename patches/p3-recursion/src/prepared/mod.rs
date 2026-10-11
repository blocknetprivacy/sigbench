mod aggregation;
mod binary;
pub(crate) mod input;
mod layer;
mod native_binary;
mod native_poly;
pub(crate) mod prover;
mod trusted;

#[cfg(test)]
#[path = "../../tests/common/mod.rs"]
pub(crate) mod test_common;

use alloc::vec::Vec;

pub use aggregation::{PreparedAggregation, PreparedAggregationCross};
pub use binary::{
    BinaryPolyStatementLayout, BinaryStatementLayout, PreparedBinaryBooleanTraceMultiStarkLayer,
    PreparedBinaryBooleanWhirTraceMultiStarkLayer,
    PreparedBinaryGroupedBooleanTraceMultiStarkLayer, PreparedBinaryGroupedMultiStarkLayer,
    PreparedBinaryMultiStarkLayer, PreparedBinaryPolyWhirMultiStarkLayer,
    PreparedBinaryWhirMultiStarkLayer,
};
pub use input::{NativeCommitment, PreparedInput, PreparedSource};
pub use layer::PreparedLayer;
pub use native_binary::{
    NativeBinaryRecursionOptions, NativeBinaryRecursiveProof, PreparedNativeBinaryWhirLayer,
};
pub use native_poly::{NativeBinaryPolyRecursiveProof, PreparedNativeBinaryPolyWhirLayer};
pub use p3_circuit::VerifiedStatementTargets;
use p3_circuit::{
    CircuitBuilder, CircuitRunner, NonPrimitiveOpId, StatementField, StatementSchema,
};
use p3_circuit_prover::{BatchStarkProof, CircuitVerifier, StatementLayout};
use p3_field::Field;
use p3_lookup::logup::LogUpGadget;
use p3_uni_stark::{StarkGenericConfig, Val};
pub use trusted::{
    TrustedPreparedAggregation, TrustedPreparedInput, TrustedPreparedLayer, TrustedPreparedSource,
};

use crate::recursion::{PcsRecursionBackend, RecursionInput};
use crate::traits::RecursiveAir;
use crate::verifier::VerificationError;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum TrustedChildStatementKind {
    Uni,
    Batch,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TrustedChildStatementLayout {
    kind: TrustedChildStatementKind,
    schema: StatementSchema,
    public_values_len: usize,
    table_instance: Option<usize>,
}

impl TrustedChildStatementLayout {
    pub(crate) fn uni(
        public_values_len: usize,
        schema: StatementSchema,
    ) -> Result<Self, VerificationError> {
        if schema.base_len() != public_values_len
            || schema
                .fields()
                .iter()
                .any(|field| *field != StatementField::Base)
        {
            return Err(VerificationError::InvalidProofShape(
                "trusted uni statement schema must contain one Base field per AIR public value"
                    .into(),
            ));
        }
        Ok(Self {
            kind: TrustedChildStatementKind::Uni,
            schema,
            public_values_len,
            table_instance: None,
        })
    }

    pub(crate) fn batch(layout: &StatementLayout) -> Self {
        Self {
            kind: TrustedChildStatementKind::Batch,
            schema: layout.schema().clone(),
            public_values_len: layout.schema().base_len(),
            table_instance: layout.table_instance(),
        }
    }

    pub const fn kind(&self) -> TrustedChildStatementKind {
        self.kind
    }

    pub const fn schema(&self) -> &StatementSchema {
        &self.schema
    }

    pub const fn public_values_len(&self) -> usize {
        self.public_values_len
    }

    pub const fn table_instance(&self) -> Option<usize> {
        self.table_instance
    }
}

pub(crate) enum ConsumedStatementTargets<'a> {
    Uni(&'a [crate::Target]),
    Batch(&'a [Vec<crate::Target>]),
}

pub(crate) fn checked_statement_targets<F: Field>(
    consumed: ConsumedStatementTargets<'_>,
    source: &TrustedChildStatementLayout,
    builder: &CircuitBuilder<F>,
) -> Result<VerifiedStatementTargets<F>, VerificationError> {
    let targets = match (consumed, source.kind) {
        (ConsumedStatementTargets::Uni(targets), TrustedChildStatementKind::Uni) => targets,
        (ConsumedStatementTargets::Batch(_), TrustedChildStatementKind::Uni)
        | (ConsumedStatementTargets::Uni(_), TrustedChildStatementKind::Batch) => {
            return Err(VerificationError::InvalidProofShape(
                "trusted statement source kind does not match verifier result branch".into(),
            ));
        }
        (ConsumedStatementTargets::Batch(_), TrustedChildStatementKind::Batch)
            if source.table_instance.is_none() =>
        {
            &[]
        }
        (ConsumedStatementTargets::Batch(all), TrustedChildStatementKind::Batch) => all
            .get(source.table_instance.expect("checked above"))
            .map(Vec::as_slice)
            .ok_or_else(|| {
                VerificationError::InvalidProofShape(
                    "trusted statement table instance is absent from verifier inputs".into(),
                )
            })?,
    };
    if targets.len() != source.public_values_len {
        return Err(VerificationError::InvalidProofShape(alloc::format!(
            "trusted statement verifier target length mismatch: expected {}, got {}",
            source.public_values_len,
            targets.len()
        )));
    }
    unsafe {
        VerifiedStatementTargets::new_unchecked(builder, source.schema.clone(), targets.to_vec())
    }
    .map_err(VerificationError::CircuitBuilder)
}

pub trait ConstrainConstantCommitment<F: Field>: crate::traits::Recursive<F> {
    fn constrain_constant(
        &self,
        circuit: &mut CircuitBuilder<F>,
        expected: &Self::Input,
    ) -> Result<(), VerificationError>;
}

pub trait PreparedPcsRecursionBackend<SC, A, const D: usize>:
    PcsRecursionBackend<SC, A, D>
where
    SC: StarkGenericConfig,
    A: RecursiveAir<Val<SC>, SC::Challenge, LogUpGadget>,
{
    type InputContract;

    fn preflight_input(
        &self,
        _config: &SC,
        _input: &PreparedInput<'_, SC>,
    ) -> Result<(), VerificationError> {
        Ok(())
    }

    fn capture_input_contract(
        &self,
        config: &SC,
        source: &RecursionInput<'_, SC, A>,
    ) -> Result<Self::InputContract, VerificationError>;

    fn validate_prepared_input(
        &self,
        config: &SC,
        contract: &Self::InputContract,
        input: &PreparedInput<'_, SC>,
    ) -> Result<(), VerificationError>;
}

pub trait TrustedPcsRecursionBackend<SC, A, const D: usize>:
    PreparedPcsRecursionBackend<SC, A, D>
where
    SC: StarkGenericConfig,
    A: RecursiveAir<Val<SC>, SC::Challenge, LogUpGadget>,
{
    fn preflight_trusted_batch(
        &self,
        verifier: &CircuitVerifier<SC>,
        proof: &BatchStarkProof<SC>,
    ) -> Result<(), VerificationError>;

    fn capture_trusted_batch_input_contract(
        &self,
        verifier: &CircuitVerifier<SC>,
        proof: &BatchStarkProof<SC>,
        expected_statement: &[Val<SC>],
    ) -> Result<Self::InputContract, VerificationError>;

    fn validate_trusted_batch_input(
        &self,
        verifier: &CircuitVerifier<SC>,
        contract: &Self::InputContract,
        proof: &BatchStarkProof<SC>,
        expected_statement: &[Val<SC>],
    ) -> Result<(), VerificationError>;

    fn build_trusted_batch_verifier_circuit(
        &self,
        verifier: &CircuitVerifier<SC>,
        proof: &BatchStarkProof<SC>,
        statement: &[Val<SC>],
        circuit: &mut CircuitBuilder<SC::Challenge>,
    ) -> Result<Self::VerifierResult, VerificationError>;

    fn set_private_data_for_trusted_batch(
        &self,
        verifier: &CircuitVerifier<SC>,
        proof: &BatchStarkProof<SC>,
        statement: &[Val<SC>],
        runner: &mut CircuitRunner<'_, SC::Challenge>,
        op_ids: &[NonPrimitiveOpId],
    ) -> Result<(), VerificationError>;

    fn verified_statement_targets(
        &self,
        result: &Self::VerifierResult,
        source: &TrustedChildStatementLayout,
        builder: &CircuitBuilder<SC::Challenge>,
    ) -> Result<VerifiedStatementTargets<SC::Challenge>, VerificationError>;

    fn constrain_trusted_preprocessing(
        &self,
        circuit: &mut CircuitBuilder<SC::Challenge>,
        result: &Self::VerifierResult,
        expected: Option<&NativeCommitment<SC>>,
    ) -> Result<(), VerificationError>;
}
