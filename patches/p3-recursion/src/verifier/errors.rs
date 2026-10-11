use alloc::string::String;

use p3_circuit::{CircuitBuilderError, CircuitError, StateTransitionError};
use p3_circuit_prover::BatchStarkProverError;
use thiserror::Error;

use crate::generation::GenerationError;
use crate::pcs::whir::params::WhirVerifierParamsError;

#[derive(Debug, Error)]
pub enum VerificationError {
    #[error("Invalid proof shape: {0}")]
    InvalidProofShape(String),

    #[error("prepared input does not match {component}")]
    PreparedInputMismatch { component: &'static str },

    #[error("verifier resource limit exceeded for {component}: {actual} > {limit}")]
    ResourceLimitExceeded {
        component: &'static str,
        actual: usize,
        limit: usize,
    },

    #[error("verifier resource arithmetic overflow for {component}")]
    ResourceArithmeticOverflow { component: &'static str },

    #[error("Missing random opened values for existing random commitment")]
    RandomizationError,

    #[error("Circuit error: {0}")]
    Circuit(#[from] CircuitError),

    #[error("Prover error: {0}")]
    Prover(#[from] BatchStarkProverError),

    #[error("Circuit builder error: {0}")]
    CircuitBuilder(#[from] CircuitBuilderError),

    #[error(transparent)]
    NativeBusCircuit(#[from] p3_circuit_prover::native_bus::NativeBusCircuitError),

    #[error(transparent)]
    StateTransition(#[from] StateTransitionError),

    #[error("Generation error: {0}")]
    Generation(#[from] GenerationError),

    #[error("WHIR verifier params error: {0}")]
    WhirVerifierParams(#[from] WhirVerifierParamsError),
}
