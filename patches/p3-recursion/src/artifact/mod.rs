mod assembly;
pub(crate) mod binary_native;
mod descriptor;
pub(crate) mod native;
pub(crate) mod wire;

use alloc::boxed::Box;
use alloc::rc::Rc;
use alloc::sync::Arc;
use alloc::vec::Vec;

pub use binary_native::{
    BinaryNativeAuthority, BinaryNativeBooleanTraceAuthority, BinaryNativeBooleanTraceConfig,
    BinaryNativeBooleanTraceProver, BinaryNativeBooleanWhirTraceAuthority,
    BinaryNativeBooleanWhirTraceConfig, BinaryNativeBooleanWhirTraceProver, BinaryNativeChallenger,
    BinaryNativeConfig, BinaryNativeGroupedAuthority, BinaryNativeGroupedBooleanTraceAuthority,
    BinaryNativeGroupedBooleanTraceConfig, BinaryNativeGroupedBooleanTraceProver,
    BinaryNativeGroupedConfig, BinaryNativeGroupedPcsParameters, BinaryNativeGroupedProver,
    BinaryNativeGroupedVerifierSpec, BinaryNativeHash, BinaryNativePcsParameters,
    BinaryNativePolyWhirAuthority, BinaryNativePolyWhirConfig, BinaryNativePolyWhirLayout,
    BinaryNativePolyWhirPcsParameters, BinaryNativePolyWhirProver, BinaryNativeProver,
    BinaryNativeVerifierSpec, BinaryNativeWhirAuthority, BinaryNativeWhirConfig,
    BinaryNativeWhirLayout, BinaryNativeWhirPcsParameters, BinaryNativeWhirProver,
    CanonicalBinaryStatement, VerifiedBinaryNativeBooleanTraceProof,
    VerifiedBinaryNativeBooleanWhirTraceProof, VerifiedBinaryNativeGroupedBooleanTraceProof,
    VerifiedBinaryNativeGroupedProof, VerifiedBinaryNativePolyWhirProof, VerifiedBinaryNativeProof,
    VerifiedBinaryNativeWhirProof,
};
use p3_circuit::{StatementError, StatementSchema};
use p3_circuit_prover::{BatchStarkProof, CircuitVerifier};
use p3_uni_stark::{StarkGenericConfig, Val};

use crate::builtin_config::BuiltinConfigError;
use crate::{BatchOnly, TrustedPreparedInput, TrustedPreparedSource, VerifierLimits};

mod import_sealed {
    pub trait Sealed {}
}

pub struct TypedArtifactVerifier<SC: StarkGenericConfig + 'static> {
    state: Arc<TypedArtifactVerifierState<SC>>,
}

struct TypedArtifactVerifierState<SC: StarkGenericConfig + 'static> {
    verifier: CircuitVerifier<SC>,
    canonical_bytes: Vec<u8>,
    suite: crate::builtin_config::SuiteIdV1,
    limits: ArtifactLimits,
}

impl<SC: StarkGenericConfig + 'static> Clone for TypedArtifactVerifier<SC> {
    fn clone(&self) -> Self {
        Self {
            state: self.state.clone(),
        }
    }
}

impl<SC: StarkGenericConfig + 'static> TypedArtifactVerifier<SC> {
    fn from_parts(
        verifier: CircuitVerifier<SC>,
        canonical_bytes: Vec<u8>,
        suite: crate::builtin_config::SuiteIdV1,
        limits: ArtifactLimits,
    ) -> Self {
        Self {
            state: Arc::new(TypedArtifactVerifierState {
                verifier,
                canonical_bytes,
                suite,
                limits,
            }),
        }
    }

    pub fn trusted_identity_bytes(&self) -> &[u8] {
        &self.state.canonical_bytes
    }

    pub fn schema(&self) -> &StatementSchema {
        self.state.verifier.statement_layout().schema()
    }

    pub fn verifier(&self) -> &CircuitVerifier<SC> {
        &self.state.verifier
    }
}

pub struct VerifiedArtifactProof<SC: StarkGenericConfig + 'static> {
    proof: BatchStarkProof<SC>,
    statement: Vec<Val<SC>>,
    authority: TypedArtifactVerifier<SC>,
}

impl<SC: StarkGenericConfig + 'static> VerifiedArtifactProof<SC> {
    const fn from_parts(
        proof: BatchStarkProof<SC>,
        statement: Vec<Val<SC>>,
        authority: TypedArtifactVerifier<SC>,
    ) -> Self {
        Self {
            proof,
            statement,
            authority,
        }
    }

    pub fn statement(&self) -> &[Val<SC>] {
        &self.statement
    }

    pub fn trusted_identity_bytes(&self) -> &[u8] {
        self.authority.trusted_identity_bytes()
    }

    pub fn as_source(&self) -> TrustedPreparedSource<'static, '_, SC, BatchOnly> {
        TrustedPreparedSource::BatchStark {
            verifier: self.authority.state.verifier.clone(),
            proof: &self.proof,
            statement: &self.statement,
        }
    }

    pub fn as_input(&self) -> TrustedPreparedInput<'_, SC> {
        TrustedPreparedInput::BatchStark {
            proof: &self.proof,
            statement: &self.statement,
        }
    }
}

pub trait PortableArtifactImport: import_sealed::Sealed {
    type Config: StarkGenericConfig + 'static;

    fn decode_with_config(
        config: Self::Config,
        candidate: &[u8],
        expected: ExpectedVerifierArtifact<'_>,
        limits: ArtifactLimits,
    ) -> Result<Self, ArtifactError>
    where
        Self: Sized;

    fn import_proof(
        &self,
        bytes: &[u8],
        expected_statement: CanonicalStatement<'_>,
    ) -> Result<VerifiedArtifactProof<Self::Config>, ArtifactError>;
}

impl<SC: StarkGenericConfig + 'static> import_sealed::Sealed for TypedArtifactVerifier<SC> {}

#[derive(Clone, Copy, Debug)]
pub struct ExpectedVerifierArtifact<'a> {
    canonical_bytes: &'a [u8],
}

impl<'a> ExpectedVerifierArtifact<'a> {
    pub const fn from_trusted_bytes(bytes: &'a [u8]) -> Self {
        Self {
            canonical_bytes: bytes,
        }
    }
}

#[derive(Clone, Copy, Debug)]
pub struct CanonicalStatement<'a> {
    canonical_bytes: &'a [u8],
    element_count: usize,
}

impl<'a> CanonicalStatement<'a> {
    pub const fn new(canonical_bytes: &'a [u8], element_count: usize) -> Self {
        Self {
            canonical_bytes,
            element_count,
        }
    }
}

pub(crate) trait PortableVerifierInner {
    fn schema(&self) -> &StatementSchema;
    fn verify_encoded(
        &self,
        bytes: &[u8],
        expected: CanonicalStatement<'_>,
    ) -> Result<(), ArtifactError>;
}

#[derive(Clone)]
pub struct PortableVerifier {
    state: Rc<PortableVerifierState>,
}

struct PortableVerifierState {
    inner: Box<dyn PortableVerifierInner>,
    canonical_bytes: Vec<u8>,
}

impl PortableVerifier {
    fn from_parts(inner: Box<dyn PortableVerifierInner>, canonical_bytes: Vec<u8>) -> Self {
        Self {
            state: Rc::new(PortableVerifierState {
                inner,
                canonical_bytes,
            }),
        }
    }

    pub fn decode(
        candidate: &[u8],
        expected: ExpectedVerifierArtifact<'_>,
        limits: ArtifactLimits,
    ) -> Result<Self, ArtifactError> {
        check_expected_verifier_candidate(candidate, expected, &limits)?;
        assembly::decode_portable_verifier(candidate, limits)
    }

    pub fn verify_encoded(
        &self,
        proof: &[u8],
        expected_statement: CanonicalStatement<'_>,
    ) -> Result<(), ArtifactError> {
        self.state.inner.verify_encoded(proof, expected_statement)
    }

    pub fn schema(&self) -> &StatementSchema {
        self.state.inner.schema()
    }

    pub fn trusted_identity_bytes(&self) -> &[u8] {
        &self.state.canonical_bytes
    }
}

pub trait PortableArtifactExport {
    type Config: StarkGenericConfig;

    fn encode_verifier_artifact(&self, limits: ArtifactLimits) -> Result<Vec<u8>, ArtifactError>;
    fn encode_proof_artifact(
        &self,
        proof: &BatchStarkProof<Self::Config>,
        limits: ArtifactLimits,
    ) -> Result<Vec<u8>, ArtifactError>;
}

fn check_expected_verifier_candidate(
    candidate: &[u8],
    expected: ExpectedVerifierArtifact<'_>,
    limits: &ArtifactLimits,
) -> Result<(), ArtifactError> {
    wire::validate_frame_envelope(candidate, ArtifactKind::Verifier, limits.max_verifier_bytes)?;
    if candidate != expected.canonical_bytes {
        return Err(ArtifactError::TrustedArtifactMismatch);
    }
    Ok(())
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u8)]
pub enum ArtifactKind {
    Verifier = 1,
    Proof = 2,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ArtifactLimits {
    pub max_verifier_bytes: usize,
    pub max_proof_bytes: usize,
    pub max_decoded_bytes: usize,
    pub max_container_entries: usize,
    pub verifier: VerifierLimits,
}

impl Default for ArtifactLimits {
    fn default() -> Self {
        Self {
            max_verifier_bytes: 16 << 20,
            max_proof_bytes: 64 << 20,
            max_decoded_bytes: 128 << 20,
            max_container_entries: 1 << 20,
            verifier: VerifierLimits::default(),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, thiserror::Error)]
pub enum ArtifactError {
    #[error("artifact magic is not P3RCART\\0")]
    BadMagic,
    #[error("artifact has the wrong kind")]
    WrongArtifactKind,
    #[error("artifact format version {0} is unsupported")]
    UnsupportedVersion(u16),
    #[error("artifact suite {0} is unsupported")]
    UnsupportedSuite(u16),
    #[error("artifact built-in AIR tag {0} is unsupported")]
    UnsupportedBuiltinAir(u16),
    #[error("candidate verifier artifact does not match the independently trusted bytes")]
    TrustedArtifactMismatch,
    #[error(
        "artifact suite {actual} does not match the caller-supplied configuration suite {expected}"
    )]
    TypedSuiteMismatch { expected: u16, actual: u16 },
    #[error("artifact configuration descriptor does not match the caller-supplied configuration")]
    TypedConfigMismatch,
    #[error("artifact is truncated")]
    Truncated,
    #[error("artifact has trailing bytes")]
    TrailingBytes,
    #[error("artifact contains invalid tag {tag} for {component}")]
    InvalidTag { component: &'static str, tag: u8 },
    #[error("artifact contains a non-canonical field element")]
    NonCanonicalField,
    #[error("artifact contains non-canonical metadata")]
    NonCanonicalMetadata,
    #[error("artifact contains malformed proof data for {component}")]
    MalformedProof { component: &'static str },
    #[error("artifact length arithmetic overflowed")]
    LengthOverflow,
    #[error("artifact decode limit exceeded for {component}: {actual} > {limit}")]
    DecodeLimitExceeded {
        component: &'static str,
        actual: usize,
        limit: usize,
    },
    #[error("artifact allocation failed for {component}")]
    AllocationFailed { component: &'static str },
    #[error("artifact contains an invalid built-in configuration: {0}")]
    BuiltinConfig(#[from] BuiltinConfigError),
    #[error("artifact statement does not match the retained schema: {0}")]
    Statement(#[from] StatementError),
    #[error("artifact proof verification was rejected")]
    VerificationRejected,
}
