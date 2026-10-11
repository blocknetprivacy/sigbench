use alloc::boxed::Box;
use alloc::string::String;
use alloc::vec::Vec;

use p3_baby_bear::BabyBear;
use p3_circuit::ops::NpoTypeId;
use p3_circuit::{StatementError, StatementSchema};
use p3_circuit_prover::{BatchStarkProof, CircuitVerifier, NonPrimitiveTableEntry, TablePacking};
use p3_field::extension::{BinomialExtensionField, QuinticTrinomialExtensionField};
use p3_field::{Algebra, BasedVectorSpace, PrimeField64};
use p3_goldilocks::Goldilocks;
use p3_koala_bear::KoalaBear;
use p3_uni_stark::{StarkGenericConfig, SymbolicExpression, SymbolicExpressionExt};
use rand::rngs::StdRng;
use rand::{CryptoRng, SeedableRng};

use super::descriptor::{
    RelationDescriptorV1, read_common, read_config, read_relation, write_common, write_config,
    write_relation,
};
use super::native::{
    MerkleMmcsCodec, SaltedMerkleMmcsCodec, read_batch_proof, read_fri_proof,
    read_hiding_fri_proof, read_merkle_cap, read_whir_uni_proof, write_batch_proof,
    write_fri_proof, write_hiding_fri_proof, write_merkle_cap, write_whir_uni_proof,
};
use super::wire::{FieldEncoding, Reader, Writer, decode_framed, encode_framed};
use super::{
    ArtifactError, ArtifactKind, ArtifactLimits, CanonicalStatement, ExpectedVerifierArtifact,
    PortableArtifactImport, PortableVerifier, PortableVerifierInner, TypedArtifactVerifier,
    VerifiedArtifactProof, check_expected_verifier_candidate,
};
use crate::builtin_config::*;

mod private {
    pub trait Sealed {}
}

pub(crate) trait BuiltinArtifactConfig:
    private::Sealed + StarkGenericConfig + Sized + Send + Sync + 'static
where
    p3_batch_stark::Val<Self>: PrimeField64,
    Self::Challenge: BasedVectorSpace<p3_batch_stark::Val<Self>>,
{
    fn artifact_descriptor(&self) -> BuiltinConfigDescriptorV1;
    fn field_encoding() -> FieldEncoding<p3_batch_stark::Val<Self>>;
    fn reconstruct(
        descriptor: &BuiltinConfigDescriptorV1,
        limits: &ArtifactLimits,
    ) -> Result<Self, ArtifactError>;
    fn write_commitment(
        writer: &mut Writer,
        commitment: &p3_batch_stark::Commitment<Self>,
    ) -> Result<(), ArtifactError>;
    fn read_commitment(
        reader: &mut Reader<'_>,
    ) -> Result<p3_batch_stark::Commitment<Self>, ArtifactError>;
    fn write_opening_proof(
        writer: &mut Writer,
        proof: &p3_batch_stark::PcsProof<Self>,
    ) -> Result<(), ArtifactError>;
    fn read_opening_proof(
        reader: &mut Reader<'_>,
    ) -> Result<p3_batch_stark::PcsProof<Self>, ArtifactError>;
}

macro_rules! ordinary_impl {
    ($config:ty, $field:ty, $challenge:ty, $digest:expr, $encoding:expr, $factory:path) => {
        impl private::Sealed for $config {}
        impl BuiltinArtifactConfig for $config {
            fn artifact_descriptor(&self) -> BuiltinConfigDescriptorV1 {
                BuiltinConfigDescriptorV1::Fri(*self.descriptor())
            }

            fn field_encoding() -> FieldEncoding<p3_batch_stark::Val<Self>> {
                $encoding
            }

            fn reconstruct(
                descriptor: &BuiltinConfigDescriptorV1,
                limits: &ArtifactLimits,
            ) -> Result<Self, ArtifactError> {
                let BuiltinConfigDescriptorV1::Fri(descriptor) = descriptor else {
                    return Err(ArtifactError::NonCanonicalMetadata);
                };
                Ok($factory(descriptor, &limits.verifier)?)
            }

            fn write_commitment(
                writer: &mut Writer,
                commitment: &p3_batch_stark::Commitment<Self>,
            ) -> Result<(), ArtifactError> {
                write_merkle_cap::<$field, $digest>(writer, commitment, Self::field_encoding())
            }

            fn read_commitment(
                reader: &mut Reader<'_>,
            ) -> Result<p3_batch_stark::Commitment<Self>, ArtifactError> {
                read_merkle_cap::<$field, $digest>(reader, Self::field_encoding())
            }

            fn write_opening_proof(
                writer: &mut Writer,
                proof: &p3_batch_stark::PcsProof<Self>,
            ) -> Result<(), ArtifactError> {
                let codec = MerkleMmcsCodec::<$field, $digest>::new(Self::field_encoding());
                write_fri_proof::<$field, $challenge, _, _, _, _>(
                    writer,
                    proof,
                    Self::field_encoding(),
                    &codec,
                    &codec,
                )
            }

            fn read_opening_proof(
                reader: &mut Reader<'_>,
            ) -> Result<p3_batch_stark::PcsProof<Self>, ArtifactError> {
                let codec = MerkleMmcsCodec::<$field, $digest>::new(Self::field_encoding());
                read_fri_proof::<$field, $challenge, _, _, _, _>(
                    reader,
                    Self::field_encoding(),
                    &codec,
                    &codec,
                )
            }
        }
    };
}

ordinary_impl!(BabyBearD4Poseidon2BinaryConfig, BabyBear, BinomialExtensionField<BabyBear, 4>, 8, FieldEncoding::u32(), baby_bear_d4_poseidon2_binary);
ordinary_impl!(BabyBearD4Poseidon1BinaryConfig, BabyBear, BinomialExtensionField<BabyBear, 4>, 8, FieldEncoding::u32(), baby_bear_d4_poseidon1_binary);
ordinary_impl!(KoalaBearD4Poseidon2BinaryConfig, KoalaBear, BinomialExtensionField<KoalaBear, 4>, 8, FieldEncoding::u32(), koala_bear_d4_poseidon2_binary);
ordinary_impl!(KoalaBearD4Poseidon1BinaryConfig, KoalaBear, BinomialExtensionField<KoalaBear, 4>, 8, FieldEncoding::u32(), koala_bear_d4_poseidon1_binary);
ordinary_impl!(GoldilocksD2Poseidon2BinaryConfig, Goldilocks, BinomialExtensionField<Goldilocks, 2>, 4, FieldEncoding::u64(), goldilocks_d2_poseidon2_binary);
ordinary_impl!(GoldilocksD2Poseidon1BinaryConfig, Goldilocks, BinomialExtensionField<Goldilocks, 2>, 4, FieldEncoding::u64(), goldilocks_d2_poseidon1_binary);
ordinary_impl!(
    KoalaBearD5Poseidon2BinaryConfig,
    KoalaBear,
    QuinticTrinomialExtensionField<KoalaBear>,
    8,
    FieldEncoding::u32(),
    koala_bear_d5_poseidon2_binary
);
ordinary_impl!(
    KoalaBearD5Poseidon1BinaryConfig,
    KoalaBear,
    QuinticTrinomialExtensionField<KoalaBear>,
    8,
    FieldEncoding::u32(),
    koala_bear_d5_poseidon1_binary
);
ordinary_impl!(BabyBearD4Poseidon2QuaternaryConfig, BabyBear, BinomialExtensionField<BabyBear, 4>, 8, FieldEncoding::u32(), baby_bear_d4_poseidon2_quaternary);
ordinary_impl!(KoalaBearD4Poseidon2QuaternaryConfig, KoalaBear, BinomialExtensionField<KoalaBear, 4>, 8, FieldEncoding::u32(), koala_bear_d4_poseidon2_quaternary);
ordinary_impl!(GoldilocksD2Poseidon2QuaternaryConfig, Goldilocks, BinomialExtensionField<Goldilocks, 2>, 4, FieldEncoding::u64(), goldilocks_d2_poseidon2_quaternary);
ordinary_impl!(
    KoalaBearD5Poseidon2QuaternaryConfig,
    KoalaBear,
    QuinticTrinomialExtensionField<KoalaBear>,
    8,
    FieldEncoding::u32(),
    koala_bear_d5_poseidon2_quaternary
);

macro_rules! random_codeword_impl {
    ($config:ident, $field:ty, $challenge:ty, $digest:expr, $encoding:expr, $factory:path) => {
        impl<R> private::Sealed for $config<R> where
            R: CryptoRng + SeedableRng + Send + Sync + 'static
        {
        }
        impl<R> BuiltinArtifactConfig for $config<R>
        where
            R: CryptoRng + SeedableRng + Send + Sync + 'static,
        {
            fn artifact_descriptor(&self) -> BuiltinConfigDescriptorV1 {
                BuiltinConfigDescriptorV1::Fri(*self.descriptor())
            }
            fn field_encoding() -> FieldEncoding<p3_batch_stark::Val<Self>> {
                $encoding
            }
            fn reconstruct(
                descriptor: &BuiltinConfigDescriptorV1,
                limits: &ArtifactLimits,
            ) -> Result<Self, ArtifactError> {
                let BuiltinConfigDescriptorV1::Fri(descriptor) = descriptor else {
                    return Err(ArtifactError::NonCanonicalMetadata);
                };
                Ok($factory(
                    descriptor,
                    &limits.verifier,
                    R::seed_from_u64(0x5033_4152_5449_4631),
                )?)
            }
            fn write_commitment(
                writer: &mut Writer,
                commitment: &p3_batch_stark::Commitment<Self>,
            ) -> Result<(), ArtifactError> {
                write_merkle_cap::<$field, $digest>(writer, commitment, Self::field_encoding())
            }
            fn read_commitment(
                reader: &mut Reader<'_>,
            ) -> Result<p3_batch_stark::Commitment<Self>, ArtifactError> {
                read_merkle_cap::<$field, $digest>(reader, Self::field_encoding())
            }
            fn write_opening_proof(
                writer: &mut Writer,
                proof: &p3_batch_stark::PcsProof<Self>,
            ) -> Result<(), ArtifactError> {
                let codec = MerkleMmcsCodec::<$field, $digest>::new(Self::field_encoding());
                write_hiding_fri_proof::<$field, $challenge, _, _, _, _>(
                    writer,
                    proof,
                    Self::field_encoding(),
                    &codec,
                    &codec,
                )
            }
            fn read_opening_proof(
                reader: &mut Reader<'_>,
            ) -> Result<p3_batch_stark::PcsProof<Self>, ArtifactError> {
                let codec = MerkleMmcsCodec::<$field, $digest>::new(Self::field_encoding());
                read_hiding_fri_proof::<$field, $challenge, _, _, _, _>(
                    reader,
                    Self::field_encoding(),
                    &codec,
                    &codec,
                )
            }
        }
    };
}

random_codeword_impl!(BabyBearD4Poseidon2RandomCodewordConfig, BabyBear, BinomialExtensionField<BabyBear, 4>, 8, FieldEncoding::u32(), baby_bear_d4_poseidon2_random_codeword);
random_codeword_impl!(BabyBearD4Poseidon1RandomCodewordConfig, BabyBear, BinomialExtensionField<BabyBear, 4>, 8, FieldEncoding::u32(), baby_bear_d4_poseidon1_random_codeword);
random_codeword_impl!(KoalaBearD4Poseidon2RandomCodewordConfig, KoalaBear, BinomialExtensionField<KoalaBear, 4>, 8, FieldEncoding::u32(), koala_bear_d4_poseidon2_random_codeword);
random_codeword_impl!(KoalaBearD4Poseidon1RandomCodewordConfig, KoalaBear, BinomialExtensionField<KoalaBear, 4>, 8, FieldEncoding::u32(), koala_bear_d4_poseidon1_random_codeword);
random_codeword_impl!(GoldilocksD2Poseidon2RandomCodewordConfig, Goldilocks, BinomialExtensionField<Goldilocks, 2>, 4, FieldEncoding::u64(), goldilocks_d2_poseidon2_random_codeword);
random_codeword_impl!(GoldilocksD2Poseidon1RandomCodewordConfig, Goldilocks, BinomialExtensionField<Goldilocks, 2>, 4, FieldEncoding::u64(), goldilocks_d2_poseidon1_random_codeword);

impl<R> private::Sealed for KoalaBearD4Poseidon2SaltedConfig<R> where
    R: CryptoRng + SeedableRng + Send + Sync + 'static
{
}
impl<R> BuiltinArtifactConfig for KoalaBearD4Poseidon2SaltedConfig<R>
where
    R: CryptoRng + SeedableRng + Send + Sync + 'static,
{
    fn artifact_descriptor(&self) -> BuiltinConfigDescriptorV1 {
        BuiltinConfigDescriptorV1::Fri(*self.descriptor())
    }
    fn field_encoding() -> FieldEncoding<p3_batch_stark::Val<Self>> {
        FieldEncoding::u32()
    }
    fn reconstruct(
        descriptor: &BuiltinConfigDescriptorV1,
        limits: &ArtifactLimits,
    ) -> Result<Self, ArtifactError> {
        let BuiltinConfigDescriptorV1::Fri(descriptor) = descriptor else {
            return Err(ArtifactError::NonCanonicalMetadata);
        };
        Ok(koala_bear_d4_poseidon2_salted(
            descriptor,
            &limits.verifier,
            R::seed_from_u64(1),
            R::seed_from_u64(2),
            R::seed_from_u64(3),
        )?)
    }
    fn write_commitment(
        writer: &mut Writer,
        commitment: &p3_batch_stark::Commitment<Self>,
    ) -> Result<(), ArtifactError> {
        write_merkle_cap::<KoalaBear, 8>(writer, commitment, Self::field_encoding())
    }
    fn read_commitment(
        reader: &mut Reader<'_>,
    ) -> Result<p3_batch_stark::Commitment<Self>, ArtifactError> {
        read_merkle_cap::<KoalaBear, 8>(reader, Self::field_encoding())
    }
    fn write_opening_proof(
        writer: &mut Writer,
        proof: &p3_batch_stark::PcsProof<Self>,
    ) -> Result<(), ArtifactError> {
        let codec = SaltedMerkleMmcsCodec::<KoalaBear, 8, 4>::new(Self::field_encoding());
        write_hiding_fri_proof::<KoalaBear, BinomialExtensionField<KoalaBear, 4>, _, _, _, _>(
            writer,
            proof,
            Self::field_encoding(),
            &codec,
            &codec,
        )
    }
    fn read_opening_proof(
        reader: &mut Reader<'_>,
    ) -> Result<p3_batch_stark::PcsProof<Self>, ArtifactError> {
        let codec = SaltedMerkleMmcsCodec::<KoalaBear, 8, 4>::new(Self::field_encoding());
        read_hiding_fri_proof::<KoalaBear, BinomialExtensionField<KoalaBear, 4>, _, _, _, _>(
            reader,
            Self::field_encoding(),
            &codec,
            &codec,
        )
    }
}

macro_rules! whir_impl {
    ($config:ty, $field:ty, $challenge:ty, $encoding:expr, $factory:path) => {
        impl private::Sealed for $config {}
        impl BuiltinArtifactConfig for $config {
            fn artifact_descriptor(&self) -> BuiltinConfigDescriptorV1 {
                BuiltinConfigDescriptorV1::Whir(self.descriptor().clone())
            }
            fn field_encoding() -> FieldEncoding<p3_batch_stark::Val<Self>> {
                $encoding
            }
            fn reconstruct(
                descriptor: &BuiltinConfigDescriptorV1,
                limits: &ArtifactLimits,
            ) -> Result<Self, ArtifactError> {
                let BuiltinConfigDescriptorV1::Whir(descriptor) = descriptor else {
                    return Err(ArtifactError::NonCanonicalMetadata);
                };
                Ok($factory(descriptor, &limits.verifier)?)
            }
            fn write_commitment(
                writer: &mut Writer,
                commitment: &p3_batch_stark::Commitment<Self>,
            ) -> Result<(), ArtifactError> {
                write_merkle_cap::<$field, 8>(writer, commitment, Self::field_encoding())
            }
            fn read_commitment(
                reader: &mut Reader<'_>,
            ) -> Result<p3_batch_stark::Commitment<Self>, ArtifactError> {
                read_merkle_cap::<$field, 8>(reader, Self::field_encoding())
            }
            fn write_opening_proof(
                writer: &mut Writer,
                proof: &p3_batch_stark::PcsProof<Self>,
            ) -> Result<(), ArtifactError> {
                let codec = MerkleMmcsCodec::<$field, 8>::new(Self::field_encoding());
                write_whir_uni_proof::<$field, $challenge, _, _>(
                    writer,
                    proof,
                    Self::field_encoding(),
                    &codec,
                )
            }
            fn read_opening_proof(
                reader: &mut Reader<'_>,
            ) -> Result<p3_batch_stark::PcsProof<Self>, ArtifactError> {
                let codec = MerkleMmcsCodec::<$field, 8>::new(Self::field_encoding());
                read_whir_uni_proof::<$field, $challenge, _, _>(
                    reader,
                    Self::field_encoding(),
                    &codec,
                )
            }
        }
    };
}

whir_impl!(BabyBearD4Poseidon2WhirConfig, BabyBear, BinomialExtensionField<BabyBear, 4>, FieldEncoding::u32(), baby_bear_d4_poseidon2_whir);
whir_impl!(KoalaBearD4Poseidon2WhirConfig, KoalaBear, BinomialExtensionField<KoalaBear, 4>, FieldEncoding::u32(), koala_bear_d4_poseidon2_whir);

pub(crate) fn encode_verifier<SC>(
    verifier: &CircuitVerifier<SC>,
    limits: ArtifactLimits,
) -> Result<Vec<u8>, ArtifactError>
where
    SC: BuiltinArtifactConfig,
    p3_batch_stark::Val<SC>: p3_circuit_prover::config::StarkField + PrimeField64,
    SC::Challenge: BasedVectorSpace<p3_batch_stark::Val<SC>>,
    SymbolicExpressionExt<p3_batch_stark::Val<SC>, SC::Challenge>:
        Algebra<SymbolicExpression<p3_batch_stark::Val<SC>>> + Algebra<SC::Challenge>,
{
    let descriptor = verifier.config().artifact_descriptor();
    let suite = descriptor.suite();
    let relation = RelationDescriptorV1::from_native(verifier.relation())?;
    encode_framed(
        super::ArtifactKind::Verifier,
        suite.as_u16(),
        limits.max_verifier_bytes,
        |writer| {
            writer.write_u16(suite.spec().protocol_revision)?;
            write_config(writer, &descriptor)?;
            write_relation(writer, &relation, SC::field_encoding())?;
            write_common(writer, verifier.common_data(), SC::write_commitment)
        },
    )
}

pub(crate) fn encode_proof<SC>(
    verifier: &CircuitVerifier<SC>,
    proof: &BatchStarkProof<SC>,
    limits: ArtifactLimits,
) -> Result<Vec<u8>, ArtifactError>
where
    SC::Challenger: p3_challenger::GrindingChallenger<Witness = p3_uni_stark::Val<SC>>,
    SC: BuiltinArtifactConfig,
    p3_batch_stark::Val<SC>: p3_circuit_prover::config::StarkField + PrimeField64,
    SC::Challenge: BasedVectorSpace<p3_batch_stark::Val<SC>>,
    SymbolicExpressionExt<p3_batch_stark::Val<SC>, SC::Challenge>:
        Algebra<SymbolicExpression<p3_batch_stark::Val<SC>>> + Algebra<SC::Challenge>,
{
    let statement = match verifier.statement_layout().table_instance() {
        Some(instance) => proof
            .non_primitives
            .get(instance - p3_circuit_prover::NUM_PRIMITIVE_TABLES)
            .ok_or(ArtifactError::NonCanonicalMetadata)?
            .public_values
            .as_slice(),
        None => &[],
    };
    verifier
        .verify(proof, statement)
        .map_err(|_| ArtifactError::VerificationRejected)?;
    let suite = verifier.config().artifact_descriptor().suite();
    encode_framed(
        ArtifactKind::Proof,
        suite.as_u16(),
        limits.max_proof_bytes,
        |writer| {
            writer.write_u16(suite.spec().protocol_revision)?;
            writer.write_vec("attached statement", statement, |writer, value| {
                writer.write_field(SC::field_encoding(), *value)
            })?;
            write_batch_proof::<SC, p3_batch_stark::Val<SC>>(
                writer,
                &proof.proof,
                SC::field_encoding(),
                SC::write_commitment,
                SC::write_opening_proof,
            )
        },
    )
}

impl<SC> super::PortableArtifactExport for CircuitVerifier<SC>
where
    SC::Challenger: p3_challenger::GrindingChallenger<Witness = p3_uni_stark::Val<SC>>,
    SC: BuiltinArtifactConfig,
    p3_batch_stark::Val<SC>: p3_circuit_prover::config::StarkField + PrimeField64,
    SC::Challenge: BasedVectorSpace<p3_batch_stark::Val<SC>>,
    SymbolicExpressionExt<p3_batch_stark::Val<SC>, SC::Challenge>:
        Algebra<SymbolicExpression<p3_batch_stark::Val<SC>>> + Algebra<SC::Challenge>,
{
    type Config = SC;

    fn encode_verifier_artifact(&self, limits: ArtifactLimits) -> Result<Vec<u8>, ArtifactError> {
        encode_verifier(self, limits)
    }

    fn encode_proof_artifact(
        &self,
        proof: &BatchStarkProof<Self::Config>,
        limits: ArtifactLimits,
    ) -> Result<Vec<u8>, ArtifactError> {
        encode_proof(self, proof, limits)
    }
}

pub(crate) struct TypedPortableVerifier<SC>
where
    SC: BuiltinArtifactConfig,
    p3_batch_stark::Val<SC>: p3_circuit_prover::config::StarkField + PrimeField64,
    SC::Challenge: BasedVectorSpace<p3_batch_stark::Val<SC>>,
{
    verifier: CircuitVerifier<SC>,
    suite: SuiteIdV1,
    limits: ArtifactLimits,
}

fn try_copy_slice<T: Copy>(
    reader: &mut Reader<'_>,
    values: &[T],
    component: &'static str,
) -> Result<Vec<T>, ArtifactError> {
    reader.charge_conversion_vec::<T>(values.len())?;
    let mut copied = Vec::new();
    copied
        .try_reserve_exact(values.len())
        .map_err(|_| ArtifactError::AllocationFailed { component })?;
    copied.extend_from_slice(values);
    Ok(copied)
}

fn try_copy_npo_id(reader: &mut Reader<'_>, id: &NpoTypeId) -> Result<NpoTypeId, ArtifactError> {
    reader.charge_conversion_vec::<u8>(id.as_str().len())?;
    let mut owned = String::new();
    owned
        .try_reserve_exact(id.as_str().len())
        .map_err(|_| ArtifactError::AllocationFailed {
            component: "NPO identifier copy",
        })?;
    owned.push_str(id.as_str());
    Ok(NpoTypeId::new(owned))
}

fn charge_table_packing_copy(
    reader: &mut Reader<'_>,
    packing: &TablePacking,
) -> Result<(), ArtifactError> {
    let lane_count = packing.npo_lanes_iter().count();
    reader.charge_conversion_vec::<(NpoTypeId, usize)>(lane_count)?;
    for (id, _) in packing.npo_lanes_iter() {
        reader.charge_conversion_vec::<u8>(id.as_str().len())?;
    }
    let height_count = packing.npo_min_heights().count();
    reader.charge_conversion_vec::<(NpoTypeId, usize)>(height_count)?;
    for (id, _) in packing.npo_min_heights() {
        reader.charge_conversion_vec::<u8>(id.as_str().len())?;
    }
    Ok(())
}

impl<SC> PortableVerifierInner for TypedPortableVerifier<SC>
where
    SC::Challenger: p3_challenger::GrindingChallenger<Witness = p3_uni_stark::Val<SC>>,
    SC: BuiltinArtifactConfig,
    p3_batch_stark::Val<SC>: p3_circuit_prover::config::StarkField + PrimeField64,
    SC::Challenge: BasedVectorSpace<p3_batch_stark::Val<SC>>,
    SymbolicExpressionExt<p3_batch_stark::Val<SC>, SC::Challenge>:
        Algebra<SymbolicExpression<p3_batch_stark::Val<SC>>> + Algebra<SC::Challenge>,
{
    fn schema(&self) -> &StatementSchema {
        self.verifier.statement_layout().schema()
    }

    fn verify_encoded(
        &self,
        bytes: &[u8],
        expected: CanonicalStatement<'_>,
    ) -> Result<(), ArtifactError> {
        decode_verified_proof(&self.verifier, self.suite, &self.limits, bytes, expected).map(|_| ())
    }
}

fn decode_verified_proof<SC>(
    verifier: &CircuitVerifier<SC>,
    suite: SuiteIdV1,
    limits: &ArtifactLimits,
    bytes: &[u8],
    expected: CanonicalStatement<'_>,
) -> Result<(BatchStarkProof<SC>, Vec<p3_batch_stark::Val<SC>>), ArtifactError>
where
    SC::Challenger: p3_challenger::GrindingChallenger<Witness = p3_uni_stark::Val<SC>>,
    SC: BuiltinArtifactConfig,
    p3_batch_stark::Val<SC>: p3_circuit_prover::config::StarkField + PrimeField64,
    SC::Challenge: BasedVectorSpace<p3_batch_stark::Val<SC>>,
    SymbolicExpressionExt<p3_batch_stark::Val<SC>, SC::Challenge>:
        Algebra<SymbolicExpression<p3_batch_stark::Val<SC>>> + Algebra<SC::Challenge>,
{
    let (native, expected_statement) = decode_framed(
        bytes,
        ArtifactKind::Proof,
        limits,
        |raw| raw == suite.as_u16(),
        |raw, reader| {
            if raw != suite.as_u16() || reader.read_u16()? != suite.spec().protocol_revision {
                return Err(ArtifactError::NonCanonicalMetadata);
            }
            let expected_statement = decode_canonical_statement::<p3_batch_stark::Val<SC>>(
                expected,
                verifier.statement_layout().schema(),
                SC::field_encoding(),
                reader,
            )?;
            let attached = reader.read_vec_exact(
                "attached statement",
                verifier.statement_layout().schema().base_len(),
                SC::field_encoding().encoded_bytes(),
                |reader| reader.read_field(SC::field_encoding()),
            )?;
            let proof = read_batch_proof::<SC, p3_batch_stark::Val<SC>>(
                reader,
                SC::field_encoding(),
                SC::read_commitment,
                SC::read_opening_proof,
            )?;
            let relation = verifier.relation();
            reader.charge_conversion_vec::<NonPrimitiveTableEntry<SC>>(
                relation.non_primitives().len(),
            )?;
            let mut non_primitives = Vec::new();
            non_primitives
                .try_reserve_exact(relation.non_primitives().len())
                .map_err(|_| ArtifactError::AllocationFailed {
                    component: "proof NPO conversion",
                })?;
            let statement_index = verifier
                .statement_layout()
                .table_instance()
                .and_then(|index| index.checked_sub(p3_circuit_prover::NUM_PRIMITIVE_TABLES));
            let mut attached = Some(attached);
            for (index, npo) in relation.non_primitives().iter().enumerate() {
                let public_values = if statement_index == Some(index) {
                    attached.take().ok_or(ArtifactError::NonCanonicalMetadata)?
                } else {
                    try_copy_slice(reader, npo.public_values(), "NPO public values copy")?
                };
                non_primitives.push(NonPrimitiveTableEntry {
                    op_type: try_copy_npo_id(reader, npo.op_type())?,
                    rows: npo.rows(),
                    lanes: npo.lanes(),
                    public_values,
                    air_variant: npo.air_variant(),
                });
            }
            charge_table_packing_copy(reader, relation.table_packing())?;
            let table_packing =
                relation
                    .table_packing()
                    .try_clone_for_artifact()
                    .map_err(|_| ArtifactError::AllocationFailed {
                        component: "table packing copy",
                    })?;
            reader.charge_conversion_vec::<()>(0)?;
            let (w_binomial, alu_quintic_trinomial) = match relation.reduction() {
                p3_circuit_prover::air::AluExtMulKind::Base => (None, false),
                p3_circuit_prover::air::AluExtMulKind::Binomial { w } => (Some(w), false),
                p3_circuit_prover::air::AluExtMulKind::QuinticTrinomial => (None, true),
            };
            let native = BatchStarkProof {
                proof,
                table_packing,
                rows: *relation.rows(),
                alu_variant: relation.alu_variant(),
                ext_degree: relation.ext_degree(),
                w_binomial,
                alu_quintic_trinomial,
                non_primitives,
                stark_common: p3_batch_stark::CommonData::new(None, Vec::new()),
            };
            Ok((native, expected_statement))
        },
    )?;
    verifier
        .verify(&native, &expected_statement)
        .map_err(|_| ArtifactError::VerificationRejected)?;
    Ok((native, expected_statement))
}

fn decode_canonical_statement<F: PrimeField64>(
    expected: CanonicalStatement<'_>,
    schema: &StatementSchema,
    field: FieldEncoding<F>,
    reader: &mut Reader<'_>,
) -> Result<Vec<F>, ArtifactError> {
    if expected.element_count != schema.base_len() {
        return Err(ArtifactError::Statement(
            StatementError::ValueLengthMismatch {
                expected: schema.base_len(),
                got: expected.element_count,
            },
        ));
    }
    reader.read_alternate_slice(expected.canonical_bytes, |reader| {
        reader.read_exact_items(
            "expected statement",
            expected.element_count,
            field.encoded_bytes(),
            |reader| reader.read_field(field),
        )
    })
}

pub(crate) fn decode_portable_verifier(
    candidate: &[u8],
    limits: ArtifactLimits,
) -> Result<PortableVerifier, ArtifactError> {
    let raw_suite = u16::from_le_bytes(candidate[11..13].try_into().unwrap());
    let suite = SuiteIdV1::from_u16(raw_suite)?;
    macro_rules! decode {
        ($config:ty) => {
            decode_typed::<$config>(candidate, suite, limits)
        };
    }
    match suite {
        SuiteIdV1::BabyBearD4Poseidon2BinaryFri => decode!(BabyBearD4Poseidon2BinaryConfig),
        SuiteIdV1::BabyBearD4Poseidon1BinaryFri => decode!(BabyBearD4Poseidon1BinaryConfig),
        SuiteIdV1::KoalaBearD4Poseidon2BinaryFri => decode!(KoalaBearD4Poseidon2BinaryConfig),
        SuiteIdV1::KoalaBearD4Poseidon1BinaryFri => decode!(KoalaBearD4Poseidon1BinaryConfig),
        SuiteIdV1::GoldilocksD2Poseidon2BinaryFri => decode!(GoldilocksD2Poseidon2BinaryConfig),
        SuiteIdV1::GoldilocksD2Poseidon1BinaryFri => decode!(GoldilocksD2Poseidon1BinaryConfig),
        SuiteIdV1::KoalaBearD5Poseidon2BinaryFri => decode!(KoalaBearD5Poseidon2BinaryConfig),
        SuiteIdV1::KoalaBearD5Poseidon1BinaryFri => decode!(KoalaBearD5Poseidon1BinaryConfig),
        SuiteIdV1::BabyBearD4Poseidon2QuaternaryFri => decode!(BabyBearD4Poseidon2QuaternaryConfig),
        SuiteIdV1::KoalaBearD4Poseidon2QuaternaryFri => {
            decode!(KoalaBearD4Poseidon2QuaternaryConfig)
        }
        SuiteIdV1::GoldilocksD2Poseidon2QuaternaryFri => {
            decode!(GoldilocksD2Poseidon2QuaternaryConfig)
        }
        SuiteIdV1::KoalaBearD5Poseidon2QuaternaryFri => {
            decode!(KoalaBearD5Poseidon2QuaternaryConfig)
        }
        SuiteIdV1::BabyBearD4Poseidon2RandomCodewordFri => {
            decode!(BabyBearD4Poseidon2RandomCodewordConfig<StdRng>)
        }
        SuiteIdV1::BabyBearD4Poseidon1RandomCodewordFri => {
            decode!(BabyBearD4Poseidon1RandomCodewordConfig<StdRng>)
        }
        SuiteIdV1::KoalaBearD4Poseidon2RandomCodewordFri => {
            decode!(KoalaBearD4Poseidon2RandomCodewordConfig<StdRng>)
        }
        SuiteIdV1::KoalaBearD4Poseidon1RandomCodewordFri => {
            decode!(KoalaBearD4Poseidon1RandomCodewordConfig<StdRng>)
        }
        SuiteIdV1::GoldilocksD2Poseidon2RandomCodewordFri => {
            decode!(GoldilocksD2Poseidon2RandomCodewordConfig<StdRng>)
        }
        SuiteIdV1::GoldilocksD2Poseidon1RandomCodewordFri => {
            decode!(GoldilocksD2Poseidon1RandomCodewordConfig<StdRng>)
        }
        SuiteIdV1::KoalaBearD4Poseidon2SaltedFri => {
            decode!(KoalaBearD4Poseidon2SaltedConfig<StdRng>)
        }
        SuiteIdV1::BabyBearD4Poseidon2Whir => decode!(BabyBearD4Poseidon2WhirConfig),
        SuiteIdV1::KoalaBearD4Poseidon2Whir => decode!(KoalaBearD4Poseidon2WhirConfig),
    }
}

fn decode_typed<SC>(
    candidate: &[u8],
    suite: SuiteIdV1,
    limits: ArtifactLimits,
) -> Result<PortableVerifier, ArtifactError>
where
    SC::Challenger: p3_challenger::GrindingChallenger<Witness = p3_uni_stark::Val<SC>>,
    SC: BuiltinArtifactConfig,
    p3_batch_stark::Val<SC>: p3_circuit_prover::config::StarkField + PrimeField64,
    SC::Challenge: BasedVectorSpace<p3_batch_stark::Val<SC>>,
    SymbolicExpressionExt<p3_batch_stark::Val<SC>, SC::Challenge>:
        Algebra<SymbolicExpression<p3_batch_stark::Val<SC>>> + Algebra<SC::Challenge>,
{
    let (descriptor, relation, common) =
        decode_verifier_parts::<SC>(candidate, suite, &limits, None)?;
    let config = SC::reconstruct(&descriptor, &limits)?;
    let verifier = CircuitVerifier::from_independently_trusted_builtin_artifact(
        config,
        relation.into_trusted()?,
        common,
    )
    .map_err(|_| ArtifactError::NonCanonicalMetadata)?;
    let canonical = encode_verifier(&verifier, limits)?;
    if canonical != candidate {
        return Err(ArtifactError::NonCanonicalMetadata);
    }
    Ok(PortableVerifier::from_parts(
        Box::new(TypedPortableVerifier {
            verifier,
            suite,
            limits,
        }),
        canonical,
    ))
}

type DecodedVerifierParts<SC> = (
    BuiltinConfigDescriptorV1,
    RelationDescriptorV1<p3_batch_stark::Val<SC>>,
    p3_batch_stark::CommonData<SC>,
);

fn decode_verifier_parts<SC>(
    candidate: &[u8],
    suite: SuiteIdV1,
    limits: &ArtifactLimits,
    expected_descriptor: Option<&BuiltinConfigDescriptorV1>,
) -> Result<DecodedVerifierParts<SC>, ArtifactError>
where
    SC: BuiltinArtifactConfig,
    p3_batch_stark::Val<SC>: PrimeField64,
    SC::Challenge: BasedVectorSpace<p3_batch_stark::Val<SC>>,
{
    decode_framed(
        candidate,
        ArtifactKind::Verifier,
        limits,
        |raw| raw == suite.as_u16(),
        |raw, reader| {
            if raw != suite.as_u16() || reader.read_u16()? != suite.spec().protocol_revision {
                return Err(ArtifactError::NonCanonicalMetadata);
            }
            let descriptor = read_config(reader, suite)?;
            if expected_descriptor.is_some_and(|expected| expected != &descriptor) {
                return Err(ArtifactError::TypedConfigMismatch);
            }
            let relation = read_relation(reader, SC::field_encoding())?;
            let common = read_common::<SC>(reader, SC::read_commitment)?;
            Ok((descriptor, relation, common))
        },
    )
}

impl<SC> PortableArtifactImport for TypedArtifactVerifier<SC>
where
    SC::Challenger: p3_challenger::GrindingChallenger<Witness = p3_uni_stark::Val<SC>>,
    SC: BuiltinArtifactConfig,
    p3_batch_stark::Val<SC>: p3_circuit_prover::config::StarkField + PrimeField64,
    SC::Challenge: BasedVectorSpace<p3_batch_stark::Val<SC>>,
    SymbolicExpressionExt<p3_batch_stark::Val<SC>, SC::Challenge>:
        Algebra<SymbolicExpression<p3_batch_stark::Val<SC>>> + Algebra<SC::Challenge>,
{
    type Config = SC;

    fn decode_with_config(
        config: SC,
        candidate: &[u8],
        expected: ExpectedVerifierArtifact<'_>,
        limits: ArtifactLimits,
    ) -> Result<Self, ArtifactError> {
        check_expected_verifier_candidate(candidate, expected, &limits)?;
        let descriptor = config.artifact_descriptor();
        let suite = descriptor.suite();
        let actual = u16::from_le_bytes(candidate[11..13].try_into().unwrap());
        if actual != suite.as_u16() {
            return Err(ArtifactError::TypedSuiteMismatch {
                expected: suite.as_u16(),
                actual,
            });
        }
        let (_, relation, common) =
            decode_verifier_parts::<SC>(candidate, suite, &limits, Some(&descriptor))?;
        let verifier = CircuitVerifier::from_independently_trusted_builtin_artifact(
            config,
            relation.into_trusted()?,
            common,
        )
        .map_err(|_| ArtifactError::NonCanonicalMetadata)?;
        let canonical = encode_verifier(&verifier, limits)?;
        if canonical != candidate {
            return Err(ArtifactError::NonCanonicalMetadata);
        }
        Ok(Self::from_parts(verifier, canonical, suite, limits))
    }

    fn import_proof(
        &self,
        bytes: &[u8],
        expected_statement: CanonicalStatement<'_>,
    ) -> Result<VerifiedArtifactProof<SC>, ArtifactError> {
        let (proof, statement) = decode_verified_proof(
            &self.state.verifier,
            self.state.suite,
            &self.state.limits,
            bytes,
            expected_statement,
        )?;
        Ok(VerifiedArtifactProof::from_parts(
            proof,
            statement,
            self.clone(),
        ))
    }
}
