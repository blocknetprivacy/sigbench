use alloc::vec::Vec;

use p3_circuit::ops::NativePoly192Target;

use super::*;

pub(crate) fn poly_seed_bytes_with_host<H, CF>(
    b: &mut CircuitBuilder<CF>,
    seed: &[Poly64],
) -> Result<Vec<ExprId>, CircuitBuilderError>
where
    CF: Field + Eq + Hash,
    H: BinaryCircuitHost<CF>,
{
    seed.iter()
        .flat_map(|value| value.to_bits().to_le_bytes())
        .map(|byte| Ok(b.define_const(H::encode_u16(u16::from(byte))?)))
        .collect()
}

pub(crate) fn poly_observe_seed_with_host<H, CF>(
    b: &mut CircuitBuilder<CF>,
    ch: &mut BinaryTower128Challenger,
    seed: &[Poly64],
) -> Result<(), VerificationError>
where
    CF: Field + Eq + Hash,
    H: BinaryCircuitHost<CF>,
{
    let bytes = poly_seed_bytes_with_host::<H, CF>(b, seed)?;
    Ok(ch.observe_bytes_with_host::<H, CF>(b, &bytes)?)
}

pub(crate) fn poly_native_values(
    limbs: &[u16],
    cells: usize,
) -> Result<Vec<Poly64>, VerificationError> {
    let expected = cells
        .checked_mul(4)
        .ok_or(VerificationError::ResourceArithmeticOverflow {
            component: "native polynomial coefficient limbs",
        })?;
    if limbs.len() != expected {
        return Err(VerificationError::InvalidProofShape(
            "native polynomial coefficient count mismatch".into(),
        ));
    }
    Ok(limbs
        .as_chunks::<4>()
        .0
        .iter()
        .map(|limbs| {
            let raw = limbs
                .iter()
                .enumerate()
                .fold(0u64, |raw, (i, &limb)| raw | (u64::from(limb) << (16 * i)));
            Poly64::new(raw)
        })
        .collect())
}

pub(crate) trait BinaryPolyPolicy<CF: Field + Eq + Hash>:
    BinaryRelationPolicy<CF, Base = Poly64, Challenge = Poly192>
{
    fn challenge_bits(
        b: &mut CircuitBuilder<CF>,
        value: &Self::ChallengeTarget,
    ) -> Result<[ExprId; 192], CircuitBuilderError>;
    fn from_checked_bits(
        b: &mut CircuitBuilder<CF>,
        bits: [ExprId; 192],
    ) -> Result<Self::ChallengeTarget, CircuitBuilderError>;
    fn observe_base<H: BinaryCircuitHost<CF>>(
        b: &mut CircuitBuilder<CF>,
        ch: &mut BinaryTower128Challenger,
        values: &[Self::BaseTarget],
    ) -> Result<(), VerificationError>;
    fn scale_base_constant(
        b: &mut CircuitBuilder<CF>,
        value: &Self::ChallengeTarget,
        raw: u64,
    ) -> Result<Self::ChallengeTarget, CircuitBuilderError>;
}

impl<CF: Field + Eq + Hash> BinaryPolyPolicy<CF> for Poly64Relation {
    fn challenge_bits(
        _b: &mut CircuitBuilder<CF>,
        value: &BinaryPoly192Target,
    ) -> Result<[ExprId; 192], CircuitBuilderError> {
        Ok(core::array::from_fn(|i| {
            value.coefficients()[i / 64].bits()[i % 64]
        }))
    }
    fn from_checked_bits(
        b: &mut CircuitBuilder<CF>,
        bits: [ExprId; 192],
    ) -> Result<BinaryPoly192Target, CircuitBuilderError> {
        let a0 = b.binary_poly64_from_bits(bits[..64].try_into().expect("fixed coefficient"))?;
        let a1 = b.binary_poly64_from_bits(bits[64..128].try_into().expect("fixed coefficient"))?;
        let a2 = b.binary_poly64_from_bits(bits[128..].try_into().expect("fixed coefficient"))?;
        Ok(b.binary_poly192_from_coefficients([a0, a1, a2]))
    }
    fn observe_base<H: BinaryCircuitHost<CF>>(
        b: &mut CircuitBuilder<CF>,
        ch: &mut BinaryTower128Challenger,
        values: &[BinaryPoly64Target],
    ) -> Result<(), VerificationError> {
        let bytes = values
            .iter()
            .flat_map(|value| value.bits().as_chunks::<8>().0.iter())
            .map(|bits| H::recompose_word(b, bits))
            .collect::<Result<Vec<_>, _>>()?;
        Ok(ch.observe_bytes_with_host::<H, CF>(b, &bytes)?)
    }
    fn scale_base_constant(
        b: &mut CircuitBuilder<CF>,
        value: &BinaryPoly192Target,
        raw: u64,
    ) -> Result<BinaryPoly192Target, CircuitBuilderError> {
        let constant = b.binary_poly64_constant(raw)?;
        Ok(b.binary_poly192_scale(value, &constant))
    }
}

pub(crate) struct NativePoly64Relation;
impl sealed::Relation for NativePoly64Relation {}
impl BinaryRelationPolicy<Poly64> for NativePoly64Relation {
    type Base = Poly64;
    type Challenge = Poly192;
    type BaseTarget = ExprId;
    type ChallengeTarget = NativePoly192Target;

    fn constant(
        b: &mut CircuitBuilder<Poly64>,
        raw: u128,
    ) -> Result<NativePoly192Target, CircuitBuilderError> {
        let raw = u64::try_from(raw).map_err(|_| {
            CircuitBuilderError::BinaryDecompositionTooManyBits {
                expected: 64,
                n_bits: (128 - raw.leading_zeros()) as usize,
            }
        })?;
        Ok(b.native_poly192_constant([raw, 0, 0]))
    }
    fn lift(
        b: &mut CircuitBuilder<Poly64>,
        value: &ExprId,
    ) -> Result<NativePoly192Target, CircuitBuilderError> {
        Ok(b.native_poly192_from_coefficients([*value, ExprId::ZERO, ExprId::ZERO]))
    }
    fn constrain_base(
        _b: &mut CircuitBuilder<Poly64>,
        _value: &ExprId,
    ) -> Result<(), CircuitBuilderError> {
        Ok(())
    }
    fn constrain_challenge(_b: &mut CircuitBuilder<Poly64>, _value: &NativePoly192Target) {}
    fn add(
        b: &mut CircuitBuilder<Poly64>,
        a: &NativePoly192Target,
        c: &NativePoly192Target,
    ) -> NativePoly192Target {
        b.native_poly192_add(a, c)
    }
    fn mul(
        b: &mut CircuitBuilder<Poly64>,
        a: &NativePoly192Target,
        c: &NativePoly192Target,
    ) -> NativePoly192Target {
        b.native_poly192_mul(a, c)
    }
}

impl BinaryPolyPolicy<Poly64> for NativePoly64Relation {
    fn challenge_bits(
        b: &mut CircuitBuilder<Poly64>,
        value: &NativePoly192Target,
    ) -> Result<[ExprId; 192], CircuitBuilderError> {
        b.native_poly192_to_bits(value)
    }
    fn from_checked_bits(
        b: &mut CircuitBuilder<Poly64>,
        bits: [ExprId; 192],
    ) -> Result<NativePoly192Target, CircuitBuilderError> {
        b.native_poly192_from_bits(bits)
    }
    fn observe_base<H: BinaryCircuitHost<Poly64>>(
        b: &mut CircuitBuilder<Poly64>,
        ch: &mut BinaryTower128Challenger,
        values: &[ExprId],
    ) -> Result<(), VerificationError> {
        let mut bytes = Vec::new();
        for &value in values {
            let bits = b.binary_decompose_coordinates(value, 64)?;
            for bits in bits.as_chunks::<8>().0 {
                bytes.push(H::recompose_word(b, bits)?);
            }
        }
        Ok(ch.observe_bytes_with_host::<H, Poly64>(b, &bytes)?)
    }
    fn scale_base_constant(
        b: &mut CircuitBuilder<Poly64>,
        value: &NativePoly192Target,
        raw: u64,
    ) -> Result<NativePoly192Target, CircuitBuilderError> {
        let constant = b.define_const(Poly64::new(raw));
        let coefficients = value
            .coefficients()
            .map(|coefficient| b.mul(coefficient, constant));
        Ok(b.native_poly192_from_coefficients(coefficients))
    }
}

impl BinaryProtocolPolicy<Poly64> for NativePoly64Relation {
    fn observe<H: BinaryCircuitHost<Poly64>>(
        b: &mut CircuitBuilder<Poly64>,
        ch: &mut BinaryTower128Challenger,
        values: &[NativePoly192Target],
    ) -> Result<(), VerificationError> {
        let bytes = native_bytes::<H>(b, values)?;
        Ok(ch.observe_bytes_with_host::<H, Poly64>(b, &bytes)?)
    }
    fn observe_after_queries<H: BinaryCircuitHost<Poly64>>(
        b: &mut CircuitBuilder<Poly64>,
        token: crate::BinaryQueryContinuation,
        values: &[NativePoly192Target],
    ) -> Result<BinaryTower128Challenger, VerificationError> {
        let bytes = native_bytes::<H>(b, values)?;
        Ok(token.resume_with_observation_with_host::<H, Poly64>(b, &bytes)?)
    }
    fn sample<H: BinaryCircuitHost<Poly64>>(
        b: &mut CircuitBuilder<Poly64>,
        ch: &mut BinaryTower128Challenger,
    ) -> Result<NativePoly192Target, VerificationError> {
        let value = ch.sample_poly192_with_host::<H, Poly64>(b)?;
        let bits = core::array::from_fn(|i| value.coefficients()[i / 64].bits()[i % 64]);
        Ok(b.native_poly192_from_bits(bits)?)
    }
    fn assert_equal(
        b: &mut CircuitBuilder<Poly64>,
        a: &NativePoly192Target,
        c: &NativePoly192Target,
    ) {
        for (&a, &c) in a.coefficients().iter().zip(c.coefficients()) {
            let difference = b.sub(a, c);
            b.assert_zero(difference);
        }
    }
    fn eq_eval(
        b: &mut CircuitBuilder<Poly64>,
        a: &[NativePoly192Target],
        c: &[NativePoly192Target],
    ) -> Result<NativePoly192Target, CircuitBuilderError> {
        assert_eq!(a.len(), c.len(), "binary equality point lengths differ");
        let one = b.native_poly192_constant([1, 0, 0]);
        let mut weight = one.clone();
        for (a, c) in a.iter().zip(c) {
            let sum = b.native_poly192_add(a, c);
            let equal = b.native_poly192_add(&one, &sum);
            weight = b.native_poly192_mul(&weight, &equal);
        }
        Ok(weight)
    }
}

fn native_bytes<H: BinaryCircuitHost<Poly64>>(
    b: &mut CircuitBuilder<Poly64>,
    values: &[NativePoly192Target],
) -> Result<Vec<ExprId>, CircuitBuilderError> {
    let mut bytes = Vec::new();
    for value in values {
        let bits = b.native_poly192_to_bits(value)?;
        for byte in bits.as_chunks::<8>().0 {
            bytes.push(H::recompose_word(b, byte)?);
        }
    }
    Ok(bytes)
}
