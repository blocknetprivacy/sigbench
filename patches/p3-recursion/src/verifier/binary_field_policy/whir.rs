use alloc::vec::Vec;

use p3_binary_field::TowerLevel;
use p3_circuit::ops::NativePoly192Target;

use super::*;

#[derive(Clone, Copy)]
pub(crate) enum BinaryOracleWord {
    Base,
    Challenge,
}

pub(crate) trait BinaryWhirPolicy<CF: Field + Eq + Hash>: BinaryProtocolPolicy<CF> {
    fn observe_seed<H: BinaryCircuitHost<CF>>(
        b: &mut CircuitBuilder<CF>,
        ch: &mut BinaryTower128Challenger,
        seed: &[Self::Base],
    ) -> Result<(), VerificationError>;
    fn oracle_bytes<H: BinaryCircuitHost<CF>>(
        b: &mut CircuitBuilder<CF>,
        value: &Self::ChallengeTarget,
        mode: BinaryOracleWord,
    ) -> Result<Vec<ExprId>, VerificationError>;
    fn query_point(
        b: &mut CircuitBuilder<CF>,
        index_bits: &[ExprId],
        num_variables: usize,
    ) -> Result<Vec<Self::ChallengeTarget>, CircuitBuilderError>;
    fn square(b: &mut CircuitBuilder<CF>, value: &Self::ChallengeTarget) -> Self::ChallengeTarget {
        Self::mul(b, value, value)
    }
}

impl<CF, F, E> BinaryWhirPolicy<CF> for TowerRelation<F, E>
where
    CF: Field + Eq + Hash,
    F: RecursiveBinaryTowerField,
    E: RecursiveBinaryChallengeField + ExtensionField<F>,
{
    fn observe_seed<H: BinaryCircuitHost<CF>>(
        b: &mut CircuitBuilder<CF>,
        ch: &mut BinaryTower128Challenger,
        seed: &[F],
    ) -> Result<(), VerificationError> {
        crate::pcs::binary::observe_seed_with_host::<F, H, CF>(b, ch, seed)
    }
    fn oracle_bytes<H: BinaryCircuitHost<CF>>(
        b: &mut CircuitBuilder<CF>,
        value: &BinaryTower128Target,
        mode: BinaryOracleWord,
    ) -> Result<Vec<ExprId>, VerificationError> {
        let width = match mode {
            BinaryOracleWord::Base => F::RAW_BITS,
            BinaryOracleWord::Challenge => E::RAW_BITS,
        };
        <Self as BinaryTowerPolicy<CF>>::word_bytes::<H>(b, value, width)
    }
    fn query_point(
        b: &mut CircuitBuilder<CF>,
        index_bits: &[ExprId],
        num_variables: usize,
    ) -> Result<Vec<BinaryTower128Target>, CircuitBuilderError> {
        <Self as BinaryTowerPolicy<CF>>::query_point(b, index_bits, num_variables)
    }
}
impl<F> BinaryWhirPolicy<BinaryField128> for NativeTower128Relation<F>
where
    F: RecursiveBinaryTowerField,
    BinaryField128: ExtensionField<F>,
{
    fn observe_seed<H: BinaryCircuitHost<BinaryField128>>(
        b: &mut CircuitBuilder<BinaryField128>,
        ch: &mut BinaryTower128Challenger,
        seed: &[F],
    ) -> Result<(), VerificationError> {
        crate::pcs::binary::observe_seed_with_host::<F, H, BinaryField128>(b, ch, seed)
    }
    fn oracle_bytes<H: BinaryCircuitHost<BinaryField128>>(
        b: &mut CircuitBuilder<BinaryField128>,
        value: &NativeTower128Target,
        mode: BinaryOracleWord,
    ) -> Result<Vec<ExprId>, VerificationError> {
        let width = match mode {
            BinaryOracleWord::Base => F::RAW_BITS,
            BinaryOracleWord::Challenge => 128,
        };
        <Self as BinaryTowerPolicy<BinaryField128>>::word_bytes::<H>(b, value, width)
    }
    fn query_point(
        b: &mut CircuitBuilder<BinaryField128>,
        index_bits: &[ExprId],
        num_variables: usize,
    ) -> Result<Vec<NativeTower128Target>, CircuitBuilderError> {
        <Self as BinaryTowerPolicy<BinaryField128>>::query_point(b, index_bits, num_variables)
    }
}

impl<CF: Field + Eq + Hash> BinaryWhirPolicy<CF> for Poly64Relation {
    fn observe_seed<H: BinaryCircuitHost<CF>>(
        b: &mut CircuitBuilder<CF>,
        ch: &mut BinaryTower128Challenger,
        seed: &[Poly64],
    ) -> Result<(), VerificationError> {
        poly_observe_seed_with_host::<H, CF>(b, ch, seed)
    }
    fn oracle_bytes<H: BinaryCircuitHost<CF>>(
        b: &mut CircuitBuilder<CF>,
        value: &BinaryPoly192Target,
        mode: BinaryOracleWord,
    ) -> Result<Vec<ExprId>, VerificationError> {
        H::check_carrier()?;
        let bits = <Self as BinaryPolyPolicy<CF>>::challenge_bits(b, value)?;
        let width = match mode {
            BinaryOracleWord::Base => {
                for &bit in &bits[64..] {
                    b.assert_zero(bit);
                }
                64
            }
            BinaryOracleWord::Challenge => 192,
        };
        Ok(bits[..width]
            .as_chunks::<8>()
            .0
            .iter()
            .map(|bits| H::recompose_word(b, bits))
            .collect::<Result<_, _>>()?)
    }
    fn query_point(
        b: &mut CircuitBuilder<CF>,
        index_bits: &[ExprId],
        num_variables: usize,
    ) -> Result<Vec<BinaryPoly192Target>, CircuitBuilderError> {
        crate::pcs::binary::poly_whir_query_point(b, index_bits, num_variables)
    }
    fn square(b: &mut CircuitBuilder<CF>, value: &BinaryPoly192Target) -> BinaryPoly192Target {
        b.binary_poly192_square(value)
    }
}

impl BinaryWhirPolicy<Poly64> for NativePoly64Relation {
    fn observe_seed<H: BinaryCircuitHost<Poly64>>(
        b: &mut CircuitBuilder<Poly64>,
        ch: &mut BinaryTower128Challenger,
        seed: &[Poly64],
    ) -> Result<(), VerificationError> {
        poly_observe_seed_with_host::<H, Poly64>(b, ch, seed)
    }
    fn oracle_bytes<H: BinaryCircuitHost<Poly64>>(
        b: &mut CircuitBuilder<Poly64>,
        value: &NativePoly192Target,
        mode: BinaryOracleWord,
    ) -> Result<Vec<ExprId>, VerificationError> {
        H::check_carrier()?;
        match mode {
            BinaryOracleWord::Base => {
                for &coefficient in &value.coefficients()[1..] {
                    b.assert_zero(coefficient);
                }
                let bits = b.binary_decompose_coordinates(value.coefficients()[0], 64)?;
                Ok(bits
                    .as_chunks::<8>()
                    .0
                    .iter()
                    .map(|bits| H::recompose_word(b, bits))
                    .collect::<Result<_, _>>()?)
            }
            BinaryOracleWord::Challenge => {
                let bits = b.native_poly192_to_bits(value)?;
                Ok(bits
                    .as_chunks::<8>()
                    .0
                    .iter()
                    .map(|bits| H::recompose_word(b, bits))
                    .collect::<Result<_, _>>()?)
            }
        }
    }
    fn query_point(
        b: &mut CircuitBuilder<Poly64>,
        index_bits: &[ExprId],
        num_variables: usize,
    ) -> Result<Vec<NativePoly192Target>, CircuitBuilderError> {
        if index_bits.len() > 64 || num_variables > 64 {
            return Err(CircuitBuilderError::NonPrimitiveOpArity {
                op: "BinaryWhirQueryPoint",
                expected: alloc::format!("at most {} alphabet coordinates", 64),
                got: index_bits.len().max(num_variables),
            });
        }
        for &bit in index_bits {
            b.assert_bool(bit);
        }
        b.check_construction_limits()?;
        (0..num_variables)
            .rev()
            .map(|shift| {
                let mut value = ExprId::ZERO;
                for (i, &bit) in index_bits.iter().skip(shift).enumerate() {
                    let basis = b.define_const(Poly64::cantor_basis(i));
                    let term = b.mul(bit, basis);
                    value = b.add(value, term);
                }
                b.check_construction_limits()?;
                Ok(b.native_poly192_from_coefficients([value, ExprId::ZERO, ExprId::ZERO]))
            })
            .collect()
    }
    fn square(b: &mut CircuitBuilder<Poly64>, value: &NativePoly192Target) -> NativePoly192Target {
        b.native_poly192_square(value)
    }
}
