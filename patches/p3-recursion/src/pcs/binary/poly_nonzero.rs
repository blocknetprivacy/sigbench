use alloc::vec::Vec;
use core::hash::Hash;

use p3_binary_field::{Poly64, Poly192};
use p3_challenger::FieldChallenger;
use p3_circuit::CircuitBuilder;
#[cfg(test)]
use p3_circuit::ExprId;
use p3_circuit::ops::binary_encoding::{NativeBinaryEncoding, PrimeBinaryEncoding};
use p3_circuit::ops::binary_host::BinaryCircuitHost;
use p3_circuit::ops::{BinaryPoly192Target, NativePoly192Target};
use p3_field::{ExtensionField, Field, PrimeCharacteristicRing, PrimeField64};

use super::nonzero::select_nonzero_words;
use super::whir_plan::invalid;
use crate::verifier::binary_field_policy::{
    BinaryPolyPolicy, NativePoly64Relation, Poly64Relation,
};
use crate::verifier::{InputResourceUsage, VerificationError, VerifierLimits};
use crate::{BinaryQueryContinuation, BinaryTower128Challenger};

#[derive(Clone, Debug)]
pub struct BinaryPolyNonzeroChallengePlan {
    count: usize,
    max_draws: usize,
    usage: InputResourceUsage,
}

#[derive(Debug)]
pub struct BinaryPolyNonzeroChallengeOutput<T = BinaryPoly192Target> {
    pub values: Vec<T>,
    pub continuation: BinaryQueryContinuation,
}

impl BinaryPolyNonzeroChallengePlan {
    pub fn new(count: usize, max_draws: usize) -> Result<Self, VerificationError> {
        Self::with_limits(count, max_draws, &VerifierLimits::default())
    }

    pub fn with_limits(
        count: usize,
        max_draws: usize,
        limits: &VerifierLimits,
    ) -> Result<Self, VerificationError> {
        if count == 0 || max_draws < count {
            return Err(invalid("polynomial nonzero challenge count or draw budget"));
        }
        let mut usage = InputResourceUsage::default();
        usage.add_rounds(limits, count)?;
        usage.add_query_round(limits, max_draws)?;
        let entries = count
            .checked_add(192 + 32)
            .and_then(|n| n.checked_mul(max_draws))
            .ok_or(VerificationError::ResourceArithmeticOverflow {
                component: "polynomial nonzero challenge selection",
            })?;
        usage.add_metadata_entries(limits, entries)?;
        Ok(Self {
            count,
            max_draws,
            usage,
        })
    }

    pub const fn input_resource_usage(&self) -> InputResourceUsage {
        self.usage
    }

    pub fn sample<BF, EF>(
        &self,
        b: &mut CircuitBuilder<EF>,
        ch: BinaryTower128Challenger,
    ) -> Result<BinaryPolyNonzeroChallengeOutput, VerificationError>
    where
        BF: PrimeField64,
        EF: ExtensionField<BF> + Eq + Hash,
    {
        self.sample_using::<Poly64Relation, PrimeBinaryEncoding<BF>, EF>(b, ch)
    }

    pub(crate) fn sample_using<P, H, CF>(
        &self,
        b: &mut CircuitBuilder<CF>,
        mut ch: BinaryTower128Challenger,
    ) -> Result<BinaryPolyNonzeroChallengeOutput<P::ChallengeTarget>, VerificationError>
    where
        CF: Field + Eq + Hash,
        H: BinaryCircuitHost<CF>,
        P: BinaryPolyPolicy<CF>,
    {
        let mut candidates = Vec::with_capacity(self.max_draws);
        for _ in 0..self.max_draws {
            let value = ch.sample_poly192_with_host::<H, CF>(b)?;
            let bits = core::array::from_fn(|i| value.coefficients()[i / 64].bits()[i % 64]);
            let (_, digest) = ch.retained_query_digest()?;
            candidates.push((bits, digest));
        }
        let (hash, _) = ch.retained_query_digest()?;
        let (selected, _, digest) =
            select_nonzero_words::<192, _>(b, self.count, 192, self.max_draws, 0, &candidates)?;
        let values = selected
            .into_iter()
            .map(|bits| P::from_checked_bits(b, bits))
            .collect::<Result<_, _>>()?;
        Ok(BinaryPolyNonzeroChallengeOutput {
            values,
            continuation: BinaryQueryContinuation::from_digest(hash, digest),
        })
    }

    pub fn sample_native<Ch>(&self, ch: &mut Ch) -> Result<Vec<Poly192>, VerificationError>
    where
        Ch: FieldChallenger<Poly64> + Clone,
    {
        let mut staged = ch.clone();
        let mut values = Vec::with_capacity(self.count);
        for _ in 0..self.max_draws {
            let value = staged.sample_algebra_element::<Poly192>();
            if value != Poly192::ZERO {
                values.push(value);
                if values.len() == self.count {
                    *ch = staged;
                    return Ok(values);
                }
            }
        }
        Err(invalid(
            "polynomial nonzero challenge draw budget exhausted",
        ))
    }
}

#[derive(Clone, Debug)]
pub struct BinaryPolyNonzeroChallengeTailPlan {
    prefix: BinaryPolyNonzeroChallengePlan,
    following_count: usize,
    total_draws: usize,
    usage: InputResourceUsage,
}

#[derive(Debug)]
pub struct BinaryPolyNonzeroChallengeTailOutput<T = BinaryPoly192Target> {
    pub values: Vec<T>,
    pub following: Vec<T>,
    pub continuation: BinaryQueryContinuation,
}

impl BinaryPolyNonzeroChallengeTailPlan {
    pub fn new(
        count: usize,
        max_draws: usize,
        following_count: usize,
    ) -> Result<Self, VerificationError> {
        Self::with_limits(
            count,
            max_draws,
            following_count,
            &VerifierLimits::default(),
        )
    }

    pub fn with_limits(
        count: usize,
        max_draws: usize,
        following_count: usize,
        limits: &VerifierLimits,
    ) -> Result<Self, VerificationError> {
        let prefix = BinaryPolyNonzeroChallengePlan::with_limits(count, max_draws, limits)?;
        let overflow = || VerificationError::ResourceArithmeticOverflow {
            component: "polynomial nonzero following challenges",
        };
        let total_draws = max_draws
            .checked_add(following_count)
            .ok_or_else(overflow)?;
        total_draws.checked_mul(24).ok_or_else(overflow)?;
        let additional_metadata = max_draws
            .checked_mul(193)
            .and_then(|n| n.checked_add(416))
            .and_then(|n| n.checked_mul(following_count))
            .ok_or_else(overflow)?;
        let mut usage = prefix.usage;
        usage.add_rounds(limits, following_count)?;
        usage.queries = 0;
        usage.add_query_round(limits, total_draws)?;
        usage.add_metadata_entries(limits, additional_metadata)?;
        Ok(Self {
            prefix,
            following_count,
            total_draws,
            usage,
        })
    }

    pub const fn input_resource_usage(&self) -> InputResourceUsage {
        self.usage
    }

    pub fn sample<BF, EF>(
        &self,
        b: &mut CircuitBuilder<EF>,
        ch: BinaryTower128Challenger,
    ) -> Result<BinaryPolyNonzeroChallengeTailOutput, VerificationError>
    where
        BF: PrimeField64,
        EF: ExtensionField<BF> + Eq + Hash,
    {
        self.sample_using::<Poly64Relation, PrimeBinaryEncoding<BF>, EF>(b, ch)
    }

    pub(crate) fn sample_using<P, H, CF>(
        &self,
        b: &mut CircuitBuilder<CF>,
        mut ch: BinaryTower128Challenger,
    ) -> Result<BinaryPolyNonzeroChallengeTailOutput<P::ChallengeTarget>, VerificationError>
    where
        CF: Field + Eq + Hash,
        H: BinaryCircuitHost<CF>,
        P: BinaryPolyPolicy<CF>,
    {
        let mut candidates = Vec::with_capacity(self.total_draws);
        for _ in 0..self.total_draws {
            let value = ch.sample_poly192_with_host::<H, CF>(b)?;
            let bits = core::array::from_fn(|i| value.coefficients()[i / 64].bits()[i % 64]);
            let (_, digest) = ch.retained_query_digest()?;
            candidates.push((bits, digest));
        }
        let (hash, _) = ch.retained_query_digest()?;
        let (values, following, digest) = select_nonzero_words::<192, _>(
            b,
            self.prefix.count,
            192,
            self.prefix.max_draws,
            self.following_count,
            &candidates,
        )?;
        let values = values
            .into_iter()
            .map(|bits| P::from_checked_bits(b, bits))
            .collect::<Result<_, _>>()?;
        let following = following
            .into_iter()
            .map(|bits| P::from_checked_bits(b, bits))
            .collect::<Result<_, _>>()?;
        Ok(BinaryPolyNonzeroChallengeTailOutput {
            values,
            following,
            continuation: BinaryQueryContinuation::from_digest(hash, digest),
        })
    }

    pub fn sample_native<Ch>(
        &self,
        ch: &mut Ch,
    ) -> Result<(Vec<Poly192>, Vec<Poly192>), VerificationError>
    where
        Ch: FieldChallenger<Poly64> + Clone,
    {
        let mut staged = ch.clone();
        let values = self.prefix.sample_native(&mut staged)?;
        let following = (0..self.following_count)
            .map(|_| staged.sample_algebra_element::<Poly192>())
            .collect();
        *ch = staged;
        Ok((values, following))
    }
}

#[cfg(test)]
fn target_from_bits<EF: p3_field::Field + Eq + Hash>(
    b: &mut CircuitBuilder<EF>,
    bits: [ExprId; 192],
) -> Result<BinaryPoly192Target, VerificationError> {
    let a0 = b.binary_poly64_from_bits(bits[..64].try_into().expect("fixed coefficient"))?;
    let a1 = b.binary_poly64_from_bits(bits[64..128].try_into().expect("fixed coefficient"))?;
    let a2 = b.binary_poly64_from_bits(bits[128..].try_into().expect("fixed coefficient"))?;
    Ok(b.binary_poly192_from_coefficients([a0, a1, a2]))
}

impl BinaryPolyNonzeroChallengePlan {
    pub fn sample_native_targets(
        &self,
        b: &mut CircuitBuilder<Poly64>,
        ch: BinaryTower128Challenger,
    ) -> Result<BinaryPolyNonzeroChallengeOutput<NativePoly192Target>, VerificationError> {
        self.sample_using::<NativePoly64Relation, NativeBinaryEncoding, Poly64>(b, ch)
    }
}
impl BinaryPolyNonzeroChallengeTailPlan {
    pub fn sample_native_targets(
        &self,
        b: &mut CircuitBuilder<Poly64>,
        ch: BinaryTower128Challenger,
    ) -> Result<BinaryPolyNonzeroChallengeTailOutput<NativePoly192Target>, VerificationError> {
        self.sample_using::<NativePoly64Relation, NativeBinaryEncoding, Poly64>(b, ch)
    }
}
