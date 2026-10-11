use alloc::vec;
use alloc::vec::Vec;
use core::hash::Hash;
use core::marker::PhantomData;

use p3_binary_field::BinaryField128;
use p3_challenger::FieldChallenger;
use p3_circuit::ops::BinaryTower128Target;
use p3_circuit::ops::binary_encoding::PrimeBinaryEncoding;
use p3_circuit::ops::binary_host::BinaryCircuitHost;
use p3_circuit::{CircuitBuilder, ExprId};
use p3_field::{ExtensionField, Field, PrimeField64};

use super::RecursiveBinaryChallengeField;
use super::whir_plan::invalid;
use crate::verifier::{InputResourceUsage, VerificationError, VerifierLimits};
use crate::{BinaryQueryContinuation, BinaryTower128Challenger};

type NonzeroSelection<T> = (Vec<T>, Vec<T>, [ExprId; 32]);

#[derive(Clone, Debug)]
pub struct BinaryNonzeroChallengePlan<E = BinaryField128> {
    count: usize,
    max_draws: usize,
    usage: InputResourceUsage,
    field: PhantomData<E>,
}

#[derive(Debug)]
pub struct BinaryNonzeroChallengeOutput {
    pub values: Vec<BinaryTower128Target>,
    pub continuation: BinaryQueryContinuation,
}

#[derive(Clone, Debug)]
pub struct BinaryNonzeroChallengeTailPlan<E = BinaryField128> {
    prefix: BinaryNonzeroChallengePlan<E>,
    following_count: usize,
    total_draws: usize,
    usage: InputResourceUsage,
}

#[derive(Debug)]
pub struct BinaryNonzeroChallengeTailOutput {
    pub values: Vec<BinaryTower128Target>,
    pub following: Vec<BinaryTower128Target>,
    pub continuation: BinaryQueryContinuation,
}

impl<E: RecursiveBinaryChallengeField> BinaryNonzeroChallengePlan<E> {
    pub fn new(count: usize, max_draws: usize) -> Result<Self, VerificationError> {
        Self::with_limits(count, max_draws, &VerifierLimits::default())
    }

    pub fn with_limits(
        count: usize,
        max_draws: usize,
        limits: &VerifierLimits,
    ) -> Result<Self, VerificationError> {
        if count == 0 || max_draws < count {
            return Err(invalid("binary nonzero challenge count or draw budget"));
        }
        let mut usage = InputResourceUsage::default();
        usage.add_rounds(limits, count)?;
        usage.add_query_round(limits, max_draws)?;
        let metadata = count
            .checked_add(E::RAW_BITS + 32)
            .and_then(|n| n.checked_mul(max_draws))
            .ok_or(VerificationError::ResourceArithmeticOverflow {
                component: "binary nonzero challenge selection",
            })?;
        usage.add_metadata_entries(limits, metadata)?;
        Ok(Self {
            count,
            max_draws,
            usage,
            field: PhantomData,
        })
    }

    pub const fn input_resource_usage(&self) -> InputResourceUsage {
        self.usage
    }

    pub fn sample<BF, EF>(
        &self,
        b: &mut CircuitBuilder<EF>,
        ch: BinaryTower128Challenger,
    ) -> Result<BinaryNonzeroChallengeOutput, VerificationError>
    where
        BF: PrimeField64,
        EF: ExtensionField<BF> + Eq + Hash,
    {
        self.sample_with_host::<PrimeBinaryEncoding<BF>, EF>(b, ch)
    }

    pub fn sample_with_host<H, EF>(
        &self,
        b: &mut CircuitBuilder<EF>,
        ch: BinaryTower128Challenger,
    ) -> Result<BinaryNonzeroChallengeOutput, VerificationError>
    where
        H: BinaryCircuitHost<EF>,
        EF: Field + Eq + Hash,
    {
        let (candidates, hash) = sample_words::<E, H, EF>(b, ch, self.max_draws)?;
        let (values, digest) = select_nonzero(b, self.count, E::RAW_BITS, &candidates)?;
        Ok(BinaryNonzeroChallengeOutput {
            values,
            continuation: BinaryQueryContinuation::from_digest(hash, digest),
        })
    }

    pub fn sample_native<F, Ch>(&self, ch: &mut Ch) -> Result<Vec<E>, VerificationError>
    where
        F: super::RecursiveBinaryTowerField,
        E: ExtensionField<F>,
        Ch: FieldChallenger<F> + Clone,
    {
        let mut staged = ch.clone();
        let mut values = Vec::with_capacity(self.count);
        for _ in 0..self.max_draws {
            let value = staged.sample_algebra_element::<E>();
            if value != E::ZERO {
                values.push(value);
                if values.len() == self.count {
                    *ch = staged;
                    return Ok(values);
                }
            }
        }
        Err(invalid("binary nonzero challenge draw budget exhausted"))
    }
}

impl<E: RecursiveBinaryChallengeField> BinaryNonzeroChallengeTailPlan<E> {
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
        let prefix = BinaryNonzeroChallengePlan::with_limits(count, max_draws, limits)?;
        let overflow = || VerificationError::ResourceArithmeticOverflow {
            component: "binary nonzero following challenges",
        };
        let total_draws = max_draws
            .checked_add(following_count)
            .ok_or_else(overflow)?;
        total_draws
            .checked_mul(E::RAW_BITS / 8)
            .ok_or_else(overflow)?;
        let additional_metadata = max_draws
            .checked_mul(129)
            .and_then(|n| n.checked_add(288))
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
    ) -> Result<BinaryNonzeroChallengeTailOutput, VerificationError>
    where
        BF: PrimeField64,
        EF: ExtensionField<BF> + Eq + Hash,
    {
        self.sample_with_host::<PrimeBinaryEncoding<BF>, EF>(b, ch)
    }

    pub fn sample_with_host<H, EF>(
        &self,
        b: &mut CircuitBuilder<EF>,
        ch: BinaryTower128Challenger,
    ) -> Result<BinaryNonzeroChallengeTailOutput, VerificationError>
    where
        H: BinaryCircuitHost<EF>,
        EF: Field + Eq + Hash,
    {
        let (candidates, hash) = sample_words::<E, H, EF>(b, ch, self.total_draws)?;
        let (values, following, digest) = select_nonzero_with_tail(
            b,
            self.prefix.count,
            E::RAW_BITS,
            self.prefix.max_draws,
            self.following_count,
            &candidates,
        )?;
        Ok(BinaryNonzeroChallengeTailOutput {
            values,
            following,
            continuation: BinaryQueryContinuation::from_digest(hash, digest),
        })
    }

    pub fn sample_native<F, Ch>(&self, ch: &mut Ch) -> Result<(Vec<E>, Vec<E>), VerificationError>
    where
        F: super::RecursiveBinaryTowerField,
        E: ExtensionField<F>,
        Ch: FieldChallenger<F> + Clone,
    {
        let mut staged = ch.clone();
        let values = self.prefix.sample_native::<F, _>(&mut staged)?;
        let following = (0..self.following_count)
            .map(|_| staged.sample_algebra_element::<E>())
            .collect();
        *ch = staged;
        Ok((values, following))
    }
}

type Candidate = (BinaryTower128Target, [ExprId; 32]);

fn sample_words<E, H, EF>(
    b: &mut CircuitBuilder<EF>,
    mut ch: BinaryTower128Challenger,
    count: usize,
) -> Result<(Vec<Candidate>, p3_circuit::ops::ByteHash), VerificationError>
where
    E: RecursiveBinaryChallengeField,
    H: BinaryCircuitHost<EF>,
    EF: Field + Eq + Hash,
{
    let mut candidates = Vec::with_capacity(count);
    for _ in 0..count {
        let bytes = ch.sample_bytes_with_host::<H, EF>(b, E::RAW_BITS / 8)?;
        let mut bits = [ExprId::ZERO; 128];
        for (i, byte) in bytes.into_iter().enumerate() {
            let byte_bits = H::decompose_word(b, byte, 8)?;
            bits[8 * i..8 * i + 8].copy_from_slice(&byte_bits);
        }
        let value = b.binary128_from_bits(bits)?;
        let (_, digest) = ch.retained_query_digest()?;
        candidates.push((value, digest));
    }
    let (hash, _) = ch.retained_query_digest()?;
    Ok((candidates, hash))
}

fn select_nonzero<EF: p3_field::Field + Eq + Hash>(
    b: &mut CircuitBuilder<EF>,
    count: usize,
    bits: usize,
    candidates: &[(BinaryTower128Target, [ExprId; 32])],
) -> Result<(Vec<BinaryTower128Target>, [ExprId; 32]), VerificationError> {
    let (values, _, digest) =
        select_nonzero_with_tail(b, count, bits, candidates.len(), 0, candidates)?;
    Ok((values, digest))
}

fn select_nonzero_with_tail<EF: p3_field::Field + Eq + Hash>(
    b: &mut CircuitBuilder<EF>,
    count: usize,
    bits: usize,
    max_draws: usize,
    following_count: usize,
    candidates: &[Candidate],
) -> Result<NonzeroSelection<BinaryTower128Target>, VerificationError> {
    if !matches!(bits, 64 | 128) {
        return Err(invalid("binary nonzero selection shape"));
    }
    let candidates = candidates
        .iter()
        .map(|(value, digest)| (*value.bits(), *digest))
        .collect::<Vec<_>>();
    let (selected, following, retained) =
        select_nonzero_words(b, count, bits, max_draws, following_count, &candidates)?;
    let values = selected
        .into_iter()
        .map(|bits| {
            let value = b.binary128_from_bits(bits)?;
            b.check_construction_limits()?;
            Ok::<_, VerificationError>(value)
        })
        .collect::<Result<_, _>>()?;
    let following = following
        .into_iter()
        .map(|bits| {
            let value = b.binary128_from_bits(bits)?;
            b.check_construction_limits()?;
            Ok::<_, VerificationError>(value)
        })
        .collect::<Result<_, _>>()?;
    Ok((values, following, retained))
}

pub(super) fn select_nonzero_words<const W: usize, EF: p3_field::Field + Eq + Hash>(
    b: &mut CircuitBuilder<EF>,
    count: usize,
    bits: usize,
    max_draws: usize,
    following_count: usize,
    candidates: &[([ExprId; W], [ExprId; 32])],
) -> Result<NonzeroSelection<[ExprId; W]>, VerificationError> {
    if count == 0
        || count > max_draws
        || bits == 0
        || bits > W
        || max_draws.checked_add(following_count) != Some(candidates.len())
    {
        return Err(invalid("binary nonzero selection shape"));
    }
    let state_count =
        count
            .checked_add(1)
            .ok_or(VerificationError::ResourceArithmeticOverflow {
                component: "binary nonzero selection states",
            })?;
    b.check_construction_limits()?;
    let one = b.define_const(EF::ONE);
    let mut states = vec![ExprId::ZERO; state_count];
    states[0] = one;
    let mut selected = vec![[ExprId::ZERO; W]; count];
    let mut following = vec![[ExprId::ZERO; W]; following_count];
    let mut retained = [ExprId::ZERO; 32];
    for (index, (candidate, _)) in candidates[..max_draws].iter().enumerate() {
        let factors: Vec<_> = candidate[..bits]
            .iter()
            .map(|&bit| b.sub(one, bit))
            .collect();
        b.check_construction_limits()?;
        let zero = b.mul_many(&factors);
        let accepted = b.sub(one, zero);
        b.check_construction_limits()?;
        let mut next = vec![ExprId::ZERO; state_count];
        next[count] = states[count];
        for j in 0..count {
            let take = b.mul(states[j], accepted);
            let stay = b.mul(states[j], zero);
            next[j] = b.add(next[j], stay);
            next[j + 1] = b.add(next[j + 1], take);
            for (out, &bit) in selected[j].iter_mut().zip(candidate) {
                *out = b.mul_add(take, bit, *out);
            }
            if j + 1 == count {
                let digest = &candidates[index + following_count].1;
                for (out, &byte) in retained.iter_mut().zip(digest) {
                    *out = b.mul_add(take, byte, *out);
                }
                for (offset, output) in following.iter_mut().enumerate() {
                    for (out, &bit) in output.iter_mut().zip(&candidates[index + offset + 1].0) {
                        *out = b.mul_add(take, bit, *out);
                    }
                    b.check_construction_limits()?;
                }
            }
            b.check_construction_limits()?;
        }
        states = next;
    }
    let incomplete = b.sub(states[count], one);
    b.assert_zero(incomplete);
    b.check_construction_limits()?;
    Ok((selected, following, retained))
}
