use alloc::vec::Vec;
use core::hash::Hash;
use core::marker::PhantomData;

use p3_circuit::ops::{BinaryTower128Target, ByteHash};
use p3_circuit::{CircuitBuilder, ExprId};
use p3_field::{ExtensionField, PrimeField64};

use super::RecursiveBinaryTowerField;
use super::verifier::{assert_equal, constrain_width, tower_bytes};
use super::whir_plan::{invalid, limit};
use crate::verifier::{InputResourceUsage, VerificationError, VerifierLimits};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BinaryGroupedOraclePlan<F> {
    symbol_bits: usize,
    group_size: usize,
    group_bits: usize,
    cap_height: usize,
    hash: ByteHash,
    usage: InputResourceUsage,
    _field: PhantomData<F>,
}

impl<F: RecursiveBinaryTowerField> BinaryGroupedOraclePlan<F> {
    pub fn new(
        symbol_bits: usize,
        group_size: usize,
        hash: ByteHash,
        cap_height: usize,
    ) -> Result<Self, VerificationError> {
        Self::with_limits(
            symbol_bits,
            group_size,
            hash,
            cap_height,
            &VerifierLimits::default(),
        )
    }

    pub fn with_limits(
        symbol_bits: usize,
        group_size: usize,
        hash: ByteHash,
        cap_height: usize,
        limits: &VerifierLimits,
    ) -> Result<Self, VerificationError> {
        limit(
            "binary grouped codeword bits",
            symbol_bits,
            limits
                .max_log_domain_or_degree
                .min(usize::BITS as usize - 1),
        )?;
        if !group_size.is_power_of_two() || group_size > 1usize << symbol_bits {
            return Err(invalid(
                "binary grouped leaf width must be a power of two within the codeword",
            ));
        }
        limit(
            "binary grouped leaf width",
            group_size,
            limits.max_matrix_width,
        )?;
        let group_bits = group_size.ilog2() as usize;
        let leaf_bits = symbol_bits - group_bits;
        if cap_height > leaf_bits {
            return Err(invalid("binary grouped cap exceeds the grouped tree depth"));
        }
        let depth = leaf_bits - cap_height;
        let roots = 1usize << cap_height;
        let mut usage = InputResourceUsage::default();
        usage.add_instances(limits, 1)?;
        usage.add_metadata_entries(limits, 1)?;
        usage.add_query_round(limits, 1)?;
        usage.add_cap_roots(limits, roots)?;
        usage.add_restored_authentication_path_hashes(limits, 1, depth)?;
        usage.add_compressed_frontier_hashes(limits, depth)?;
        usage.add_scalar_elements(limits, symbol_bits)?;
        usage.add_scalar_elements(limits, 8)?;
        usage.add_scalar_elements(limits, checked_mul(group_size, 8)?)?;
        usage.add_scalar_elements(limits, checked_mul(depth, 16)?)?;
        usage.add_scalar_elements(limits, checked_mul(roots, 16)?)?;
        Ok(Self {
            symbol_bits,
            group_size,
            group_bits,
            cap_height,
            hash,
            usage,
            _field: PhantomData,
        })
    }

    pub const fn group_size(&self) -> usize {
        self.group_size
    }

    pub const fn path_len(&self) -> usize {
        self.symbol_bits - self.group_bits - self.cap_height
    }

    pub const fn input_resource_usage(&self) -> InputResourceUsage {
        self.usage
    }

    pub fn verify_symbol<BF, EF>(
        &self,
        b: &mut CircuitBuilder<EF>,
        symbol_index: &[ExprId],
        symbol: &BinaryTower128Target,
        leaf: &[BinaryTower128Target],
        path: &[Vec<ExprId>],
        cap: &[Vec<ExprId>],
    ) -> Result<(), VerificationError>
    where
        BF: PrimeField64,
        EF: ExtensionField<BF> + Eq + Hash,
    {
        if symbol_index.len() != self.symbol_bits
            || leaf.len() != self.group_size
            || path.len() != self.path_len()
            || path.iter().any(|digest| digest.len() != 16)
            || cap.len() != 1usize << self.cap_height
            || cap.iter().any(|digest| digest.len() != 16)
        {
            return Err(invalid(
                "binary grouped symbol, leaf or path shape mismatch",
            ));
        }
        for &bit in symbol_index {
            b.assert_bool(bit);
        }
        constrain_width(b, symbol, F::RAW_BITS);
        let mut bytes = Vec::new();
        for value in leaf {
            constrain_width(b, value, F::RAW_BITS);
            bytes.extend(tower_bytes::<BF, EF>(b, value, F::RAW_BITS)?);
        }
        let mut layer = leaf.to_vec();
        for &bit in &symbol_index[..self.group_bits] {
            layer = layer
                .as_chunks::<2>()
                .0
                .iter()
                .map(|pair| {
                    let bits = core::array::from_fn(|i| {
                        b.select(bit, pair[1].bits()[i], pair[0].bits()[i])
                    });
                    b.binary128_from_bits(bits)
                })
                .collect::<Result<_, _>>()?;
        }
        assert_equal(b, symbol, &layer[0]);
        for &limb in path.iter().flatten().chain(cap.iter().flatten()) {
            b.decompose_to_bits::<BF>(limb, 16)?;
        }
        b.verify_byte_hash_mmcs_opening_bytes::<BF>(
            self.hash,
            &[bytes],
            &[1usize << (self.symbol_bits - self.group_bits)],
            &symbol_index[self.group_bits..],
            path,
            cap,
        )?;
        Ok(())
    }
}

fn checked_mul(a: usize, b: usize) -> Result<usize, VerificationError> {
    a.checked_mul(b)
        .ok_or(VerificationError::ResourceArithmeticOverflow {
            component: "binary grouped oracle inputs",
        })
}
