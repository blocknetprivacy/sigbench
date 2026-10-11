use alloc::vec::Vec;
use alloc::{format, vec};
use core::cmp::{Reverse, min};
use core::marker::PhantomData;

use itertools::Itertools;
use p3_challenger::{CanObserve, FieldChallenger, GrindingChallenger};
use p3_circuit::ops::{PermCall, PermConfig, perm_private_data};
use p3_circuit::{CircuitBuilder, CircuitBuilderError, CircuitRunner, NonPrimitiveOpId};
use p3_commit::{
    CommitmentOpening, CommitmentWithOpeningPoints, MatrixOpening, Mmcs, PointOpening,
};
use p3_field::coset::TwoAdicMultiplicativeCoset;
use p3_field::{BasedVectorSpace, ExtensionField, Field, PackedValue, PrimeField64, TwoAdicField};
use p3_fri::verifier::{FriError, PowPhase, fold_query, open_inputs};
use p3_fri::{
    BatchMultiOpening, FriFoldingStrategy, FriParameters, FriProof, FriShape, TwoAdicFriFolding,
    TwoAdicFriFoldingForMmcs,
};
use p3_matrix::Dimensions;
use p3_maybe_rayon::prelude::*;
use p3_merkle_tree::{MerkleTreeError, MerkleTreeHidingMmcs, MerkleTreeMmcs, PrunedMerklePaths};
use p3_symmetric::{CryptographicHasher, PseudoCompressionFunction};
use p3_util::log2_strict_usize;
use p3_whir::pcs::proof::QueryOpenings;
use rand::distr::{Distribution, StandardUniform};
use rand::{CryptoRng, SeedableRng};
use serde::de::DeserializeOwned;
use serde::{Deserialize, Serialize};

use crate::Target;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum BaseCoeffPacking {
    Alu,
    CoeffBound,
}

fn use_coeff_bound_binary_base_opening<F, EF>(
    permutation_config: PermConfig,
    salts: Option<&[Vec<Target>]>,
) -> bool
where
    F: Field,
    EF: ExtensionField<F>,
{
    <EF as BasedVectorSpace<F>>::DIMENSION == 4
        && salts.is_none()
        && permutation_config.as_poseidon2().is_some_and(|config| {
            config.d() == 4
                && config.width() == 16
                && (config.is_baby_bear() || config.is_koala_bear())
                && !config.is_challenger()
                && !config.is_shared()
        })
}

fn add_hash_base_coeffs_overwrite<F, EF>(
    circuit: &mut CircuitBuilder<EF>,
    permutation_config: &PermConfig,
    base_coeffs: &[Target],
    reset: bool,
    packing: BaseCoeffPacking,
    merkle_seed: bool,
) -> Result<Vec<Target>, CircuitBuilderError>
where
    F: Field + PrimeField64,
    EF: ExtensionField<F>,
{
    if base_coeffs.is_empty() {
        let zero = circuit.define_const(EF::ZERO);
        return Ok(vec![zero, zero]);
    }

    let ext_degree = <EF as BasedVectorSpace<F>>::DIMENSION;
    let rate = permutation_config.rate();
    let rate_ext = permutation_config.rate_ext();
    let width_ext = permutation_config.width_ext();

    let num_chunks = base_coeffs.len().div_ceil(rate);

    let single_chunk_seed = merkle_seed && num_chunks == 1;
    let merkle_bit = single_chunk_seed.then(|| circuit.define_const(EF::ZERO));
    let mut last_rate_outputs: Option<Vec<Target>> = None;
    let mut final_outputs: Vec<Option<Target>> = vec![None; width_ext];

    let use_per_base_lift = permutation_config.d() == 1 && ext_degree > 1;

    for (chunk_idx, chunk) in base_coeffs.chunks(rate).enumerate() {
        let is_first = chunk_idx == 0;
        let is_last = chunk_idx == num_chunks - 1;

        let mut inputs: Vec<Option<Target>> = vec![None; width_ext];

        if use_per_base_lift {
            for ext_idx in 0..rate_ext {
                if ext_idx < chunk.len() {
                    inputs[ext_idx] = Some(chunk[ext_idx]);
                } else {
                    inputs[ext_idx] = None;
                }
            }
        } else {
            for ext_idx in 0..rate_ext {
                let base_start = ext_idx * ext_degree;
                let num_values_in_ext = min(ext_degree, chunk.len().saturating_sub(base_start));

                if num_values_in_ext == 0 {
                    inputs[ext_idx] = None;
                } else if num_values_in_ext == ext_degree {
                    let ext_coeffs: Vec<_> =
                        (0..ext_degree).map(|i| chunk[base_start + i]).collect();
                    inputs[ext_idx] = Some(if packing == BaseCoeffPacking::Alu {
                        circuit.recompose_base_coeffs_to_ext_via_alu::<F>(&ext_coeffs)?
                    } else {
                        circuit.recompose_base_coeffs_to_ext_with_coeff_lookups::<F>(&ext_coeffs)?
                    });
                } else {
                    let prev_coeffs: Option<Vec<Target>> = if !is_first {
                        if let Some(ref prev_rate) = last_rate_outputs {
                            Some(if packing == BaseCoeffPacking::Alu {
                                circuit
                                    .decompose_ext_to_base_coeffs_via_alu::<F>(prev_rate[ext_idx])?
                            } else {
                                circuit.decompose_ext_to_base_coeffs_with_coeff_lookups::<F>(
                                    prev_rate[ext_idx],
                                )?
                            })
                        } else {
                            None
                        }
                    } else {
                        None
                    };

                    let mut ext_coeffs = Vec::with_capacity(ext_degree);
                    for coeff_idx in 0..ext_degree {
                        if coeff_idx < num_values_in_ext {
                            ext_coeffs.push(chunk[base_start + coeff_idx]);
                        } else if let Some(ref prev) = prev_coeffs {
                            ext_coeffs.push(prev[coeff_idx]);
                        } else {
                            ext_coeffs.push(circuit.define_const(EF::ZERO));
                        }
                    }

                    inputs[ext_idx] = Some(if packing == BaseCoeffPacking::Alu {
                        circuit.recompose_base_coeffs_to_ext_via_alu::<F>(&ext_coeffs)?
                    } else {
                        circuit.recompose_base_coeffs_to_ext_with_coeff_lookups::<F>(&ext_coeffs)?
                    });
                }
            }
        }

        let (_, maybe_outputs) = circuit.add_perm(
            *permutation_config,
            &PermCall {
                new_start: if is_first { reset } else { false },
                merkle_path: single_chunk_seed,
                mmcs_bit: merkle_bit,
                mmcs_bit2: merkle_bit,
                inputs,
                out_ctl: vec![true; rate_ext],
                return_all_outputs: false,
                mmcs_index_sum: None,
            },
        )?;

        if !is_last {
            last_rate_outputs = Some(
                maybe_outputs
                    .iter()
                    .take(rate_ext)
                    .map(|o| o.ok_or(CircuitBuilderError::MissingOutput))
                    .collect::<Result<Vec<_>, _>>()?,
            );
        }

        final_outputs = maybe_outputs;
    }

    final_outputs
        .into_iter()
        .take(rate_ext)
        .map(|o| o.ok_or(CircuitBuilderError::MissingOutput))
        .collect()
}

fn add_hash_extension_elements<F, EF>(
    circuit: &mut CircuitBuilder<EF>,
    permutation_config: &PermConfig,
    ext_elements: &[Target],
    reset: bool,
    merkle_seed: bool,
) -> Result<Vec<Target>, CircuitBuilderError>
where
    F: Field + PrimeField64,
    EF: ExtensionField<F>,
{
    let ext_degree = <EF as BasedVectorSpace<F>>::DIMENSION;

    if permutation_config.d() == 1 && ext_degree > 1 {
        if ext_elements.is_empty() {
            let zero = circuit.define_const(EF::ZERO);
            return Ok(vec![zero; permutation_config.rate_ext()]);
        }
        let mut base_coeffs: Vec<Target> = Vec::with_capacity(ext_elements.len() * ext_degree);
        let live_inputs = !merkle_seed
            || ext_elements.len() * ext_degree > permutation_config.rate()
            || permutation_config
                .as_poseidon2()
                .is_some_and(|config| config.is_arity4_shape());
        for (i, &t) in ext_elements.iter().enumerate() {
            let coeffs = if EF::DIMENSION != 5 {
                circuit.decompose_ext_to_base_coeffs::<F>(t)?
            } else if live_inputs && i.is_multiple_of(2) {
                circuit.decompose_ext_to_base_coeffs_fresh_via_alu::<F>(t)?
            } else if live_inputs {
                circuit.decompose_ext_to_base_coeffs::<F>(t)?
            } else {
                circuit.decompose_ext_to_base_coeffs_fresh_with_coeff_lookups::<F>(t)?
            };
            base_coeffs.extend(coeffs);
        }
        return add_hash_base_coeffs_overwrite::<F, EF>(
            circuit,
            permutation_config,
            &base_coeffs,
            reset,
            BaseCoeffPacking::Alu,
            merkle_seed,
        );
    }

    let rate_ext = permutation_config.rate_ext();
    let width_ext = permutation_config.width_ext();
    if ext_elements.is_empty() {
        let zero = circuit.define_const(EF::ZERO);
        return Ok(vec![zero; rate_ext]);
    }

    let num_chunks = ext_elements.len().div_ceil(rate_ext);
    let single_chunk_seed = merkle_seed && num_chunks == 1;

    let zero = circuit.define_const(EF::ZERO);
    let mut last_rate_outputs: Option<Vec<Target>> = None;
    let mut final_outputs: Vec<Option<Target>> = vec![None; width_ext];

    for (i, chunk) in ext_elements.chunks(rate_ext).enumerate() {
        let is_first = i == 0;
        let mut inputs: Vec<Option<Target>> = vec![None; width_ext];
        for (j, &t) in chunk.iter().enumerate() {
            inputs[j] = Some(t);
        }
        for j in chunk.len()..rate_ext {
            inputs[j] = Some(if is_first {
                zero
            } else {
                last_rate_outputs.as_ref().map(|o| o[j]).unwrap_or(zero)
            });
        }

        let (_, maybe_outputs) = circuit.add_perm(
            *permutation_config,
            &PermCall {
                new_start: is_first && reset,
                merkle_path: single_chunk_seed,
                mmcs_bit: single_chunk_seed.then_some(zero),
                mmcs_bit2: single_chunk_seed.then_some(zero),
                inputs,
                out_ctl: vec![true; rate_ext],
                return_all_outputs: false,
                mmcs_index_sum: None,
            },
        )?;

        if chunk.len() == rate_ext {
            last_rate_outputs = Some(
                maybe_outputs
                    .iter()
                    .take(rate_ext)
                    .map(|o| o.ok_or(CircuitBuilderError::MissingOutput))
                    .collect::<Result<Vec<_>, _>>()?,
            );
        }
        final_outputs = maybe_outputs;
    }

    final_outputs
        .into_iter()
        .take(rate_ext)
        .map(|o| o.ok_or(CircuitBuilderError::MissingOutput))
        .collect()
}

pub fn verify_batch_circuit<F, EF>(
    circuit: &mut CircuitBuilder<EF>,
    permutation_config: impl Into<PermConfig>,
    commitment_cap: &[Vec<Target>],
    dimensions: &[Dimensions],
    index_bits: &[Target],
    opened_base_coeffs: &[Vec<Target>],
    salts: Option<&[Vec<Target>]>,
) -> Result<Vec<NonPrimitiveOpId>, CircuitBuilderError>
where
    F: Field + TwoAdicField + PrimeField64,
    EF: ExtensionField<F>,
{
    let permutation_config: PermConfig = permutation_config.into();
    let packing = if use_coeff_bound_binary_base_opening::<F, EF>(permutation_config, salts) {
        BaseCoeffPacking::CoeffBound
    } else {
        BaseCoeffPacking::Alu
    };
    verify_batch_circuit_with_packing::<F, EF>(
        circuit,
        permutation_config,
        commitment_cap,
        dimensions,
        index_bits,
        opened_base_coeffs,
        salts,
        packing,
    )
}

pub(crate) fn verify_whir_base_batch_circuit<F, EF>(
    circuit: &mut CircuitBuilder<EF>,
    permutation_config: impl Into<PermConfig>,
    commitment_cap: &[Vec<Target>],
    dimensions: &[Dimensions],
    index_bits: &[Target],
    opened_base_coeffs: &[Vec<Target>],
) -> Result<Vec<NonPrimitiveOpId>, CircuitBuilderError>
where
    F: Field + TwoAdicField + PrimeField64,
    EF: ExtensionField<F>,
{
    let permutation_config: PermConfig = permutation_config.into();
    let degree = <EF as BasedVectorSpace<F>>::DIMENSION;
    let packing = if (matches!(degree, 2 | 4) && permutation_config.d() == degree)
        || use_coeff_bound_binary_base_opening::<F, EF>(permutation_config, None)
    {
        BaseCoeffPacking::CoeffBound
    } else {
        BaseCoeffPacking::Alu
    };
    verify_batch_circuit_with_packing::<F, EF>(
        circuit,
        permutation_config,
        commitment_cap,
        dimensions,
        index_bits,
        opened_base_coeffs,
        None,
        packing,
    )
}

#[expect(
    clippy::too_many_arguments,
    reason = "shared MMCS body adds caller-resolved policy"
)]
fn verify_batch_circuit_with_packing<F, EF>(
    circuit: &mut CircuitBuilder<EF>,
    permutation_config: PermConfig,
    commitment_cap: &[Vec<Target>],
    dimensions: &[Dimensions],
    index_bits: &[Target],
    opened_base_coeffs: &[Vec<Target>],
    salts: Option<&[Vec<Target>]>,
    packing: BaseCoeffPacking,
) -> Result<Vec<NonPrimitiveOpId>, CircuitBuilderError>
where
    F: Field + TwoAdicField + PrimeField64,
    EF: ExtensionField<F>,
{
    if dimensions.len() != opened_base_coeffs.len() {
        return Err(CircuitBuilderError::WrongBatchSize {
            expected: dimensions.len(),
            got: opened_base_coeffs.len(),
        });
    }

    if let Some(salts) = salts
        && salts.len() != opened_base_coeffs.len()
    {
        return Err(CircuitBuilderError::WrongBatchSize {
            expected: opened_base_coeffs.len(),
            got: salts.len(),
        });
    }

    let cap_height = validate_commitment_cap(commitment_cap, index_bits.len())?;

    let max_height_log = index_bits.len();
    let path_depth = max_height_log - cap_height;

    let path_bits = &index_bits[..path_depth];
    let cap_index_bits = &index_bits[path_depth..];

    let selected_root = select_cap_entry(circuit, commitment_cap, cap_index_bits);

    let mut heights_tallest_first = dimensions
        .iter()
        .enumerate()
        .sorted_by_key(|(_, dims)| Reverse(dims.height))
        .peekable();

    let digest_levels = path_depth + 1;
    let mut formatted_digests = vec![vec![]; digest_levels];
    for (i, digest) in formatted_digests.iter_mut().enumerate() {
        let curr_height = 1 << (max_height_log - i);

        let all_base_coeffs: Vec<Target> = heights_tallest_first
            .peeking_take_while(|(_, dims)| dims.height.next_power_of_two() == curr_height)
            .flat_map(|(mat_idx, _)| {
                let mut coeffs: Vec<Target> = opened_base_coeffs[mat_idx].clone();
                if let Some(salts) = salts {
                    coeffs.extend(salts[mat_idx].iter().copied());
                }
                coeffs
            })
            .collect();

        if all_base_coeffs.is_empty() {
            continue;
        }

        *digest = add_hash_base_coeffs_overwrite::<F, EF>(
            circuit,
            &permutation_config,
            &all_base_coeffs,
            true,
            packing,
            false,
        )?;
    }

    let op_vals_digests = formatted_digests;

    circuit.add_mmcs_verify(
        permutation_config,
        &op_vals_digests,
        path_bits,
        &selected_root,
    )
}

pub fn verify_batch_circuit_from_extension_opened<F, EF>(
    circuit: &mut CircuitBuilder<EF>,
    permutation_config: impl Into<PermConfig>,
    commitment_cap: &[Vec<Target>],
    dimensions: &[Dimensions],
    index_bits: &[Target],
    opened_extension_values: &[Vec<Target>],
    salts: Option<&[Vec<Target>]>,
) -> Result<Vec<NonPrimitiveOpId>, CircuitBuilderError>
where
    F: Field + TwoAdicField + PrimeField64,
    EF: ExtensionField<F>,
{
    let permutation_config: PermConfig = permutation_config.into();
    if dimensions.len() != opened_extension_values.len() {
        return Err(CircuitBuilderError::WrongBatchSize {
            expected: dimensions.len(),
            got: opened_extension_values.len(),
        });
    }

    if let Some(salts) = salts
        && salts.len() != opened_extension_values.len()
    {
        return Err(CircuitBuilderError::WrongBatchSize {
            expected: opened_extension_values.len(),
            got: salts.len(),
        });
    }

    let cap_height = validate_commitment_cap(commitment_cap, index_bits.len())?;

    let max_height_log = index_bits.len();
    let path_depth = max_height_log - cap_height;
    let path_bits = &index_bits[..path_depth];
    let cap_index_bits = &index_bits[path_depth..];

    let selected_root = select_cap_entry(circuit, commitment_cap, cap_index_bits);

    let mut heights_tallest_first = dimensions
        .iter()
        .enumerate()
        .sorted_by_key(|(_, dims)| Reverse(dims.height))
        .peekable();

    let digest_levels = path_depth + 1;
    let mut formatted_digests = vec![vec![]; digest_levels];
    for (i, digest) in formatted_digests.iter_mut().enumerate() {
        let curr_height = 1 << (max_height_log - i);

        let mats_at_height: Vec<usize> = heights_tallest_first
            .peeking_take_while(|(_, dims)| dims.height.next_power_of_two() == curr_height)
            .map(|(mat_idx, _)| mat_idx)
            .collect();

        if mats_at_height.is_empty() {
            continue;
        }

        *digest = if let Some(salts) = salts {
            let mut all_base: Vec<Target> = Vec::new();
            for &mat_idx in &mats_at_height {
                for &ext in &opened_extension_values[mat_idx] {
                    let coeffs = if permutation_config.d() == 1 {
                        circuit.decompose_ext_to_base_coeffs_fresh_via_alu::<F>(ext)?
                    } else {
                        circuit.decompose_ext_to_base_coeffs_fresh_with_coeff_lookups::<F>(ext)?
                    };
                    all_base.extend(coeffs);
                }
                all_base.extend(salts[mat_idx].iter().copied());
            }
            add_hash_base_coeffs_overwrite::<F, EF>(
                circuit,
                &permutation_config,
                &all_base,
                true,
                BaseCoeffPacking::Alu,
                false,
            )?
        } else {
            let all_ext: Vec<Target> = mats_at_height
                .iter()
                .flat_map(|&mat_idx| opened_extension_values[mat_idx].iter().copied())
                .collect();
            add_hash_extension_elements::<F, EF>(
                circuit,
                &permutation_config,
                &all_ext,
                true,
                false,
            )?
        };
    }

    circuit.add_mmcs_verify(
        permutation_config,
        &formatted_digests,
        path_bits,
        &selected_root,
    )
}

pub(crate) fn validate_commitment_cap_len<T>(
    commitment_cap: &[T],
) -> Result<usize, CircuitBuilderError> {
    validate_commitment_cap_count(commitment_cap.len())
}

pub(crate) fn validate_commitment_cap_count(roots: usize) -> Result<usize, CircuitBuilderError> {
    if roots == 0 {
        return Err(CircuitBuilderError::InvalidMerkleCap {
            details: "commitment cap must have at least one entry".into(),
        });
    }
    if !roots.is_power_of_two() {
        return Err(CircuitBuilderError::InvalidMerkleCap {
            details: format!("commitment cap length must be a power of two, got {roots}"),
        });
    }
    Ok(roots.trailing_zeros() as usize)
}

pub(crate) fn validate_commitment_cap<T>(
    commitment_cap: &[T],
    tree_height: usize,
) -> Result<usize, CircuitBuilderError> {
    validate_binary_cap_count(commitment_cap.len(), tree_height)
}

pub(crate) fn validate_binary_cap_count(
    roots: usize,
    tree_height: usize,
) -> Result<usize, CircuitBuilderError> {
    let cap_height = validate_commitment_cap_count(roots)?;
    if cap_height > tree_height {
        return Err(CircuitBuilderError::InvalidMerkleCap {
            details: format!(
                "commitment cap height {cap_height} exceeds tree height {tree_height}"
            ),
        });
    }
    Ok(cap_height)
}

pub(crate) fn checked_next_power_of_two(value: usize) -> Result<usize, CircuitBuilderError> {
    value
        .checked_next_power_of_two()
        .ok_or_else(|| CircuitBuilderError::InvalidMerkleCap {
            details: "matrix height cannot be rounded to a power of two".into(),
        })
}

pub(crate) fn checked_padded_len(raw_len: usize) -> Result<usize, CircuitBuilderError> {
    if raw_len <= 1 {
        Ok(raw_len)
    } else if raw_len < 4 {
        Ok(4)
    } else {
        raw_len
            .div_ceil(4)
            .checked_mul(4)
            .ok_or_else(|| CircuitBuilderError::InvalidMerkleCap {
                details: "padded arity-4 matrix height overflows".into(),
            })
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct Arity4StepGeometry {
    pub(crate) step: usize,
    pub(crate) injection_height: Option<usize>,
}

#[allow(clippy::needless_pass_by_value)]
pub(crate) fn visit_arity4_path<I, V>(
    heights: I,
    roots: usize,
    mut visit: V,
) -> Result<usize, CircuitBuilderError>
where
    I: Iterator<Item = usize> + Clone,
    V: FnMut(Arity4StepGeometry),
{
    validate_commitment_cap_count(roots)?;

    let scan = heights.clone();
    let mut max_height = 0usize;
    let mut has_height = false;
    for height in scan {
        if height == 0 {
            continue;
        }
        has_height = true;
        max_height = max_height.max(height);
    }
    if !has_height {
        return Err(CircuitBuilderError::Poseidon2ConfigMismatch {
            expected: "at least one non-empty matrix".into(),
            got: "empty batch".into(),
        });
    }

    let mut buckets: [Option<usize>; usize::BITS as usize + 1] = [None; usize::BITS as usize + 1];
    for height in heights {
        let bucket = checked_next_power_of_two(height)?;
        let bucket_index = bucket.trailing_zeros() as usize;
        match buckets[bucket_index] {
            Some(existing) if existing != height => {
                return Err(CircuitBuilderError::Poseidon2ConfigMismatch {
                    expected: "matrix heights that round up to the same power of two must be equal"
                        .into(),
                    got: "incompatible matrix heights".into(),
                });
            }
            None => buckets[bucket_index] = Some(height),
            Some(_) => {}
        }
    }

    let mut curr = checked_padded_len(max_height)?;
    let mut consumed_below = checked_next_power_of_two(max_height)?;
    let mut path_bits = 0usize;
    while curr > roots {
        let step = if curr < 4 {
            2
        } else {
            let target = checked_next_power_of_two(curr / 4)?;
            let mut has_intermediate = false;
            for (bucket_index, height) in buckets.iter().enumerate() {
                if height.is_some() {
                    let bucket = 1usize << bucket_index;
                    if bucket < consumed_below && bucket > target {
                        has_intermediate = true;
                        break;
                    }
                }
            }
            if has_intermediate { 2 } else { 4 }
        };

        let logical_next = curr / step;
        let next = checked_padded_len(logical_next)?;
        let logical_next_bucket = checked_next_power_of_two(logical_next)?;
        let injection_height = if logical_next_bucket < consumed_below {
            let bucket_index = logical_next_bucket.trailing_zeros() as usize;
            buckets[bucket_index]
        } else {
            None
        };
        if injection_height.is_some() {
            consumed_below = logical_next_bucket;
        }
        if next == curr && injection_height.is_none() {
            return Err(CircuitBuilderError::InvalidMerkleCap {
                details: "arity-4 cap walk made no progress".into(),
            });
        }

        visit(Arity4StepGeometry {
            step,
            injection_height,
        });
        curr = next;
        path_bits = path_bits
            .checked_add(if step == 4 { 2 } else { 1 })
            .ok_or_else(|| CircuitBuilderError::InvalidMerkleCap {
                details: "arity-4 path bit count overflows".into(),
            })?;
    }
    Ok(path_bits)
}

#[allow(dead_code)]
pub(crate) fn validate_arity4_cap_geometry(
    heights: &[usize],
    roots: usize,
) -> Result<usize, CircuitBuilderError> {
    visit_arity4_path(heights.iter().copied(), roots, |_| {})
}

fn select_cap_entry<EF: Field>(
    circuit: &mut CircuitBuilder<EF>,
    cap: &[Vec<Target>],
    index_bits: &[Target],
) -> Vec<Target> {
    if cap.len() == 1 {
        return cap[0].clone();
    }

    debug_assert_eq!(cap.len(), 1 << index_bits.len());

    let rate_ext = cap[0].len();

    let mut current: Vec<Vec<Target>> = cap.to_vec();

    for &bit in index_bits {
        let half = current.len() / 2;
        let mut next = Vec::with_capacity(half);
        for i in 0..half {
            let left = &current[2 * i];
            let right = &current[2 * i + 1];
            let mut selected = Vec::with_capacity(rate_ext);
            for j in 0..rate_ext {
                let diff = circuit.sub(right[j], left[j]);
                let val = circuit.mul_add(bit, diff, left[j]);
                selected.push(val);
            }
            next.push(selected);
        }
        current = next;
    }

    debug_assert_eq!(current.len(), 1);
    current.into_iter().next().unwrap()
}

pub fn convert_merkle_proof_to_siblings<F, EF, const DIGEST_ELEMS: usize>(
    opening_proof: &[[F; DIGEST_ELEMS]],
) -> Vec<Vec<EF>>
where
    F: Field,
    EF: ExtensionField<F> + BasedVectorSpace<F>,
{
    let d = EF::DIMENSION;
    opening_proof
        .iter()
        .map(|digest| {
            if DIGEST_ELEMS.is_multiple_of(d) {
                let ext_count = DIGEST_ELEMS / d;
                (0..ext_count)
                    .map(|chunk_idx| {
                        let start = chunk_idx * d;
                        let mut coeffs = vec![F::ZERO; d];
                        coeffs[..d].copy_from_slice(&digest[start..(d + start)]);
                        EF::from_basis_coefficients_slice(&coeffs)
                            .expect("coefficients match extension degree")
                    })
                    .collect()
            } else {
                digest
                    .iter()
                    .map(|&b| {
                        let mut coeffs = vec![F::ZERO; d];
                        coeffs[0] = b;
                        EF::from_basis_coefficients_slice(&coeffs)
                            .expect("embedded base digest element")
                    })
                    .collect()
            }
        })
        .collect()
}

#[derive(Clone, Debug)]
pub struct FriQueryPaths<F, const DIGEST_ELEMS: usize> {
    pub input: Vec<Vec<[F; DIGEST_ELEMS]>>,
    pub commit_phase: Vec<Vec<[F; DIGEST_ELEMS]>>,
}

type FriTreeMmcs<Val, H, C, const N: usize, const DIGEST_ELEMS: usize> =
    MerkleTreeMmcs<<Val as Field>::Packing, <Val as Field>::Packing, H, C, N, DIGEST_ELEMS>;

#[derive(Clone, Debug)]
pub struct FriQueryLayout<Challenge> {
    pub indices: Vec<usize>,
    pub log_global_max_height: usize,
    pub log_arities: Vec<usize>,
    pub group_indices_by_round: Vec<Vec<usize>>,
    pub rows_by_round: Vec<Vec<Vec<Vec<Challenge>>>>,
}

pub fn replay_fri_query_layout<Val, Challenge, InputMmcs, FriMmcs, Challenger>(
    params: &FriParameters<FriMmcs>,
    input_mmcs: &InputMmcs,
    proof: &FriProof<
        Challenge,
        FriMmcs,
        Challenger::Witness,
        Vec<BatchMultiOpening<Val, InputMmcs>>,
    >,
    challenger: &mut Challenger,
    commitments_with_opening_points: &[CommitmentWithOpeningPoints<
        Challenge,
        InputMmcs::Commitment,
        TwoAdicMultiplicativeCoset<Val>,
    >],
) -> Result<FriQueryLayout<Challenge>, FriError<FriMmcs::Error, InputMmcs::Error>>
where
    Val: TwoAdicField + PrimeField64,
    Challenge: ExtensionField<Val>,
    InputMmcs: Mmcs<Val, MultiProof: Sync, Error: Sync>,
    FriMmcs: Mmcs<Challenge>,
    Challenger: FieldChallenger<Val> + GrindingChallenger + CanObserve<FriMmcs::Commitment>,
{
    let samples = sample_fri_queries(params, proof, challenger, commitments_with_opening_points)?;
    fold_fri_queries(
        params,
        input_mmcs,
        proof,
        commitments_with_opening_points,
        samples,
    )
}

struct FriQuerySamples<Challenge> {
    alpha: Challenge,
    betas: Vec<Challenge>,
    log_arities: Vec<usize>,
    log_global_max_height: usize,
    log_final_height: usize,
    extra_query_index_bits: usize,
    indices: Vec<usize>,
}

fn sample_fri_queries<Val, Challenge, InputMmcs, FriMmcs, Challenger>(
    params: &FriParameters<FriMmcs>,
    proof: &FriProof<
        Challenge,
        FriMmcs,
        Challenger::Witness,
        Vec<BatchMultiOpening<Val, InputMmcs>>,
    >,
    challenger: &mut Challenger,
    commitments_with_opening_points: &[CommitmentWithOpeningPoints<
        Challenge,
        InputMmcs::Commitment,
        TwoAdicMultiplicativeCoset<Val>,
    >],
) -> Result<FriQuerySamples<Challenge>, FriError<FriMmcs::Error, InputMmcs::Error>>
where
    Val: TwoAdicField + PrimeField64,
    Challenge: ExtensionField<Val>,
    InputMmcs: Mmcs<Val, MultiProof: Sync, Error: Sync>,
    FriMmcs: Mmcs<Challenge>,
    Challenger: FieldChallenger<Val> + GrindingChallenger + CanObserve<FriMmcs::Commitment>,
{
    type Folding<Val, InputMmcs> = TwoAdicFriFoldingForMmcs<Val, InputMmcs>;
    let folding: Folding<Val, InputMmcs> = TwoAdicFriFolding(PhantomData);

    if params.num_queries == 0 {
        return Err(FriError::ZeroQueries);
    }

    let expected_rounds = proof.commit_phase_commits.len();
    if proof.commit_phase_openings.len() != expected_rounds {
        return Err(FriError::CommitPhaseOpeningsCountMismatch {
            expected: expected_rounds,
            got: proof.commit_phase_openings.len(),
        });
    }

    if params.max_log_arity == 0 {
        return Err(FriError::ZeroFoldingArity);
    }
    let mut input_log_heights = Vec::new();
    for claim in commitments_with_opening_points {
        for MatrixOpening { domain, .. } in &claim.matrices {
            let height = log2_strict_usize(domain.size())
                .checked_add(params.log_blowup)
                .filter(|&height| height < usize::BITS as usize)
                .ok_or(FriError::GlobalMaxHeightTooLarge {
                    log_global_max_height: usize::MAX,
                    two_adicity: Val::TWO_ADICITY,
                })?;
            input_log_heights.push(height);
        }
    }
    input_log_heights.sort_unstable_by(|a, b| b.cmp(a));
    input_log_heights.dedup();
    let log_final_height_for_schedule = params
        .log_blowup
        .checked_add(params.log_final_poly_len)
        .ok_or(FriError::GlobalMaxHeightTooLarge {
            log_global_max_height: usize::MAX,
            two_adicity: Val::TWO_ADICITY,
        })?;
    let log_arities = p3_fri::fold_schedule(
        &input_log_heights,
        log_final_height_for_schedule,
        params.max_log_arity,
    );
    if proof.commit_phase_openings.len() != log_arities.len() {
        return Err(FriError::CommitPhaseOpeningsCountMismatch {
            expected: log_arities.len(),
            got: proof.commit_phase_openings.len(),
        });
    }

    for (round, opening) in proof.commit_phase_openings.iter().enumerate() {
        if opening.sibling_values.len() != params.num_queries {
            return Err(FriError::CommitPhaseQueryCountMismatch {
                round,
                expected: params.num_queries,
                got: opening.sibling_values.len(),
            });
        }
        let expected_siblings = (1usize << log_arities[round]) - 1;
        if let Some(actual) = opening
            .sibling_values
            .iter()
            .map(Vec::len)
            .find(|&actual| actual != expected_siblings)
        {
            return Err(FriError::SiblingValuesLengthMismatch {
                round,
                expected: expected_siblings,
                got: actual,
            });
        }
    }

    let log_global_max_height = log_arities
        .iter()
        .try_fold(0usize, |sum, &arity| sum.checked_add(arity))
        .and_then(|sum| sum.checked_add(params.log_blowup))
        .and_then(|sum| sum.checked_add(params.log_final_poly_len))
        .ok_or(FriError::GlobalMaxHeightTooLarge {
            log_global_max_height: usize::MAX,
            two_adicity: Val::TWO_ADICITY,
        })?;

    if log_global_max_height > Val::TWO_ADICITY || log_global_max_height >= usize::BITS as usize {
        return Err(FriError::GlobalMaxHeightTooLarge {
            log_global_max_height,
            two_adicity: Val::TWO_ADICITY,
        });
    }

    let mut expected_log_global_max_height = None;
    for claim in commitments_with_opening_points {
        for MatrixOpening { domain, .. } in &claim.matrices {
            let height = log2_strict_usize(domain.size())
                .checked_add(params.log_blowup)
                .filter(|&height| height < usize::BITS as usize)
                .ok_or(FriError::GlobalMaxHeightTooLarge {
                    log_global_max_height: usize::MAX,
                    two_adicity: Val::TWO_ADICITY,
                })?;
            expected_log_global_max_height =
                Some(expected_log_global_max_height.map_or(height, |old: usize| old.max(height)));
        }
    }
    if let Some(expected) = expected_log_global_max_height
        && log_global_max_height != expected
    {
        return Err(FriError::GlobalMaxHeightTooLarge {
            log_global_max_height: log_global_max_height.max(expected),
            two_adicity: Val::TWO_ADICITY,
        });
    }

    if proof.commit_pow_witnesses.len() != proof.commit_phase_commits.len() {
        return Err(FriError::CommitPowWitnessCountMismatch {
            expected: proof.commit_phase_commits.len(),
            got: proof.commit_pow_witnesses.len(),
        });
    }

    if proof.final_poly.len() != params.final_poly_len() {
        return Err(FriError::FinalPolyLengthMismatch {
            expected: params.final_poly_len(),
            got: proof.final_poly.len(),
        });
    }

    let log_final_height = params
        .log_blowup
        .checked_add(params.log_final_poly_len)
        .filter(|&height| height < usize::BITS as usize)
        .ok_or(FriError::GlobalMaxHeightTooLarge {
            log_global_max_height: usize::MAX,
            two_adicity: Val::TWO_ADICITY,
        })?;

    let extra_query_index_bits =
        FriFoldingStrategy::<Val, Challenge>::extra_query_index_bits(&folding);
    let query_index_bits = log_global_max_height
        .checked_add(extra_query_index_bits)
        .filter(|&bits| bits < usize::BITS as usize)
        .ok_or(FriError::GlobalMaxHeightTooLarge {
            log_global_max_height: usize::MAX,
            two_adicity: Val::TWO_ADICITY,
        })?;

    if proof.input_openings.len() != commitments_with_opening_points.len() {
        return Err(FriError::InputProofBatchCountMismatch {
            expected: commitments_with_opening_points.len(),
            got: proof.input_openings.len(),
        });
    }
    for (batch, (opening, CommitmentOpening { matrices, .. })) in proof
        .input_openings
        .iter()
        .zip(commitments_with_opening_points)
        .enumerate()
    {
        if opening.opened_values.len() != params.num_queries {
            return Err(FriError::InputOpeningsQueryCountMismatch {
                batch,
                expected: params.num_queries,
                got: opening.opened_values.len(),
            });
        }
        for rows in &opening.opened_values {
            if rows.len() != matrices.len() {
                return Err(FriError::BatchOpenedValuesCountMismatch {
                    batch,
                    expected: matrices.len(),
                    got: rows.len(),
                });
            }
            for (matrix, (row, MatrixOpening { points, .. })) in
                rows.iter().zip(matrices).enumerate()
            {
                if points.is_empty() {
                    return Err(FriError::MatrixWithoutOpeningPoints { batch, matrix });
                }
                for (
                    point,
                    PointOpening {
                        values: claimed, ..
                    },
                ) in points.iter().enumerate()
                {
                    if row.len() != claimed.len() {
                        return Err(FriError::PointEvaluationCountMismatch {
                            batch,
                            matrix,
                            point,
                            expected: row.len(),
                            got: claimed.len(),
                        });
                    }
                }
            }
        }
    }

    if !challenger.check_witness(params.batch_proof_of_work_bits, proof.batch_pow_witness) {
        return Err(FriError::InvalidPowWitness(PowPhase::Batch));
    }
    let alpha: Challenge = challenger.sample_algebra_element();
    FriShape::with_schedule(params, log_arities.clone(), query_index_bits)
        .domain_separator::<Val, Challenge>()
        .seed(challenger);

    let betas: Vec<Challenge> = proof
        .commit_phase_commits
        .iter()
        .zip(&proof.commit_pow_witnesses)
        .map(|(comm, witness)| {
            challenger.observe(comm.clone());
            if !challenger.check_witness(params.commit_proof_of_work_bits, *witness) {
                return Err(FriError::InvalidPowWitness(PowPhase::CommitPhase));
            }
            Ok(challenger.sample_algebra_element())
        })
        .collect::<Result<Vec<_>, _>>()?;

    challenger.observe_algebra_slice(&proof.final_poly);

    if !challenger.check_witness(params.query_proof_of_work_bits, proof.query_pow_witness) {
        return Err(FriError::InvalidPowWitness(PowPhase::Query));
    }

    let indices: Vec<usize> = core::iter::repeat_with(|| challenger.sample_bits(query_index_bits))
        .take(params.num_queries)
        .collect();

    Ok(FriQuerySamples {
        alpha,
        betas,
        log_arities,
        log_global_max_height,
        log_final_height,
        extra_query_index_bits,
        indices,
    })
}

fn fold_fri_queries<Val, Challenge, InputMmcs, FriMmcs, Witness>(
    params: &FriParameters<FriMmcs>,
    input_mmcs: &InputMmcs,
    proof: &FriProof<Challenge, FriMmcs, Witness, Vec<BatchMultiOpening<Val, InputMmcs>>>,
    commitments_with_opening_points: &[CommitmentWithOpeningPoints<
        Challenge,
        InputMmcs::Commitment,
        TwoAdicMultiplicativeCoset<Val>,
    >],
    samples: FriQuerySamples<Challenge>,
) -> Result<FriQueryLayout<Challenge>, FriError<FriMmcs::Error, InputMmcs::Error>>
where
    Val: TwoAdicField,
    Challenge: ExtensionField<Val>,
    InputMmcs: Mmcs<Val, MultiProof: Sync, Error: Sync>,
    FriMmcs: Mmcs<Challenge>,
{
    type Folding<Val, InputMmcs> = TwoAdicFriFoldingForMmcs<Val, InputMmcs>;
    let folding: Folding<Val, InputMmcs> = TwoAdicFriFolding(PhantomData);
    let FriQuerySamples {
        alpha,
        betas,
        log_arities,
        log_global_max_height,
        log_final_height,
        extra_query_index_bits,
        indices,
    } = samples;

    let reduced_openings = open_inputs::<Val, Challenge, _, FriMmcs>(
        params,
        log_global_max_height,
        &indices,
        &proof.input_openings,
        alpha,
        input_mmcs,
        commitments_with_opening_points,
    )?;

    let num_rounds = proof.commit_phase_commits.len();
    let mut group_indices_by_round: Vec<Vec<usize>> = vec![Vec::new(); num_rounds];
    let mut rows_by_round: Vec<Vec<Vec<Vec<Challenge>>>> = vec![Vec::new(); num_rounds];
    for (query, (&index, ro)) in indices.iter().zip(reduced_openings).enumerate() {
        let mut domain_index = index >> extra_query_index_bits;
        fold_query(
            &folding,
            query,
            &mut domain_index,
            &betas,
            &log_arities,
            &proof.commit_phase_openings,
            ro,
            log_global_max_height,
            log_final_height,
            &mut group_indices_by_round,
            &mut rows_by_round,
        )?;
    }

    Ok(FriQueryLayout {
        indices,
        log_global_max_height,
        log_arities,
        group_indices_by_round,
        rows_by_round,
    })
}

fn input_batch_layout<Val, Challenge, E1: core::fmt::Debug, E2: core::fmt::Debug>(
    params: &FriParameters<impl Mmcs<Challenge>>,
    batch: usize,
    log_global_max_height: usize,
    indices: &[usize],
    mats: &[MatrixOpening<Challenge, TwoAdicMultiplicativeCoset<Val>>],
) -> Result<(Vec<Dimensions>, Vec<usize>), FriError<E1, E2>>
where
    Val: TwoAdicField,
    Challenge: ExtensionField<Val>,
{
    let batch_heights: Vec<usize> = mats
        .iter()
        .map(|matrix| matrix.domain.size() << params.log_blowup)
        .collect();
    let batch_dims = batch_heights
        .iter()
        .zip(mats)
        .enumerate()
        .map(|(matrix, (&height, opening))| {
            let PointOpening { values, .. } = opening
                .points
                .first()
                .ok_or(FriError::MatrixWithoutOpeningPoints { batch, matrix })?;
            Ok(Dimensions {
                width: values.len(),
                height,
            })
        })
        .collect::<Result<Vec<_>, FriError<E1, E2>>>()?;

    let reduced_indices: Vec<usize> = batch_heights
        .iter()
        .max()
        .map(|&h| {
            let bits_reduced = log_global_max_height - log2_strict_usize(h);
            indices.iter().map(|&index| index >> bits_reduced).collect()
        })
        .unwrap_or_else(|| vec![0; indices.len()]);

    Ok((batch_dims, reduced_indices))
}

const fn commit_phase_dims<Challenge: BasedVectorSpace<Val>, Val: Field>(
    log_arity: usize,
    log_folded_height: usize,
) -> Dimensions {
    Dimensions {
        width: (1 << log_arity) * Challenge::DIMENSION,
        height: 1 << log_folded_height,
    }
}

fn transpose_query_paths<Val, const DIGEST_ELEMS: usize>(
    num_queries: usize,
    input_paths_by_batch: &[Vec<Vec<[Val; DIGEST_ELEMS]>>],
    commit_phase_paths_by_round: &[Vec<Vec<[Val; DIGEST_ELEMS]>>],
) -> Vec<FriQueryPaths<Val, DIGEST_ELEMS>>
where
    Val: Clone,
{
    (0..num_queries)
        .map(|query| FriQueryPaths {
            input: input_paths_by_batch
                .iter()
                .map(|batch| batch[query].clone())
                .collect(),
            commit_phase: commit_phase_paths_by_round
                .iter()
                .map(|round| round[query].clone())
                .collect(),
        })
        .collect()
}

#[expect(clippy::type_complexity)]
pub fn restore_fri_query_paths<
    Val,
    Challenge,
    FriMmcs,
    Challenger,
    H,
    C,
    const N: usize,
    const DIGEST_ELEMS: usize,
>(
    params: &FriParameters<FriMmcs>,
    input_mmcs: &FriTreeMmcs<Val, H, C, N, DIGEST_ELEMS>,
    commit_phase_mmcs: &FriTreeMmcs<Val, H, C, N, DIGEST_ELEMS>,
    proof: &FriProof<
        Challenge,
        FriMmcs,
        Challenger::Witness,
        Vec<BatchMultiOpening<Val, FriTreeMmcs<Val, H, C, N, DIGEST_ELEMS>>>,
    >,
    challenger: &mut Challenger,
    commitments_with_opening_points: &[CommitmentWithOpeningPoints<
        Challenge,
        <FriTreeMmcs<Val, H, C, N, DIGEST_ELEMS> as Mmcs<Val>>::Commitment,
        TwoAdicMultiplicativeCoset<Val>,
    >],
) -> Result<Vec<FriQueryPaths<Val, DIGEST_ELEMS>>, FriError<MerkleTreeError, MerkleTreeError>>
where
    Val: TwoAdicField + PrimeField64 + Serialize + DeserializeOwned,
    Challenge: ExtensionField<Val>,
    FriMmcs: Mmcs<Challenge, MultiProof = PrunedMerklePaths<Val, DIGEST_ELEMS>, Error = MerkleTreeError>
        + Sync,
    FriMmcs::Commitment: Sync,
    Challenger: FieldChallenger<Val> + GrindingChallenger + CanObserve<FriMmcs::Commitment>,
    H: CryptographicHasher<Val, [Val; DIGEST_ELEMS]>
        + CryptographicHasher<Val::Packing, [Val::Packing; DIGEST_ELEMS]>
        + Sync,
    C: PseudoCompressionFunction<[Val; DIGEST_ELEMS], N>
        + PseudoCompressionFunction<[Val::Packing; DIGEST_ELEMS], N>
        + Sync,
    [Val; DIGEST_ELEMS]: Serialize + DeserializeOwned,
{
    let samples = sample_fri_queries(params, proof, challenger, commitments_with_opening_points)?;
    let indices = samples.indices.clone();
    let log_global_max_height = samples.log_global_max_height;

    let (layout, input_paths_by_batch) = join(
        || {
            fold_fri_queries(
                params,
                input_mmcs,
                proof,
                commitments_with_opening_points,
                samples,
            )
        },
        || {
            proof
                .input_openings
                .par_iter()
                .zip(commitments_with_opening_points.par_iter())
                .enumerate()
                .map(
                    |(batch, (batch_opening, CommitmentOpening { matrices: mats, .. }))| {
                        let (batch_dims, reduced_indices) =
                            input_batch_layout::<Val, Challenge, MerkleTreeError, MerkleTreeError>(
                                params,
                                batch,
                                log_global_max_height,
                                &indices,
                                mats,
                            )?;
                        Ok(input_mmcs
                            .restore_and_recompute_paths(
                                &batch_dims,
                                &reduced_indices,
                                &batch_opening.opened_values,
                                &batch_opening.opening_proof,
                            )
                            .map_err(FriError::InputError)?
                            .into_iter()
                            .map(|path| path.siblings)
                            .collect())
                    },
                )
                .collect::<Result<
                    Vec<Vec<Vec<[Val; DIGEST_ELEMS]>>>,
                    FriError<MerkleTreeError, MerkleTreeError>,
                >>()
        },
    );
    let layout = layout?;
    let input_paths_by_batch = input_paths_by_batch?;

    let log_folded_heights: Vec<usize> = layout
        .log_arities
        .iter()
        .scan(layout.log_global_max_height, |log_height, &log_arity| {
            *log_height -= log_arity;
            Some(*log_height)
        })
        .collect();
    let commit_phase_paths_by_round: Vec<Vec<Vec<[Val; DIGEST_ELEMS]>>> = proof
        .commit_phase_openings
        .par_iter()
        .zip(
            layout
                .log_arities
                .par_iter()
                .zip(log_folded_heights.par_iter()),
        )
        .enumerate()
        .map(|(round, (opening, (&log_arity, &log_folded_height)))| {
            let dims = [commit_phase_dims::<Challenge, Val>(
                log_arity,
                log_folded_height,
            )];
            let opened_values: Vec<Vec<Vec<Val>>> = layout.rows_by_round[round]
                .iter()
                .map(|rows| {
                    rows.iter()
                        .map(|row| Challenge::flatten_to_base(row.clone()))
                        .collect()
                })
                .collect();

            Ok(commit_phase_mmcs
                .restore_and_recompute_paths(
                    &dims,
                    &layout.group_indices_by_round[round],
                    &opened_values,
                    &opening.opening_proof,
                )
                .map_err(FriError::CommitPhaseMmcsError)?
                .into_iter()
                .map(|path| path.siblings)
                .collect())
        })
        .collect::<Result<_, FriError<MerkleTreeError, MerkleTreeError>>>()?;

    Ok(transpose_query_paths(
        params.num_queries,
        &input_paths_by_batch,
        &commit_phase_paths_by_round,
    ))
}

#[expect(clippy::type_complexity)]
pub fn restore_hiding_fri_query_paths<
    Val,
    Challenge,
    FriMmcs,
    Challenger,
    R,
    H,
    C,
    const N: usize,
    const DIGEST_ELEMS: usize,
    const SALT_ELEMS: usize,
>(
    params: &FriParameters<FriMmcs>,
    input_mmcs: &HidingTreeMmcs<Val, H, C, R, N, DIGEST_ELEMS, SALT_ELEMS>,
    input_tree: &FriTreeMmcs<Val, H, C, N, DIGEST_ELEMS>,
    commit_phase_tree: &FriTreeMmcs<Val, H, C, N, DIGEST_ELEMS>,
    proof: &FriProof<
        Challenge,
        FriMmcs,
        Challenger::Witness,
        Vec<BatchMultiOpening<Val, HidingTreeMmcs<Val, H, C, R, N, DIGEST_ELEMS, SALT_ELEMS>>>,
    >,
    challenger: &mut Challenger,
    commitments_with_opening_points: &[CommitmentWithOpeningPoints<
        Challenge,
        <HidingTreeMmcs<Val, H, C, R, N, DIGEST_ELEMS, SALT_ELEMS> as Mmcs<Val>>::Commitment,
        TwoAdicMultiplicativeCoset<Val>,
    >],
) -> Result<Vec<FriQueryPaths<Val, DIGEST_ELEMS>>, FriError<MerkleTreeError, MerkleTreeError>>
where
    Val: TwoAdicField + PrimeField64 + Serialize + DeserializeOwned,
    Challenge: ExtensionField<Val>,
    FriMmcs: Mmcs<
            Challenge,
            MultiProof = (Vec<Vec<Vec<Val>>>, PrunedMerklePaths<Val, DIGEST_ELEMS>),
            Error = MerkleTreeError,
        >,
    Challenger: FieldChallenger<Val> + GrindingChallenger + CanObserve<FriMmcs::Commitment>,
    R: CryptoRng + SeedableRng + Send,
    H: CryptographicHasher<Val, [Val; DIGEST_ELEMS]>
        + CryptographicHasher<Val::Packing, [Val::Packing; DIGEST_ELEMS]>
        + Sync,
    C: PseudoCompressionFunction<[Val; DIGEST_ELEMS], N>
        + PseudoCompressionFunction<[Val::Packing; DIGEST_ELEMS], N>
        + Sync,
    StandardUniform: Distribution<Val>,
    [Val; DIGEST_ELEMS]: Serialize + DeserializeOwned,
{
    let layout = replay_fri_query_layout(
        params,
        input_mmcs,
        proof,
        challenger,
        commitments_with_opening_points,
    )?;

    let mut input_paths_by_batch: Vec<Vec<Vec<[Val; DIGEST_ELEMS]>>> =
        Vec::with_capacity(proof.input_openings.len());
    for (batch, (batch_opening, CommitmentOpening { matrices: mats, .. })) in proof
        .input_openings
        .iter()
        .zip(commitments_with_opening_points)
        .enumerate()
    {
        let (batch_dims, reduced_indices) = input_batch_layout::<Val, Challenge, _, _>(
            params,
            batch,
            layout.log_global_max_height,
            &layout.indices,
            mats,
        )?;
        let (salts, paths) = &batch_opening.opening_proof;
        let salted_dims = salted_dimensions::<SALT_ELEMS>(&batch_dims);
        let salted_values =
            salt_opened_values::<Val, SALT_ELEMS>(&batch_opening.opened_values, salts)
                .map_err(FriError::InputError)?;

        input_paths_by_batch.push(
            input_tree
                .restore_and_recompute_paths(&salted_dims, &reduced_indices, &salted_values, paths)
                .map_err(FriError::InputError)?
                .into_iter()
                .map(|path| path.siblings)
                .collect(),
        );
    }

    let mut commit_phase_paths_by_round: Vec<Vec<Vec<[Val; DIGEST_ELEMS]>>> =
        Vec::with_capacity(layout.log_arities.len());
    let mut log_current_height = layout.log_global_max_height;
    for (round, (opening, &log_arity)) in proof
        .commit_phase_openings
        .iter()
        .zip(&layout.log_arities)
        .enumerate()
    {
        let log_folded_height = log_current_height - log_arity;
        let dims = [commit_phase_dims::<Challenge, Val>(
            log_arity,
            log_folded_height,
        )];
        let opened_values: Vec<Vec<Vec<Val>>> = layout.rows_by_round[round]
            .iter()
            .map(|rows| {
                rows.iter()
                    .map(|row| Challenge::flatten_to_base(row.clone()))
                    .collect()
            })
            .collect();
        let (salts, paths) = &opening.opening_proof;
        let salted_dims = salted_dimensions::<SALT_ELEMS>(&dims);
        let salted_values = salt_opened_values::<Val, SALT_ELEMS>(&opened_values, salts)
            .map_err(FriError::CommitPhaseMmcsError)?;

        commit_phase_paths_by_round.push(
            commit_phase_tree
                .restore_and_recompute_paths(
                    &salted_dims,
                    &layout.group_indices_by_round[round],
                    &salted_values,
                    paths,
                )
                .map_err(FriError::CommitPhaseMmcsError)?
                .into_iter()
                .map(|path| path.siblings)
                .collect(),
        );
        log_current_height = log_folded_height;
    }

    Ok(transpose_query_paths(
        params.num_queries,
        &input_paths_by_batch,
        &commit_phase_paths_by_round,
    ))
}

type HidingTreeMmcs<
    Val,
    H,
    C,
    R,
    const N: usize,
    const DIGEST_ELEMS: usize,
    const SALT_ELEMS: usize,
> = MerkleTreeHidingMmcs<
    <Val as Field>::Packing,
    <Val as Field>::Packing,
    H,
    C,
    R,
    N,
    DIGEST_ELEMS,
    SALT_ELEMS,
>;

fn salted_dimensions<const SALT_ELEMS: usize>(dimensions: &[Dimensions]) -> Vec<Dimensions> {
    dimensions
        .iter()
        .map(|dims| Dimensions {
            width: dims.width + SALT_ELEMS,
            height: dims.height,
        })
        .collect()
}

fn salt_opened_values<Val: Clone, const SALT_ELEMS: usize>(
    opened_values: &[Vec<Vec<Val>>],
    salts: &[Vec<Vec<Val>>],
) -> Result<Vec<Vec<Vec<Val>>>, MerkleTreeError> {
    if salts.len() != opened_values.len() {
        return Err(MerkleTreeError::WrongBatchSize {
            expected: opened_values.len(),
            got: salts.len(),
        });
    }
    opened_values
        .iter()
        .zip(salts)
        .map(|(rows, query_salts)| {
            if query_salts.len() != rows.len() {
                return Err(MerkleTreeError::WrongBatchSize {
                    expected: rows.len(),
                    got: query_salts.len(),
                });
            }
            rows.iter()
                .zip(query_salts)
                .map(|(row, salt)| {
                    if salt.len() != SALT_ELEMS {
                        return Err(MerkleTreeError::WrongBatchSize {
                            expected: SALT_ELEMS,
                            got: salt.len(),
                        });
                    }
                    Ok(row.iter().chain(salt).cloned().collect())
                })
                .collect()
        })
        .collect()
}

fn set_path_private_data<F, EF, const DIGEST_ELEMS: usize>(
    runner: &mut CircuitRunner<'_, EF>,
    op_ids: &[NonPrimitiveOpId],
    op_idx: &mut usize,
    path: &[[F; DIGEST_ELEMS]],
    permutation_config: PermConfig,
    label: &'static str,
) -> Result<(), &'static str>
where
    F: Field,
    EF: ExtensionField<F> + BasedVectorSpace<F>,
{
    for sibling in convert_merkle_proof_to_siblings::<F, EF, DIGEST_ELEMS>(path) {
        if *op_idx >= op_ids.len() {
            return Err("More siblings in proof than op_ids provided");
        }
        runner
            .set_private_data(
                op_ids[*op_idx],
                perm_private_data(permutation_config, sibling),
            )
            .map_err(|_| label)?;
        *op_idx += 1;
    }
    Ok(())
}

pub fn set_fri_mmcs_private_data<F, EF, const DIGEST_ELEMS: usize>(
    runner: &mut CircuitRunner<'_, EF>,
    op_ids: &[NonPrimitiveOpId],
    query_paths: &[FriQueryPaths<F, DIGEST_ELEMS>],
    permutation_config: impl Into<PermConfig>,
) -> Result<(), &'static str>
where
    F: Field,
    EF: ExtensionField<F> + BasedVectorSpace<F>,
{
    let permutation_config: PermConfig = permutation_config.into();
    let mut op_idx = 0;

    for query in query_paths {
        for path in &query.input {
            set_path_private_data::<F, EF, DIGEST_ELEMS>(
                runner,
                op_ids,
                &mut op_idx,
                path,
                permutation_config,
                "Failed to set private data for input batch MMCS",
            )?;
        }

        for path in &query.commit_phase {
            set_path_private_data::<F, EF, DIGEST_ELEMS>(
                runner,
                op_ids,
                &mut op_idx,
                path,
                permutation_config,
                "Failed to set private data for commit-phase MMCS",
            )?;
        }
    }

    if op_idx != op_ids.len() {
        return Err("Fewer siblings in proof than op_ids provided");
    }

    Ok(())
}

struct Arity4PathStep {
    step: usize,
    injection_rows: Vec<usize>,
}

fn arity4_leaf_rows(dimensions: &[Dimensions]) -> Result<Vec<usize>, CircuitBuilderError> {
    let max_height = dimensions.iter().map(|dims| dims.height).max().unwrap_or(0);
    let leaf_height_npt = crate::pcs::mmcs::checked_next_power_of_two(max_height)?;
    dimensions
        .iter()
        .enumerate()
        .filter_map(|(mat_idx, dims)| {
            if dims.height == 0 {
                None
            } else {
                Some(
                    crate::pcs::mmcs::checked_next_power_of_two(dims.height)
                        .map(|height| (mat_idx, height)),
                )
            }
        })
        .filter_map(|result| match result {
            Ok((mat_idx, height)) if height == leaf_height_npt => Some(Ok(mat_idx)),
            Ok(_) => None,
            Err(error) => Some(Err(error)),
        })
        .collect()
}

fn arity4_path_schedule(
    dimensions: &[Dimensions],
    num_roots: usize,
) -> Result<Vec<Arity4PathStep>, CircuitBuilderError> {
    let mut steps = Vec::new();
    crate::pcs::mmcs::visit_arity4_path(
        dimensions.iter().map(|dims| dims.height),
        num_roots,
        |geometry| {
            let injection_rows = geometry.injection_height.map_or_else(Vec::new, |height| {
                dimensions
                    .iter()
                    .enumerate()
                    .filter_map(|(mat_idx, dims)| (dims.height == height).then_some(mat_idx))
                    .collect()
            });
            let step = geometry.step;
            steps.push(Arity4PathStep {
                step,
                injection_rows,
            });
        },
    )?;
    Ok(steps)
}

fn add_arity4_leaf_digest_from_base<F, EF>(
    circuit: &mut CircuitBuilder<EF>,
    permutation_config: PermConfig,
    leaf_data: &[Target],
    merkle_seed: bool,
) -> Result<Vec<Target>, CircuitBuilderError>
where
    F: Field + PrimeField64,
    EF: ExtensionField<F>,
{
    let digest = add_hash_base_coeffs_overwrite::<F, EF>(
        circuit,
        &permutation_config,
        leaf_data,
        true,
        BaseCoeffPacking::Alu,
        merkle_seed,
    )?;
    Ok(digest
        .into_iter()
        .take(permutation_config.capacity_ext())
        .collect())
}

fn add_hash_packed_ext_leaf<F, EF>(
    circuit: &mut CircuitBuilder<EF>,
    permutation_config: PermConfig,
    leaf_data: &[Target],
    merkle_seed: bool,
) -> Result<Vec<Target>, CircuitBuilderError>
where
    F: Field + PrimeField64,
    EF: ExtensionField<F>,
{
    let digest = add_hash_extension_elements::<F, EF>(
        circuit,
        &permutation_config,
        leaf_data,
        true,
        merkle_seed,
    )?;
    Ok(digest
        .into_iter()
        .take(permutation_config.capacity_ext())
        .collect())
}

fn add_arity4_compression_row<EF: Field>(
    circuit: &mut CircuitBuilder<EF>,
    permutation_config: PermConfig,
    direction: [Target; 2],
    step: usize,
    injected_digest: Option<&[Target]>,
    is_final: bool,
    zero: Target,
) -> Result<(NonPrimitiveOpId, Vec<Option<Target>>), CircuitBuilderError> {
    let width_ext = permutation_config.width_ext();
    let rate_ext = permutation_config.rate_ext();
    let capacity_ext = permutation_config.capacity_ext();
    let mut inputs = vec![None; width_ext];

    let active_chunks = if injected_digest.is_some() { 2 } else { step };

    if let Some(digest) = injected_digest {
        if digest.len() != capacity_ext {
            return Err(CircuitBuilderError::Poseidon2ConfigMismatch {
                expected: format!("injected digest len == capacity_ext ({capacity_ext})"),
                got: format!("injected digest len = {}", digest.len()),
            });
        }
        let base = capacity_ext;
        for (j, &target) in digest.iter().enumerate() {
            inputs[base + j] = Some(target);
        }
    }

    for chunk_k in active_chunks..4 {
        let base = chunk_k * capacity_ext;
        for slot in inputs[base..base + capacity_ext].iter_mut() {
            *slot = Some(zero);
        }
    }

    circuit.add_perm(
        permutation_config,
        &PermCall {
            new_start: false,
            merkle_path: true,
            mmcs_bit: Some(direction[0]),
            mmcs_bit2: Some(direction[1]),
            inputs,
            out_ctl: vec![is_final; rate_ext],
            return_all_outputs: false,
            mmcs_index_sum: None,
        },
    )
}

#[allow(clippy::type_complexity)]
fn arity4_prepare<EF: Field>(
    circuit: &mut CircuitBuilder<EF>,
    permutation_config: PermConfig,
    commitment_cap: &[Vec<Target>],
    dimensions: &[Dimensions],
    index_bits: &[Target],
) -> Result<(Vec<Target>, Vec<Arity4PathStep>, Vec<usize>), CircuitBuilderError> {
    if !permutation_config.is_arity4_shape() {
        return Err(CircuitBuilderError::Poseidon2ConfigMismatch {
            expected: "width_ext == 4 * capacity_ext for 4-to-1 MMCS".into(),
            got: format!(
                "width_ext = {}, capacity_ext = {}",
                permutation_config.width_ext(),
                permutation_config.capacity_ext()
            ),
        });
    }

    let cap_log2 = validate_commitment_cap_len(commitment_cap)?;

    let num_roots = commitment_cap.len();

    let leaf_rows = arity4_leaf_rows(dimensions)?;
    let schedule = arity4_path_schedule(dimensions, num_roots)?;

    let path_bit_total = schedule.iter().try_fold(0usize, |total, step| {
        total
            .checked_add(if step.step == 4 { 2 } else { 1 })
            .ok_or_else(|| CircuitBuilderError::InvalidMerkleCap {
                details: "arity-4 path bit count overflows".into(),
            })
    })?;
    let cap_index_bits: Vec<Target> = if cap_log2 == 0 {
        Vec::new()
    } else {
        let zero = circuit.define_const(EF::ZERO);
        (0..cap_log2)
            .map(|i| {
                path_bit_total
                    .checked_add(i)
                    .and_then(|index| index_bits.get(index).copied())
                    .unwrap_or(zero)
            })
            .collect()
    };

    let selected_root = select_cap_entry(circuit, commitment_cap, &cap_index_bits);

    Ok((selected_root, schedule, leaf_rows))
}

fn arity4_emit_path<EF: Field>(
    circuit: &mut CircuitBuilder<EF>,
    permutation_config: PermConfig,
    schedule: &[Arity4PathStep],
    index_bits: &[Target],
    leaf_digest: &[Target],
    injected_digests: &[Vec<Target>],
    selected_root: &[Target],
) -> Result<Vec<NonPrimitiveOpId>, CircuitBuilderError> {
    let mut output: Vec<Option<Target>> = leaf_digest.iter().copied().map(Some).collect();
    let mut op_ids = Vec::new();

    let zero = circuit.define_const(EF::ZERO);
    let mut bits_consumed = 0usize;
    let mut injected_digest_idx = 0usize;
    let n_steps = schedule.len();

    for (i, path_step) in schedule.iter().enumerate() {
        let step = path_step.step;
        let step_bits = if step == 4 { 2 } else { 1 };
        let direction = if step == 4 {
            [
                index_bits.get(bits_consumed).copied().unwrap_or(zero),
                index_bits.get(bits_consumed + 1).copied().unwrap_or(zero),
            ]
        } else {
            [index_bits.get(bits_consumed).copied().unwrap_or(zero), zero]
        };
        bits_consumed += step_bits;

        let has_injection = !path_step.injection_rows.is_empty();
        let is_last_step = i == n_steps - 1;

        let (op_id, maybe_output) = add_arity4_compression_row(
            circuit,
            permutation_config,
            direction,
            step,
            None,
            is_last_step && !has_injection,
            zero,
        )?;
        for _ in 0..(step - 1) {
            op_ids.push(op_id);
        }
        output = maybe_output;

        if has_injection {
            let injected_digest = &injected_digests[injected_digest_idx];
            injected_digest_idx += 1;
            let (_, maybe_output) = add_arity4_compression_row(
                circuit,
                permutation_config,
                [zero, zero],
                step,
                Some(injected_digest),
                is_last_step,
                zero,
            )?;
            output = maybe_output;
        }
    }

    let output = output
        .into_iter()
        .take(permutation_config.capacity_ext())
        .map(|x| x.ok_or(CircuitBuilderError::MissingOutput))
        .collect::<Result<Vec<_>, _>>()?;
    for (o, r) in output.iter().zip(selected_root.iter()) {
        circuit.connect(*o, *r);
    }
    Ok(op_ids)
}

pub fn verify_batch_circuit_arity4<F, EF>(
    circuit: &mut CircuitBuilder<EF>,
    permutation_config: impl Into<PermConfig>,
    commitment_cap: &[Vec<Target>],
    dimensions: &[Dimensions],
    index_bits: &[Target],
    opened_base_coeffs: &[Vec<Target>],
) -> Result<Vec<NonPrimitiveOpId>, CircuitBuilderError>
where
    F: Field + TwoAdicField + PrimeField64,
    EF: ExtensionField<F>,
{
    let permutation_config: PermConfig = permutation_config.into();
    if dimensions.len() != opened_base_coeffs.len() {
        return Err(CircuitBuilderError::WrongBatchSize {
            expected: dimensions.len(),
            got: opened_base_coeffs.len(),
        });
    }

    let (selected_root, schedule, leaf_rows) = arity4_prepare::<EF>(
        circuit,
        permutation_config,
        commitment_cap,
        dimensions,
        index_bits,
    )?;

    let mut injected_digests = Vec::new();
    for step in &schedule {
        if step.injection_rows.is_empty() {
            continue;
        }
        let injected_leaf_data: Vec<Target> = step
            .injection_rows
            .iter()
            .flat_map(|&mat_idx| opened_base_coeffs[mat_idx].iter().copied())
            .collect();
        injected_digests.push(add_arity4_leaf_digest_from_base::<F, EF>(
            circuit,
            permutation_config,
            &injected_leaf_data,
            false,
        )?);
    }

    let leaf_data: Vec<Target> = leaf_rows
        .iter()
        .flat_map(|&mat_idx| opened_base_coeffs[mat_idx].iter().copied())
        .collect();
    let leaf_digest =
        add_arity4_leaf_digest_from_base::<F, EF>(circuit, permutation_config, &leaf_data, true)?;

    arity4_emit_path::<EF>(
        circuit,
        permutation_config,
        &schedule,
        index_bits,
        &leaf_digest,
        &injected_digests,
        &selected_root,
    )
}

pub fn verify_batch_circuit_from_extension_opened_arity4<F, EF>(
    circuit: &mut CircuitBuilder<EF>,
    permutation_config: impl Into<PermConfig>,
    commitment_cap: &[Vec<Target>],
    dimensions: &[Dimensions],
    index_bits: &[Target],
    opened_extension_values: &[Vec<Target>],
) -> Result<Vec<NonPrimitiveOpId>, CircuitBuilderError>
where
    F: Field + TwoAdicField + PrimeField64,
    EF: ExtensionField<F>,
{
    let permutation_config: PermConfig = permutation_config.into();
    if dimensions.len() != opened_extension_values.len() {
        return Err(CircuitBuilderError::WrongBatchSize {
            expected: dimensions.len(),
            got: opened_extension_values.len(),
        });
    }

    let (selected_root, schedule, leaf_rows) = arity4_prepare::<EF>(
        circuit,
        permutation_config,
        commitment_cap,
        dimensions,
        index_bits,
    )?;

    let ext_degree = <EF as BasedVectorSpace<F>>::DIMENSION;
    let flatten_to_base = permutation_config.d() == 1 && ext_degree > 1;

    let leaf_digest_from_ext = |circuit: &mut CircuitBuilder<EF>,
                                mats: &[usize],
                                merkle_seed: bool|
     -> Result<Vec<Target>, CircuitBuilderError> {
        if flatten_to_base {
            let mut data = Vec::new();
            let mut element_idx: usize = 0;
            for &mat_idx in mats {
                for &t in &opened_extension_values[mat_idx] {
                    let coeffs = if EF::DIMENSION == 5 && element_idx.is_multiple_of(2) {
                        circuit.decompose_ext_to_base_coeffs_fresh_via_alu::<F>(t)?
                    } else {
                        let saved = circuit.set_decompose_skip_select_provenance(true);
                        let coeffs = circuit.decompose_ext_to_base_coeffs::<F>(t);
                        circuit.set_decompose_skip_select_provenance(saved);
                        coeffs?
                    };
                    data.extend(coeffs);
                    element_idx += 1;
                }
            }
            add_arity4_leaf_digest_from_base::<F, EF>(
                circuit,
                permutation_config,
                &data,
                merkle_seed,
            )
        } else {
            let data: Vec<Target> = mats
                .iter()
                .flat_map(|&mat_idx| opened_extension_values[mat_idx].iter().copied())
                .collect();
            add_hash_packed_ext_leaf::<F, EF>(circuit, permutation_config, &data, merkle_seed)
        }
    };

    let mut injected_digests = Vec::new();
    for step in &schedule {
        if step.injection_rows.is_empty() {
            continue;
        }
        injected_digests.push(leaf_digest_from_ext(circuit, &step.injection_rows, false)?);
    }

    let leaf_digest = leaf_digest_from_ext(circuit, &leaf_rows, true)?;

    arity4_emit_path::<EF>(
        circuit,
        permutation_config,
        &schedule,
        index_bits,
        &leaf_digest,
        &injected_digests,
        &selected_root,
    )
}

fn set_arity4_opening_private_data<F, EF, const DIGEST_ELEMS: usize>(
    runner: &mut CircuitRunner<'_, EF>,
    op_ids: &[NonPrimitiveOpId],
    op_idx: &mut usize,
    opening_proof: &[[F; DIGEST_ELEMS]],
    permutation_config: PermConfig,
) -> Result<(), &'static str>
where
    F: Field,
    EF: ExtensionField<F> + BasedVectorSpace<F>,
{
    let siblings = convert_merkle_proof_to_siblings::<F, EF, DIGEST_ELEMS>(opening_proof);
    let sibling_limb_len = siblings.first().map(Vec::len).unwrap_or(0);
    let mut sibling_idx = 0usize;
    while sibling_idx < siblings.len() {
        if *op_idx >= op_ids.len() {
            return Err("More arity-4 siblings in proof than op_ids provided");
        }
        let op_id = op_ids[*op_idx];
        let mut flat = Vec::new();
        let mut siblings_for_op = 0usize;
        while *op_idx < op_ids.len() && op_ids[*op_idx] == op_id {
            if sibling_idx >= siblings.len() {
                return Err("Arity-4 op_id group has more entries than proof siblings");
            }
            flat.extend(siblings[sibling_idx].iter().copied());
            sibling_idx += 1;
            *op_idx += 1;
            siblings_for_op += 1;
            if siblings_for_op > 3 {
                return Err("Arity-4 op_id group cannot contain more than 3 siblings");
            }
        }
        for _ in siblings_for_op..3 {
            flat.extend(vec![EF::ZERO; sibling_limb_len]);
        }
        runner
            .set_private_data(op_id, perm_private_data(permutation_config, flat))
            .map_err(|_| "Failed to set private data for arity-4 MMCS")?;
    }

    Ok(())
}

pub fn set_fri_mmcs_private_data_arity4<F, EF, const DIGEST_ELEMS: usize>(
    runner: &mut CircuitRunner<'_, EF>,
    op_ids: &[NonPrimitiveOpId],
    query_paths: &[FriQueryPaths<F, DIGEST_ELEMS>],
    permutation_config: impl Into<PermConfig>,
) -> Result<(), &'static str>
where
    F: Field,
    EF: ExtensionField<F> + BasedVectorSpace<F>,
{
    let permutation_config: PermConfig = permutation_config.into();
    let mut op_idx = 0;

    for query in query_paths {
        for path in &query.input {
            set_arity4_opening_private_data::<F, EF, DIGEST_ELEMS>(
                runner,
                op_ids,
                &mut op_idx,
                path,
                permutation_config,
            )?;
        }

        for path in &query.commit_phase {
            set_arity4_opening_private_data::<F, EF, DIGEST_ELEMS>(
                runner,
                op_ids,
                &mut op_idx,
                path,
                permutation_config,
            )?;
        }
    }

    if op_idx != op_ids.len() {
        return Err("Fewer arity-4 siblings in proof than op_ids provided");
    }

    Ok(())
}

pub fn restore_whir_query_paths<P, PW, EF, H, C, const N: usize, const DIGEST_ELEMS: usize>(
    mmcs: &MerkleTreeMmcs<P, PW, H, C, N, DIGEST_ELEMS>,
    openings: &QueryOpenings<P::Value, EF, PrunedMerklePaths<PW::Value, DIGEST_ELEMS>>,
    dimensions: &[Dimensions],
    indices: &[usize],
) -> Result<Vec<Vec<[PW::Value; DIGEST_ELEMS]>>, MerkleTreeError>
where
    P: PackedValue,
    P::Value: Field,
    PW: PackedValue,
    PW::Value: Eq + Clone,
    EF: ExtensionField<P::Value>,
    H: CryptographicHasher<P::Value, [PW::Value; DIGEST_ELEMS]>
        + CryptographicHasher<P, [PW; DIGEST_ELEMS]>
        + Sync,
    C: PseudoCompressionFunction<[PW::Value; DIGEST_ELEMS], N>
        + PseudoCompressionFunction<[PW; DIGEST_ELEMS], N>
        + Sync,
    [PW::Value; DIGEST_ELEMS]: Serialize + for<'de> Deserialize<'de>,
{
    let (opened_values, proof, width_scale) = match openings {
        QueryOpenings::Base(opening) => (
            opening
                .rows
                .iter()
                .map(|row| vec![row.clone()])
                .collect::<Vec<_>>(),
            &opening.proof,
            1,
        ),
        QueryOpenings::Extension(opening) => (
            opening
                .rows
                .iter()
                .map(|row| vec![EF::flatten_to_base(row.clone())])
                .collect::<Vec<_>>(),
            &opening.proof,
            EF::DIMENSION,
        ),
    };

    let base_dimensions: Vec<Dimensions> = dimensions
        .iter()
        .map(|dims| Dimensions {
            width: dims.width * width_scale,
            height: dims.height,
        })
        .collect();

    Ok(mmcs
        .restore_and_recompute_paths(&base_dimensions, indices, &opened_values, proof)?
        .into_iter()
        .map(|path| path.siblings)
        .collect())
}

pub fn set_whir_mmcs_private_data<F, EF, const DIGEST_ELEMS: usize>(
    runner: &mut CircuitRunner<'_, EF>,
    op_ids: &[NonPrimitiveOpId],
    round_paths: &[Vec<Vec<[F; DIGEST_ELEMS]>>],
    final_paths: &[Vec<[F; DIGEST_ELEMS]>],
    permutation_config: impl Into<PermConfig>,
) -> Result<(), &'static str>
where
    F: Field,
    EF: ExtensionField<F> + BasedVectorSpace<F>,
{
    let permutation_config: PermConfig = permutation_config.into();
    let mut op_idx = 0;

    for round in round_paths {
        for path in round {
            set_path_private_data::<F, EF, DIGEST_ELEMS>(
                runner,
                op_ids,
                &mut op_idx,
                path,
                permutation_config,
                "More siblings than op_ids (round query)",
            )?;
        }
    }

    for path in final_paths {
        set_path_private_data::<F, EF, DIGEST_ELEMS>(
            runner,
            op_ids,
            &mut op_idx,
            path,
            permutation_config,
            "More siblings than op_ids (final query)",
        )?;
    }

    if op_idx != op_ids.len() {
        return Err("Fewer siblings in proof than op_ids provided");
    }

    Ok(())
}
