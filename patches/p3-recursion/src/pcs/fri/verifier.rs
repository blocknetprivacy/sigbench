#![allow(clippy::too_many_arguments)]
#![allow(clippy::option_if_let_else)]

use alloc::collections::btree_map::BTreeMap;
use alloc::string::ToString;
use alloc::vec::Vec;
use alloc::{format, vec};
use core::iter;

use hashbrown::HashMap;
use p3_circuit::ops::PermConfig;
use p3_circuit::{CircuitBuilder, NonPrimitiveOpId};
use p3_field::coset::TwoAdicMultiplicativeCoset;
use p3_field::{BasedVectorSpace, ExtensionField, Field, PrimeField64, TwoAdicField};
use p3_matrix::Dimensions;
use p3_util::zip_eq::zip_eq;

use super::{FriProofTargets, InputProofTargets};
use crate::Target;
use crate::pcs::{
    MmcsProofTargets, verify_batch_circuit, verify_batch_circuit_arity4,
    verify_batch_circuit_from_extension_opened, verify_batch_circuit_from_extension_opened_arity4,
};
use crate::traits::{ComsWithOpeningsTargets, Recursive, RecursiveExtensionMmcs, RecursiveMmcs};
use crate::verifier::{ObservableCommitment, VerificationError};

pub(crate) fn pack_lifted_to_ext<F, EF>(
    builder: &mut CircuitBuilder<EF>,
    lifted: &[Target],
) -> Vec<Target>
where
    F: Field,
    EF: ExtensionField<F> + BasedVectorSpace<F>,
{
    if lifted.is_empty() {
        return Vec::new();
    }

    let d = EF::DIMENSION;

    let basis: Vec<EF> = (0..d)
        .map(|i| {
            let mut coeffs = vec![F::ZERO; d];
            coeffs[i] = F::ONE;
            EF::from_basis_coefficients_slice(&coeffs).expect("valid basis element")
        })
        .collect();

    let basis_consts: Vec<Target> = basis.iter().map(|b| builder.define_const(*b)).collect();

    let zero = builder.define_const(EF::ZERO);

    lifted
        .chunks(d)
        .map(|chunk| {
            let mut packed = chunk[0];
            for j in 1..d {
                let val = if j < chunk.len() { chunk[j] } else { zero };
                packed = builder.mul_add(val, basis_consts[j], packed);
            }
            packed
        })
        .collect()
}

pub(crate) fn commitment_cap_rows_from_lifted<F, EF>(
    builder: &mut CircuitBuilder<EF>,
    perm_config: PermConfig,
    lifted: &[Target],
) -> Vec<Vec<Target>>
where
    F: Field,
    EF: ExtensionField<F> + BasedVectorSpace<F>,
{
    let chunk_ext = if perm_config.is_arity4_shape() {
        perm_config.capacity_ext()
    } else {
        perm_config.rate_ext()
    };
    if perm_config.d() == 1 && EF::DIMENSION > 1 {
        debug_assert_eq!(
            lifted.len() % chunk_ext,
            0,
            "lifted cap length should be a multiple of the digest size"
        );
        lifted.chunks(chunk_ext).map(|c| c.to_vec()).collect()
    } else {
        let packed = pack_lifted_to_ext::<F, EF>(builder, lifted);
        packed.chunks(chunk_ext).map(|c| c.to_vec()).collect()
    }
}

fn one_hot_from_two_bits<EF: Field>(
    builder: &mut CircuitBuilder<EF>,
    b0: Target,
    b1: Target,
) -> [Target; 4] {
    let one = builder.define_const(EF::ONE);
    let nb0 = builder.sub(one, b0);
    let nb1 = builder.sub(one, b1);

    let h0 = builder.mul(nb0, nb1);
    let h1 = builder.mul(b0, nb1);
    let h2 = builder.mul(nb0, b1);
    let h3 = builder.mul(b0, b1);

    [h0, h1, h2, h3]
}

fn one_hot_from_three_bits<EF: Field>(
    builder: &mut CircuitBuilder<EF>,
    b0: Target,
    b1: Target,
    b2: Target,
) -> [Target; 8] {
    let one = builder.define_const(EF::ONE);
    let nb0 = builder.sub(one, b0);
    let nb1 = builder.sub(one, b1);
    let nb2 = builder.sub(one, b2);

    let t00 = builder.mul(nb1, nb2);
    let t01 = builder.mul(nb1, b2);
    let t10 = builder.mul(b1, nb2);
    let t11 = builder.mul(b1, b2);

    let h0 = builder.mul(nb0, t00);
    let h1 = builder.mul(b0, t00);
    let h2 = builder.mul(nb0, t10);
    let h3 = builder.mul(b0, t10);
    let h4 = builder.mul(nb0, t01);
    let h5 = builder.mul(b0, t01);
    let h6 = builder.mul(nb0, t11);
    let h7 = builder.mul(b0, t11);

    [h0, h1, h2, h3, h4, h5, h6, h7]
}

#[unroll::unroll_for_loops]
fn one_hot_from_four_bits<EF: Field>(
    builder: &mut CircuitBuilder<EF>,
    bits: &[Target],
) -> Vec<Target> {
    debug_assert_eq!(bits.len(), 4);
    let low = one_hot_from_two_bits(builder, bits[0], bits[1]);
    let high = one_hot_from_two_bits(builder, bits[2], bits[3]);

    let mut result = Vec::with_capacity(16);
    for j in 0..16 {
        let low_idx = j & 3;
        let high_idx = j >> 2;
        let val = builder.mul(low[low_idx], high[high_idx]);
        result.push(val);
    }
    result
}

fn one_hot_from_bits<EF: Field>(builder: &mut CircuitBuilder<EF>, bits: &[Target]) -> Vec<Target> {
    let log_arity = bits.len();
    let arity = 1usize << log_arity;

    match log_arity {
        0 => {
            vec![builder.define_const(EF::ONE)]
        }
        1 => {
            let one = builder.define_const(EF::ONE);
            let b0 = bits[0];
            let nb0 = builder.sub(one, b0);
            vec![nb0, b0]
        }
        2 => {
            let [h0, h1, h2, h3] = one_hot_from_two_bits(builder, bits[0], bits[1]);
            vec![h0, h1, h2, h3]
        }
        3 => {
            let [h0, h1, h2, h3, h4, h5, h6, h7] =
                one_hot_from_three_bits(builder, bits[0], bits[1], bits[2]);
            vec![h0, h1, h2, h3, h4, h5, h6, h7]
        }
        4 => one_hot_from_four_bits(builder, bits),
        _ => {
            let one = builder.define_const(EF::ONE);
            let not_bits: Vec<Target> = bits.iter().map(|&bit| builder.sub(one, bit)).collect();

            let mut one_hot = Vec::with_capacity(arity);
            for j in 0..arity {
                let mut product = one;
                for (k, &bit) in bits.iter().enumerate() {
                    if (j >> k) & 1 == 1 {
                        product = builder.mul(product, bit);
                    } else {
                        product = builder.mul(product, not_bits[k]);
                    }
                }
                one_hot.push(product);
            }
            one_hot
        }
    }
}

fn reconstruct_evals<EF: Field>(
    builder: &mut CircuitBuilder<EF>,
    folded: Target,
    siblings: &[Target],
    index_in_group_bits: &[Target],
) -> Vec<Target> {
    builder.push_scope("fri_reconstruct_evals");
    let log_arity = index_in_group_bits.len();
    let arity = 1usize << log_arity;
    debug_assert_eq!(siblings.len(), arity - 1);

    let evals = match log_arity {
        0 => vec![folded],

        1 => {
            let b0 = index_in_group_bits[0];
            let s0 = siblings[0];

            let e0 = builder.select(b0, s0, folded);
            let e1 = builder.select(b0, folded, s0);

            vec![e0, e1]
        }

        2 => {
            let b0 = index_in_group_bits[0];
            let b1 = index_in_group_bits[1];

            let s0 = siblings[0];
            let s1 = siblings[1];
            let s2 = siblings[2];

            let [h0, h1, h2, h3] = one_hot_from_two_bits(builder, b0, b1);

            let diff_f_s0 = builder.sub(folded, s0);
            let e0 = builder.mul_add(h0, diff_f_s0, s0);

            let h2_plus_h3 = builder.add(h2, h3);
            let s1_term_for_e1 = builder.mul(s1, h2_plus_h3);
            let f_h1 = builder.mul(folded, h1);
            let tmp_e1 = builder.mul_add(s0, h0, f_h1);
            let e1 = builder.add(tmp_e1, s1_term_for_e1);

            let h0_plus_h1 = builder.add(h0, h1);
            let s1_term_for_e2 = builder.mul(s1, h0_plus_h1);
            let tmp_e2 = builder.mul_add(folded, h2, s1_term_for_e2);
            let e2 = builder.mul_add(s2, h3, tmp_e2);

            let diff_f_s2 = builder.sub(folded, s2);
            let e3 = builder.mul_add(h3, diff_f_s2, s2);

            vec![e0, e1, e2, e3]
        }

        3 => {
            let b0 = index_in_group_bits[0];
            let b1 = index_in_group_bits[1];
            let b2 = index_in_group_bits[2];

            let s0 = siblings[0];
            let s1 = siblings[1];
            let s2 = siblings[2];
            let s3 = siblings[3];
            let s4 = siblings[4];
            let s5 = siblings[5];
            let s6 = siblings[6];

            let [h0, h1, h2, h3, h4, h5, h6, h7] = one_hot_from_three_bits(builder, b0, b1, b2);

            let p1 = h0;
            let p2 = builder.add(p1, h1);
            let p3 = builder.add(p2, h2);
            let p4 = builder.add(p3, h3);
            let p5 = builder.add(p4, h4);
            let p6 = builder.add(p5, h5);
            let p7 = builder.add(p6, h6);

            let su6 = h7;
            let su5 = builder.add(h6, su6);
            let su4 = builder.add(h5, su5);
            let su3 = builder.add(h4, su4);
            let su2 = builder.add(h3, su3);
            let su1 = builder.add(h2, su2);
            let su0 = builder.add(h1, su1);

            let e0_sib = builder.mul(s0, su0);
            let e0 = builder.mul_add(h0, folded, e0_sib);

            let e1_lo = builder.mul(s0, p1);
            let e1_sib = builder.mul_add(s1, su1, e1_lo);
            let e1 = builder.mul_add(h1, folded, e1_sib);

            let e2_lo = builder.mul(s1, p2);
            let e2_sib = builder.mul_add(s2, su2, e2_lo);
            let e2 = builder.mul_add(h2, folded, e2_sib);

            let e3_lo = builder.mul(s2, p3);
            let e3_sib = builder.mul_add(s3, su3, e3_lo);
            let e3 = builder.mul_add(h3, folded, e3_sib);

            let e4_lo = builder.mul(s3, p4);
            let e4_sib = builder.mul_add(s4, su4, e4_lo);
            let e4 = builder.mul_add(h4, folded, e4_sib);

            let e5_lo = builder.mul(s4, p5);
            let e5_sib = builder.mul_add(s5, su5, e5_lo);
            let e5 = builder.mul_add(h5, folded, e5_sib);

            let e6_lo = builder.mul(s5, p6);
            let e6_sib = builder.mul_add(s6, su6, e6_lo);
            let e6 = builder.mul_add(h6, folded, e6_sib);

            let e7_sib = builder.mul(s6, p7);
            let e7 = builder.mul_add(h7, folded, e7_sib);

            vec![e0, e1, e2, e3, e4, e5, e6, e7]
        }

        _ => {
            let one_hot = one_hot_from_bits(builder, index_in_group_bits);

            let mut cum = Vec::with_capacity(arity);
            cum.push(one_hot[0]);
            for j in 1..arity {
                cum.push(builder.add(cum[j - 1], one_hot[j]));
            }

            let mut evals = Vec::with_capacity(arity);
            for j in 0..arity {
                let left_idx = if j > 0 { j - 1 } else { 0 };
                let right_idx = if j < arity - 1 { j } else { arity - 2 };
                let actual_sibling =
                    builder.select(cum[j], siblings[left_idx], siblings[right_idx]);
                let eval_j = builder.select(one_hot[j], folded, actual_sibling);
                evals.push(eval_j);
            }
            evals
        }
    };

    builder.pop_scope();
    evals
}

fn precompute_subgroup_starts<F, EF>(
    builder: &mut CircuitBuilder<EF>,
    index_bits: &[Target],
    log_max_height: usize,
    log_arities: &[usize],
    cumulative_bits: &[usize],
) -> Vec<Target>
where
    F: Field + TwoAdicField,
    EF: ExtensionField<F>,
{
    let num_phases = log_arities.len();
    let one = builder.define_const(EF::ONE);

    let log_folded_heights: Vec<usize> = (0..num_phases)
        .map(|i| log_max_height - cumulative_bits[i + 1])
        .collect();

    let max_chain_len = log_folded_heights[0];

    if max_chain_len == 0 {
        builder.pop_scope();
        return vec![one; num_phases];
    }

    let g_0 = F::two_adic_generator(log_max_height);
    let powers_of_g: Vec<_> = iter::successors(Some(g_0), |&prev| Some(prev.square()))
        .take(max_chain_len)
        .map(|p| builder.define_const(EF::from(p)))
        .collect();

    let parent_offset_0 = cumulative_bits[1];

    let mut capture_at: BTreeMap<usize, Vec<usize>> = BTreeMap::new();
    for (i, &lf) in log_folded_heights
        .iter()
        .enumerate()
        .take(num_phases)
        .skip(1)
    {
        if lf > 0 {
            capture_at.entry(lf).or_default().push(i);
        }
    }

    let mut g_pow = one;
    let mut result = vec![one; num_phases];

    for j in 0..max_chain_len {
        let bit = index_bits[parent_offset_0 + max_chain_len - 1 - j];
        let multiplier = builder.select(bit, powers_of_g[j], one);
        g_pow = builder.mul(g_pow, multiplier);

        let bits_done = j + 1;
        if let Some(phase_indices) = capture_at.get(&bits_done) {
            for &phase_i in phase_indices {
                result[phase_i] = builder.exp_power_of_2(g_pow, cumulative_bits[phase_i]);
            }
        }
    }

    result[0] = g_pow;

    result
}

fn precompute_beta_powers_per_phase<EF: Field>(
    builder: &mut CircuitBuilder<EF>,
    betas: &[Target],
    log_arities: &[usize],
) -> Vec<Target> {
    builder.push_scope("fri_precompute_betas");

    debug_assert_eq!(betas.len(), log_arities.len());
    let result = betas
        .iter()
        .zip(log_arities.iter())
        .map(|(&beta, &log_arity)| builder.exp_power_of_2(beta, log_arity))
        .collect();

    builder.pop_scope();
    result
}

fn fold_one_phase<F, EF>(
    builder: &mut CircuitBuilder<EF>,
    folded: Target,
    siblings: &[Target],
    beta: Target,
    index_bits: &[Target],
    bits_consumed: usize,
    log_arity: usize,
    roll_in: Option<Target>,
    precomputed_beta_pow: Option<Target>,
    precomputed_evals: Option<&[Target]>,
    precomputed_subgroup_start: Target,
) -> Target
where
    F: Field + TwoAdicField,
    EF: ExtensionField<F>,
{
    builder.push_scope("fri_fold_one_phase");

    let index_in_group_bits = &index_bits[bits_consumed..bits_consumed + log_arity];

    if log_arity == 1 {
        let sibling = siblings[0];
        let neg_one = builder.define_const(EF::NEG_ONE);
        let two = builder.define_const(EF::TWO);
        let half = builder.define_const(EF::ONE.halve());
        let inv = builder.div(half, precomputed_subgroup_start);
        let d = builder.sub(sibling, folded);
        let sign = builder.mul_add(two, index_bits[bits_consumed], neg_one);
        let beta_inv = builder.mul(beta, inv);
        let weight = builder.mul_add(sign, beta_inv, half);
        let mut new_folded = builder.mul_add(weight, d, folded);

        if let Some(ro) = roll_in {
            let beta_sq = precomputed_beta_pow.unwrap_or_else(|| builder.mul(beta, beta));
            new_folded = builder.mul_add(beta_sq, ro, new_folded);
        }
        builder.pop_scope();
        return new_folded;
    }

    let owned_evals;
    let evals: &[Target] = match precomputed_evals {
        Some(e) => e,
        None => {
            owned_evals = reconstruct_evals(builder, folded, siblings, index_in_group_bits);
            &owned_evals
        }
    };

    let half_target = builder.define_const(EF::ONE.halve());
    let inverse_start = builder.div(half_target, precomputed_subgroup_start);
    let mut half_normalized_beta = builder.mul(beta, inverse_start);
    let inverse_omega = F::two_adic_generator(log_arity).inverse();
    let coefficients: Vec<_> = (1..evals.len() / 2)
        .map(|j| {
            let exponent = p3_util::reverse_bits_len(2 * j, log_arity);
            builder.define_const(-EF::from(inverse_omega.exp_u64(exponent as u64)))
        })
        .collect();
    let mut data = evals.to_vec();
    for level in 0..log_arity {
        let pairs = data.len() / 2;
        for j in 0..pairs {
            let weight = if j == 0 {
                builder.sub(half_target, half_normalized_beta)
            } else {
                builder.mul_add(half_normalized_beta, coefficients[j - 1], half_target)
            };
            let difference = builder.sub(data[2 * j + 1], data[2 * j]);
            data[j] = builder.mul_add(weight, difference, data[2 * j]);
        }
        data.truncate(pairs);
        if level + 1 < log_arity {
            let square = builder.mul(half_normalized_beta, half_normalized_beta);
            half_normalized_beta = builder.add(square, square);
        }
    }
    let mut new_folded = data[0];

    if let Some(ro) = roll_in {
        let beta_pow =
            precomputed_beta_pow.unwrap_or_else(|| builder.exp_power_of_2(beta, log_arity));
        new_folded = builder.mul_add(beta_pow, ro, new_folded);
    }

    builder.pop_scope();
    new_folded
}

fn evaluate_polynomial<EF: Field>(
    builder: &mut CircuitBuilder<EF>,
    coefficients: &[Target],
    point: Target,
) -> Target {
    builder.push_scope("evaluate_polynomial");

    assert!(
        !coefficients.is_empty(),
        "we should have at least a constant polynomial"
    );
    if coefficients.len() == 1 {
        return coefficients[0];
    }

    let zero = builder.define_const(EF::ZERO);
    let mut result = zero;
    for &coeff in coefficients.iter().rev() {
        result = builder.horner_acc_step(result, point, coeff, zero);
    }

    builder.pop_scope();
    result
}

fn precompute_two_adic_powers<F, EF>(
    builder: &mut CircuitBuilder<EF>,
    log_height: usize,
) -> Vec<Target>
where
    F: Field + TwoAdicField,
    EF: ExtensionField<F>,
{
    builder.push_scope("fri_precompute_two_adic_powers");

    let g = F::two_adic_generator(log_height);
    let result = iter::successors(Some(g), |&prev| Some(prev.square()))
        .take(log_height)
        .map(|p| builder.define_const(EF::from(p)))
        .collect();

    builder.pop_scope();
    result
}

fn compute_final_query_point<F, EF>(
    builder: &mut CircuitBuilder<EF>,
    index_bits: &[Target],
    log_max_height: usize,
    total_bits_consumed: usize,
    powers_of_g: &[Target],
) -> Target
where
    F: Field + TwoAdicField,
    EF: ExtensionField<F>,
{
    builder.push_scope("compute_final_query_point");

    let domain_index_bits: Vec<Target> = index_bits[total_bits_consumed..log_max_height].to_vec();

    let mut reversed_bits = vec![builder.define_const(EF::ZERO); total_bits_consumed];
    reversed_bits.extend(domain_index_bits.iter().rev().copied());

    let one = builder.define_const(EF::ONE);
    let mut result = one;
    for (&bit, &power) in reversed_bits.iter().zip(powers_of_g.iter()) {
        let multiplier = builder.select(bit, power, one);
        result = builder.mul(result, multiplier);
    }

    builder.pop_scope();
    result
}

fn precompute_evaluation_points<F, EF>(
    builder: &mut CircuitBuilder<EF>,
    unique_heights_desc: &[usize],
    index_bits: &[Target],
    log_global_max_height: usize,
) -> BTreeMap<usize, Target>
where
    F: Field + TwoAdicField,
    EF: ExtensionField<F>,
{
    builder.push_scope("precompute_evaluation_points");

    debug_assert!(
        !unique_heights_desc.is_empty(),
        "must have at least one height"
    );
    debug_assert!(
        unique_heights_desc.windows(2).all(|w| w[0] > w[1]),
        "heights must be sorted in strictly descending order"
    );

    let h_max = unique_heights_desc[0];
    let bits_reduced = log_global_max_height - h_max;
    let rev_bits: Vec<Target> = index_bits[bits_reduced..bits_reduced + h_max]
        .iter()
        .rev()
        .copied()
        .collect();

    let g = F::two_adic_generator(h_max);
    let powers_of_g: Vec<_> = iter::successors(Some(g), |&prev| Some(prev.square()))
        .take(h_max)
        .map(|p| builder.define_const(EF::from(p)))
        .collect();

    let capture_set: BTreeMap<usize, ()> =
        unique_heights_desc[1..].iter().map(|&h| (h, ())).collect();

    let one = builder.define_const(EF::ONE);
    let generator = builder.alloc_const(EF::from(F::GENERATOR), "coset_generator");
    let mut g_pow = one;
    let mut result = BTreeMap::new();

    for i in 0..h_max {
        let multiplier = builder.select(rev_bits[i], powers_of_g[i], one);
        g_pow = builder.mul(g_pow, multiplier);

        let bits_done = i + 1;
        if capture_set.contains_key(&bits_done) {
            let derived = builder.exp_power_of_2(g_pow, h_max - bits_done);
            let x = builder.alloc_mul(generator, derived, "eval_point");
            result.insert(bits_done, x);
        }
    }

    let x_max = builder.alloc_mul(generator, g_pow, "eval_point");
    result.insert(h_max, x_max);

    builder.pop_scope();
    result
}

fn compute_single_reduced_opening<EF: Field>(
    builder: &mut CircuitBuilder<EF>,
    opened_values: &[Target],
    point_values: &[Target],
    alpha_pow: Target,
    alpha: Target,
    alpha_powers_set: &mut HashMap<usize, Target>,
    inv_z_minus_x: Target,
    compressed_x: Option<Target>,
) -> (Target, Target)
{
    builder.push_scope("compute_single_reduced_opening");

    let n = opened_values.len();

    if n == 0 {
        let zero = builder.define_const(EF::ZERO);
        builder.pop_scope();
        return (alpha_pow, zero);
    }

    let inner = if let Some(compressed_x) = compressed_x {
        let compressed_z = if n == 1 {
            point_values[0]
        } else {
            let mut reduced_z = point_values[n - 1];
            for &value in point_values[..n - 1].iter().rev() {
                reduced_z = builder.mul_add(reduced_z, alpha, value);
            }
            reduced_z
        };
        builder.sub(compressed_z, compressed_x)
    } else {
        let zero = builder.define_const(EF::ZERO);
        let mut inner = zero;
        for i in (0..n).rev() {
            inner = builder.horner_acc_step(inner, alpha, point_values[i], opened_values[i]);
        }
        inner
    };

    let numerator = builder.mul(alpha_pow, inner);
    let reduced_opening = builder.mul(numerator, inv_z_minus_x);

    let alpha_n = if let Some(alpha_n) = alpha_powers_set.get(&n) {
        *alpha_n
    } else {
        let alpha_n = circuit_exp_by_constant(builder, alpha, n);
        alpha_powers_set.insert(n, alpha_n);
        alpha_n
    };
    let new_alpha_pow = builder.mul(alpha_pow, alpha_n);

    builder.pop_scope();
    (new_alpha_pow, reduced_opening)
}

fn circuit_exp_by_constant<EF: Field>(
    builder: &mut CircuitBuilder<EF>,
    base: Target,
    n: usize,
) -> Target {
    debug_assert!(n > 0);
    if n == 1 {
        return base;
    }
    let num_bits = usize::BITS - n.leading_zeros();
    let mut result = base;
    for i in (0..num_bits - 1).rev() {
        result = builder.mul(result, result);
        if (n >> i) & 1 == 1 {
            result = builder.mul(result, base);
        }
    }
    result
}

#[allow(clippy::type_complexity)]
fn open_input<F, EF, Comm>(
    builder: &mut CircuitBuilder<EF>,
    log_global_max_height: usize,
    index_bits: &[Target],
    alpha: Target,
    log_blowup: usize,
    commitments_with_opening_points: &ComsWithOpeningsTargets<Comm, TwoAdicMultiplicativeCoset<F>>,
    batch_opened_values: &[Vec<Vec<Target>>],
    batch_salts: &[Vec<Vec<Target>>],
    permutation_config: PermConfig,
    pre_packed_input_caps: &[Vec<Vec<Target>>],
) -> Result<(Vec<(usize, Target)>, Vec<NonPrimitiveOpId>), VerificationError>
where
    F: Field + TwoAdicField + PrimeField64,
    EF: ExtensionField<F>,
    Comm: ObservableCommitment,
{
    builder.push_scope("open_input");

    for &b in index_bits {
        builder.assert_bool(b);
    }
    debug_assert_eq!(
        index_bits.len(),
        log_global_max_height,
        "index_bits.len() must equal log_global_max_height"
    );

    let unique_heights_desc: Vec<usize> = {
        let mut heights: Vec<usize> = commitments_with_opening_points
            .iter()
            .flat_map(|(_, mats)| {
                mats.iter()
                    .map(|(domain, _)| domain.log_size() + log_blowup)
            })
            .collect();
        heights.sort_unstable();
        heights.dedup();
        heights.reverse();
        heights
    };

    let eval_points = if unique_heights_desc.is_empty() {
        BTreeMap::new()
    } else {
        precompute_evaluation_points::<F, EF>(
            builder,
            &unique_heights_desc,
            index_bits,
            log_global_max_height,
        )
    };

    let mut reduced_openings = BTreeMap::<usize, (Target, Target)>::new();
    let mut mmcs_op_ids = Vec::new();

    for (batch_idx, ((_batch_commit, mats), batch_openings)) in zip_eq(
        commitments_with_opening_points.iter(),
        batch_opened_values.iter(),
        VerificationError::InvalidProofShape(
            "Opened values and commitments count must match".to_string(),
        ),
    )?
    .enumerate()
    {
        let batch_log_height = mats
            .iter()
            .map(|(domain, _)| domain.log_size() + log_blowup)
            .max()
            .unwrap_or(0);
        let batch_index_bits = local_mmcs_index_bits(
            index_bits,
            batch_log_height,
            log_global_max_height,
            batch_idx,
        )?;

        {
            let commitment_cap = pre_packed_input_caps[batch_idx].clone();

            let dimensions: Vec<Dimensions> = mats
                .iter()
                .map(|(domain, _)| Dimensions {
                    height: 1 << (domain.log_size() + log_blowup),
                    width: 0,
                })
                .collect();

            let batch_salt = batch_salts.get(batch_idx);
            let salts_for_batch = match batch_salt {
                Some(s) if !s.is_empty() => Some(s.as_slice()),
                _ => None,
            };

            let op_ids = if permutation_config.is_arity4_shape() {
                verify_batch_circuit_arity4::<F, EF>(
                    builder,
                    permutation_config,
                    &commitment_cap,
                    &dimensions,
                    batch_index_bits,
                    batch_openings,
                )
            } else {
                verify_batch_circuit::<F, EF>(
                    builder,
                    permutation_config,
                    &commitment_cap,
                    &dimensions,
                    batch_index_bits,
                    batch_openings,
                    salts_for_batch,
                )
            }
            .map_err(|e| {
                VerificationError::InvalidProofShape(format!(
                    "MMCS verification failed for batch {batch_idx}: {e:?}"
                ))
            })?;
            mmcs_op_ids.extend(op_ids);
        }

        let mut alpha_powers_set = HashMap::new();
        let mut inv_z_minus_x_cache: HashMap<(usize, Target), Target> = HashMap::new();

        type MatRef<'a> = (&'a [Target], &'a [(Target, Vec<Target>)]);
        let mut height_groups: BTreeMap<usize, Vec<MatRef<'_>>> = BTreeMap::new();

        for (mat_idx, ((mat_domain, mat_points_and_values), mat_opening)) in zip_eq(
            mats.iter(),
            batch_openings.iter(),
            VerificationError::InvalidProofShape(format!(
                "batch {batch_idx}: opened_values and point_values count must match"
            )),
        )?
        .enumerate()
        {
            for (_, ps_at_z) in mat_points_and_values {
                if mat_opening.len() != ps_at_z.len() {
                    return Err(VerificationError::InvalidProofShape(format!(
                        "batch {batch_idx} mat {mat_idx}: opened_values columns must match point_values columns"
                    )));
                }
            }
            let log_height = mat_domain.log_size() + log_blowup;
            height_groups
                .entry(log_height)
                .or_default()
                .push((mat_opening.as_slice(), mat_points_and_values.as_slice()));
        }

        for (log_height, matrices) in &height_groups {
            let x = eval_points[log_height];

            let unified_z: Option<Target> = if matrices.iter().all(|(_, pv)| pv.len() == 1) {
                let z0 = matrices[0].1[0].0;
                if matrices.iter().all(|(_, pv)| pv[0].0 == z0) {
                    Some(z0)
                } else {
                    None
                }
            } else {
                None
            };

            if let Some(z) = unified_z {
                let inv_z_minus_x =
                    *inv_z_minus_x_cache
                        .entry((*log_height, z))
                        .or_insert_with(|| {
                            let z_minus_x = builder.sub(z, x);
                            let one = builder.define_const(EF::ONE);
                            builder.div(one, z_minus_x)
                        });

                let zero = builder.define_const(EF::ZERO);
                let mut inner = zero;
                let mut total_n = 0usize;
                for (mat_opening, points_and_values) in matrices.iter().rev() {
                    let ps_at_z = &points_and_values[0].1;
                    for i in (0..mat_opening.len()).rev() {
                        inner = builder.horner_acc_step(inner, alpha, ps_at_z[i], mat_opening[i]);
                    }
                    total_n += mat_opening.len();
                }

                let alpha_total_n = match alpha_powers_set.get(&total_n) {
                    Some(&v) => v,
                    None => {
                        let v = circuit_exp_by_constant(builder, alpha, total_n);
                        alpha_powers_set.insert(total_n, v);
                        v
                    }
                };

                let (alpha_pow_h, ro_h) =
                    reduced_openings.entry(*log_height).or_insert_with(|| {
                        (
                            builder.define_const(EF::ONE),
                            builder.define_const(EF::ZERO),
                        )
                    });
                let alpha_pow_old = *alpha_pow_h;
                let c = builder.mul(alpha_pow_old, inv_z_minus_x);
                *ro_h = builder.mul_add(c, inner, *ro_h);
                *alpha_pow_h = builder.mul(alpha_pow_old, alpha_total_n);
            } else {
                for (mat_opening, points_and_values) in matrices {
                    let compressed_x = if points_and_values.len() > 1 && mat_opening.len() > 1 {
                        Some(evaluate_polynomial(builder, mat_opening, alpha))
                    } else {
                        None
                    };
                    for (z, ps_at_z) in points_and_values.iter() {
                        let inv_z_minus_x = *inv_z_minus_x_cache
                            .entry((*log_height, *z))
                            .or_insert_with(|| {
                                let z_minus_x = builder.sub(*z, x);
                                let one = builder.define_const(EF::ONE);
                                builder.div(one, z_minus_x)
                            });

                        let alpha_pow_value = {
                            let (alpha_pow_h, _ro_h) =
                                reduced_openings.entry(*log_height).or_insert_with(|| {
                                    (
                                        builder.define_const(EF::ONE),
                                        builder.define_const(EF::ZERO),
                                    )
                                });
                            *alpha_pow_h
                        };

                        let (new_alpha_pow_h, ro_contrib) = compute_single_reduced_opening(
                            builder,
                            mat_opening,
                            ps_at_z,
                            alpha_pow_value,
                            alpha,
                            &mut alpha_powers_set,
                            inv_z_minus_x,
                            compressed_x,
                        );

                        let entry = reduced_openings.get_mut(log_height).expect("entry");
                        entry.1 = builder.add(entry.1, ro_contrib);
                        entry.0 = new_alpha_pow_h;
                    }
                }
            }
        }

        if let Some((_ap, ro0)) = reduced_openings.get(&log_blowup) {
            let zero = builder.define_const(EF::ZERO);
            builder.connect(*ro0, zero);
        }
    }

    builder.pop_scope();

    let reduced_list: Vec<_> = reduced_openings
        .into_iter()
        .rev()
        .map(|(h, (_ap, ro))| (h, ro))
        .collect();
    Ok((reduced_list, mmcs_op_ids))
}

fn local_mmcs_index_bits(
    global_bits: &[Target],
    local_log_height: usize,
    global_log_height: usize,
    batch: usize,
) -> Result<&[Target], VerificationError> {
    if global_bits.len() != global_log_height || local_log_height > global_log_height {
        return Err(VerificationError::InvalidProofShape(format!(
            "FRI input batch {batch} height {local_log_height} is incompatible with global height \
             {global_log_height}"
        )));
    }
    Ok(&global_bits[global_log_height - local_log_height..])
}

fn verify_fri_circuit_engine<F, EF, RecMmcs, Inner, Witness, Comm>(
    builder: &mut CircuitBuilder<EF>,
    fri_proof_targets: &FriProofTargets<F, EF, RecMmcs, InputProofTargets<F, EF, Inner>, Witness>,
    alpha: Target,
    betas: &[Target],
    index_bits_per_query: &[Vec<Target>],
    commitments_with_opening_points: &ComsWithOpeningsTargets<Comm, TwoAdicMultiplicativeCoset<F>>,
    log_blowup: usize,
    permutation_config: PermConfig,
) -> Result<Vec<NonPrimitiveOpId>, VerificationError>
where
    F: Field + TwoAdicField + PrimeField64,
    EF: ExtensionField<F>,
    RecMmcs: RecursiveExtensionMmcs<F, EF>,
    RecMmcs::Commitment: ObservableCommitment,
    RecMmcs::Proof: MmcsProofTargets,
    Inner: RecursiveMmcs<F, EF>,
    Inner::Proof: MmcsProofTargets,
    Witness: Recursive<EF>,
    Comm: ObservableCommitment,
{
    let num_phases = betas.len();
    let num_queries = fri_proof_targets.query_proofs.len();
    let log_arities = &fri_proof_targets.log_arities;

    let total_log_reduction = log_arities.iter().try_fold(0usize, |sum, &arity| {
        sum.checked_add(arity).ok_or_else(|| {
            VerificationError::InvalidProofShape("FRI fold arity sum overflows usize".to_string())
        })
    })?;

    tracing::debug!(
        "verify_fri_circuit: num_phases={}, num_queries={}, log_blowup={}, log_arities={:?}",
        num_phases,
        num_queries,
        log_blowup,
        log_arities,
    );

    if num_phases != fri_proof_targets.commit_phase_commits.len() {
        return Err(VerificationError::InvalidProofShape(format!(
            "betas length must equal number of commit-phase commitments: expected {}, got {}",
            num_phases,
            fri_proof_targets.commit_phase_commits.len()
        )));
    }

    if num_phases != fri_proof_targets.commit_pow_witnesses.len() {
        return Err(VerificationError::InvalidProofShape(format!(
            "Number of commit-phase commitments must equal number of commit-phase pow witnesses: expected {}, got {}",
            num_phases,
            fri_proof_targets.commit_pow_witnesses.len()
        )));
    }

    if log_arities.len() != num_phases {
        return Err(VerificationError::InvalidProofShape(format!(
            "log_arities length must equal number of phases: expected {}, got {}",
            num_phases,
            log_arities.len()
        )));
    }

    if num_queries != index_bits_per_query.len() {
        return Err(VerificationError::InvalidProofShape(format!(
            "index_bits_per_query length must equal number of query proofs: expected {}, got {}",
            num_queries,
            index_bits_per_query.len()
        )));
    }

    if num_queries == 0 {
        return Err(VerificationError::InvalidProofShape(
            "FRI proof must have at least one query".to_string(),
        ));
    }

    let log_max_height = index_bits_per_query[0].len();
    if log_max_height > F::TWO_ADICITY || log_max_height >= usize::BITS as usize {
        return Err(VerificationError::InvalidProofShape(format!(
            "FRI global query height {log_max_height} exceeds field two-adicity {}",
            F::TWO_ADICITY
        )));
    }
    if index_bits_per_query
        .iter()
        .any(|v| v.len() != log_max_height)
    {
        return Err(VerificationError::InvalidProofShape(
            "all index_bits_per_query entries must have same length".to_string(),
        ));
    }

    if betas.is_empty() {
        return Err(VerificationError::InvalidProofShape(
            "FRI must have at least one fold phase".to_string(),
        ));
    }

    for (commitment, matrices) in commitments_with_opening_points {
        let _ = commitment;
        for (domain, _) in matrices {
            checked_input_lde_log(domain.log_size(), log_blowup)?;
        }
    }

    let ef_dim = EF::DIMENSION;
    for (q, query_proof) in fri_proof_targets.query_proofs.iter().enumerate() {
        if query_proof.commit_phase_openings.len() != num_phases {
            return Err(VerificationError::InvalidProofShape(format!(
                "query {q}: commit-phase opening count must equal number of phases: expected {}, got {}",
                num_phases,
                query_proof.commit_phase_openings.len()
            )));
        }
        for (phase, opening) in query_proof.commit_phase_openings.iter().enumerate() {
            let expected_log_arity = log_arities[phase];
            if opening.log_arity != expected_log_arity {
                return Err(VerificationError::InvalidProofShape(format!(
                    "query {q} phase {phase}: log_arity disagrees with global FRI schedule: expected {expected_log_arity}, got {}",
                    opening.log_arity
                )));
            }
            let expected_coeffs = u32::try_from(expected_log_arity)
                .ok()
                .and_then(|shift| 1usize.checked_shl(shift))
                .and_then(|size| size.checked_sub(1))
                .and_then(|siblings| siblings.checked_mul(ef_dim))
                .ok_or_else(|| {
                    VerificationError::InvalidProofShape(format!(
                        "query {q} phase {phase}: log_arity {expected_log_arity} exceeds checked usize geometry"
                    ))
                })?;
            if opening.sibling_coefficients.len() != expected_coeffs {
                return Err(VerificationError::InvalidProofShape(format!(
                    "query {q} phase {phase}: sibling coefficient count must be \
                     (2^log_arity - 1) * EF::DIMENSION = {expected_coeffs}, got {}",
                    opening.sibling_coefficients.len()
                )));
            }
        }
    }

    let log_final_poly_len = log_max_height
        .checked_sub(total_log_reduction)
        .and_then(|x| x.checked_sub(log_blowup))
        .ok_or_else(|| {
            VerificationError::InvalidProofShape(
                "Invalid FRI parameters: log_max_height too small for given log_arities"
                    .to_string(),
            )
        })?;

    let expected_final_poly_len = u32::try_from(log_final_poly_len)
        .ok()
        .and_then(|shift| 1usize.checked_shl(shift))
        .ok_or_else(|| {
            VerificationError::InvalidProofShape(format!(
                "FRI final polynomial exponent {log_final_poly_len} exceeds checked usize geometry"
            ))
        })?;
    let actual_final_poly_len = fri_proof_targets.final_poly.len();

    if actual_final_poly_len != expected_final_poly_len {
        return Err(VerificationError::InvalidProofShape(format!(
            "Final polynomial length mismatch: expected 2^{log_final_poly_len} = {expected_final_poly_len}, got {actual_final_poly_len}"
        )));
    }

    let mut cumulative_bits = Vec::with_capacity(num_phases + 1);
    cumulative_bits.push(0usize);
    for &la in log_arities {
        let next = cumulative_bits
            .last()
            .and_then(|&sum| sum.checked_add(la))
            .ok_or_else(|| {
                VerificationError::InvalidProofShape(
                    "FRI cumulative fold arity overflows usize".to_string(),
                )
            })?;
        cumulative_bits.push(next);
    }

    let folded_height_after: Vec<usize> = (0..num_phases)
        .map(|i| log_max_height - cumulative_bits[i + 1])
        .collect();

    builder.push_scope("verify_fri");

    let beta_pows_per_phase = precompute_beta_powers_per_phase(builder, betas, log_arities);
    let powers_of_g_final = precompute_two_adic_powers::<F, EF>(builder, log_max_height);

    let pre_packed_input_caps: Vec<Vec<Vec<Target>>> = commitments_with_opening_points
        .iter()
        .map(|(commit, _)| {
            let lifted = commit.to_observation_targets();
            commitment_cap_rows_from_lifted::<F, EF>(builder, permutation_config, &lifted)
        })
        .collect();

    let pre_packed_commit_caps: Vec<Vec<Vec<Target>>> = fri_proof_targets
        .commit_phase_commits
        .iter()
        .map(|commit| {
            let lifted = commit.to_observation_targets();
            commitment_cap_rows_from_lifted::<F, EF>(builder, permutation_config, &lifted)
        })
        .collect();

    let mut all_mmcs_op_ids = Vec::new();

    for (q, query_proof) in fri_proof_targets.query_proofs.iter().enumerate() {
        builder.push_scope("verify_fri_query");
        let batch_opened_values: Vec<Vec<Vec<Target>>> = query_proof
            .input_proof
            .iter()
            .map(|batch| batch.opened_values.clone())
            .collect();

        let batch_salts: Vec<Vec<Vec<Target>>> = query_proof
            .input_proof
            .iter()
            .map(|batch| batch.opening_proof.salt_targets().to_vec())
            .collect();

        let (reduced_by_height, input_mmcs_ops) = open_input::<F, EF, Comm>(
            builder,
            log_max_height,
            &index_bits_per_query[q],
            alpha,
            log_blowup,
            commitments_with_opening_points,
            &batch_opened_values,
            &batch_salts,
            permutation_config,
            &pre_packed_input_caps,
        )?;
        all_mmcs_op_ids.extend(input_mmcs_ops);

        if reduced_by_height.is_empty() {
            return Err(VerificationError::InvalidProofShape(
                "No reduced openings; did you commit to zero polynomials?".to_string(),
            ));
        }
        if reduced_by_height[0].0 != log_max_height {
            return Err(VerificationError::InvalidProofShape(format!(
                "First reduced opening must be at max height {}, got {}",
                log_max_height, reduced_by_height[0].0
            )));
        }
        let initial_folded_eval = reduced_by_height[0].1;

        let sibling_values_per_phase: Vec<Vec<Target>> = query_proof
            .commit_phase_openings
            .iter()
            .map(|opening| opening.sibling_values_packed(builder))
            .collect();

        if sibling_values_per_phase.len() != num_phases {
            return Err(VerificationError::InvalidProofShape(format!(
                "commit_phase_openings count must match phases: expected {}, got {}",
                num_phases,
                sibling_values_per_phase.len()
            )));
        }

        let mut roll_ins: Vec<Option<Target>> = vec![None; num_phases];
        for &(h, ro) in reduced_by_height.iter().skip(1) {
            let phase_idx = folded_height_after.iter().position(|&fh| fh == h);
            if let Some(i) = phase_idx {
                if roll_ins[i].is_some() {
                    return Err(VerificationError::InvalidProofShape(format!(
                        "duplicate roll-in for phase {i} (height {h})",
                    )));
                }
                roll_ins[i] = Some(ro);
            } else {
                let zero = builder.define_const(EF::ZERO);
                builder.connect(ro, zero);
            }
        }

        builder.push_scope("compute_final_query_point");
        let final_query_point = compute_final_query_point::<F, EF>(
            builder,
            &index_bits_per_query[q],
            log_max_height,
            total_log_reduction,
            &powers_of_g_final,
        );
        builder.pop_scope();

        let final_poly_eval =
            evaluate_polynomial(builder, &fri_proof_targets.final_poly, final_query_point);

        {
            let subgroup_starts = precompute_subgroup_starts::<F, EF>(
                builder,
                &index_bits_per_query[q],
                log_max_height,
                log_arities,
                &cumulative_bits,
            );

            let mut current_folded = initial_folded_eval;
            let mut bits_consumed = 0usize;
            let mut log_current_height = log_max_height;

            for (phase_idx, (_commit, opening)) in fri_proof_targets
                .commit_phase_commits
                .iter()
                .zip(query_proof.commit_phase_openings.iter())
                .enumerate()
            {
                let log_arity = log_arities[phase_idx];
                let arity = 1usize << log_arity;
                let log_folded_height = log_current_height - log_arity;
                let siblings = &sibling_values_per_phase[phase_idx];

                builder.push_scope("fri_commit_phase_mmcs");

                let index_in_group_bits =
                    &index_bits_per_query[q][bits_consumed..bits_consumed + log_arity];
                let evals =
                    reconstruct_evals(builder, current_folded, siblings, index_in_group_bits);

                let commitment_cap = pre_packed_commit_caps[phase_idx].clone();

                let folded_height = 1usize << log_folded_height;
                let dimensions = vec![Dimensions {
                    height: folded_height,
                    width: arity,
                }];

                let parent_bit_start = bits_consumed + log_arity;
                let parent_bit_end = (parent_bit_start + log_folded_height).min(log_max_height);
                let zero = builder.define_const(EF::ZERO);

                let mut parent_index_bits: Vec<Target> =
                    index_bits_per_query[q][parent_bit_start..parent_bit_end].to_vec();
                while parent_index_bits.len() < log_folded_height {
                    parent_index_bits.push(zero);
                }

                let phase_salts = opening.opening_proof.salt_targets();
                let salts_for_phase = if phase_salts.is_empty() {
                    None
                } else {
                    Some(phase_salts)
                };

                let commit_phase_ops = if permutation_config.is_arity4_shape() {
                    verify_batch_circuit_from_extension_opened_arity4::<F, EF>(
                        builder,
                        permutation_config,
                        &commitment_cap,
                        &dimensions,
                        &parent_index_bits,
                        core::slice::from_ref(&evals),
                    )
                } else {
                    verify_batch_circuit_from_extension_opened::<F, EF>(
                        builder,
                        permutation_config,
                        &commitment_cap,
                        &dimensions,
                        &parent_index_bits,
                        core::slice::from_ref(&evals),
                        salts_for_phase,
                    )
                }
                .map_err(|e| {
                    VerificationError::InvalidProofShape(format!(
                        "Commit-phase MMCS verification failed for query {q}, phase {phase_idx}: {e:?}"
                    ))
                })?;
                all_mmcs_op_ids.extend(commit_phase_ops);

                current_folded = fold_one_phase::<F, EF>(
                    builder,
                    current_folded,
                    siblings,
                    betas[phase_idx],
                    &index_bits_per_query[q],
                    bits_consumed,
                    log_arity,
                    roll_ins[phase_idx],
                    Some(beta_pows_per_phase[phase_idx]),
                    Some(&evals),
                    subgroup_starts[phase_idx],
                );

                bits_consumed += log_arity;
                log_current_height = log_folded_height;

                builder.pop_scope();
            }

            builder.connect(current_folded, final_poly_eval);
        }

        builder.pop_scope();
    }

    builder.pop_scope();

    Ok(all_mmcs_op_ids)
}

fn checked_input_lde_log(log_domain: usize, log_blowup: usize) -> Result<usize, VerificationError> {
    log_domain
        .checked_add(log_blowup)
        .filter(|&height| height < usize::BITS as usize)
        .ok_or_else(|| {
            VerificationError::InvalidProofShape(
                "FRI input matrix LDE height exceeds checked usize geometry".into(),
            )
        })
}

pub fn verify_fri_circuit<F, EF, RecMmcs, Inner, Witness, Comm>(
    builder: &mut CircuitBuilder<EF>,
    fri_proof_targets: &FriProofTargets<F, EF, RecMmcs, InputProofTargets<F, EF, Inner>, Witness>,
    alpha: Target,
    betas: &[Target],
    index_bits_per_query: &[Vec<Target>],
    commitments_with_opening_points: &ComsWithOpeningsTargets<Comm, TwoAdicMultiplicativeCoset<F>>,
    log_blowup: usize,
    permutation_config: PermConfig,
) -> Result<Vec<NonPrimitiveOpId>, VerificationError>
where
    F: Field + TwoAdicField + PrimeField64,
    EF: ExtensionField<F>,
    RecMmcs: RecursiveExtensionMmcs<F, EF>,
    RecMmcs::Commitment: ObservableCommitment,
    RecMmcs::Proof: MmcsProofTargets,
    Inner: RecursiveMmcs<F, EF>,
    Inner::Proof: MmcsProofTargets,
    Witness: Recursive<EF>,
    Comm: ObservableCommitment,
{
    verify_fri_circuit_engine(
        builder,
        fri_proof_targets,
        alpha,
        betas,
        index_bits_per_query,
        commitments_with_opening_points,
        log_blowup,
        permutation_config,
    )
}
