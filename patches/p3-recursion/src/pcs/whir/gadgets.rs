use alloc::vec::Vec;

use p3_circuit::CircuitBuilder;
use p3_field::Field;

use crate::Target;

pub fn expand_from_univariate<F: Field>(
    builder: &mut CircuitBuilder<F>,
    z: Target,
    num_variables: usize,
) -> Vec<Target> {
    if num_variables == 0 {
        return Vec::new();
    }

    let mut res = Vec::with_capacity(num_variables);
    let mut cur = z;
    res.push(cur);
    for _ in 1..num_variables {
        cur = builder.mul(cur, cur);
        res.push(cur);
    }
    res.reverse();
    res
}

pub fn eq_eval<F: Field>(builder: &mut CircuitBuilder<F>, a: &[Target], b: &[Target]) -> Target {
    assert_eq!(a.len(), b.len(), "eq_eval: point length mismatch");

    let zero = builder.define_const(F::ZERO);
    let one = builder.define_const(F::ONE);
    let mut selectors = Vec::new();
    let mut terms = Vec::new();
    for (&ai, &bi) in a.iter().zip(b) {
        if bi == one {
            selectors.push(ai);
        } else if bi == zero {
            selectors.push(builder.sub(one, ai));
        } else {
            let two_ai = builder.add(ai, ai);
            let slope = builder.sub(two_ai, one);
            let complement = builder.sub(one, ai);
            terms.push(builder.mul_add(slope, bi, complement));
        }
    }
    let local_eq = builder.mul_many(&terms);
    let selector_eq = builder.mul_many(&selectors);
    builder.mul(local_eq, selector_eq)
}

pub fn select_eval<F: Field>(
    builder: &mut CircuitBuilder<F>,
    point: &[Target],
    z: Target,
) -> Target {
    let one = builder.define_const(F::ONE);
    let n = point.len();
    if n == 0 {
        return one;
    }

    let mut var = z;
    let mut terms = Vec::with_capacity(n);
    for (k, &coord) in point.iter().rev().enumerate() {
        let complement = builder.sub(one, coord);
        let term = builder.mul_add(coord, var, complement);
        terms.push(term);
        if k + 1 < n {
            var = builder.mul(var, var);
        }
    }
    builder.mul_many(&terms)
}

pub fn horner_eval<F: Field>(
    builder: &mut CircuitBuilder<F>,
    evals: &[Target],
    z: Target,
) -> Target {
    let n = evals.len();
    if n == 0 {
        return builder.define_const(F::ZERO);
    }
    let mut acc = evals[n - 1];
    for &c in evals[..n - 1].iter().rev() {
        acc = builder.mul_add(acc, z, c);
    }
    acc
}

pub fn eval_multilinear<F: Field>(
    builder: &mut CircuitBuilder<F>,
    evals: &[Target],
    point: &[Target],
) -> Target {
    assert_eq!(
        evals.len(),
        1usize << point.len(),
        "eval_multilinear: evals length must be 2^point.len()"
    );

    let mut cur = evals.to_vec();
    for &p in point {
        let half = cur.len() / 2;
        let mut next = Vec::with_capacity(half);
        for j in 0..half {
            let diff = builder.sub(cur[half + j], cur[j]);
            next.push(builder.mul_add(p, diff, cur[j]));
        }
        cur = next;
    }
    cur[0]
}

pub(crate) fn eval_multilinear_batched<F: Field>(
    builder: &mut CircuitBuilder<F>,
    leaves: &[&[Target]],
    point: &[Target],
    gamma: Target,
) -> Target {
    let Some(last) = leaves.last() else {
        return builder.define_const(F::ZERO);
    };
    let width = 1usize << point.len();
    assert!(
        leaves.iter().all(|leaf| leaf.len() == width),
        "multilinear batch leaf width mismatch"
    );

    let combined: Vec<_> = (0..width)
        .map(|column| {
            leaves[..leaves.len() - 1]
                .iter()
                .rev()
                .fold(last[column], |acc, leaf| {
                    builder.mul_add(acc, gamma, leaf[column])
                })
        })
        .collect();
    eval_multilinear(builder, &combined, point)
}

pub(crate) fn multilinear_eq_weights<F: Field>(
    builder: &mut CircuitBuilder<F>,
    point: &[Target],
) -> Vec<Target> {
    let mut weights = alloc::vec![builder.define_const(F::ONE)];
    for &coordinate in point {
        let mut next = Vec::with_capacity(2 * weights.len());
        for weight in weights {
            let right = builder.mul(weight, coordinate);
            let left = builder.sub(weight, right);
            next.extend([left, right]);
        }
        weights = next;
    }
    weights
}

pub fn eval_powers_combination<F: Field>(
    builder: &mut CircuitBuilder<F>,
    values: &[Target],
    base: Target,
) -> Target {
    let mut iter = values.iter().rev();
    match iter.next() {
        None => builder.define_const(F::ZERO),
        Some(&hi) => {
            let mut acc = hi;
            for &v in iter {
                acc = builder.mul_add(acc, base, v);
            }
            acc
        }
    }
}

pub fn pow_const_base<F: Field>(
    builder: &mut CircuitBuilder<F>,
    base: F,
    bits: &[Target],
) -> Target {
    let one = builder.define_const(F::ONE);
    if bits.is_empty() {
        return one;
    }

    let mut power = base;
    let mut factors = Vec::with_capacity(bits.len());
    for (i, &bit) in bits.iter().enumerate() {
        let coeff = builder.define_const(power - F::ONE);
        factors.push(builder.mul_add(bit, coeff, one));
        if i + 1 < bits.len() {
            power = power.square();
        }
    }
    builder.mul_many(&factors)
}

pub fn eval_constraint_weight<F: Field>(
    builder: &mut CircuitBuilder<F>,
    point: &[Target],
    eq_points: &[&[Target]],
    sel_scalars: &[Target],
    gamma: Target,
) -> Target {
    assert!(
        eq_points.iter().all(|z| z.len() == point.len()),
        "eq_eval: point length mismatch"
    );
    let selections: Vec<_> = sel_scalars
        .iter()
        .map(|&z| select_eval(builder, point, z))
        .collect();
    let mut acc =
        (!selections.is_empty()).then(|| eval_powers_combination(builder, &selections, gamma));
    if eq_points.is_empty() {
        return acc.unwrap_or_else(|| builder.define_const(F::ZERO));
    }

    let zero = builder.define_const(F::ZERO);
    let one = builder.define_const(F::ONE);
    let mut blocks = Vec::new();
    let mut start = 0;
    while start < eq_points.len() {
        let (width, coordinates) = boolean_eq_block(&eq_points[start..], zero, one);
        blocks.push((start, width, coordinates));
        start += width;
    }

    let mut gamma_powers = alloc::vec![gamma];
    for (start, width, coordinates) in blocks.into_iter().rev() {
        let bits = coordinates.len();
        while gamma_powers.len() <= bits {
            let last = *gamma_powers.last().unwrap();
            gamma_powers.push(builder.mul(last, last));
        }

        let block_weight = if bits == 0 {
            eq_eval(builder, point, eq_points[start])
        } else {
            let mut fixed_a = Vec::with_capacity(point.len() - bits);
            let mut fixed_b = Vec::with_capacity(point.len() - bits);
            for (coordinate, (&a, &b)) in point.iter().zip(eq_points[start]).enumerate() {
                if !coordinates.contains(&coordinate) {
                    fixed_a.push(a);
                    fixed_b.push(b);
                }
            }
            let fixed_eq = eq_eval(builder, &fixed_a, &fixed_b);
            let factors: Vec<_> = coordinates
                .iter()
                .enumerate()
                .map(|(bit, &coordinate)| {
                    let r = point[coordinate];
                    let complement = builder.sub(one, r);
                    builder.mul_add(r, gamma_powers[bit], complement)
                })
                .collect();
            let selector_weight = builder.mul_many(&factors);
            builder.mul(fixed_eq, selector_weight)
        };

        debug_assert_eq!(width, 1usize << bits);
        acc = Some(acc.map_or(block_weight, |later| {
            builder.mul_add(later, gamma_powers[bits], block_weight)
        }));
    }
    acc.unwrap()
}

fn boolean_eq_block(points: &[&[Target]], zero: Target, one: Target) -> (usize, Vec<usize>) {
    let first = points[0];
    let mut width = 1;
    let mut coordinates = Vec::new();
    while width <= points.len() / 2 {
        let mut differences = first
            .iter()
            .zip(points[width])
            .enumerate()
            .filter_map(|(coordinate, (&a, &b))| (a != b).then_some(coordinate));
        let Some(coordinate) = differences.next() else {
            break;
        };
        if differences.next().is_some()
            || first[coordinate] != zero
            || points[width][coordinate] != one
            || coordinates.contains(&coordinate)
        {
            break;
        }
        let matches =
            points[..width]
                .iter()
                .zip(&points[width..2 * width])
                .all(|(&lower, &upper)| {
                    lower[coordinate] == zero
                        && upper[coordinate] == one
                        && lower
                            .iter()
                            .zip(upper)
                            .enumerate()
                            .all(|(i, (a, b))| i == coordinate || a == b)
                });
        if !matches {
            break;
        }
        coordinates.push(coordinate);
        width *= 2;
    }
    (width, coordinates)
}

pub struct ConstraintWeightData {
    pub num_variables: usize,
    pub eq_points: Vec<Vec<Target>>,
    pub sel_scalars: Vec<Target>,
    pub gamma: Target,
    pub initial_power: usize,
}

pub fn eval_constraints_poly_circuit<F: Field>(
    builder: &mut CircuitBuilder<F>,
    all_r: &[Target],
    constraints: &[ConstraintWeightData],
    is_suffix: bool,
) -> Target {
    let n = all_r.len();
    let zero = builder.define_const(F::ZERO);
    let mut total = zero;
    for c in constraints {
        let k = c.num_variables.min(n);
        let local_r_slice = &all_r[n - k..];
        let local_r: Vec<Target> = if is_suffix {
            local_r_slice.iter().copied().rev().collect()
        } else {
            local_r_slice.to_vec()
        };
        let eq_refs: Vec<&[Target]> = c.eq_points.iter().map(|v| v.as_slice()).collect();
        let mut w = eval_constraint_weight(builder, &local_r, &eq_refs, &c.sel_scalars, c.gamma);
        for _ in 0..c.initial_power {
            w = builder.mul(w, c.gamma);
        }
        total = builder.add(total, w);
    }
    total
}
