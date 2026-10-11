use alloc::format;
use alloc::vec::Vec;

use p3_circuit::CircuitBuilder;
use p3_dft::{Radix2Dit, TwoAdicSubgroupDft};
use p3_field::coset::TwoAdicMultiplicativeCoset;
use p3_field::{ExtensionField, TwoAdicField};
use p3_util::log2_strict_usize;

use crate::Target;
use crate::verifier::VerificationError;

pub(crate) fn evaluate_periodic_columns_circuit<Val, Challenge>(
    circuit: &mut CircuitBuilder<Challenge>,
    domain: &TwoAdicMultiplicativeCoset<Val>,
    periodic_columns: &[Vec<Val>],
    point: Target,
) -> Result<Vec<Target>, VerificationError>
where
    Val: TwoAdicField,
    Challenge: ExtensionField<Val>,
{
    periodic_columns
        .iter()
        .map(|col| evaluate_one(circuit, domain, col, point))
        .collect()
}

fn evaluate_one<Val, Challenge>(
    circuit: &mut CircuitBuilder<Challenge>,
    domain: &TwoAdicMultiplicativeCoset<Val>,
    col: &[Val],
    point: Target,
) -> Result<Target, VerificationError>
where
    Val: TwoAdicField,
    Challenge: ExtensionField<Val>,
{
    let period = col.len();
    if !period.is_power_of_two() {
        return Err(VerificationError::InvalidProofShape(format!(
            "periodic column length must be a power of two, got {period}"
        )));
    }
    if period > domain.size() {
        return Err(VerificationError::InvalidProofShape(format!(
            "periodic column length {period} exceeds trace domain size {}",
            domain.size()
        )));
    }

    let log_period = log2_strict_usize(period);
    let folds = domain.log_size() - log_period;

    let sub_shift = domain.shift().exp_power_of_2(folds);
    let coeffs: Vec<Val> = Radix2Dit::default().coset_idft(col.to_vec(), sub_shift);

    let (&leading, rest) = coeffs
        .split_last()
        .expect("a power-of-two periodic column has at least one coefficient");
    let mut acc = circuit.define_const(Challenge::from(leading));
    if rest.is_empty() {
        return Ok(acc);
    }

    let zp = circuit.exp_power_of_2(point, folds);
    for &c in rest.iter().rev() {
        let c_target = circuit.define_const(Challenge::from(c));
        acc = circuit.mul_add(acc, zp, c_target);
    }
    Ok(acc)
}
