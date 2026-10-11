use alloc::vec::Vec;

use p3_circuit::CircuitBuilder;
use p3_field::Field;
use p3_multilinear_util::point::Point;

use crate::Target;
use crate::pcs::whir::gadgets::expand_from_univariate;

pub fn univariate_eq_point<EF: Field>(zeta: EF, num_variables: usize) -> (Point<EF>, EF) {
    let powers = Point::<EF>::expand_from_univariate(zeta, num_variables);
    let mut scale = EF::ONE;
    let coords: Vec<EF> = powers
        .as_slice()
        .iter()
        .map(|&y| {
            let denom = EF::ONE + y;
            assert!(
                !denom.is_zero(),
                "opening point is a root of unity of the committed size"
            );
            scale *= denom;
            y * denom.inverse()
        })
        .collect();
    (Point::new(coords), scale)
}

pub fn univariate_eq_point_circuit<F: Field>(
    builder: &mut CircuitBuilder<F>,
    zeta: Target,
    num_variables: usize,
) -> (Vec<Target>, Target) {
    let one = builder.define_const(F::ONE);
    if num_variables == 0 {
        return (Vec::new(), one);
    }

    let powers = expand_from_univariate(builder, zeta, num_variables);
    let mut denoms = Vec::with_capacity(num_variables);
    let mut coords = Vec::with_capacity(num_variables);
    for &y in &powers {
        let denom = builder.add(one, y);
        coords.push(builder.alloc_div(y, denom, "whir uni bridge coord"));
        denoms.push(denom);
    }
    let scale = builder.mul_many(&denoms);
    (coords, scale)
}
