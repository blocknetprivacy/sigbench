use alloc::vec::Vec;

use p3_circuit::{CircuitBuilder, CircuitBuilderError};
use p3_field::{ExtensionField, Field, PrimeField64};
use p3_sumcheck::strategy::Basis;
use p3_sumcheck::transcript::SumcheckShape;

use crate::Target;
use crate::traits::RecursiveChallenger;
use crate::transcript::domain_separator_seed;

pub fn sumcheck_round_claim_update<F: Field>(
    builder: &mut CircuitBuilder<F>,
    claimed_sum: Target,
    c0: Target,
    c_inf: Target,
    r: Target,
) -> Target {
    let one = builder.define_const(F::ONE);

    let twice_c0 = builder.add(c0, c0);
    let linear = builder.sub(claimed_sum, twice_c0);
    let r_minus_one = builder.sub(r, one);
    let inner = builder.mul_add(c_inf, r_minus_one, linear);
    builder.mul_add(r, inner, c0)
}

pub fn fold_sumcheck_claim<F: Field>(
    builder: &mut CircuitBuilder<F>,
    initial_claim: Target,
    round_polys: &[[Target; 2]],
    challenges: &[Target],
) -> Target {
    assert_eq!(
        round_polys.len(),
        challenges.len(),
        "fold_sumcheck_claim: round/challenge count mismatch"
    );

    let mut claim = initial_claim;
    for (&[c0, c_inf], &r) in round_polys.iter().zip(challenges) {
        claim = sumcheck_round_claim_update(builder, claim, c0, c_inf, r);
    }
    claim
}

pub fn verify_sumcheck_rounds<BF, EF, Ch>(
    circuit: &mut CircuitBuilder<EF>,
    challenger: &mut Ch,
    claimed_sum: Target,
    round_polys: &[[Target; 2]],
    pow_witnesses: &[Target],
    pow_bits: usize,
) -> Result<(Target, Vec<Target>), CircuitBuilderError>
where
    BF: PrimeField64,
    EF: ExtensionField<BF>,
    Ch: RecursiveChallenger<BF, EF>,
{
    if pow_bits > 0 {
        assert_eq!(
            pow_witnesses.len(),
            round_polys.len(),
            "verify_sumcheck_rounds: pow witness count must equal round count"
        );
    }

    if !round_polys.is_empty() {
        let shape = SumcheckShape::new(round_polys.len(), pow_bits, Basis::Evaluation);
        challenger.observe_seed(
            circuit,
            &domain_separator_seed(&shape.domain_separator::<BF, EF>()),
        );
    }

    let mut claim = claimed_sum;
    let mut randomness = Vec::with_capacity(round_polys.len());
    for (i, &[c0, c_inf]) in round_polys.iter().enumerate() {
        challenger.observe_ext_slice(circuit, &[c0, c_inf]);
        if pow_bits > 0 {
            challenger.check_pow_witness(circuit, pow_bits, pow_witnesses[i])?;
        }
        let r = challenger.sample_ext(circuit);
        claim = sumcheck_round_claim_update(circuit, claim, c0, c_inf, r);
        randomness.push(r);
    }
    Ok((claim, randomness))
}
