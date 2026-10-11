use alloc::vec;
use alloc::vec::Vec;
use core::hash::Hash;

use p3_binary_field::{Poly64, Poly192};
use p3_circuit::CircuitBuilder;
use p3_field::{Field, PrimeCharacteristicRing};

use super::generic_sumcheck::lagrange_coefficients;
use super::whir_plan::invalid;
use crate::verifier::binary_field_policy::BinaryPolyPolicy;
use crate::verifier::{VerificationError, VerifierLimits};

#[derive(Clone, Debug)]
pub(crate) struct Poly192SumcheckInterpolator {
    coefficients: Vec<Vec<u64>>,
}

impl Poly192SumcheckInterpolator {
    pub(crate) fn with_limits(
        degree: usize,
        limits: &VerifierLimits,
    ) -> Result<Self, VerificationError> {
        let native = lagrange_coefficients::<Poly192>(degree, limits)?;
        let count = native.len();
        let mut coefficients = Vec::with_capacity(count);
        for basis in native {
            let mut row = Vec::with_capacity(count);
            for coefficient in basis {
                let [base, c1, c2] = coefficient.coefficients();
                if c1 != Poly64::ZERO || c2 != Poly64::ZERO {
                    return Err(invalid(
                        "binary Poly sumcheck interpolation left the base field",
                    ));
                }
                row.push(base.to_bits());
            }
            coefficients.push(row);
        }
        Ok(Self { coefficients })
    }

    pub(crate) const fn metadata_entries(&self) -> usize {
        self.coefficients.len() * self.coefficients.len()
    }

    pub(crate) fn reduce_claim_using<P, EF>(
        &self,
        b: &mut CircuitBuilder<EF>,
        claim: &P::ChallengeTarget,
        evaluations: &[P::ChallengeTarget],
        challenge: &P::ChallengeTarget,
    ) -> Result<P::ChallengeTarget, VerificationError>
    where
        EF: Field + Eq + Hash,
        P: BinaryPolyPolicy<EF>,
    {
        if evaluations.len() != self.coefficients.len() - 1 {
            return Err(invalid("binary Poly sumcheck message width mismatch"));
        }
        let mut values = Vec::with_capacity(self.coefficients.len());
        values.push(evaluations[0].clone());
        values.push(P::add(b, claim, &evaluations[0]));
        values.extend_from_slice(&evaluations[1..]);
        let zero = P::constant(b, 0)?;
        let mut polynomial = vec![zero; self.coefficients.len()];
        for (value, basis) in values.iter().zip(&self.coefficients) {
            for (coefficient, &constant) in polynomial.iter_mut().zip(basis) {
                if constant == 0 {
                    continue;
                }
                let term = if constant == 1 {
                    value.clone()
                } else {
                    P::scale_base_constant(b, value, constant)?
                };
                *coefficient = P::add(b, coefficient, &term);
                b.check_construction_limits()?;
            }
        }
        let mut iter = polynomial.into_iter().rev();
        let mut result = iter.next().expect("checked positive degree");
        for coefficient in iter {
            let product = P::mul(b, &result, challenge);
            result = P::add(b, &product, &coefficient);
            b.check_construction_limits()?;
        }
        Ok(result)
    }
}
