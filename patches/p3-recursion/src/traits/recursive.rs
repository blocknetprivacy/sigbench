use alloc::vec;
use alloc::vec::Vec;

use p3_circuit::CircuitBuilder;
use p3_field::Field;
use p3_lookup::LookupProtocol;
use p3_lookup::logup::LogUpGadget;

use crate::Target;
use crate::verifier::VerificationError;

pub trait Recursive<F: Field> {
    type Input;

    fn new(circuit: &mut CircuitBuilder<F>, input: &Self::Input) -> Self;

    fn get_private_values(_input: &Self::Input) -> Vec<F> {
        vec![]
    }

    fn get_values(input: &Self::Input) -> Vec<F>;
}

pub trait CheckedRecursive<F: Field>: Recursive<F> {
    fn validate_input(input: &Self::Input) -> Result<(), VerificationError>;
}

pub trait PreparedRecursive<F: Field>: Recursive<F> {
    type Shape: Clone + PartialEq;

    fn input_shape(input: &Self::Input) -> Result<Self::Shape, VerificationError>;
}

pub trait RecursiveLookupGadget<F: Field>: LookupProtocol {
    fn verify_terminal_sum_circuit(&self, circuit: &mut CircuitBuilder<F>, terminals: &[Target]);
}

impl<F: Field> RecursiveLookupGadget<F> for LogUpGadget {
    fn verify_terminal_sum_circuit(&self, circuit: &mut CircuitBuilder<F>, terminals: &[Target]) {
        let mut total = circuit.define_const(F::ZERO);
        for terminal in terminals {
            total = circuit.add(total, *terminal);
        }

        circuit.assert_zero(total);
    }
}
