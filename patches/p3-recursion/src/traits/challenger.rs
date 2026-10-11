use alloc::vec::Vec;

use p3_circuit::{CircuitBuilder, CircuitBuilderError};
use p3_field::{ExtensionField, PrimeField64};

use crate::Target;

pub trait RecursiveChallenger<BF: PrimeField64, EF: ExtensionField<BF>> {

    fn observe(&mut self, circuit: &mut CircuitBuilder<EF>, value: Target);

    fn observe_slice(&mut self, circuit: &mut CircuitBuilder<EF>, values: &[Target]) {
        for &value in values {
            self.observe(circuit, value);
        }
    }

    fn observe_seed(&mut self, circuit: &mut CircuitBuilder<EF>, seed: &[BF]) {
        for &value in seed {
            let target = circuit.alloc_const(EF::from(value), "transcript domain separator seed");
            self.observe(circuit, target);
        }
    }

    fn sample(&mut self, circuit: &mut CircuitBuilder<EF>) -> Target;

    fn observe_ext(&mut self, circuit: &mut CircuitBuilder<EF>, value: Target);

    fn observe_ext_slice(&mut self, circuit: &mut CircuitBuilder<EF>, values: &[Target]) {
        for &value in values {
            self.observe_ext(circuit, value);
        }
    }

    fn sample_ext(&mut self, circuit: &mut CircuitBuilder<EF>) -> Target;

    fn sample_ext_vec(&mut self, circuit: &mut CircuitBuilder<EF>, count: usize) -> Vec<Target> {
        (0..count).map(|_| self.sample_ext(circuit)).collect()
    }

    fn sample_bits(
        &mut self,
        circuit: &mut CircuitBuilder<EF>,
        num_bits: usize,
    ) -> Result<Vec<Target>, CircuitBuilderError>;

    fn check_pow_witness(
        &mut self,
        circuit: &mut CircuitBuilder<EF>,
        witness_bits: usize,
        witness: Target,
    ) -> Result<(), CircuitBuilderError>;

    fn clear(&mut self, circuit: &mut CircuitBuilder<EF>);
}
