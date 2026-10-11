use alloc::vec;
use alloc::vec::Vec;

use p3_circuit::ops::{Poseidon1Config, Poseidon2Config};
use p3_circuit::{CircuitBuilder, CircuitBuilderError};
use p3_field::{ExtensionField, PrimeField64};

use crate::Target;
use crate::challenger_perm::ChallengerPermConfig;
use crate::traits::RecursiveChallenger;

pub struct CircuitChallenger<const WIDTH: usize, const RATE: usize, C: ChallengerPermConfig> {
    config: C,

    state: Vec<Target>,

    input_buffer: Vec<Target>,

    output_len: usize,

    packed_rate: Vec<Option<Target>>,

    initialized: bool,

    duplexed_once: bool,

    alu_state_packing: bool,
}

impl<const WIDTH: usize, const RATE: usize, C: ChallengerPermConfig>
    CircuitChallenger<WIDTH, RATE, C>
{
    pub const fn new(config: C) -> Self {
        Self {
            config,
            state: Vec::new(),
            input_buffer: Vec::new(),
            output_len: 0,
            packed_rate: Vec::new(),
            initialized: false,
            duplexed_once: false,
            alu_state_packing: false,
        }
    }

    #[must_use]
    pub const fn with_alu_state_packing(mut self) -> Self {
        self.alu_state_packing = true;
        self
    }

    fn pack_limb<BF, EF>(&self, circuit: &mut CircuitBuilder<EF>, coeffs: &[Target]) -> Target
    where
        BF: PrimeField64,
        EF: ExtensionField<BF>,
    {
        if self.alu_state_packing {
            circuit.recompose_base_coeffs_to_ext_via_alu::<BF>(coeffs)
        } else {
            circuit.recompose_base_coeffs_to_ext_with_coeff_lookups::<BF>(coeffs)
        }
        .expect("the challenger's sponge packing needs `enable_recompose`")
    }

    fn unpack_limb<BF, EF>(&self, circuit: &mut CircuitBuilder<EF>, limb: Target) -> Vec<Target>
    where
        BF: PrimeField64,
        EF: ExtensionField<BF>,
    {
        if self.alu_state_packing {
            circuit.decompose_ext_to_base_coeffs_via_alu::<BF>(limb)
        } else {
            circuit.decompose_ext_to_base_coeffs_with_coeff_lookups::<BF>(limb)
        }
        .expect("the challenger's sponge unpacking needs `enable_recompose`")
    }

    pub fn init<BF, EF>(&mut self, circuit: &mut CircuitBuilder<EF>)
    where
        BF: PrimeField64,
        EF: ExtensionField<BF>,
    {
        if self.initialized {
            return;
        }
        let zero = circuit.define_const(EF::ZERO);
        self.state = vec![zero; WIDTH];
        self.initialized = true;
    }

    fn duplexing<BF, EF>(&mut self, circuit: &mut CircuitBuilder<EF>)
    where
        BF: PrimeField64,
        EF: ExtensionField<BF>,
    {
        debug_assert!(self.initialized, "Challenger must be initialized");
        let num_absorbed = self.input_buffer.len();
        debug_assert!(num_absorbed <= RATE, "Input buffer exceeds RATE");

        let p2_config = self.config.as_poseidon2().copied();
        let p1_config = self.config.as_poseidon1().copied();

        for (i, val) in self.input_buffer.drain(..).enumerate() {
            self.state[i] = val;
        }

        if num_absorbed > 0 {
            let zero = circuit.define_const(EF::ZERO);
            for slot in self.state.iter_mut().take(RATE).skip(num_absorbed) {
                *slot = zero;
            }
            self.packed_rate.clear();
        }

        if let Some(cfg) = p2_config {
            if cfg.d() == 1 {
                self.duplexing_base(circuit, cfg, num_absorbed);
            } else {
                self.duplexing_ext::<BF, EF>(circuit, cfg, num_absorbed);
            }
        } else if let Some(cfg) = p1_config {
            if cfg.d() == 1 {
                self.duplexing_base_p1(circuit, cfg, num_absorbed);
            } else {
                self.duplexing_ext_p1::<BF, EF>(circuit, cfg, num_absorbed);
            }
        } else {
            panic!("unsupported challenger permutation");
        }

        self.output_len = RATE;
    }

    fn duplexing_base<EF>(
        &mut self,
        circuit: &mut CircuitBuilder<EF>,
        poseidon2_config: Poseidon2Config,
        absorb_len: usize,
    ) where
        EF: p3_field::Field,
    {
        let (new_start, inputs) = if !self.duplexed_once {
            let inputs: [Option<Target>; 16] =
                core::array::from_fn(|i| if i < RATE { Some(self.state[i]) } else { None });
            (true, inputs)
        } else {
            let inputs: [Option<Target>; 16] =
                core::array::from_fn(|i| if i < RATE { Some(self.state[i]) } else { None });
            (false, inputs)
        };
        self.duplexed_once = true;

        let outputs = circuit
            .add_poseidon2_perm_for_challenger_base(poseidon2_config, new_start, inputs, absorb_len)
            .expect("poseidon2 base permutation should succeed");

        self.state = outputs.to_vec();
    }

    fn duplexing_ext<BF, EF>(
        &mut self,
        circuit: &mut CircuitBuilder<EF>,
        poseidon2_config: Poseidon2Config,
        absorb_len: usize,
    ) where
        BF: PrimeField64,
        EF: ExtensionField<BF>,
    {
        let new_start = !self.duplexed_once;
        self.duplexed_once = true;

        let ext_inputs = self.ext_perm_inputs::<BF, EF>(circuit, new_start, absorb_len);
        let ext_outputs = circuit
            .add_poseidon2_perm_for_challenger(poseidon2_config, new_start, &ext_inputs, absorb_len)
            .expect("poseidon2 permutation should succeed");

        self.packed_rate = ext_outputs[..RATE / EF::DIMENSION]
            .iter()
            .copied()
            .map(Some)
            .collect();
    }

    fn ext_perm_inputs<BF, EF>(
        &self,
        circuit: &mut CircuitBuilder<EF>,
        new_start: bool,
        absorb_len: usize,
    ) -> Vec<Option<Target>>
    where
        BF: PrimeField64,
        EF: ExtensionField<BF>,
    {
        let d = EF::DIMENSION;
        let chained_squeeze = absorb_len == 0 && !new_start;
        debug_assert!(
            chained_squeeze || self.packed_rate.is_empty(),
            "a rate limb fed over CTL must be packed from unpacked coefficients"
        );
        (0..WIDTH / d)
            .map(|limb| {
                (limb < RATE / d && !chained_squeeze).then(|| {
                    self.pack_limb::<BF, EF>(circuit, &self.state[limb * d..(limb + 1) * d])
                })
            })
            .collect()
    }

    fn rate_slot<BF, EF>(&mut self, circuit: &mut CircuitBuilder<EF>, i: usize) -> Target
    where
        BF: PrimeField64,
        EF: ExtensionField<BF>,
    {
        let d = EF::DIMENSION;
        let limb = i / d;
        if let Some(packed) = self.packed_rate.get_mut(limb).and_then(Option::take) {
            let coeffs = self.unpack_limb::<BF, EF>(circuit, packed);
            self.state[limb * d..(limb + 1) * d].copy_from_slice(&coeffs);
        }
        self.state[i]
    }

    fn duplexing_base_p1<EF>(
        &mut self,
        circuit: &mut CircuitBuilder<EF>,
        poseidon1_config: Poseidon1Config,
        absorb_len: usize,
    ) where
        EF: p3_field::Field,
    {
        let new_start = !self.duplexed_once;
        let inputs: [Option<Target>; 16] =
            core::array::from_fn(|i| if i < RATE { Some(self.state[i]) } else { None });
        self.duplexed_once = true;

        let outputs = circuit
            .add_poseidon1_perm_for_challenger_base(poseidon1_config, new_start, inputs, absorb_len)
            .expect("poseidon1 base permutation should succeed");

        self.state = outputs.to_vec();
    }

    fn duplexing_ext_p1<BF, EF>(
        &mut self,
        circuit: &mut CircuitBuilder<EF>,
        poseidon1_config: Poseidon1Config,
        absorb_len: usize,
    ) where
        BF: PrimeField64,
        EF: ExtensionField<BF>,
    {
        let new_start = !self.duplexed_once;
        self.duplexed_once = true;

        let ext_inputs = self.ext_perm_inputs::<BF, EF>(circuit, new_start, absorb_len);
        let ext_outputs = circuit
            .add_poseidon1_perm_for_challenger(poseidon1_config, new_start, &ext_inputs, absorb_len)
            .expect("poseidon1 permutation should succeed");

        self.packed_rate = ext_outputs[..RATE / EF::DIMENSION]
            .iter()
            .copied()
            .map(Some)
            .collect();
    }
}

impl<const WIDTH: usize, const RATE: usize> CircuitChallenger<WIDTH, RATE, Poseidon2Config> {
    pub const fn new_babybear() -> Self {
        Self::new(Poseidon2Config::BABY_BEAR_D4_W16)
    }

    pub const fn new_babybear_base() -> Self {
        Self::new(Poseidon2Config::BABY_BEAR_D1_W16)
    }

    pub const fn new_koalabear() -> Self {
        Self::new(Poseidon2Config::KOALA_BEAR_D4_W16)
    }

    pub const fn new_koalabear_base() -> Self {
        Self::new(Poseidon2Config::KOALA_BEAR_D1_W16)
    }
}

impl CircuitChallenger<8, 4, Poseidon2Config> {
    pub const fn new_goldilocks() -> Self {
        Self::new(Poseidon2Config::GOLDILOCKS_D2_W8)
    }
}

impl<const WIDTH: usize, const RATE: usize> CircuitChallenger<WIDTH, RATE, Poseidon1Config> {
    pub const fn new_babybear_poseidon1_base() -> Self {
        Self::new(Poseidon1Config::BABY_BEAR_D1_W16)
    }

    pub const fn new_koalabear_poseidon1_base() -> Self {
        Self::new(Poseidon1Config::KOALA_BEAR_D1_W16)
    }
}

impl CircuitChallenger<8, 4, Poseidon1Config> {
    pub const fn new_goldilocks_poseidon1() -> Self {
        Self::new(Poseidon1Config::GOLDILOCKS_D2_W8)
    }
}

impl<BF, EF, const WIDTH: usize, const RATE: usize, C: ChallengerPermConfig>
    RecursiveChallenger<BF, EF> for CircuitChallenger<WIDTH, RATE, C>
where
    BF: PrimeField64,
    EF: ExtensionField<BF>,
{
    fn observe(&mut self, circuit: &mut CircuitBuilder<EF>, value: Target) {
        self.init::<BF, EF>(circuit);

        self.output_len = 0;

        self.input_buffer.push(value);

        if self.input_buffer.len() == RATE {
            self.duplexing::<BF, EF>(circuit);
        }
    }

    fn sample(&mut self, circuit: &mut CircuitBuilder<EF>) -> Target {
        self.init::<BF, EF>(circuit);

        if !self.input_buffer.is_empty() || self.output_len == 0 {
            self.duplexing::<BF, EF>(circuit);
        }

        self.output_len = self
            .output_len
            .checked_sub(1)
            .expect("Output buffer should be non-empty after duplexing");
        self.rate_slot::<BF, EF>(circuit, self.output_len)
    }

    fn observe_ext(&mut self, circuit: &mut CircuitBuilder<EF>, value: Target) {
        let coeffs = self.unpack_limb::<BF, EF>(circuit, value);

        for coeff in coeffs {
            self.observe(circuit, coeff);
        }
    }

    fn sample_ext(&mut self, circuit: &mut CircuitBuilder<EF>) -> Target {
        let coeffs: Vec<_> = (0..EF::DIMENSION).map(|_| self.sample(circuit)).collect();

        self.pack_limb::<BF, EF>(circuit, &coeffs)
    }

    fn sample_bits(
        &mut self,
        circuit: &mut CircuitBuilder<EF>,
        num_bits: usize,
    ) -> Result<Vec<Target>, CircuitBuilderError> {
        let bf_bits = BF::bits();
        if num_bits > bf_bits {
            return Err(CircuitBuilderError::BinaryDecompositionTooManyBits {
                expected: bf_bits,
                n_bits: num_bits,
            });
        }
        let base_sample = self.sample(circuit);
        let bits = circuit.decompose_to_bits::<BF>(base_sample, bf_bits)?;
        Ok(bits[..num_bits].to_vec())
    }

    fn check_pow_witness(
        &mut self,
        circuit: &mut CircuitBuilder<EF>,
        witness_bits: usize,
        witness: Target,
    ) -> Result<(), CircuitBuilderError> {
        if witness_bits == 0 {
            return Ok(());
        }

        self.observe(circuit, witness);

        let bits = self.sample_bits(circuit, witness_bits)?;
        for bit in bits {
            circuit.assert_zero(bit);
        }

        Ok(())
    }

    fn clear(&mut self, circuit: &mut CircuitBuilder<EF>) {
        let zero = circuit.define_const(EF::ZERO);
        self.state = vec![zero; WIDTH];
        self.input_buffer.clear();
        self.output_len = 0;
        self.packed_rate.clear();
        self.initialized = true;
        self.duplexed_once = false;
    }
}
