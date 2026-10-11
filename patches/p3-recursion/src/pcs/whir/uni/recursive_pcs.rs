use alloc::vec::Vec;

use p3_challenger::{FieldChallenger, GrindingChallenger};
use p3_circuit::ops::PermConfig;
use p3_circuit::symbolic::RowSelectorsTargets;
use p3_circuit::{CircuitBuilder, CircuitBuilderError, NonPrimitiveOpId};
use p3_commit::{Mmcs, PolynomialSpace};
use p3_dft::TwoAdicSubgroupDft;
use p3_field::coset::TwoAdicMultiplicativeCoset;
use p3_field::{ExtensionField, Field, PrimeCharacteristicRing, PrimeField64, TwoAdicField};
use p3_merkle_tree::MerkleCap;
use p3_sumcheck::layout::Layout;
use p3_sumcheck::strategy::VariableOrder;
use p3_uni_stark::{StarkGenericConfig, Val};
use p3_whir::parameters::{ProtocolParameters, WhirConfig};

use crate::Target;
use crate::challenger::CircuitChallenger;
use crate::challenger_perm::ChallengerPermConfig;
use crate::pcs::whir::params::{WhirVerifierParams, WhirVerifierParamsError};
use crate::pcs::whir::uni::WhirRatePolicy;
use crate::pcs::whir::uni::circuit::verify_whir_uni_circuit;
use crate::pcs::whir::uni::pcs::WhirUniPcs;
use crate::pcs::whir::uni::plan::initial_layout_folding;
use crate::pcs::whir::uni::targets::WhirUniProofTargets;
use crate::traits::{ComsWithOpeningsTargets, Recursive, RecursivePcs};
use crate::types::{OpenedValuesTargetsWithLookups, RecursiveLagrangeSelectors};
use crate::verifier::{ObservableCommitment, VerificationError};

pub(crate) fn validate_round_config_inputs(
    stacked_num_variables: usize,
    protocol_params: &ProtocolParameters,
) -> Result<(), WhirVerifierParamsError> {
    let rate = protocol_params.starting_log_inv_rate;
    let exponent = stacked_num_variables.checked_add(rate).ok_or(
        WhirVerifierParamsError::InvalidStackedArity {
            arity: stacked_num_variables,
            rate,
        },
    )?;
    if exponent >= usize::BITS as usize {
        return Err(WhirVerifierParamsError::InvalidStackedArity {
            arity: stacked_num_variables,
            rate,
        });
    }

    let schedule = protocol_params
        .folding_factor
        .compute_folding_schedule(stacked_num_variables)
        .map_err(|error| {
            WhirVerifierParamsError::InvalidConfig(
                p3_whir::parameters::WhirConfigError::FoldingFactor(error),
            )
        })?;
    let num_rounds = schedule.len() - 1;
    if !protocol_params.round_log_inv_rates.is_empty()
        && protocol_params.round_log_inv_rates.len() != num_rounds
    {
        return Err(WhirVerifierParamsError::InvalidConfig(
            p3_whir::parameters::WhirConfigError::RoundRateCountMismatch {
                expected: num_rounds,
                actual: protocol_params.round_log_inv_rates.len(),
            },
        ));
    }
    if let p3_whir::parameters::FoldingFactor::PerRound(factors) = &protocol_params.folding_factor
        && factors.len() != num_rounds + 1
    {
        return Err(WhirVerifierParamsError::InvalidConfig(
            p3_whir::parameters::WhirConfigError::FoldingFactorCountMismatch {
                expected: num_rounds + 1,
                actual: factors.len(),
            },
        ));
    }
    let mut previous_rate = rate;
    for (round, &factor) in schedule.iter().take(num_rounds).enumerate() {
        let max_next_rate = previous_rate
            .checked_add(factor)
            .ok_or(WhirVerifierParamsError::RateArithmeticOverflow { round })?;
        let next_rate = protocol_params
            .round_log_inv_rates
            .get(round)
            .copied()
            .unwrap_or_else(|| previous_rate + (factor - 1));
        if next_rate > max_next_rate {
            return Err(WhirVerifierParamsError::InvalidConfig(
                p3_whir::parameters::WhirConfigError::RateGrowsDomain { round },
            ));
        }
        previous_rate = next_rate;
    }
    Ok(())
}

#[derive(Clone, Debug)]
pub struct WhirUniVerifierParams<F> {
    protocol_params: ProtocolParameters,
    rate_policy: WhirRatePolicy,
    folding: usize,
    variable_order: VariableOrder,
    permutation_config: PermConfig,
    _marker: core::marker::PhantomData<F>,
}

impl<F: TwoAdicField> WhirUniVerifierParams<F> {
    pub fn new(
        protocol_params: ProtocolParameters,
        variable_order: VariableOrder,
        permutation_config: impl Into<PermConfig>,
    ) -> Result<Self, WhirVerifierParamsError> {
        let folding = initial_layout_folding(&protocol_params.folding_factor)
            .ok_or(WhirVerifierParamsError::UnsupportedFoldingFactor)?;
        Ok(Self {
            protocol_params,
            rate_policy: WhirRatePolicy::Native,
            folding,
            variable_order,
            permutation_config: permutation_config.into(),
            _marker: core::marker::PhantomData,
        })
    }

    pub fn with_rate_policy(
        mut self,
        policy: WhirRatePolicy,
    ) -> Result<Self, WhirVerifierParamsError> {
        policy.validate(&self.protocol_params)?;
        self.rate_policy = policy;
        Ok(self)
    }

    pub fn round_params<EF, Ch>(
        &self,
        stacked_num_variables: usize,
    ) -> Result<WhirVerifierParams<F>, WhirVerifierParamsError>
    where
        EF: ExtensionField<F> + TwoAdicField,
        Ch: FieldChallenger<F> + GrindingChallenger<Witness = F>,
    {
        let protocol = self
            .rate_policy
            .resolve(stacked_num_variables, &self.protocol_params)?;
        let config = WhirConfig::<EF, F, Ch>::new(stacked_num_variables, protocol)?;
        WhirVerifierParams::from_config(&config, self.variable_order, self.permutation_config)
    }

    pub const fn protocol_params(&self) -> &ProtocolParameters {
        &self.protocol_params
    }
    pub const fn rate_policy(&self) -> WhirRatePolicy {
        self.rate_policy
    }
    pub const fn folding(&self) -> usize {
        self.folding
    }
    pub const fn variable_order(&self) -> VariableOrder {
        self.variable_order
    }
    pub const fn permutation_config(&self) -> PermConfig {
        self.permutation_config
    }
}

#[derive(Clone, Debug, Default)]
pub struct DummyChallenger<F>(core::marker::PhantomData<F>);

impl<F: p3_field::Field> p3_challenger::CanObserve<F> for DummyChallenger<F> {
    fn observe(&mut self, _value: F) {
        unreachable!("DummyChallenger only satisfies WhirConfig's phantom bound")
    }
}
impl<F: p3_field::Field> p3_challenger::CanSample<F> for DummyChallenger<F> {
    fn sample(&mut self) -> F {
        unreachable!("DummyChallenger only satisfies WhirConfig's phantom bound")
    }
}
impl<F: p3_field::Field> p3_challenger::CanSampleBits<usize> for DummyChallenger<F> {
    fn sample_bits(&mut self, _bits: usize) -> usize {
        unreachable!("DummyChallenger only satisfies WhirConfig's phantom bound")
    }
}
impl<F: p3_field::Field> p3_challenger::GrindingChallenger for DummyChallenger<F> {
    type Witness = F;
    fn grind(&mut self, _bits: usize) -> Self::Witness {
        unreachable!("DummyChallenger only satisfies WhirConfig's phantom bound")
    }
}
impl<F: p3_field::PrimeField64> p3_challenger::FieldChallenger<F> for DummyChallenger<F> {}

impl<F: p3_field::Field> Recursive<F> for () {
    type Input = ();

    fn new(_circuit: &mut CircuitBuilder<F>, _input: &Self::Input) -> Self {}

    fn get_values(_input: &Self::Input) -> Vec<F> {
        Vec::new()
    }
}

const NO_RANDOM_OPENED_VALUES: &[Vec<Vec<Vec<Target>>>] = &[];

impl<SC, Dft, MT, Comm, L, const DIGEST_ELEMS: usize>
    RecursivePcs<
        SC,
        (),
        WhirUniProofTargets<Val<SC>, SC::Challenge, MT, DIGEST_ELEMS>,
        Comm,
        TwoAdicMultiplicativeCoset<Val<SC>>,
    > for WhirUniPcs<SC::Challenge, Val<SC>, Dft, MT, SC::Challenger, L>
where
    SC: StarkGenericConfig,
    Val<SC>: TwoAdicField + PrimeField64 + Ord,
    SC::Challenge: TwoAdicField + ExtensionField<Val<SC>>,
    Dft: TwoAdicSubgroupDft<Val<SC>> + Clone,
    MT: Mmcs<Val<SC>, Commitment = MerkleCap<Val<SC>, [Val<SC>; DIGEST_ELEMS]>> + Clone,
    Comm: Recursive<SC::Challenge> + ObservableCommitment,
    L: Layout<Val<SC>, SC::Challenge>,
{
    type VerifierParams = WhirUniVerifierParams<Val<SC>>;
    type RecursiveProof = WhirUniProofTargets<Val<SC>, SC::Challenge, MT, DIGEST_ELEMS>;

    const PRE_OBSERVES_OPENED_VALUES: bool = false;

    fn get_challenges_circuit<const WIDTH: usize, const RATE: usize, C: ChallengerPermConfig>(
        _circuit: &mut CircuitBuilder<SC::Challenge>,
        _challenger: &mut CircuitChallenger<WIDTH, RATE, C>,
        _proof_targets: &Self::RecursiveProof,
        _opened_values: &OpenedValuesTargetsWithLookups<SC>,
        _params: &Self::VerifierParams,
    ) -> Result<Vec<Target>, CircuitBuilderError> {
        Ok(Vec::new())
    }

    fn verify_circuit<const WIDTH: usize, const RATE: usize, C: ChallengerPermConfig>(
        &self,
        circuit: &mut CircuitBuilder<SC::Challenge>,
        _challenges: &[Target],
        challenger: &mut CircuitChallenger<WIDTH, RATE, C>,
        commitments_with_opening_points: &ComsWithOpeningsTargets<
            Comm,
            TwoAdicMultiplicativeCoset<Val<SC>>,
        >,
        opening_proof: &Self::RecursiveProof,
        params: &Self::VerifierParams,
    ) -> Result<Vec<NonPrimitiveOpId>, VerificationError> {
        verify_whir_uni_circuit::<Val<SC>, SC::Challenge, _, Comm>(
            circuit,
            challenger,
            params,
            commitments_with_opening_points,
            &opening_proof.rounds,
        )
    }

    fn selectors_at_point_circuit(
        &self,
        circuit: &mut CircuitBuilder<SC::Challenge>,
        domain: &TwoAdicMultiplicativeCoset<Val<SC>>,
        point: &Target,
    ) -> RecursiveLagrangeSelectors {
        let shift_inv = circuit.alloc_const(
            SC::Challenge::from(domain.shift_inverse()),
            "whir shift_inv",
        );
        let one = circuit.alloc_const(SC::Challenge::from(Val::<SC>::ONE), "whir one");
        let subgroup_gen_inv = circuit.alloc_const(
            SC::Challenge::from(domain.subgroup_generator().inverse()),
            "whir subgroup_gen_inv",
        );

        let unshifted_point = circuit.alloc_mul(shift_inv, *point, "whir unshifted_point");
        let us_exp = circuit.exp_power_of_2(unshifted_point, domain.log_size());
        let z_h = circuit.alloc_sub(us_exp, one, "whir z_h");

        let us_minus_one = circuit.alloc_sub(unshifted_point, one, "whir us_minus_one");
        let us_minus_gen_inv =
            circuit.alloc_sub(unshifted_point, subgroup_gen_inv, "whir us_minus_gen_inv");

        RecursiveLagrangeSelectors {
            row_selectors: RowSelectorsTargets {
                is_first_row: circuit.alloc_div(z_h, us_minus_one, "whir is_first_row"),
                is_last_row: circuit.alloc_div(z_h, us_minus_gen_inv, "whir is_last_row"),
                is_transition: us_minus_gen_inv,
            },
            inv_vanishing: circuit.alloc_div(one, z_h, "whir inv_vanishing"),
        }
    }

    fn evaluate_periodic_columns_at_point_circuit(
        &self,
        circuit: &mut CircuitBuilder<SC::Challenge>,
        domain: &TwoAdicMultiplicativeCoset<Val<SC>>,
        periodic_columns: &[Vec<Val<SC>>],
        point: Target,
    ) -> Result<Vec<Target>, VerificationError> {
        crate::verifier::evaluate_periodic_columns_circuit(circuit, domain, periodic_columns, point)
    }

    fn create_disjoint_domain(
        &self,
        trace_domain: TwoAdicMultiplicativeCoset<Val<SC>>,
        degree: usize,
    ) -> TwoAdicMultiplicativeCoset<Val<SC>> {
        trace_domain.create_disjoint_domain(degree)
    }

    fn split_domains(
        &self,
        trace_domain: &TwoAdicMultiplicativeCoset<Val<SC>>,
        degree: usize,
    ) -> Vec<TwoAdicMultiplicativeCoset<Val<SC>>> {
        trace_domain.split_domains(degree)
    }

    fn log_size(&self, trace_domain: &TwoAdicMultiplicativeCoset<Val<SC>>) -> usize {
        trace_domain.log_size()
    }

    fn first_point(&self, trace_domain: &TwoAdicMultiplicativeCoset<Val<SC>>) -> SC::Challenge {
        SC::Challenge::from(trace_domain.first_point())
    }

    fn get_fri_random_opened_values(_proof: &Self::RecursiveProof) -> &[Vec<Vec<Vec<Target>>>] {
        NO_RANDOM_OPENED_VALUES
    }
}
