use p3_air::{SymbolicExpression, SymbolicExpressionExt};
use p3_circuit::Circuit;
use p3_circuit_prover::CircuitVerifier;
use p3_circuit_prover::batch_stark_prover::ProvingMaybeSend;
use p3_circuit_prover::config::StarkField;
use p3_circuit_prover::field_params::ExtractBinomialW;
use p3_commit::Pcs;
use p3_field::{Algebra, BasedVectorSpace, ExtensionField, PrimeField64};
use p3_lookup::logup::LogUpGadget;
use p3_uni_stark::{StarkGenericConfig, Val};

use super::input::legacy_input;
use super::prover::{PreparedProver, prepare_prover};
use super::{PreparedInput, PreparedPcsRecursionBackend, PreparedSource};
use crate::profile::RecursionLayerProfile;
use crate::recursion::{
    PcsRecursionBackend, ProveNextLayerParams, RecursionOutput, VerifierCircuitResult,
    build_next_layer_circuit,
};
use crate::traits::RecursiveAir;
use crate::verifier::VerificationError;

pub struct PreparedLayer<'air, SC, A, B, const D: usize>
where
    SC: StarkGenericConfig + 'static,
    A: RecursiveAir<Val<SC>, SC::Challenge, LogUpGadget>,
    B: PreparedPcsRecursionBackend<SC, A, D>,
{
    air: Option<&'air A>,
    contract: B::InputContract,
    circuit: Circuit<SC::Challenge>,
    verifier_result: B::VerifierResult,
    config: SC,
    backend: B,
    params: ProveNextLayerParams,
    profile: Option<RecursionLayerProfile>,
    prep: PreparedProver<SC>,
}

impl<'air, SC, A, B, const D: usize> PreparedLayer<'air, SC, A, B, D>
where
    p3_uni_stark::PcsProverError<SC>: Send,
    SC::Challenger: p3_challenger::GrindingChallenger<Witness = p3_uni_stark::Val<SC>>,
    SC: StarkGenericConfig + Send + Sync + Clone + 'static,
    A: RecursiveAir<Val<SC>, SC::Challenge, LogUpGadget>,
    B: PreparedPcsRecursionBackend<SC, A, D>,
    Val<SC>: PrimeField64 + StarkField,
    SC::Challenge: BasedVectorSpace<Val<SC>>
        + From<Val<SC>>
        + ExtensionField<Val<SC>>
        + ExtractBinomialW<Val<SC>>,
    SymbolicExpressionExt<Val<SC>, SC::Challenge>:
        Algebra<SymbolicExpression<Val<SC>>> + Algebra<SC::Challenge>,
    <SC::Pcs as Pcs<SC::Challenge, SC::Challenger>>::Domain: Send + Sync,
    SC::Pcs: Sync,
    <SC::Pcs as Pcs<SC::Challenge, SC::Challenger>>::ProverData: Sync,
    <SC::Pcs as Pcs<SC::Challenge, SC::Challenger>>::Commitment: Sync,
{
    pub fn new(
        source: PreparedSource<'air, '_, SC, A>,
        config: SC,
        backend: B,
        params: ProveNextLayerParams,
    ) -> Result<Self, VerificationError> {
        Self::new_inner(source, config, backend, params, None)
    }

    pub fn new_with_profile(
        source: PreparedSource<'air, '_, SC, A>,
        config: SC,
        backend: B,
        profile: RecursionLayerProfile,
    ) -> Result<Self, VerificationError> {
        let params = ProveNextLayerParams {
            table_packing: profile.table_packing.clone(),
            constraint_profile: profile.constraint_profile,
        };
        Self::new_inner(source, config, backend, params, Some(profile))
    }

    fn new_inner(
        source: PreparedSource<'air, '_, SC, A>,
        config: SC,
        backend: B,
        params: ProveNextLayerParams,
        profile: Option<RecursionLayerProfile>,
    ) -> Result<Self, VerificationError> {
        let air = match &source {
            PreparedSource::UniStark { air, .. } => Some(*air),
            PreparedSource::BatchStark { .. } => None,
        };
        let input = source.as_input();
        <B as PreparedPcsRecursionBackend<SC, A, D>>::preflight_input(&backend, &config, &input)?;
        let prev = legacy_input(air, &input)?;
        let contract = backend.capture_input_contract(&config, &prev)?;
        let (circuit, verifier_result) =
            build_next_layer_circuit::<SC, A, B, D>(&prev, &config, &backend)?;
        let prep = prepare_prover::<SC, A, B, D>(&circuit, &config, &backend, &params)?;
        Ok(Self {
            air,
            contract,
            circuit,
            verifier_result,
            config,
            backend,
            params,
            profile,
            prep,
        })
    }

    pub fn check_input(&self, input: &PreparedInput<'_, SC>) -> Result<(), VerificationError> {
        <B as PreparedPcsRecursionBackend<SC, A, D>>::preflight_input(
            &self.backend,
            &self.config,
            input,
        )?;
        self.backend
            .validate_prepared_input(&self.config, &self.contract, input)
    }

    #[tracing::instrument(name = "prove_next_layer", skip_all)]
    pub fn prove(
        &self,
        input: PreparedInput<'_, SC>,
    ) -> Result<RecursionOutput<SC>, VerificationError>
    where
        p3_batch_stark::BatchProof<SC>: ProvingMaybeSend,
    {
        self.check_input(&input)?;
        let prev = legacy_input(self.air, &input)?;
        let public = self.verifier_result.pack_public_inputs(&prev)?;
        let private = self.verifier_result.pack_private_inputs(&prev)?;
        let mut runner = self.circuit.runner();
        runner
            .set_public_inputs(&public)
            .map_err(VerificationError::Circuit)?;
        runner
            .set_private_inputs(&private)
            .map_err(VerificationError::Circuit)?;
        <B as PcsRecursionBackend<SC, A, D>>::set_private_data_for_result(
            &self.backend,
            &self.config,
            &mut runner,
            &self.verifier_result,
            &prev,
        )
        .map_err(|message| VerificationError::InvalidProofShape(message.into()))?;
        let traces = runner.run().map_err(VerificationError::Circuit)?;
        let output = self.prep.prove(&traces)?;
        if let Some(profile) = &self.profile {
            profile.check_proof_shape(&output.0)?;
        }
        Ok(output)
    }

    pub const fn params(&self) -> &ProveNextLayerParams {
        &self.params
    }

    pub const fn profile(&self) -> Option<&RecursionLayerProfile> {
        self.profile.as_ref()
    }

    pub fn verifier(&self) -> CircuitVerifier<SC> {
        self.prep.verifier()
    }
}
