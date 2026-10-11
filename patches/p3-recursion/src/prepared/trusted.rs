use alloc::string::ToString;
use alloc::vec;

use p3_air::{SymbolicExpression, SymbolicExpressionExt};
use p3_circuit::{
    Circuit, CircuitBuilder, StateTransitionError, StateTransitionLayout, StatementField,
    StatementSchema,
};
use p3_circuit_prover::batch_stark_prover::ProvingMaybeSend;
use p3_circuit_prover::config::StarkField;
use p3_circuit_prover::field_params::ExtractBinomialW;
use p3_circuit_prover::{BatchStarkProof, CircuitVerifier, StatementPreprocessor};
use p3_commit::{Pcs, PolynomialSpace};
use p3_field::{Algebra, BasedVectorSpace, ExtensionField, PrimeField64};
use p3_lookup::logup::LogUpGadget;
use p3_uni_stark::{Proof, StarkGenericConfig, Val};

use super::prover::{PreparedProver, prepare_prover_with_statement};
use super::{
    NativeCommitment, PreparedInput, PreparedPcsRecursionBackend, TrustedChildStatementLayout,
    TrustedPcsRecursionBackend, VerifiedStatementTargets,
};
use crate::recursion::{
    BatchOnly, PcsRecursionBackend, ProveNextLayerParams, RecursionInput, RecursionOutput,
    VerifierCircuitResult,
};
use crate::traits::RecursiveAir;
use crate::verifier::VerificationError;

pub enum TrustedPreparedSource<'air, 'p, SC, A>
where
    SC: StarkGenericConfig + 'static,
{
    UniStark {
        config: SC,
        air: &'air A,
        preprocessed_commit: Option<NativeCommitment<SC>>,
        proof: &'p Proof<SC>,
        public_inputs: &'p [Val<SC>],
    },
    BatchStark {
        verifier: CircuitVerifier<SC>,
        proof: &'p BatchStarkProof<SC>,
        statement: &'p [Val<SC>],
    },
}

pub enum TrustedPreparedInput<'p, SC>
where
    SC: StarkGenericConfig + 'static,
{
    UniStark {
        proof: &'p Proof<SC>,
        public_inputs: &'p [Val<SC>],
    },
    BatchStark {
        proof: &'p BatchStarkProof<SC>,
        statement: &'p [Val<SC>],
    },
}

impl<SC> Clone for TrustedPreparedInput<'_, SC>
where
    SC: StarkGenericConfig + 'static,
{
    fn clone(&self) -> Self {
        *self
    }
}

impl<SC> Copy for TrustedPreparedInput<'_, SC> where SC: StarkGenericConfig + 'static {}

impl<SC> TrustedPreparedInput<'_, SC>
where
    SC: StarkGenericConfig + 'static,
{
    const fn statement_values(&self) -> &[Val<SC>] {
        match self {
            Self::UniStark { public_inputs, .. } => public_inputs,
            Self::BatchStark { statement, .. } => statement,
        }
    }
}

enum TrustedChildAuthority<'air, SC, A>
where
    SC: StarkGenericConfig + 'static,
{
    Uni {
        config: SC,
        air: &'air A,
        preprocessed_commit: Option<NativeCommitment<SC>>,
    },
    Batch {
        verifier: CircuitVerifier<SC>,
    },
}

struct TrustedConstruction<'air, 'p, SC, A>
where
    SC: StarkGenericConfig + 'static,
{
    authority: TrustedChildAuthority<'air, SC, A>,
    input: TrustedPreparedInput<'p, SC>,
}

impl<'air, 'p, SC, A> TrustedConstruction<'air, 'p, SC, A>
where
    SC: StarkGenericConfig + 'static,
    Val<SC>: PrimeField64 + StarkField,
    SC::Challenge: ExtensionField<Val<SC>> + ExtractBinomialW<Val<SC>>,
    SymbolicExpressionExt<Val<SC>, SC::Challenge>:
        Algebra<SymbolicExpression<Val<SC>>> + Algebra<SC::Challenge>,
{
    fn new(source: TrustedPreparedSource<'air, 'p, SC, A>) -> Result<Self, VerificationError> {
        match source {
            TrustedPreparedSource::UniStark {
                config,
                air,
                preprocessed_commit,
                proof,
                public_inputs,
            } => Ok(Self {
                authority: TrustedChildAuthority::Uni {
                    config,
                    air,
                    preprocessed_commit,
                },
                input: TrustedPreparedInput::UniStark {
                    proof,
                    public_inputs,
                },
            }),
            TrustedPreparedSource::BatchStark {
                verifier,
                proof,
                statement,
            } => Ok(Self {
                authority: TrustedChildAuthority::Batch { verifier },
                input: TrustedPreparedInput::BatchStark { proof, statement },
            }),
        }
    }
}

impl<'air, SC, A> TrustedChildAuthority<'air, SC, A>
where
    SC: StarkGenericConfig + 'static,
    A: RecursiveAir<Val<SC>, SC::Challenge, LogUpGadget>,
    Val<SC>: PrimeField64 + StarkField,
    SymbolicExpressionExt<Val<SC>, SC::Challenge>:
        Algebra<SymbolicExpression<Val<SC>>> + Algebra<SC::Challenge>,
{
    fn config(&self) -> &SC {
        match self {
            Self::Uni { config, .. } => config,
            Self::Batch { verifier, .. } => verifier.config(),
        }
    }

    fn expected_preprocessed(&self) -> Option<&NativeCommitment<SC>> {
        match self {
            Self::Uni {
                preprocessed_commit,
                ..
            } => preprocessed_commit.as_ref(),
            Self::Batch { verifier, .. } => verifier
                .common_data()
                .preprocessed
                .as_ref()
                .map(|global| &global.commitment),
        }
    }

    fn recursion_input<'a, 'p: 'a>(
        &'a self,
        input: &'a TrustedPreparedInput<'p, SC>,
    ) -> Result<RecursionInput<'a, SC, A>, VerificationError>
    where
        SC::Challenger: p3_challenger::GrindingChallenger<Witness = p3_uni_stark::Val<SC>>,
        NativeCommitment<SC>: Clone,
    {
        match (self, input) {
            (
                Self::Uni {
                    air,
                    preprocessed_commit,
                    ..
                },
                TrustedPreparedInput::UniStark {
                    proof,
                    public_inputs,
                },
            ) => Ok(RecursionInput::UniStark {
                proof,
                air,
                public_inputs: public_inputs.to_vec(),
                preprocessed_commit: preprocessed_commit.clone(),
            }),
            (Self::Batch { verifier }, TrustedPreparedInput::BatchStark { proof, statement }) => {
                verifier
                    .verify(proof, statement)
                    .map_err(|error| VerificationError::InvalidProofShape(error.to_string()))?;
                let table_public_inputs = verifier
                    .table_public_values(statement)
                    .map_err(|error| VerificationError::InvalidProofShape(error.to_string()))?;
                Ok(RecursionInput::BatchStark {
                    proof,
                    common_data: verifier.common_data(),
                    table_public_inputs,
                })
            }
            _ => Err(VerificationError::PreparedInputMismatch {
                component: "input.kind",
            }),
        }
    }
}

pub struct TrustedPreparedLayer<'air, InSC, OutSC, A, B, const D: usize>
where
    InSC: StarkGenericConfig + 'static,
    OutSC: StarkGenericConfig<Challenge = InSC::Challenge> + 'static,
    A: RecursiveAir<Val<InSC>, InSC::Challenge, LogUpGadget>,
    B: TrustedPcsRecursionBackend<InSC, A, D>,
{
    child: TrustedChildAuthority<'air, InSC, A>,
    contract: B::InputContract,
    circuit: Circuit<InSC::Challenge>,
    result: B::VerifierResult,
    backend: B,
    params: ProveNextLayerParams,
    prep: PreparedProver<OutSC>,
}

impl<'air, InSC, OutSC, A, B, const D: usize> TrustedPreparedLayer<'air, InSC, OutSC, A, B, D>
where
    p3_uni_stark::PcsProverError<OutSC>: Send,
    OutSC::Challenger: p3_challenger::GrindingChallenger<Witness = p3_uni_stark::Val<OutSC>>,
    InSC::Challenger: p3_challenger::GrindingChallenger<Witness = p3_uni_stark::Val<InSC>>,
    InSC: StarkGenericConfig + Send + Sync + Clone + 'static,
    OutSC: StarkGenericConfig<Challenge = InSC::Challenge> + Send + Sync + Clone + 'static,
    A: RecursiveAir<Val<InSC>, InSC::Challenge, LogUpGadget>,
    B: TrustedPcsRecursionBackend<InSC, A, D> + PcsRecursionBackend<OutSC, BatchOnly, D>,
    Val<InSC>: PrimeField64 + StarkField,
    Val<OutSC>: PrimeField64 + StarkField,
    InSC::Challenge: BasedVectorSpace<Val<InSC>>
        + BasedVectorSpace<Val<OutSC>>
        + From<Val<InSC>>
        + From<Val<OutSC>>
        + ExtensionField<Val<InSC>>
        + ExtensionField<Val<OutSC>>
        + ExtractBinomialW<Val<InSC>>
        + ExtractBinomialW<Val<OutSC>>,
    SymbolicExpressionExt<Val<InSC>, InSC::Challenge>:
        Algebra<SymbolicExpression<Val<InSC>>> + Algebra<InSC::Challenge>,
    SymbolicExpressionExt<Val<OutSC>, OutSC::Challenge>:
        Algebra<SymbolicExpression<Val<OutSC>>> + Algebra<OutSC::Challenge>,
    <InSC::Pcs as Pcs<InSC::Challenge, InSC::Challenger>>::Domain:
        PolynomialSpace<Val = Val<OutSC>>,
    <InSC::Pcs as Pcs<InSC::Challenge, InSC::Challenger>>::Commitment: Clone,
    <OutSC::Pcs as Pcs<OutSC::Challenge, OutSC::Challenger>>::Domain: Send + Sync,
    OutSC::Pcs: Sync,
    <OutSC::Pcs as Pcs<OutSC::Challenge, OutSC::Challenger>>::ProverData: Sync,
    <OutSC::Pcs as Pcs<OutSC::Challenge, OutSC::Challenger>>::Commitment: Sync,
    StatementPreprocessor: p3_circuit_prover::common::NpoPreprocessor<Val<OutSC>>,
{
    #[allow(
        clippy::needless_pass_by_value,
        reason = "prepared-owner constructors deliberately consume output configuration authority"
    )]
    pub fn new(
        source: TrustedPreparedSource<'air, '_, InSC, A>,
        output_config: OutSC,
        backend: B,
        params: ProveNextLayerParams,
    ) -> Result<Self, VerificationError> {
        match &source {
            TrustedPreparedSource::UniStark {
                config,
                proof,
                public_inputs,
                preprocessed_commit,
                ..
            } => <B as PreparedPcsRecursionBackend<InSC, A, D>>::preflight_input(
                &backend,
                config,
                &PreparedInput::UniStark {
                    proof,
                    public_inputs,
                    preprocessed_commit: preprocessed_commit.as_ref(),
                },
            )?,
            TrustedPreparedSource::BatchStark {
                verifier, proof, ..
            } => backend.preflight_trusted_batch(verifier, proof)?,
        }
        let statement_layout = match &source {
            TrustedPreparedSource::UniStark { public_inputs, .. } => {
                let schema =
                    StatementSchema::try_new(vec![StatementField::Base; public_inputs.len()])
                        .map_err(|error| VerificationError::InvalidProofShape(error.to_string()))?;
                super::TrustedChildStatementLayout::uni(public_inputs.len(), schema)?
            }
            TrustedPreparedSource::BatchStark { verifier, .. } => {
                super::TrustedChildStatementLayout::batch(verifier.statement_layout())
            }
        };
        let source = TrustedConstruction::<InSC, A>::new(source)?;
        let prev = source.authority.recursion_input(&source.input)?;
        let contract = capture_trusted_input_contract::<InSC, A, B, D>(
            &backend,
            &source.authority,
            &source.input,
            &prev,
        )?;

        let mut builder = CircuitBuilder::new();
        <B as PcsRecursionBackend<InSC, A, D>>::prepare_circuit(
            &backend,
            source.authority.config(),
            &mut builder,
        )?;
        let result = match (&source.authority, &source.input) {
            (TrustedChildAuthority::Uni { .. }, TrustedPreparedInput::UniStark { .. }) => {
                backend.build_verifier_circuit(&prev, source.authority.config(), &mut builder)?
            }
            (
                TrustedChildAuthority::Batch { verifier, .. },
                TrustedPreparedInput::BatchStark { proof, statement },
            ) => backend.build_trusted_batch_verifier_circuit(
                verifier,
                proof,
                statement,
                &mut builder,
            )?,
            _ => unreachable!(),
        };
        backend.constrain_trusted_preprocessing(
            &mut builder,
            &result,
            source.authority.expected_preprocessed(),
        )?;
        backend
            .verified_statement_targets(&result, &statement_layout, &builder)?
            .install::<Val<OutSC>>(&mut builder)?;
        let circuit = builder.build().map_err(VerificationError::CircuitBuilder)?;
        let prep = prepare_prover_with_statement::<OutSC, BatchOnly, B, D>(
            &circuit,
            &output_config,
            &backend,
            &params,
            statement_layout.schema(),
        )?;
        Ok(Self {
            child: source.authority,
            contract,
            circuit,
            result,
            backend,
            params,
            prep,
        })
    }

    pub fn check_input(
        &self,
        input: &TrustedPreparedInput<'_, InSC>,
    ) -> Result<(), VerificationError> {
        preflight_trusted_input::<InSC, A, B, D>(&self.backend, &self.child, input)?;
        validate_trusted_input_contract::<InSC, A, B, D>(
            &self.backend,
            &self.child,
            &self.contract,
            input,
        )
    }

    pub fn prove(
        &self,
        input: TrustedPreparedInput<'_, InSC>,
    ) -> Result<RecursionOutput<OutSC>, VerificationError>
    where
        p3_batch_stark::BatchProof<OutSC>: ProvingMaybeSend,
    {
        self.check_input(&input)?;
        let prev = self.child.recursion_input(&input)?;
        let public = self.result.pack_public_inputs(&prev)?;
        let private = self.result.pack_private_inputs(&prev)?;
        let mut runner = self.circuit.runner();
        runner
            .set_public_inputs(&public)
            .map_err(VerificationError::Circuit)?;
        runner
            .set_private_inputs(&private)
            .map_err(VerificationError::Circuit)?;
        match (&self.child, &input) {
            (TrustedChildAuthority::Uni { .. }, TrustedPreparedInput::UniStark { .. }) => {
                <B as PcsRecursionBackend<InSC, A, D>>::set_private_data_for_result(
                    &self.backend,
                    self.child.config(),
                    &mut runner,
                    &self.result,
                    &prev,
                )
                .map_err(|message| VerificationError::InvalidProofShape(message.into()))?;
            }
            (
                TrustedChildAuthority::Batch { verifier, .. },
                TrustedPreparedInput::BatchStark { proof, statement },
            ) => self.backend.set_private_data_for_trusted_batch(
                verifier,
                proof,
                statement,
                &mut runner,
                self.result.op_ids(),
            )?,
            _ => unreachable!(),
        }
        let traces = runner.run().map_err(VerificationError::Circuit)?;
        self.prep.prove(&traces)
    }

    pub const fn params(&self) -> &ProveNextLayerParams {
        &self.params
    }

    pub fn verifier(&self) -> CircuitVerifier<OutSC> {
        self.prep.verifier()
    }
}

pub struct TrustedPreparedAggregation<'left_air, 'right_air, InSC, OutSC, A1, A2, B, const D: usize>
where
    InSC: StarkGenericConfig + 'static,
    OutSC: StarkGenericConfig<Challenge = InSC::Challenge> + 'static,
    A1: RecursiveAir<Val<InSC>, InSC::Challenge, LogUpGadget>,
    A2: RecursiveAir<Val<InSC>, InSC::Challenge, LogUpGadget>,
    B: TrustedPcsRecursionBackend<InSC, A1, D> + TrustedPcsRecursionBackend<InSC, A2, D>,
{
    left: TrustedChildAuthority<'left_air, InSC, A1>,
    right: TrustedChildAuthority<'right_air, InSC, A2>,
    left_contract: <B as PreparedPcsRecursionBackend<InSC, A1, D>>::InputContract,
    right_contract: <B as PreparedPcsRecursionBackend<InSC, A2, D>>::InputContract,
    circuit: Circuit<InSC::Challenge>,
    left_result: <B as PcsRecursionBackend<InSC, A1, D>>::VerifierResult,
    right_result: <B as PcsRecursionBackend<InSC, A2, D>>::VerifierResult,
    backend: B,
    params: ProveNextLayerParams,
    prep: PreparedProver<OutSC>,
    state_transition_layout: Option<StateTransitionLayout>,
}

impl<'left_air, 'right_air, InSC, OutSC, A1, A2, B, const D: usize>
    TrustedPreparedAggregation<'left_air, 'right_air, InSC, OutSC, A1, A2, B, D>
where
    p3_uni_stark::PcsProverError<OutSC>: Send,
    OutSC::Challenger: p3_challenger::GrindingChallenger<Witness = p3_uni_stark::Val<OutSC>>,
    InSC::Challenger: p3_challenger::GrindingChallenger<Witness = p3_uni_stark::Val<InSC>>,
    InSC: StarkGenericConfig + Send + Sync + Clone + 'static,
    OutSC: StarkGenericConfig<Challenge = InSC::Challenge> + Send + Sync + Clone + 'static,
    A1: RecursiveAir<Val<InSC>, InSC::Challenge, LogUpGadget>,
    A2: RecursiveAir<Val<InSC>, InSC::Challenge, LogUpGadget>,
    B: TrustedPcsRecursionBackend<InSC, A1, D>
        + TrustedPcsRecursionBackend<InSC, A2, D>
        + PcsRecursionBackend<OutSC, BatchOnly, D>,
    Val<InSC>: PrimeField64 + StarkField,
    Val<OutSC>: PrimeField64 + StarkField,
    InSC::Challenge: BasedVectorSpace<Val<InSC>>
        + BasedVectorSpace<Val<OutSC>>
        + From<Val<InSC>>
        + From<Val<OutSC>>
        + ExtensionField<Val<InSC>>
        + ExtensionField<Val<OutSC>>
        + ExtractBinomialW<Val<InSC>>
        + ExtractBinomialW<Val<OutSC>>,
    SymbolicExpressionExt<Val<InSC>, InSC::Challenge>:
        Algebra<SymbolicExpression<Val<InSC>>> + Algebra<InSC::Challenge>,
    SymbolicExpressionExt<Val<OutSC>, OutSC::Challenge>:
        Algebra<SymbolicExpression<Val<OutSC>>> + Algebra<OutSC::Challenge>,
    <InSC::Pcs as Pcs<InSC::Challenge, InSC::Challenger>>::Domain:
        PolynomialSpace<Val = Val<OutSC>>,
    <InSC::Pcs as Pcs<InSC::Challenge, InSC::Challenger>>::Commitment: Clone,
    <OutSC::Pcs as Pcs<OutSC::Challenge, OutSC::Challenger>>::Domain: Send + Sync,
    OutSC::Pcs: Sync,
    <OutSC::Pcs as Pcs<OutSC::Challenge, OutSC::Challenger>>::ProverData: Sync,
    <OutSC::Pcs as Pcs<OutSC::Challenge, OutSC::Challenger>>::Commitment: Sync,
    StatementPreprocessor: p3_circuit_prover::common::NpoPreprocessor<Val<OutSC>>,
{
    #[allow(
        clippy::needless_pass_by_value,
        reason = "prepared-owner constructors deliberately consume output configuration authority"
    )]
    pub fn new(
        left: TrustedPreparedSource<'left_air, '_, InSC, A1>,
        right: TrustedPreparedSource<'right_air, '_, InSC, A2>,
        output_config: OutSC,
        backend: B,
        params: ProveNextLayerParams,
    ) -> Result<Self, VerificationError> {
        Self::new_with_composition(left, right, output_config, backend, params, None)
    }

    pub fn new_state_transition(
        left: TrustedPreparedSource<'left_air, '_, InSC, A1>,
        right: TrustedPreparedSource<'right_air, '_, InSC, A2>,
        output_config: OutSC,
        backend: B,
        params: ProveNextLayerParams,
        layout: StateTransitionLayout,
    ) -> Result<Self, VerificationError> {
        Self::new_with_composition(left, right, output_config, backend, params, Some(layout))
    }

    #[allow(
        clippy::needless_pass_by_value,
        reason = "shared constructor consumes output configuration authority"
    )]
    fn new_with_composition(
        left: TrustedPreparedSource<'left_air, '_, InSC, A1>,
        right: TrustedPreparedSource<'right_air, '_, InSC, A2>,
        output_config: OutSC,
        backend: B,
        params: ProveNextLayerParams,
        state_transition_layout: Option<StateTransitionLayout>,
    ) -> Result<Self, VerificationError> {
        preflight_trusted_source::<InSC, A1, B, D>(&backend, &left)?;
        preflight_trusted_source::<InSC, A2, B, D>(&backend, &right)?;

        let left = TrustedConstruction::<InSC, A1>::new(left)?;
        let right = TrustedConstruction::<InSC, A2>::new(right)?;
        let left_statement = trusted_child_statement_layout(&left.authority)?;
        let right_statement = trusted_child_statement_layout(&right.authority)?;
        if let Some(layout) = &state_transition_layout {
            if left_statement.schema() != layout.statement_schema() {
                return Err(StateTransitionError::ChildSchemaMismatch { child: 0 }.into());
            }
            if right_statement.schema() != layout.statement_schema() {
                return Err(StateTransitionError::ChildSchemaMismatch { child: 1 }.into());
            }
            layout.validate_field_pair::<Val<InSC>, Val<OutSC>>()?;
        }
        let left_prev = left.authority.recursion_input(&left.input)?;
        let right_prev = right.authority.recursion_input(&right.input)?;
        let left_contract = capture_trusted_input_contract::<InSC, A1, B, D>(
            &backend,
            &left.authority,
            &left.input,
            &left_prev,
        )?;
        let right_contract = capture_trusted_input_contract::<InSC, A2, B, D>(
            &backend,
            &right.authority,
            &right.input,
            &right_prev,
        )?;
        if let Some(layout) = &state_transition_layout {
            layout.compose_statement(
                left.input.statement_values(),
                right.input.statement_values(),
            )?;
        }

        let mut builder = CircuitBuilder::new();
        <B as PcsRecursionBackend<InSC, A1, D>>::prepare_circuit(
            &backend,
            left.authority.config(),
            &mut builder,
        )?;
        <B as PcsRecursionBackend<InSC, A2, D>>::prepare_circuit(
            &backend,
            right.authority.config(),
            &mut builder,
        )?;
        let left_result = build_trusted_child::<InSC, A1, B, D>(
            &backend,
            &left.authority,
            &left.input,
            &left_prev,
            &mut builder,
        )?;
        let right_result = build_trusted_child::<InSC, A2, B, D>(
            &backend,
            &right.authority,
            &right.input,
            &right_prev,
            &mut builder,
        )?;
        <B as TrustedPcsRecursionBackend<InSC, A1, D>>::constrain_trusted_preprocessing(
            &backend,
            &mut builder,
            &left_result,
            left.authority.expected_preprocessed(),
        )?;
        <B as TrustedPcsRecursionBackend<InSC, A2, D>>::constrain_trusted_preprocessing(
            &backend,
            &mut builder,
            &right_result,
            right.authority.expected_preprocessed(),
        )?;
        let left_targets =
            <B as TrustedPcsRecursionBackend<InSC, A1, D>>::verified_statement_targets(
                &backend,
                &left_result,
                &left_statement,
                &builder,
            )?;
        let right_targets =
            <B as TrustedPcsRecursionBackend<InSC, A2, D>>::verified_statement_targets(
                &backend,
                &right_result,
                &right_statement,
                &builder,
            )?;
        let output_schema = if let Some(layout) = &state_transition_layout {
            VerifiedStatementTargets::install_state_transition::<Val<InSC>>(
                left_targets,
                right_targets,
                &mut builder,
                layout,
            )?;
            layout.statement_schema().clone()
        } else {
            VerifiedStatementTargets::install_ordered_aggregation::<Val<InSC>>(
                left_targets,
                right_targets,
                &mut builder,
            )?
            .output()
            .clone()
        };
        let circuit = builder.build().map_err(VerificationError::CircuitBuilder)?;
        let prep = prepare_prover_with_statement::<OutSC, BatchOnly, B, D>(
            &circuit,
            &output_config,
            &backend,
            &params,
            &output_schema,
        )?;

        Ok(Self {
            left: left.authority,
            right: right.authority,
            left_contract,
            right_contract,
            circuit,
            left_result,
            right_result,
            backend,
            params,
            prep,
            state_transition_layout,
        })
    }

    pub fn check_inputs(
        &self,
        left: &TrustedPreparedInput<'_, InSC>,
        right: &TrustedPreparedInput<'_, InSC>,
    ) -> Result<(), VerificationError> {
        preflight_trusted_input::<InSC, A1, B, D>(&self.backend, &self.left, left)?;
        preflight_trusted_input::<InSC, A2, B, D>(&self.backend, &self.right, right)?;
        validate_trusted_input_contract::<InSC, A1, B, D>(
            &self.backend,
            &self.left,
            &self.left_contract,
            left,
        )?;
        validate_trusted_input_contract::<InSC, A2, B, D>(
            &self.backend,
            &self.right,
            &self.right_contract,
            right,
        )?;
        if let Some(layout) = &self.state_transition_layout {
            layout.compose_statement(left.statement_values(), right.statement_values())?;
        }
        Ok(())
    }

    pub fn prove(
        &self,
        left: TrustedPreparedInput<'_, InSC>,
        right: TrustedPreparedInput<'_, InSC>,
    ) -> Result<RecursionOutput<OutSC>, VerificationError>
    where
        p3_batch_stark::BatchProof<OutSC>: ProvingMaybeSend,
    {
        self.check_inputs(&left, &right)?;
        let left_prev = self.left.recursion_input(&left)?;
        let right_prev = self.right.recursion_input(&right)?;
        let mut public = self.left_result.pack_public_inputs(&left_prev)?;
        public.extend(self.right_result.pack_public_inputs(&right_prev)?);
        let mut private = self.left_result.pack_private_inputs(&left_prev)?;
        private.extend(self.right_result.pack_private_inputs(&right_prev)?);
        let mut runner = self.circuit.runner();
        runner
            .set_public_inputs(&public)
            .map_err(VerificationError::Circuit)?;
        runner
            .set_private_inputs(&private)
            .map_err(VerificationError::Circuit)?;
        set_trusted_child_private::<InSC, A1, B, D>(
            &self.backend,
            &self.left,
            &left,
            &left_prev,
            &self.left_result,
            &mut runner,
        )?;
        set_trusted_child_private::<InSC, A2, B, D>(
            &self.backend,
            &self.right,
            &right,
            &right_prev,
            &self.right_result,
            &mut runner,
        )?;
        let traces = runner.run().map_err(VerificationError::Circuit)?;
        self.prep.prove(&traces)
    }

    pub const fn params(&self) -> &ProveNextLayerParams {
        &self.params
    }

    pub const fn state_transition_layout(&self) -> Option<&StateTransitionLayout> {
        self.state_transition_layout.as_ref()
    }

    pub fn verifier(&self) -> CircuitVerifier<OutSC> {
        self.prep.verifier()
    }
}

fn trusted_child_statement_layout<SC, A>(
    authority: &TrustedChildAuthority<'_, SC, A>,
) -> Result<TrustedChildStatementLayout, VerificationError>
where
    SC: StarkGenericConfig + 'static,
    A: RecursiveAir<Val<SC>, SC::Challenge, LogUpGadget>,
    Val<SC>: PrimeField64 + StarkField,
    SymbolicExpressionExt<Val<SC>, SC::Challenge>:
        Algebra<SymbolicExpression<Val<SC>>> + Algebra<SC::Challenge>,
{
    match authority {
        TrustedChildAuthority::Uni { air, .. } => {
            let public_values_len = air.expected_public_input_count().ok_or_else(|| {
                VerificationError::InvalidProofShape(
                    "trusted uni-STARK AIR does not declare an exact public input count".into(),
                )
            })?;
            let schema = StatementSchema::try_new(vec![StatementField::Base; public_values_len])
                .map_err(|error| {
                    VerificationError::InvalidProofShape(alloc::format!(
                        "trusted uni statement schema is invalid: {error}"
                    ))
                })?;
            TrustedChildStatementLayout::uni(public_values_len, schema)
        }
        TrustedChildAuthority::Batch { verifier } => Ok(TrustedChildStatementLayout::batch(
            verifier.statement_layout(),
        )),
    }
}

fn capture_trusted_input_contract<'air, 'p, SC, A, B, const D: usize>(
    backend: &B,
    authority: &TrustedChildAuthority<'air, SC, A>,
    input: &TrustedPreparedInput<'p, SC>,
    recursion_input: &RecursionInput<'_, SC, A>,
) -> Result<B::InputContract, VerificationError>
where
    SC: StarkGenericConfig + 'static,
    A: RecursiveAir<Val<SC>, SC::Challenge, LogUpGadget>,
    B: TrustedPcsRecursionBackend<SC, A, D>,
    Val<SC>: PrimeField64 + StarkField,
    SymbolicExpressionExt<Val<SC>, SC::Challenge>:
        Algebra<SymbolicExpression<Val<SC>>> + Algebra<SC::Challenge>,
{
    match (authority, input) {
        (TrustedChildAuthority::Uni { .. }, TrustedPreparedInput::UniStark { .. }) => {
            backend.capture_input_contract(authority.config(), recursion_input)
        }
        (
            TrustedChildAuthority::Batch { verifier },
            TrustedPreparedInput::BatchStark { proof, statement },
        ) => backend.capture_trusted_batch_input_contract(verifier, proof, statement),
        _ => Err(VerificationError::PreparedInputMismatch {
            component: "input.kind",
        }),
    }
}

fn validate_trusted_input_contract<'air, 'p, SC, A, B, const D: usize>(
    backend: &B,
    authority: &TrustedChildAuthority<'air, SC, A>,
    contract: &B::InputContract,
    input: &TrustedPreparedInput<'p, SC>,
) -> Result<(), VerificationError>
where
    SC: StarkGenericConfig + 'static,
    A: RecursiveAir<Val<SC>, SC::Challenge, LogUpGadget>,
    B: TrustedPcsRecursionBackend<SC, A, D>,
    Val<SC>: PrimeField64 + StarkField,
    SymbolicExpressionExt<Val<SC>, SC::Challenge>:
        Algebra<SymbolicExpression<Val<SC>>> + Algebra<SC::Challenge>,
{
    match (authority, input) {
        (
            TrustedChildAuthority::Uni {
                preprocessed_commit,
                ..
            },
            TrustedPreparedInput::UniStark {
                proof,
                public_inputs,
            },
        ) => backend.validate_prepared_input(
            authority.config(),
            contract,
            &PreparedInput::UniStark {
                proof,
                public_inputs,
                preprocessed_commit: preprocessed_commit.as_ref(),
            },
        ),
        (
            TrustedChildAuthority::Batch { verifier },
            TrustedPreparedInput::BatchStark { proof, statement },
        ) => backend.validate_trusted_batch_input(verifier, contract, proof, statement),
        _ => Err(VerificationError::PreparedInputMismatch {
            component: "input.kind",
        }),
    }
}

fn preflight_trusted_input<'air, 'p, SC, A, B, const D: usize>(
    backend: &B,
    authority: &TrustedChildAuthority<'air, SC, A>,
    input: &TrustedPreparedInput<'p, SC>,
) -> Result<(), VerificationError>
where
    SC: StarkGenericConfig + 'static,
    A: RecursiveAir<Val<SC>, SC::Challenge, LogUpGadget>,
    B: TrustedPcsRecursionBackend<SC, A, D>,
    Val<SC>: PrimeField64 + StarkField,
    SymbolicExpressionExt<Val<SC>, SC::Challenge>:
        Algebra<SymbolicExpression<Val<SC>>> + Algebra<SC::Challenge>,
{
    match (authority, input) {
        (
            TrustedChildAuthority::Uni {
                preprocessed_commit,
                ..
            },
            TrustedPreparedInput::UniStark {
                proof,
                public_inputs,
            },
        ) => <B as PreparedPcsRecursionBackend<SC, A, D>>::preflight_input(
            backend,
            authority.config(),
            &PreparedInput::UniStark {
                proof,
                public_inputs,
                preprocessed_commit: preprocessed_commit.as_ref(),
            },
        ),
        (
            TrustedChildAuthority::Batch { verifier },
            TrustedPreparedInput::BatchStark { proof, .. },
        ) => backend.preflight_trusted_batch(verifier, proof),
        _ => Err(VerificationError::PreparedInputMismatch {
            component: "input.kind",
        }),
    }
}

fn preflight_trusted_source<SC, A, B, const D: usize>(
    backend: &B,
    source: &TrustedPreparedSource<'_, '_, SC, A>,
) -> Result<(), VerificationError>
where
    SC: StarkGenericConfig + 'static,
    A: RecursiveAir<Val<SC>, SC::Challenge, LogUpGadget>,
    B: TrustedPcsRecursionBackend<SC, A, D>,
    Val<SC>: PrimeField64 + StarkField,
    SymbolicExpressionExt<Val<SC>, SC::Challenge>:
        Algebra<SymbolicExpression<Val<SC>>> + Algebra<SC::Challenge>,
{
    match source {
        TrustedPreparedSource::UniStark {
            config,
            proof,
            public_inputs,
            preprocessed_commit,
            ..
        } => <B as PreparedPcsRecursionBackend<SC, A, D>>::preflight_input(
            backend,
            config,
            &PreparedInput::UniStark {
                proof,
                public_inputs,
                preprocessed_commit: preprocessed_commit.as_ref(),
            },
        ),
        TrustedPreparedSource::BatchStark {
            verifier, proof, ..
        } => backend.preflight_trusted_batch(verifier, proof),
    }
}

fn build_trusted_child<'air, 'p, SC, A, B, const D: usize>(
    backend: &B,
    authority: &TrustedChildAuthority<'air, SC, A>,
    input: &TrustedPreparedInput<'p, SC>,
    prev: &RecursionInput<'_, SC, A>,
    builder: &mut CircuitBuilder<SC::Challenge>,
) -> Result<B::VerifierResult, VerificationError>
where
    SC: StarkGenericConfig + 'static,
    A: RecursiveAir<Val<SC>, SC::Challenge, LogUpGadget>,
    B: TrustedPcsRecursionBackend<SC, A, D>,
    Val<SC>: PrimeField64 + StarkField,
    SymbolicExpressionExt<Val<SC>, SC::Challenge>:
        Algebra<SymbolicExpression<Val<SC>>> + Algebra<SC::Challenge>,
{
    match (authority, input) {
        (TrustedChildAuthority::Uni { .. }, TrustedPreparedInput::UniStark { .. }) => {
            backend.build_verifier_circuit(prev, authority.config(), builder)
        }
        (
            TrustedChildAuthority::Batch { verifier, .. },
            TrustedPreparedInput::BatchStark { proof, statement },
        ) => backend.build_trusted_batch_verifier_circuit(verifier, proof, statement, builder),
        _ => unreachable!(),
    }
}

fn set_trusted_child_private<'air, 'p, SC, A, B, const D: usize>(
    backend: &B,
    authority: &TrustedChildAuthority<'air, SC, A>,
    input: &TrustedPreparedInput<'p, SC>,
    prev: &RecursionInput<'_, SC, A>,
    result: &B::VerifierResult,
    runner: &mut p3_circuit::CircuitRunner<'_, SC::Challenge>,
) -> Result<(), VerificationError>
where
    SC: StarkGenericConfig + 'static,
    A: RecursiveAir<Val<SC>, SC::Challenge, LogUpGadget>,
    B: TrustedPcsRecursionBackend<SC, A, D>,
    Val<SC>: PrimeField64 + StarkField,
    SymbolicExpressionExt<Val<SC>, SC::Challenge>:
        Algebra<SymbolicExpression<Val<SC>>> + Algebra<SC::Challenge>,
{
    match (authority, input) {
        (TrustedChildAuthority::Uni { .. }, TrustedPreparedInput::UniStark { .. }) => {
            <B as PcsRecursionBackend<SC, A, D>>::set_private_data_for_result(
                backend,
                authority.config(),
                runner,
                result,
                prev,
            )
            .map_err(|message| VerificationError::InvalidProofShape(message.into()))
        }
        (
            TrustedChildAuthority::Batch { verifier, .. },
            TrustedPreparedInput::BatchStark { proof, statement },
        ) => backend.set_private_data_for_trusted_batch(
            verifier,
            proof,
            statement,
            runner,
            result.op_ids(),
        ),
        _ => unreachable!(),
    }
}
