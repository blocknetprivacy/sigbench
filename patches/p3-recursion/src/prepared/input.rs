use alloc::boxed::Box;
use alloc::format;
use alloc::string::ToString;
use alloc::vec::Vec;

use p3_batch_stark::CommonData;
use p3_circuit_prover::batch_stark_prover::{NUM_PRIMITIVE_TABLES, TableProver};
use p3_circuit_prover::field_params::ExtractBinomialW;
use p3_circuit_prover::{BatchStarkProof, CircuitVerifier};
use p3_commit::Pcs;
use p3_field::{ExtensionField, PrimeField64};
use p3_uni_stark::{Proof, StarkGenericConfig, Val};

use crate::input_contract::stark::{validate_batch_native, validate_uni_native};
use crate::input_contract::{
    BatchInputContract, CommitmentsShape, GlobalPreprocessedShape, InputContract,
    NonPrimitiveContract, OpenedValuesShape, OpenedValuesWithLookupsShape,
    PreprocessedInstanceShape, UniInputContract,
};
use crate::recursion::{BatchOnly, RecursionInput};
use crate::traits::{CheckedRecursive, PreparedRecursive, Recursive, RecursiveAir};
use crate::verifier::{ReconstructedBatchTables, VerificationError, reconstruct_batch_tables};

pub type NativeCommitment<SC> = <<SC as StarkGenericConfig>::Pcs as Pcs<
    <SC as StarkGenericConfig>::Challenge,
    <SC as StarkGenericConfig>::Challenger,
>>::Commitment;

pub(crate) type CaptureShapeResult<SC, CommShape, OpeningShape> =
    Result<InputContract<Val<SC>, CommShape, OpeningShape>, VerificationError>;

pub enum PreparedInput<'p, SC: StarkGenericConfig> {
    UniStark {
        proof: &'p Proof<SC>,
        public_inputs: &'p [Val<SC>],
        preprocessed_commit: Option<&'p NativeCommitment<SC>>,
    },
    BatchStark {
        proof: &'p BatchStarkProof<SC>,
        common_data: &'p CommonData<SC>,
        table_public_inputs: &'p [Vec<Val<SC>>],
    },
}

impl<'p, SC: StarkGenericConfig> Clone for PreparedInput<'p, SC> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<'p, SC: StarkGenericConfig> Copy for PreparedInput<'p, SC> {}

pub enum PreparedSource<'air, 'p, SC: StarkGenericConfig, A> {
    UniStark {
        air: &'air A,
        proof: &'p Proof<SC>,
        public_inputs: &'p [Val<SC>],
        preprocessed_commit: Option<&'p NativeCommitment<SC>>,
    },
    BatchStark {
        proof: &'p BatchStarkProof<SC>,
        common_data: &'p CommonData<SC>,
        table_public_inputs: &'p [Vec<Val<SC>>],
    },
}

impl<'air, 'p, SC: StarkGenericConfig, A> Clone for PreparedSource<'air, 'p, SC, A> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<'air, 'p, SC: StarkGenericConfig, A> Copy for PreparedSource<'air, 'p, SC, A> {}

impl<'p, SC: StarkGenericConfig> PreparedSource<'static, 'p, SC, BatchOnly> {
    pub const fn batch(
        proof: &'p BatchStarkProof<SC>,
        common_data: &'p CommonData<SC>,
        table_public_inputs: &'p [Vec<Val<SC>>],
    ) -> Self {
        Self::BatchStark {
            proof,
            common_data,
            table_public_inputs,
        }
    }
}

impl<'air, 'p, SC: StarkGenericConfig, A> PreparedSource<'air, 'p, SC, A> {
    pub(crate) const fn as_input(&self) -> PreparedInput<'_, SC> {
        match self {
            Self::UniStark {
                proof,
                public_inputs,
                preprocessed_commit,
                ..
            } => PreparedInput::UniStark {
                proof,
                public_inputs,
                preprocessed_commit: *preprocessed_commit,
            },
            Self::BatchStark {
                proof,
                common_data,
                table_public_inputs,
            } => PreparedInput::BatchStark {
                proof,
                common_data,
                table_public_inputs,
            },
        }
    }
}

pub(crate) fn legacy_input<'a, 'p: 'a, SC, A>(
    air: Option<&'a A>,
    input: &'a PreparedInput<'p, SC>,
) -> Result<RecursionInput<'a, SC, A>, VerificationError>
where
    SC: StarkGenericConfig,
    A: crate::traits::RecursiveAir<Val<SC>, SC::Challenge, p3_lookup::logup::LogUpGadget>,
{
    match (air, input) {
        (
            Some(air),
            PreparedInput::UniStark {
                proof,
                public_inputs,
                preprocessed_commit,
            },
        ) => Ok(RecursionInput::UniStark {
            proof,
            air,
            public_inputs: public_inputs.to_vec(),
            preprocessed_commit: preprocessed_commit.cloned(),
        }),
        (
            None,
            PreparedInput::BatchStark {
                proof,
                common_data,
                table_public_inputs,
            },
        ) => Ok(RecursionInput::BatchStark {
            proof,
            common_data,
            table_public_inputs: table_public_inputs.to_vec(),
        }),
        _ => Err(VerificationError::PreparedInputMismatch {
            component: "input.kind",
        }),
    }
}

fn opened_values_shape<EF>(values: &p3_uni_stark::OpenedValues<EF>) -> OpenedValuesShape {
    let p3_uni_stark::OpenedValues {
        trace_local,
        trace_next,
        preprocessed,
        quotient_chunks,
        random,
    } = values;
    let preprocessed_local = preprocessed.as_ref().map(|p| p.local.as_slice());
    let preprocessed_next = preprocessed.as_ref().and_then(|p| p.next.as_deref());
    OpenedValuesShape {
        trace_local: trace_local.len(),
        trace_next: trace_next.as_ref().map(Vec::len),
        preprocessed_local: preprocessed_local.map(<[_]>::len),
        preprocessed_next: preprocessed_next.map(<[_]>::len),
        quotient_chunks: quotient_chunks.iter().map(Vec::len).collect(),
        random: random.as_ref().map(Vec::len),
    }
}

pub(crate) fn capture_input_shape<SC, Comm, Opening>(
    input: &PreparedInput<'_, SC>,
) -> CaptureShapeResult<SC, Comm::Shape, Opening::Shape>
where
    SC: StarkGenericConfig,
    Comm: Recursive<SC::Challenge, Input = NativeCommitment<SC>> + PreparedRecursive<SC::Challenge>,
    Opening: Recursive<SC::Challenge, Input = <SC::Pcs as Pcs<SC::Challenge, SC::Challenger>>::Proof>
        + PreparedRecursive<SC::Challenge>,
{
    match input {
        PreparedInput::UniStark {
            proof,
            public_inputs,
            preprocessed_commit,
        } => {
            let Proof {
                commitments,
                opened_values,
                opening_proof,
                degree_bits,
                ood_pow_witness: _,
            } = proof;
            let p3_uni_stark::Commitments {
                trace,
                quotient_chunks,
                random,
            } = commitments;
            Ok(InputContract::Uni(UniInputContract {
                degree_bits: *degree_bits,
                public_inputs: public_inputs.len(),
                commitments: CommitmentsShape {
                    main: Comm::input_shape(trace)?,
                    permutation: None,
                    quotient_chunks: Comm::input_shape(quotient_chunks)?,
                    random: random.as_ref().map(Comm::input_shape).transpose()?,
                },
                opened_values: opened_values_shape(opened_values),
                opening: Opening::input_shape(opening_proof)?,
                preprocessed_commit: preprocessed_commit
                    .map(|commitment| Comm::input_shape(commitment))
                    .transpose()?,
            }))
        }
        PreparedInput::BatchStark {
            proof,
            common_data,
            table_public_inputs,
        } => {
            proof
                .validate()
                .map_err(|error| VerificationError::InvalidProofShape(error.to_string()))?;
            let BatchStarkProof {
                proof: batch,
                table_packing,
                rows,
                alu_variant,
                ext_degree,
                w_binomial,
                alu_quintic_trinomial,
                non_primitives,
                stark_common: _,
            } = proof;
            let p3_batch_stark::BatchProof {
                commitments,
                opened_values,
                opening_proof,
                lookup_terminals,
                degree_bits,
                lookup_pow_witness: _,
                ood_pow_witness: _,
            } = batch;
            let p3_batch_stark::BatchOpenedValues { instances } = opened_values;
            let instance_count = instances.len();
            if instance_count == 0
                || degree_bits.len() != instance_count
                || lookup_terminals.len() != instance_count
                || table_public_inputs.len() != instance_count
            {
                return Err(VerificationError::InvalidProofShape(format!(
                    "batch input vector cardinality mismatch: instances {instance_count}, degree bits {}, lookup terminals {}, public inputs {}",
                    degree_bits.len(),
                    lookup_terminals.len(),
                    table_public_inputs.len()
                )));
            }
            let p3_batch_stark::BatchCommitments {
                main,
                permutation,
                quotient_chunks,
                random,
            } = commitments;
            let commitments = CommitmentsShape {
                main: Comm::input_shape(main)?,
                permutation: permutation.as_ref().map(Comm::input_shape).transpose()?,
                quotient_chunks: Comm::input_shape(quotient_chunks)?,
                random: random.as_ref().map(Comm::input_shape).transpose()?,
            };
            let opened_values = instances
                .iter()
                .map(|instance| {
                    let p3_batch_stark::proof::OpenedValuesWithLookups {
                        base_opened_values,
                        permutation_local,
                        permutation_next,
                    } = instance;
                    OpenedValuesWithLookupsShape {
                        base: opened_values_shape(base_opened_values),
                        permutation_local: permutation_local.len(),
                        permutation_next: permutation_next.len(),
                    }
                })
                .collect();
            let non_primitives = non_primitives
                .iter()
                .map(|entry| {
                    let p3_circuit_prover::batch_stark_prover::NonPrimitiveTableEntry {
                        op_type,
                        rows,
                        lanes,
                        public_values,
                        air_variant,
                    } = entry;
                    NonPrimitiveContract {
                        op_type: op_type.clone(),
                        rows: *rows,
                        lanes: *lanes,
                        air_variant: *air_variant,
                        public_values: public_values.clone(),
                    }
                })
                .collect();
            let CommonData {
                preprocessed: common_preprocessed,
                lookups: _,
            } = common_data;
            let preprocessed = common_preprocessed
                .as_ref()
                .map(|global| -> Result<_, VerificationError> {
                    let p3_batch_stark::common::GlobalPreprocessed {
                        commitment,
                        instances,
                        matrix_to_instance,
                    } = global;
                    Ok(GlobalPreprocessedShape {
                        commitment: Comm::input_shape(commitment)?,
                        instances: instances
                            .iter()
                            .map(|instance| {
                                instance.as_ref().map(|metadata| {
                                    let p3_batch_stark::common::PreprocessedInstanceMeta {
                                        matrix_index,
                                        width,
                                        degree_bits,
                                    } = metadata;
                                    PreprocessedInstanceShape {
                                        matrix_index: *matrix_index,
                                        width: *width,
                                        degree_bits: *degree_bits,
                                    }
                                })
                            })
                            .collect(),
                        matrix_to_instance: matrix_to_instance.clone(),
                    })
                })
                .transpose()?;
            Ok(InputContract::Batch(Box::new(BatchInputContract {
                degree_bits: degree_bits.clone(),
                public_inputs: table_public_inputs.iter().map(Vec::len).collect(),
                commitments,
                opened_values,
                lookup_terminals: lookup_terminals.iter().map(Option::is_some).collect(),
                opening: Opening::input_shape(opening_proof)?,
                table_packing: table_packing.clone(),
                rows: *rows,
                alu_variant: *alu_variant,
                ext_degree: *ext_degree,
                w_binomial: *w_binomial,
                alu_quintic_trinomial: *alu_quintic_trinomial,
                non_primitives,
                statement_instance: None,
                preprocessed,
            })))
        }
    }
}

pub(crate) fn validate_builtin_input_raw<SC, A, Comm, Opening>(
    source: &RecursionInput<'_, SC, A>,
) -> Result<(), VerificationError>
where
    SC: StarkGenericConfig,
    A: RecursiveAir<Val<SC>, SC::Challenge, p3_lookup::logup::LogUpGadget>,
    Comm: CheckedRecursive<SC::Challenge>
        + Recursive<
            SC::Challenge,
            Input = <SC::Pcs as Pcs<SC::Challenge, SC::Challenger>>::Commitment,
        >,
    Opening: CheckedRecursive<SC::Challenge>
        + Recursive<SC::Challenge, Input = <SC::Pcs as Pcs<SC::Challenge, SC::Challenger>>::Proof>,
{
    match source {
        RecursionInput::UniStark {
            proof,
            preprocessed_commit,
            ..
        } => validate_uni_native::<SC, Comm, Opening>(proof, preprocessed_commit.as_ref()),
        RecursionInput::BatchStark {
            proof,
            common_data,
            table_public_inputs,
        } => validate_batch_native::<SC, Comm, Opening>(
            &proof.proof,
            common_data,
            &table_public_inputs.iter().map(Vec::len).collect::<Vec<_>>(),
        ),
    }
}

pub(crate) fn compare_input_contract<F: PartialEq, C: PartialEq, O: PartialEq>(
    expected: &InputContract<F, C, O>,
    actual: &InputContract<F, C, O>,
) -> Result<(), VerificationError> {
    macro_rules! same {
        ($left:expr, $right:expr, $component:literal) => {
            if $left != $right {
                return Err(VerificationError::PreparedInputMismatch {
                    component: $component,
                });
            }
        };
    }
    match (expected, actual) {
        (InputContract::Uni(a), InputContract::Uni(b)) => {
            same!(a.degree_bits, b.degree_bits, "input.degree_bits");
            same!(a.public_inputs, b.public_inputs, "input.public_inputs");
            same!(a.commitments, b.commitments, "input.commitments");
            same!(a.opened_values, b.opened_values, "input.opened_values");
            same!(a.opening, b.opening, "input.opening_proof");
            same!(
                a.preprocessed_commit,
                b.preprocessed_commit,
                "input.preprocessed"
            );
        }
        (InputContract::Batch(a), InputContract::Batch(b)) => {
            same!(a.degree_bits, b.degree_bits, "input.degree_bits");
            same!(a.public_inputs, b.public_inputs, "input.public_inputs");
            same!(a.commitments, b.commitments, "input.commitments");
            same!(a.opened_values, b.opened_values, "input.opened_values");
            same!(
                a.lookup_terminals,
                b.lookup_terminals,
                "input.opened_values"
            );
            same!(a.opening, b.opening, "input.opening_proof");
            same!(a.table_packing, b.table_packing, "input.metadata");
            same!(a.rows, b.rows, "input.metadata");
            same!(a.alu_variant, b.alu_variant, "input.metadata");
            same!(a.ext_degree, b.ext_degree, "input.metadata");
            same!(a.w_binomial, b.w_binomial, "input.metadata");
            same!(a.statement_instance, b.statement_instance, "input.metadata");
            same!(
                a.alu_quintic_trinomial,
                b.alu_quintic_trinomial,
                "input.metadata"
            );
            if a.non_primitives.len() != b.non_primitives.len()
                || a.non_primitives
                    .iter()
                    .zip(&b.non_primitives)
                    .enumerate()
                    .any(|(index, (expected, actual))| {
                        expected.op_type != actual.op_type
                            || expected.rows != actual.rows
                            || expected.lanes != actual.lanes
                            || expected.air_variant != actual.air_variant
                            || if a.statement_instance == Some(NUM_PRIMITIVE_TABLES + index) {
                                expected.public_values.len() != actual.public_values.len()
                            } else {
                                expected.public_values != actual.public_values
                            }
                    })
            {
                return Err(VerificationError::PreparedInputMismatch {
                    component: "input.metadata",
                });
            }
            same!(a.preprocessed, b.preprocessed, "input.preprocessed");
        }
        _ => {
            return Err(VerificationError::PreparedInputMismatch {
                component: "input.kind",
            });
        }
    }
    Ok(())
}

pub(crate) fn capture_trusted_batch_input_contract<SC, Comm, Opening>(
    verifier: &CircuitVerifier<SC>,
    proof: &BatchStarkProof<SC>,
    expected_statement: &[Val<SC>],
) -> CaptureShapeResult<SC, Comm::Shape, Opening::Shape>
where
    SC::Challenger: p3_challenger::GrindingChallenger<Witness = p3_uni_stark::Val<SC>>,
    SC: StarkGenericConfig + 'static,
    Comm: Recursive<SC::Challenge, Input = NativeCommitment<SC>> + PreparedRecursive<SC::Challenge>,
    Opening: Recursive<SC::Challenge, Input = <SC::Pcs as Pcs<SC::Challenge, SC::Challenger>>::Proof>
        + PreparedRecursive<SC::Challenge>,
    Val<SC>: PrimeField64 + p3_circuit_prover::config::StarkField,
    SC::Challenge: ExtensionField<Val<SC>> + ExtractBinomialW<Val<SC>>,
    p3_air::SymbolicExpressionExt<Val<SC>, SC::Challenge>:
        p3_field::Algebra<p3_air::SymbolicExpression<Val<SC>>> + p3_field::Algebra<SC::Challenge>,
{
    verifier
        .verify(proof, expected_statement)
        .map_err(|error| VerificationError::InvalidProofShape(error.to_string()))?;
    let table_public_inputs = verifier
        .table_public_values(expected_statement)
        .map_err(|error| VerificationError::InvalidProofShape(error.to_string()))?;
    let mut contract = capture_input_shape::<SC, Comm, Opening>(&PreparedInput::BatchStark {
        proof,
        common_data: verifier.common_data(),
        table_public_inputs: &table_public_inputs,
    })?;
    let InputContract::Batch(batch) = &mut contract else {
        unreachable!()
    };
    batch.statement_instance = verifier.statement_layout().table_instance();
    Ok(contract)
}

pub(crate) fn validate_trusted_batch_input<SC, Comm, Opening>(
    verifier: &CircuitVerifier<SC>,
    contract: &InputContract<Val<SC>, Comm::Shape, Opening::Shape>,
    proof: &BatchStarkProof<SC>,
    expected_statement: &[Val<SC>],
) -> Result<(), VerificationError>
where
    SC::Challenger: p3_challenger::GrindingChallenger<Witness = p3_uni_stark::Val<SC>>,
    SC: StarkGenericConfig + 'static,
    Comm: Recursive<SC::Challenge, Input = NativeCommitment<SC>> + PreparedRecursive<SC::Challenge>,
    Opening: Recursive<SC::Challenge, Input = <SC::Pcs as Pcs<SC::Challenge, SC::Challenger>>::Proof>
        + PreparedRecursive<SC::Challenge>,
    Val<SC>: PrimeField64 + p3_circuit_prover::config::StarkField,
    SC::Challenge: ExtensionField<Val<SC>> + ExtractBinomialW<Val<SC>>,
    p3_air::SymbolicExpressionExt<Val<SC>, SC::Challenge>:
        p3_field::Algebra<p3_air::SymbolicExpression<Val<SC>>> + p3_field::Algebra<SC::Challenge>,
{
    let actual = capture_trusted_batch_input_contract::<SC, Comm, Opening>(
        verifier,
        proof,
        expected_statement,
    )?;
    compare_input_contract(contract, &actual)
}

pub(crate) fn validate_manifest_public_inputs<SC: StarkGenericConfig>(
    proof: &BatchStarkProof<SC>,
    table_public_inputs: &[Vec<Val<SC>>],
) -> Result<(), VerificationError> {
    let expected_len = 3 + proof.non_primitives.len();
    if table_public_inputs.len() != expected_len
        || table_public_inputs[..table_public_inputs.len().min(3)]
            .iter()
            .any(|values| !values.is_empty())
        || proof
            .non_primitives
            .iter()
            .zip(table_public_inputs.iter().skip(3))
            .any(|(entry, values)| entry.public_values != *values)
    {
        return Err(VerificationError::InvalidProofShape(
            "batch table public inputs disagree with prepared manifest".into(),
        ));
    }
    Ok(())
}

fn validate_reconstructed_public_inputs<SC, const TRACE_D: usize>(
    reconstructed: &ReconstructedBatchTables<SC, TRACE_D>,
    table_public_inputs: &[Vec<Val<SC>>],
) -> Result<(), VerificationError>
where
    SC: StarkGenericConfig,
{
    if reconstructed.public_values.as_slice() != table_public_inputs
        || reconstructed
            .airs
            .iter()
            .zip(&reconstructed.public_values)
            .any(|(air, values)| p3_air::BaseAir::<Val<SC>>::num_public_values(air) != values.len())
    {
        return Err(VerificationError::InvalidProofShape(
            "batch table public inputs disagree with reconstructed AIR/transcript".into(),
        ));
    }
    Ok(())
}

fn reconstruct_and_validate_public_inputs<SC, const TRACE_D: usize>(
    config: &SC,
    proof: &BatchStarkProof<SC>,
    table_public_inputs: &[Vec<Val<SC>>],
    non_primitive_provers: &[Box<dyn TableProver<SC>>],
) -> Result<(), VerificationError>
where
    SC: StarkGenericConfig + 'static,
    Val<SC>: PrimeField64,
    SC::Challenge: ExtensionField<Val<SC>> + ExtractBinomialW<Val<SC>>,
{
    let reconstructed =
        reconstruct_batch_tables::<SC, TRACE_D>(config, proof, non_primitive_provers)?;
    validate_reconstructed_public_inputs(&reconstructed, table_public_inputs)
}

pub(crate) fn capture_builtin_input_contract<SC, A, Comm, Opening>(
    config: &SC,
    source: &RecursionInput<'_, SC, A>,
    expected_batch_degree: Option<usize>,
    make_non_primitive_provers: impl FnOnce(usize) -> Vec<Box<dyn TableProver<SC>>>,
) -> CaptureShapeResult<SC, Comm::Shape, Opening::Shape>
where
    SC: StarkGenericConfig + 'static,
    A: RecursiveAir<Val<SC>, SC::Challenge, p3_lookup::logup::LogUpGadget>,
    Comm: Recursive<SC::Challenge, Input = NativeCommitment<SC>> + PreparedRecursive<SC::Challenge>,
    Opening: Recursive<SC::Challenge, Input = <SC::Pcs as Pcs<SC::Challenge, SC::Challenger>>::Proof>
        + PreparedRecursive<SC::Challenge>,
    Val<SC>: PrimeField64,
    SC::Challenge: ExtensionField<Val<SC>> + ExtractBinomialW<Val<SC>>,
{
    let input = match source {
        RecursionInput::UniStark {
            proof,
            public_inputs,
            preprocessed_commit,
            ..
        } => PreparedInput::UniStark {
            proof,
            public_inputs,
            preprocessed_commit: preprocessed_commit.as_ref(),
        },
        RecursionInput::BatchStark {
            proof,
            common_data,
            table_public_inputs,
        } => PreparedInput::BatchStark {
            proof,
            common_data,
            table_public_inputs,
        },
    };
    let contract = capture_input_shape::<SC, Comm, Opening>(&input)?;

    match source {
        RecursionInput::UniStark {
            air, public_inputs, ..
        } => match air.expected_public_input_count() {
            Some(expected) if expected == public_inputs.len() => {}
            Some(expected) => {
                return Err(VerificationError::InvalidProofShape(format!(
                    "uni-STARK public input count mismatch: AIR expects {expected}, got {}",
                    public_inputs.len()
                )));
            }
            None => {
                return Err(VerificationError::InvalidProofShape(
                    "prepared uni-STARK AIR does not declare an exact public input count".into(),
                ));
            }
        },
        RecursionInput::BatchStark {
            proof,
            table_public_inputs,
            ..
        } => {
            if let Some(expected) = expected_batch_degree
                && proof.ext_degree != expected
            {
                return Err(VerificationError::InvalidProofShape(format!(
                    "WhirRecursionBackend supports batch proofs of ext_degree {expected}, got {}",
                    proof.ext_degree
                )));
            }
            if !matches!(proof.ext_degree, 1 | 2 | 4 | 5) {
                return Err(VerificationError::InvalidProofShape(format!(
                    "unsupported batch proof ext_degree {}",
                    proof.ext_degree
                )));
            }
            let non_primitive_provers = make_non_primitive_provers(proof.ext_degree);
            match proof.ext_degree {
                1 => reconstruct_and_validate_public_inputs::<SC, 1>(
                    config,
                    proof,
                    table_public_inputs,
                    &non_primitive_provers,
                )?,
                2 => reconstruct_and_validate_public_inputs::<SC, 2>(
                    config,
                    proof,
                    table_public_inputs,
                    &non_primitive_provers,
                )?,
                4 => reconstruct_and_validate_public_inputs::<SC, 4>(
                    config,
                    proof,
                    table_public_inputs,
                    &non_primitive_provers,
                )?,
                5 => reconstruct_and_validate_public_inputs::<SC, 5>(
                    config,
                    proof,
                    table_public_inputs,
                    &non_primitive_provers,
                )?,
                degree => {
                    return Err(VerificationError::InvalidProofShape(format!(
                        "unsupported batch proof ext_degree {degree}"
                    )));
                }
            }
        }
    }
    Ok(contract)
}

pub(crate) fn validate_builtin_prepared_input<SC, Comm, Opening>(
    contract: &InputContract<Val<SC>, Comm::Shape, Opening::Shape>,
    input: &PreparedInput<'_, SC>,
) -> Result<(), VerificationError>
where
    SC: StarkGenericConfig,
    Comm: Recursive<SC::Challenge, Input = NativeCommitment<SC>> + PreparedRecursive<SC::Challenge>,
    Opening: Recursive<SC::Challenge, Input = <SC::Pcs as Pcs<SC::Challenge, SC::Challenger>>::Proof>
        + PreparedRecursive<SC::Challenge>,
{
    let actual = capture_input_shape::<SC, Comm, Opening>(input)?;
    compare_input_contract(contract, &actual)?;
    if let PreparedInput::BatchStark {
        proof,
        table_public_inputs,
        ..
    } = input
    {
        validate_manifest_public_inputs(proof, table_public_inputs)?;
    }
    Ok(())
}
