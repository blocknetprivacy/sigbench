#![allow(clippy::upper_case_acronyms)]

use alloc::borrow::Cow;
use alloc::boxed::Box;
use alloc::string::{String, ToString};
use alloc::vec::Vec;
use alloc::{format, vec};

use hashbrown::HashMap;
use p3_air::{Air as P3Air, BaseAir as P3BaseAir};
use p3_batch_stark::{BatchShape, CommonData};
use p3_circuit::symbolic::ColumnsTargets;
use p3_circuit::{CircuitBuilder, NonPrimitiveOpId};
use p3_circuit_prover::air::{AluAir, AluExtMulKind, ConstAir, PublicAir};
use p3_circuit_prover::batch_stark_prover::{
    AirVariant, CircuitVerifier, DynamicAirEntry, NUM_PRIMITIVE_TABLES, PrimitiveTable, RowCounts,
    TableProver, lookups_for_circuit_table_air,
};
use p3_circuit_prover::common::CircuitTableAir;
use p3_circuit_prover::field_params::ExtractBinomialW;
use p3_commit::{Pcs, PolynomialSpace, UnivariateStarkPcs};
use p3_field::{
    Algebra, BasedVectorSpace, ExtensionField, Field, PrimeCharacteristicRing, PrimeField64,
};
use p3_lookup::{Kind, Lookup, LookupProtocol};
use p3_uni_stark::{
    StarkGenericConfig, SymbolicExpression, SymbolicExpressionExt, Val, validate_degree_bits,
};

use super::{ObservableCommitment, VerificationError, recompose_quotient_from_chunks_circuit};
use crate::challenger::CircuitChallenger;
use crate::challenger_perm::ChallengerPermConfig;
use crate::input_contract::stark_layout::{
    CommitmentRole, InstanceLayout, MatrixRoute, NativeStarkLayout, checked_power_of_two,
    validate_preprocessed_metadata,
};
use crate::traits::{
    LookupMetadata, Recursive, RecursiveAir, RecursiveChallenger, RecursiveLookupGadget,
    RecursivePcs,
};
use crate::transcript::domain_separator_seed;
use crate::types::{
    BatchProofTargets, CommonDataTargets, OpenedValuesTargets, OpenedValuesTargetsWithLookups,
};
use crate::{BatchStarkVerifierInputsBuilder, Target};

pub type PcsVerifierParams<SC, InputProof, OpeningProof, Comm> =
    <<SC as StarkGenericConfig>::Pcs as RecursivePcs<
        SC,
        InputProof,
        OpeningProof,
        Comm,
        <<SC as StarkGenericConfig>::Pcs as Pcs<
            <SC as StarkGenericConfig>::Challenge,
            <SC as StarkGenericConfig>::Challenger,
        >>::Domain,
    >>::VerifierParams;

pub type DynRecursionAirEntry<SC> = DynamicAirEntry<SC>;

pub(crate) fn plan_batch_native_layout<SC, A, LG>(
    config: &SC,
    airs: &[A],
    proof: &p3_batch_stark::BatchProof<SC>,
    public_value_counts: &[usize],
    common: &CommonData<SC>,
    lookups: &[Vec<Lookup<Val<SC>>>],
    lookup_gadget: &LG,
) -> Result<NativeStarkLayout<'static>, VerificationError>
where
    SC: StarkGenericConfig,
    A: RecursiveAir<Val<SC>, SC::Challenge, LG>,
    LG: RecursiveLookupGadget<SC::Challenge>,
    Val<SC>: PrimeField64,
    SC::Challenge: ExtensionField<Val<SC>> + PrimeCharacteristicRing,
{
    let instances = &proof.opened_values.instances;
    let count = airs.len();
    if count == 0
        || instances.len() != count
        || proof.degree_bits.len() != count
        || proof.lookup_terminals.len() != count
        || public_value_counts.len() != count
        || lookups.len() != count
    {
        return Err(VerificationError::InvalidProofShape(
            "batch-STARK trusted layout cardinality mismatch".into(),
        ));
    }
    for (air, &actual) in airs.iter().zip(public_value_counts) {
        if air.expected_public_input_count() != Some(actual) {
            return Err(VerificationError::InvalidProofShape(
                "batch-STARK public input count disagrees with reconstructed AIR".into(),
            ));
        }
    }
    for (index, &degree) in proof.degree_bits.iter().enumerate() {
        validate_degree_bits(
            Some(index),
            degree,
            config.is_zk(),
            config.pcs().log_min_trace_height(),
            config.pcs().log_max_trace_height(),
        )
        .map_err(|error| VerificationError::InvalidProofShape(error.to_string()))?;
    }
    if let Some(global) = &common.preprocessed {
        let metadata = global
            .instances
            .iter()
            .map(|entry| {
                entry
                    .as_ref()
                    .map(|meta| (meta.matrix_index, meta.width, meta.degree_bits))
            })
            .collect::<Vec<_>>();
        validate_preprocessed_metadata(&metadata, &global.matrix_to_instance, &proof.degree_bits)
            .map_err(|error| VerificationError::InvalidProofShape(error.to_string()))?;
    }

    let mut planned = Vec::with_capacity(count);
    for (index, ((air, opened), lookup_set)) in airs.iter().zip(instances).zip(lookups).enumerate()
    {
        let ext_log = proof.degree_bits[index];
        let base_log = ext_log.checked_sub(config.is_zk()).ok_or_else(|| {
            VerificationError::InvalidProofShape(
                "extended degree smaller than zk adjustment".into(),
            )
        })?;
        let pre_width = common
            .preprocessed
            .as_ref()
            .and_then(|global| global.instances[index].as_ref().map(|meta| meta.width))
            .unwrap_or(0);
        let base = &opened.base_opened_values;
        let permutation_width = if lookup_set.is_empty() {
            0
        } else {
            lookup_set
                .len()
                .checked_add(1)
                .and_then(|width| width.checked_mul(SC::Challenge::DIMENSION))
                .ok_or_else(|| {
                    VerificationError::InvalidProofShape(
                        "packed permutation width overflows".into(),
                    )
                })?
        };
        let log_quotient = air.get_log_num_quotient_chunks(
            pre_width,
            checked_power_of_two(base_log)
                .map_err(|error| VerificationError::InvalidProofShape(error.to_string()))?,
            lookup_set,
            config.is_zk(),
            lookup_gadget,
        );
        let quotient_chunks =
            checked_power_of_two(log_quotient.checked_add(config.is_zk()).ok_or_else(|| {
                VerificationError::InvalidProofShape("quotient log overflows".into())
            })?)
            .map_err(|error| VerificationError::InvalidProofShape(error.to_string()))?;
        if base.trace_local.len() != air.width()
            || base.trace_next.as_ref().map_or(0, Vec::len)
                != air.width() * usize::from(air.opens_trace_next())
            || base.preprocessed_local().map_or(0, <[_]>::len) != pre_width
            || base.preprocessed_next().map_or(0, <[_]>::len)
                != pre_width * usize::from(air.opens_preprocessed_next())
            || base.quotient_chunks.len() != quotient_chunks
            || base
                .quotient_chunks
                .iter()
                .any(|chunk| chunk.len() != SC::Challenge::DIMENSION)
            || base
                .random
                .as_ref()
                .is_some_and(|values| values.len() != SC::Challenge::DIMENSION)
            || opened.permutation_local.len() != permutation_width
            || opened.permutation_next.len() != permutation_width
            || proof.lookup_terminals[index].is_some() != air.declares_interactions(pre_width)
        {
            return Err(VerificationError::InvalidProofShape(
                "batch-STARK openings disagree with reconstructed AIR metadata".into(),
            ));
        }
        planned.push(InstanceLayout {
            ext_log,
            base_log,
            challenge_width: SC::Challenge::DIMENSION,
            trace_width: air.width(),
            trace_next: air.opens_trace_next(),
            pre_width,
            pre_next: air.opens_preprocessed_next(),
            quotient_log: log_quotient,
            quotient_chunks,
            permutation_width,
        });
    }
    let has_permutation = planned
        .iter()
        .any(|instance| instance.permutation_width != 0);
    if proof.commitments.permutation.is_some() != has_permutation
        || proof.commitments.random.is_some() != SC::Pcs::ZK
        || instances
            .iter()
            .any(|instance| instance.base_opened_values.random.is_some() != SC::Pcs::ZK)
    {
        return Err(VerificationError::InvalidProofShape(
            "batch-STARK commitment presence disagrees with the trusted layout".into(),
        ));
    }
    NativeStarkLayout::new(
        planned,
        common
            .preprocessed
            .as_ref()
            .map_or(&[][..], |global| global.matrix_to_instance.as_slice()),
        proof.commitments.random.is_some(),
        common.preprocessed.is_some(),
        has_permutation,
    )
    .map(|layout| layout.to_owned_layout())
    .map_err(|error| VerificationError::InvalidProofShape(error.to_string()))
}

pub enum CircuitTablesAir<SC: StarkGenericConfig, const D: usize> {
    Const(ConstAir<Val<SC>, D>),
    Public(PublicAir<Val<SC>, D>),
    Alu(AluAir<Val<SC>, D>),
    Dynamic(DynRecursionAirEntry<SC>),
}

impl<SC: StarkGenericConfig, const D: usize> CircuitTablesAir<SC, D>
where
    SymbolicExpressionExt<Val<SC>, SC::Challenge>: Algebra<SymbolicExpression<Val<SC>>>,
{
    pub(crate) fn to_table_air(&self) -> CircuitTableAir<SC, D> {
        match self {
            Self::Const(a) => CircuitTableAir::Const(a.clone()),
            Self::Public(a) => CircuitTableAir::Public(a.clone()),
            Self::Alu(a) => CircuitTableAir::Alu(a.clone()),
            Self::Dynamic(a) => CircuitTableAir::Dynamic(a.clone()),
        }
    }

    fn from_table_air(air: CircuitTableAir<SC, D>) -> Self {
        match air {
            CircuitTableAir::Const(air) => Self::Const(air),
            CircuitTableAir::Public(air) => Self::Public(air),
            CircuitTableAir::Alu(air) => Self::Alu(air),
            CircuitTableAir::Dynamic(air) => Self::Dynamic(air),
        }
    }
}

impl<SC, const D: usize> P3BaseAir<Val<SC>> for CircuitTablesAir<SC, D>
where
    SC: StarkGenericConfig,
    SymbolicExpressionExt<Val<SC>, SC::Challenge>: Algebra<SymbolicExpression<Val<SC>>>,
{
    fn width(&self) -> usize {
        match self {
            Self::Const(a) => P3BaseAir::width(a),
            Self::Public(a) => P3BaseAir::width(a),
            Self::Alu(a) => P3BaseAir::width(a),
            Self::Dynamic(a) => P3BaseAir::width(a),
        }
    }

    fn preprocessed_width(&self) -> usize {
        match self {
            Self::Const(a) => P3BaseAir::preprocessed_width(a),
            Self::Public(a) => P3BaseAir::preprocessed_width(a),
            Self::Alu(a) => P3BaseAir::preprocessed_width(a),
            Self::Dynamic(a) => P3BaseAir::preprocessed_width(a),
        }
    }

    fn num_public_values(&self) -> usize {
        match self {
            Self::Const(a) => P3BaseAir::num_public_values(a),
            Self::Public(a) => P3BaseAir::num_public_values(a),
            Self::Alu(a) => P3BaseAir::num_public_values(a),
            Self::Dynamic(a) => P3BaseAir::num_public_values(a),
        }
    }

    fn main_next_row_columns(&self) -> Vec<usize> {
        match self {
            Self::Const(a) => P3BaseAir::main_next_row_columns(a),
            Self::Public(a) => P3BaseAir::main_next_row_columns(a),
            Self::Alu(a) => P3BaseAir::main_next_row_columns(a),
            Self::Dynamic(a) => P3BaseAir::main_next_row_columns(a),
        }
    }

    fn preprocessed_next_row_columns(&self) -> Vec<usize> {
        match self {
            Self::Const(air) => P3BaseAir::preprocessed_next_row_columns(air),
            Self::Public(air) => P3BaseAir::preprocessed_next_row_columns(air),
            Self::Alu(air) => P3BaseAir::preprocessed_next_row_columns(air),
            Self::Dynamic(air) => P3BaseAir::preprocessed_next_row_columns(air),
        }
    }

    fn num_periodic_columns(&self) -> usize {
        match self {
            Self::Const(a) => P3BaseAir::num_periodic_columns(a),
            Self::Public(a) => P3BaseAir::num_periodic_columns(a),
            Self::Alu(a) => P3BaseAir::num_periodic_columns(a),
            Self::Dynamic(a) => P3BaseAir::num_periodic_columns(a),
        }
    }

    fn periodic_columns(&self) -> Cow<'_, [Vec<Val<SC>>]> {
        match self {
            Self::Const(a) => P3BaseAir::periodic_columns(a),
            Self::Public(a) => P3BaseAir::periodic_columns(a),
            Self::Alu(a) => P3BaseAir::periodic_columns(a),
            Self::Dynamic(a) => P3BaseAir::periodic_columns(a),
        }
    }
}

impl<SC, const D: usize>
    P3Air<
        p3_lookup::symbolic::InteractionSymbolicBuilder<
            Val<SC>,
            <SC as StarkGenericConfig>::Challenge,
        >,
    > for CircuitTablesAir<SC, D>
where
    SC: StarkGenericConfig,
    Val<SC>: PrimeField64,
    <SC as StarkGenericConfig>::Challenge: ExtensionField<Val<SC>>,
    SymbolicExpressionExt<Val<SC>, SC::Challenge>:
        Algebra<SymbolicExpression<Val<SC>>> + Algebra<SC::Challenge>,
{
    fn eval(
        &self,
        builder: &mut p3_lookup::symbolic::InteractionSymbolicBuilder<
            Val<SC>,
            <SC as StarkGenericConfig>::Challenge,
        >,
    ) {
        match self {
            Self::Const(a) => P3Air::eval(a, builder),
            Self::Public(a) => P3Air::eval(a, builder),
            Self::Alu(a) => P3Air::eval(a, builder),
            Self::Dynamic(inner) => P3Air::eval(inner, builder),
        }
    }
}

fn create_alu_air<F, EF, const TRACE_D: usize>(
    num_ops: usize,
    lanes: usize,
    horner_packed_steps: usize,
    alu_quintic_trinomial: bool,
) -> Result<AluAir<F, TRACE_D>, String>
where
    F: Field + PrimeCharacteristicRing + Copy,
    EF: ExtensionField<F> + ExtractBinomialW<F>,
{
    if lanes == 0 {
        return Err("ALU lane count must be non-zero".to_string());
    }
    if horner_packed_steps == 0 {
        return Err("packed Horner step count must be positive".to_string());
    }
    let reduction = AluExtMulKind::resolve(
        TRACE_D,
        EF::extract_w(),
        TRACE_D == 5 && alu_quintic_trinomial,
    )
    .ok_or_else(|| {
        format!(
            "unsupported ALU extension-multiplication kind for trace degree {TRACE_D} \
             (alu_quintic_trinomial={alu_quintic_trinomial})"
        )
    })?;
    Ok(
        AluAir::<F, TRACE_D>::from_reduction(num_ops, lanes, reduction)
            .with_horner_pack_k(horner_packed_steps),
    )
}

pub struct ReconstructedBatchTables<SC: StarkGenericConfig, const D: usize> {
    pub airs: Vec<CircuitTablesAir<SC, D>>,
    pub trace_lens: Vec<usize>,
    pub public_values: Vec<Vec<Val<SC>>>,
}

pub fn reconstruct_batch_tables<SC: StarkGenericConfig + 'static, const TRACE_D: usize>(
    config: &SC,
    proof: &p3_circuit_prover::batch_stark_prover::BatchStarkProof<SC>,
    non_primitive_provers: &[Box<dyn TableProver<SC>>],
) -> Result<ReconstructedBatchTables<SC, TRACE_D>, VerificationError>
where
    Val<SC>: PrimeField64,
    SC::Challenge: ExtensionField<Val<SC>> + ExtractBinomialW<Val<SC>>,
{
    proof
        .validate()
        .map_err(|e| VerificationError::InvalidProofShape(e.to_string()))?;
    if proof.ext_degree != TRACE_D {
        return Err(VerificationError::InvalidProofShape(format!(
            "trace extension degree mismatch: proof declares {} but verifier expects {TRACE_D}",
            proof.ext_degree
        )));
    }
    if proof.non_primitives.len() != non_primitive_provers.len() {
        return Err(VerificationError::InvalidProofShape(format!(
            "non-primitive table count mismatch: expected {}, got {}",
            non_primitive_provers.len(),
            proof.non_primitives.len()
        )));
    }
    for (i, (entry, plugin)) in proof
        .non_primitives
        .iter()
        .zip(non_primitive_provers.iter())
        .enumerate()
    {
        let expected_op = TableProver::op_type(plugin.as_ref());
        if entry.op_type != expected_op {
            return Err(VerificationError::InvalidProofShape(format!(
                "non-primitive op_type mismatch at index {i}: expected {expected_op:?}, got {:?}",
                entry.op_type
            )));
        }
    }
    let rows: RowCounts = proof.rows;
    let packing = proof.table_packing.clone();
    let public_lanes = packing.public_lanes();
    let alu_lanes = packing.alu_lanes();

    let alu_air = match proof.alu_variant {
        AirVariant::Baseline | AirVariant::Optimized => {
            create_alu_air::<Val<SC>, SC::Challenge, TRACE_D>(
                rows[PrimitiveTable::Alu],
                alu_lanes,
                packing.horner_packed_steps(),
                proof.alu_quintic_trinomial,
            )
            .map_err(VerificationError::InvalidProofShape)?
        }
    };

    let mut airs: Vec<CircuitTablesAir<SC, TRACE_D>> = vec![
        CircuitTablesAir::Const(ConstAir::<Val<SC>, TRACE_D>::new(
            rows[PrimitiveTable::Const],
        )),
        CircuitTablesAir::Public(PublicAir::<Val<SC>, TRACE_D>::new(
            rows[PrimitiveTable::Public],
            public_lanes,
        )),
        CircuitTablesAir::Alu(alu_air),
    ];
    let mut trace_lens = vec![
        rows[PrimitiveTable::Const],
        rows[PrimitiveTable::Public],
        rows[PrimitiveTable::Alu],
    ];
    let mut public_values: Vec<Vec<Val<SC>>> = vec![Vec::new(); NUM_PRIMITIVE_TABLES];

    for (entry, plugin) in proof
        .non_primitives
        .iter()
        .zip(non_primitive_provers.iter())
    {
        let air = plugin
            .batch_air_from_table_entry(config, TRACE_D, proof.ext_degree as u32, entry)
            .map_err(VerificationError::InvalidProofShape)?;
        airs.push(CircuitTablesAir::Dynamic(air));
        trace_lens.push(entry.rows);
        public_values.push(entry.public_values.clone());
    }

    Ok(ReconstructedBatchTables {
        airs,
        trace_lens,
        public_values,
    })
}

pub fn trusted_batch_tables<SC: StarkGenericConfig + 'static, const TRACE_D: usize>(
    verifier: &CircuitVerifier<SC>,
    expected_statement: &[Val<SC>],
) -> Result<ReconstructedBatchTables<SC, TRACE_D>, VerificationError>
where
    Val<SC>: PrimeField64 + p3_circuit_prover::config::StarkField,
    SC::Challenge: ExtensionField<Val<SC>> + ExtractBinomialW<Val<SC>>,
    SymbolicExpressionExt<Val<SC>, SC::Challenge>:
        Algebra<SymbolicExpression<Val<SC>>> + Algebra<SC::Challenge>,
{
    let relation = verifier.relation();
    if relation.ext_degree() != TRACE_D {
        return Err(VerificationError::InvalidProofShape(format!(
            "trusted verifier extension degree mismatch: descriptor declares {}, backend expects {TRACE_D}",
            relation.ext_degree()
        )));
    }
    let airs = verifier
        .table_airs::<TRACE_D>()
        .map_err(|error| VerificationError::InvalidProofShape(error.to_string()))?
        .into_iter()
        .map(CircuitTablesAir::from_table_air)
        .collect::<Vec<_>>();
    if airs.len() != relation.trace_degree_bits().len() {
        return Err(VerificationError::InvalidProofShape(
            "trusted verifier table/degree cardinality mismatch".into(),
        ));
    }
    let zk = verifier.config().is_zk();
    let trace_lens = relation
        .trace_degree_bits()
        .iter()
        .map(|&degree| {
            degree
                .checked_sub(zk)
                .and_then(|base_degree| 1usize.checked_shl(base_degree as u32))
                .ok_or_else(|| {
                    VerificationError::InvalidProofShape(
                        "trusted verifier trace degree is invalid".into(),
                    )
                })
        })
        .collect::<Result<Vec<_>, _>>()?;
    let public_values = verifier
        .table_public_values(expected_statement)
        .map_err(|error| VerificationError::InvalidProofShape(error.to_string()))?;
    if public_values.len() != airs.len() {
        return Err(VerificationError::InvalidProofShape(
            "trusted verifier AIR/public-value cardinality mismatch".into(),
        ));
    }
    Ok(ReconstructedBatchTables {
        airs,
        trace_lens,
        public_values,
    })
}

#[allow(clippy::type_complexity)]
#[allow(clippy::too_many_arguments)]
pub fn verify_p3_batch_proof_circuit<
    SC: StarkGenericConfig + 'static,
    Comm: Recursive<
            SC::Challenge,
            Input = <SC::Pcs as Pcs<SC::Challenge, SC::Challenger>>::Commitment,
        > + Clone
        + ObservableCommitment,
    InputProof: Recursive<SC::Challenge>,
    OpeningProof: Recursive<SC::Challenge, Input = <SC::Pcs as Pcs<SC::Challenge, SC::Challenger>>::Proof>,
    LG: RecursiveLookupGadget<SC::Challenge>,
    CP: ChallengerPermConfig,
    const WIDTH: usize,
    const RATE: usize,
    const TRACE_D: usize,
>(
    config: &SC,
    circuit: &mut CircuitBuilder<SC::Challenge>,
    proof: &p3_circuit_prover::batch_stark_prover::BatchStarkProof<SC>,
    pcs_params: &PcsVerifierParams<SC, InputProof, OpeningProof, Comm>,
    common_data: &CommonData<SC>,
    lookup_gadget: &LG,
    challenger_perm_config: CP,
    non_primitive_provers: &[Box<dyn TableProver<SC>>],
) -> Result<
    (
        BatchStarkVerifierInputsBuilder<SC, Comm, OpeningProof>,
        Vec<NonPrimitiveOpId>,
    ),
    VerificationError,
>
where
    <SC as StarkGenericConfig>::Pcs: RecursivePcs<
            SC,
            InputProof,
            OpeningProof,
            Comm,
            <SC::Pcs as Pcs<SC::Challenge, SC::Challenger>>::Domain,
        >,
    Val<SC>: PrimeField64,
    SC::Challenge: ExtensionField<Val<SC>> + PrimeCharacteristicRing + ExtractBinomialW<Val<SC>>,
    <<SC as StarkGenericConfig>::Pcs as Pcs<SC::Challenge, SC::Challenger>>::Domain: Clone,
    SymbolicExpressionExt<Val<SC>, SC::Challenge>:
        Algebra<SymbolicExpression<Val<SC>>> + Algebra<SC::Challenge>,
{
    let tables = reconstruct_batch_tables::<SC, TRACE_D>(config, proof, non_primitive_provers)?;
    verify_p3_batch_proof_circuit_with_tables::<
        SC,
        Comm,
        InputProof,
        OpeningProof,
        LG,
        CP,
        WIDTH,
        RATE,
        TRACE_D,
    >(
        config,
        circuit,
        proof,
        pcs_params,
        common_data,
        lookup_gadget,
        challenger_perm_config,
        &tables,
        true,
    )
}

#[allow(clippy::type_complexity)]
#[allow(clippy::too_many_arguments)]
pub fn verify_trusted_p3_batch_proof_circuit<
    SC: StarkGenericConfig + 'static,
    Comm: Recursive<
            SC::Challenge,
            Input = <SC::Pcs as Pcs<SC::Challenge, SC::Challenger>>::Commitment,
        > + Clone
        + ObservableCommitment,
    InputProof: Recursive<SC::Challenge>,
    OpeningProof: Recursive<SC::Challenge, Input = <SC::Pcs as Pcs<SC::Challenge, SC::Challenger>>::Proof>,
    LG: RecursiveLookupGadget<SC::Challenge>,
    CP: ChallengerPermConfig,
    const WIDTH: usize,
    const RATE: usize,
    const TRACE_D: usize,
>(
    verifier: &CircuitVerifier<SC>,
    circuit: &mut CircuitBuilder<SC::Challenge>,
    proof: &p3_circuit_prover::batch_stark_prover::BatchStarkProof<SC>,
    statement: &[Val<SC>],
    pcs_params: &PcsVerifierParams<SC, InputProof, OpeningProof, Comm>,
    lookup_gadget: &LG,
    challenger_perm_config: CP,
) -> Result<
    (
        BatchStarkVerifierInputsBuilder<SC, Comm, OpeningProof>,
        Vec<NonPrimitiveOpId>,
    ),
    VerificationError,
>
where
    SC::Challenger: p3_challenger::GrindingChallenger<Witness = p3_uni_stark::Val<SC>>,
    <SC as StarkGenericConfig>::Pcs: RecursivePcs<
            SC,
            InputProof,
            OpeningProof,
            Comm,
            <SC::Pcs as Pcs<SC::Challenge, SC::Challenger>>::Domain,
        >,
    Val<SC>: PrimeField64 + p3_circuit_prover::config::StarkField,
    SC::Challenge: ExtensionField<Val<SC>> + PrimeCharacteristicRing + ExtractBinomialW<Val<SC>>,
    <<SC as StarkGenericConfig>::Pcs as Pcs<SC::Challenge, SC::Challenger>>::Domain: Clone,
    SymbolicExpressionExt<Val<SC>, SC::Challenge>:
        Algebra<SymbolicExpression<Val<SC>>> + Algebra<SC::Challenge>,
{
    verifier
        .verify(proof, statement)
        .map_err(|error| VerificationError::InvalidProofShape(error.to_string()))?;
    let tables = trusted_batch_tables::<SC, TRACE_D>(verifier, statement)?;
    verify_p3_batch_proof_circuit_with_tables::<
        SC,
        Comm,
        InputProof,
        OpeningProof,
        LG,
        CP,
        WIDTH,
        RATE,
        TRACE_D,
    >(
        verifier.config(),
        circuit,
        proof,
        pcs_params,
        verifier.common_data(),
        lookup_gadget,
        challenger_perm_config,
        &tables,
        false,
    )
}

#[allow(clippy::type_complexity)]
#[allow(clippy::too_many_arguments)]
fn verify_p3_batch_proof_circuit_with_tables<
    SC: StarkGenericConfig + 'static,
    Comm: Recursive<
            SC::Challenge,
            Input = <SC::Pcs as Pcs<SC::Challenge, SC::Challenger>>::Commitment,
        > + Clone
        + ObservableCommitment,
    InputProof: Recursive<SC::Challenge>,
    OpeningProof: Recursive<SC::Challenge, Input = <SC::Pcs as Pcs<SC::Challenge, SC::Challenger>>::Proof>,
    LG: RecursiveLookupGadget<SC::Challenge>,
    CP: ChallengerPermConfig,
    const WIDTH: usize,
    const RATE: usize,
    const TRACE_D: usize,
>(
    config: &SC,
    circuit: &mut CircuitBuilder<SC::Challenge>,
    proof: &p3_circuit_prover::batch_stark_prover::BatchStarkProof<SC>,
    pcs_params: &PcsVerifierParams<SC, InputProof, OpeningProof, Comm>,
    common_data: &CommonData<SC>,
    lookup_gadget: &LG,
    challenger_perm_config: CP,
    tables: &ReconstructedBatchTables<SC, TRACE_D>,
    rebuild_lookups: bool,
) -> Result<
    (
        BatchStarkVerifierInputsBuilder<SC, Comm, OpeningProof>,
        Vec<NonPrimitiveOpId>,
    ),
    VerificationError,
>
where
    <SC as StarkGenericConfig>::Pcs: RecursivePcs<
            SC,
            InputProof,
            OpeningProof,
            Comm,
            <SC::Pcs as Pcs<SC::Challenge, SC::Challenger>>::Domain,
        >,
    Val<SC>: PrimeField64,
    SC::Challenge: ExtensionField<Val<SC>> + PrimeCharacteristicRing + ExtractBinomialW<Val<SC>>,
    <<SC as StarkGenericConfig>::Pcs as Pcs<SC::Challenge, SC::Challenger>>::Domain: Clone,
    SymbolicExpressionExt<Val<SC>, SC::Challenge>:
        Algebra<SymbolicExpression<Val<SC>>> + Algebra<SC::Challenge>,
{
    let ReconstructedBatchTables {
        airs: circuit_airs,
        trace_lens,
        public_values,
    } = &tables;

    let air_public_counts: Vec<usize> = public_values.iter().map(Vec::len).collect();
    let mut verifier_inputs = BatchStarkVerifierInputsBuilder::<SC, Comm, OpeningProof>::allocate(
        circuit,
        &proof.proof,
        common_data,
        &air_public_counts,
    )?;

    if rebuild_lookups {
        verifier_inputs.common_data.lookups = circuit_airs
            .iter()
            .zip(trace_lens.iter())
            .map(|(air, &trace_len)| {
                lookups_for_circuit_table_air::<SC, TRACE_D>(
                    &air.to_table_air(),
                    trace_len,
                    config.is_zk(),
                )
                .to_vec()
            })
            .collect();
    }

    let common = &verifier_inputs.common_data;

    let mmcs_op_ids = verify_batch_circuit::<
        CircuitTablesAir<SC, TRACE_D>,
        SC,
        Comm,
        InputProof,
        OpeningProof,
        LG,
        CP,
        WIDTH,
        RATE,
    >(
        config,
        circuit_airs,
        circuit,
        &verifier_inputs.proof_targets,
        &verifier_inputs.air_public_targets,
        pcs_params,
        common,
        lookup_gadget,
        challenger_perm_config,
    )?;

    Ok((verifier_inputs, mmcs_op_ids))
}

#[allow(clippy::too_many_arguments)]
pub fn verify_batch_circuit<
    A,
    SC: StarkGenericConfig,
    Comm: Recursive<
            SC::Challenge,
            Input = <SC::Pcs as Pcs<SC::Challenge, SC::Challenger>>::Commitment,
        > + Clone
        + ObservableCommitment,
    InputProof: Recursive<SC::Challenge>,
    OpeningProof: Recursive<SC::Challenge>,
    LG: RecursiveLookupGadget<SC::Challenge>,
    CP: ChallengerPermConfig,
    const WIDTH: usize,
    const RATE: usize,
>(
    config: &SC,
    airs: &[A],
    circuit: &mut CircuitBuilder<SC::Challenge>,
    proof_targets: &BatchProofTargets<SC, Comm, OpeningProof>,
    public_values: &[Vec<Target>],
    pcs_params: &PcsVerifierParams<SC, InputProof, OpeningProof, Comm>,
    common: &CommonDataTargets<SC, Comm>,
    lookup_gadget: &LG,
    challenger_perm_config: CP,
) -> Result<Vec<NonPrimitiveOpId>, VerificationError>
where
    A: RecursiveAir<Val<SC>, SC::Challenge, LG>,
    <SC as StarkGenericConfig>::Pcs: RecursivePcs<
            SC,
            InputProof,
            OpeningProof,
            Comm,
            <SC::Pcs as Pcs<SC::Challenge, SC::Challenger>>::Domain,
        >,
    Val<SC>: PrimeField64,
    SC::Challenge: ExtensionField<Val<SC>> + PrimeCharacteristicRing,
    <<SC as StarkGenericConfig>::Pcs as Pcs<SC::Challenge, SC::Challenger>>::Domain: Clone,
{
    let BatchProofTargets {
        commitments_targets,
        flattened_opened_values_targets: flattened,
        opened_values_targets,
        opening_proof,
        lookup_terminals,
        degree_bits,
    } = proof_targets;
    let instances = &opened_values_targets.instances;

    if airs.is_empty() {
        return Err(VerificationError::InvalidProofShape(
            "batch-STARK verification requires at least one instance".to_string(),
        ));
    }

    if airs.len() != instances.len()
        || airs.len() != public_values.len()
        || airs.len() != proof_targets.degree_bits.len()
    {
        return Err(VerificationError::InvalidProofShape(
            "Mismatch between number of AIRs, instances, public values, or degree bits".to_string(),
        ));
    }

    if lookup_terminals.len() != instances.len() {
        return Err(VerificationError::InvalidProofShape(format!(
            "lookup terminal count mismatch: expected {}, got {}",
            instances.len(),
            lookup_terminals.len()
        )));
    }

    let pcs = config.pcs();
    for (i, &db) in degree_bits.iter().enumerate() {
        validate_degree_bits(
            Some(i),
            db,
            config.is_zk(),
            pcs.log_min_trace_height(),
            pcs.log_max_trace_height(),
        )
        .map_err(|e| VerificationError::InvalidProofShape(e.to_string()))?;
    }

    if common.lookups.len() != airs.len() {
        return Err(VerificationError::InvalidProofShape(format!(
            "common-data lookups length must equal number of AIR instances: expected {}, got {}",
            airs.len(),
            common.lookups.len()
        )));
    }
    if let Some(global) = &common.preprocessed {
        let metadata = global
            .instances
            .instances
            .iter()
            .map(|entry| {
                entry
                    .as_ref()
                    .map(|meta| (meta.matrix_index, meta.width, meta.degree_bits))
            })
            .collect::<Vec<_>>();
        validate_preprocessed_metadata(&metadata, &global.matrix_to_instance, degree_bits)
            .map_err(|error| VerificationError::InvalidProofShape(error.to_string()))?;
    }

    let all_lookups = &common.lookups;

    let pcs = config.pcs();

    let n_instances = airs.len();

    if (instances
        .iter()
        .any(|inst| inst.opened_values_no_lookups.random_targets.is_some() != SC::Pcs::ZK))
        || (commitments_targets.random_commit.is_some() != SC::Pcs::ZK)
    {
        return Err(VerificationError::RandomizationError);
    }

    let mut preprocessed_widths = Vec::with_capacity(airs.len());
    let mut log_quotient_degrees = Vec::with_capacity(n_instances);
    let mut quotient_degrees = Vec::with_capacity(n_instances);
    let mut permutation_widths = Vec::with_capacity(n_instances);
    for (i, (air, instance)) in airs.iter().zip(instances.iter()).enumerate() {
        let OpenedValuesTargets {
            trace_local_targets,
            trace_next_targets,
            preprocessed_local_targets,
            preprocessed_next_targets,
            quotient_chunks_targets,
            random_targets,
            ..
        } = &instance.opened_values_no_lookups;

        let pre_w = common
            .preprocessed
            .as_ref()
            .and_then(|g| g.instances.instances[i].as_ref().map(|m| m.width))
            .unwrap_or(0);
        preprocessed_widths.push(pre_w);

        let local_prep_len = preprocessed_local_targets.as_ref().map_or(0, |v| v.len());
        let next_prep_len = preprocessed_next_targets.as_ref().map_or(0, |v| v.len());
        let expected_next_prep_len = if air.opens_preprocessed_next() {
            pre_w
        } else {
            0
        };
        if local_prep_len != pre_w || next_prep_len != expected_next_prep_len {
            return Err(VerificationError::InvalidProofShape(format!(
                "Instance has incorrect preprocessed width: expected {pre_w} / {expected_next_prep_len}, got {local_prep_len} / {next_prep_len}"
            )));
        }
        let air_width = A::width(air);
        let expected_next_len = if air.opens_trace_next() { air_width } else { 0 };
        if trace_local_targets.len() != air_width || trace_next_targets.len() != expected_next_len {
            return Err(VerificationError::InvalidProofShape(format!(
                "Instance has incorrect trace width: expected {air_width} / {expected_next_len}, got {} / {}",
                trace_local_targets.len(),
                trace_next_targets.len()
            )));
        }

        let expected_permutation_width = if all_lookups[i].is_empty() {
            0
        } else {
            (all_lookups[i].len() + 1)
                .checked_mul(SC::Challenge::DIMENSION)
                .ok_or_else(|| {
                    VerificationError::InvalidProofShape(
                        "packed permutation width overflows".to_string(),
                    )
                })?
        };
        if instance.permutation_local_targets.len() != expected_permutation_width
            || instance.permutation_next_targets.len() != expected_permutation_width
        {
            return Err(VerificationError::InvalidProofShape(
                "flattened permutation opening width does not match packed lookup metadata"
                    .to_string(),
            ));
        }
        permutation_widths.push(expected_permutation_width);

        let expected_present = air.declares_interactions(pre_w);
        if lookup_terminals[i].is_some() != expected_present {
            return Err(VerificationError::InvalidProofShape(
                "Lookup terminal presence does not match the AIR's declared lookups".to_string(),
            ));
        }

        let base_db = degree_bits[i].checked_sub(config.is_zk()).ok_or_else(|| {
            VerificationError::InvalidProofShape(
                "Extended degree bits smaller than ZK adjustment".to_string(),
            )
        })?;
        let log_qd = A::get_log_num_quotient_chunks(
            air,
            pre_w,
            1usize << base_db,
            &all_lookups[i],
            config.is_zk(),
            lookup_gadget,
        );
        let quotient_degree = 1 << (log_qd + config.is_zk());

        if quotient_chunks_targets.len() != quotient_degree {
            return Err(VerificationError::InvalidProofShape(format!(
                "Instance quotient chunk count mismatch: expected {}, got {}",
                quotient_degree,
                quotient_chunks_targets.len()
            )));
        }

        if quotient_chunks_targets
            .iter()
            .any(|chunk| chunk.len() != SC::Challenge::DIMENSION)
        {
            return Err(VerificationError::InvalidProofShape(format!(
                "Invalid quotient chunk length: expected {}",
                SC::Challenge::DIMENSION
            )));
        }

        if random_targets
            .as_ref()
            .is_some_and(|r_vals| r_vals.len() != SC::Challenge::DIMENSION)
        {
            return Err(VerificationError::RandomizationError);
        }

        log_quotient_degrees.push(log_qd);
        quotient_degrees.push(quotient_degree);
    }

    let layout_instances: Vec<InstanceLayout> = airs
        .iter()
        .zip(degree_bits.iter().zip(log_quotient_degrees.iter()))
        .enumerate()
        .map(|(i, (air, (&ext_log, &quotient_log)))| InstanceLayout {
            ext_log,
            base_log: ext_log - config.is_zk(),
            challenge_width: SC::Challenge::DIMENSION,
            trace_width: air.width(),
            trace_next: air.opens_trace_next(),
            pre_width: preprocessed_widths[i],
            pre_next: air.opens_preprocessed_next(),
            quotient_log,
            quotient_chunks: quotient_degrees[i],
            permutation_width: permutation_widths[i],
        })
        .collect();
    let preprocessed_order = common
        .preprocessed
        .as_ref()
        .map_or(&[][..], |global| global.matrix_to_instance.as_slice());
    let layout = NativeStarkLayout::new(
        layout_instances,
        preprocessed_order,
        commitments_targets.random_commit.is_some(),
        common.preprocessed.is_some(),
        commitments_targets.permutation_targets.is_some(),
    )
    .map_err(|error| VerificationError::InvalidProofShape(error.to_string()))?;
    if layout.commitment_count()
        != usize::from(commitments_targets.random_commit.is_some())
            + 2
            + usize::from(common.preprocessed.is_some())
            + usize::from(commitments_targets.permutation_targets.is_some())
    {
        return Err(VerificationError::InvalidProofShape(
            "STARK opening commitment layout mismatch".to_string(),
        ));
    }
    debug_assert_eq!(
        layout.commitment_role(usize::from(layout.has_random)),
        Some(CommitmentRole::Trace)
    );

    if config.lookup_proof_of_work_bits() != 0 || config.ood_proof_of_work_bits() != 0 {
        return Err(VerificationError::InvalidProofShape(
            "recursive batch-STARK verification requires zero lookup and OOD proof of work"
                .to_string(),
        ));
    }

    let transcript_shape = BatchShape {
        trace_widths: airs.iter().map(|air| A::width(air)).collect(),
        public_value_counts: public_values.iter().map(Vec::len).collect(),
        preprocessed_widths: preprocessed_widths.clone(),
        has_preprocessed_commitment: common.preprocessed.is_some(),
        num_lookup_instances: all_lookups.iter().filter(|c| !c.is_empty()).count(),
        lookup_pow_bits: config.lookup_proof_of_work_bits(),
        has_randomization_commitment: SC::Pcs::ZK,
        ood_pow_bits: config.ood_proof_of_work_bits(),
    };
    let mut challenger = CircuitChallenger::<WIDTH, RATE, CP>::new(challenger_perm_config);
    challenger.observe_seed(
        circuit,
        &domain_separator_seed(&transcript_shape.domain_separator::<Val<SC>, SC::Challenge>()),
    );
    for &ext_db in degree_bits {
        let ext_db_target =
            circuit.alloc_const(SC::Challenge::from_usize(ext_db), "extended degree bits");
        challenger.observe_ext(circuit, ext_db_target);
    }

    challenger.observe_slice(
        circuit,
        &commitments_targets.trace_targets.to_observation_targets(),
    );
    for pv in public_values {
        challenger.observe_slice(circuit, pv);
    }
    if let Some(global) = &common.preprocessed {
        challenger.observe_slice(circuit, &global.commitment.to_observation_targets());
    }

    let is_lookup = proof_targets
        .commitments_targets
        .permutation_targets
        .is_some();
    if is_lookup != all_lookups.iter().any(|c| !c.is_empty()) {
        return Err(VerificationError::InvalidProofShape(
            "Mismatch between lookup commitment and lookup data".to_string(),
        ));
    }

    let challenges_per_instance = get_perm_challenges::<SC, CP, WIDTH, RATE, LG>(
        circuit,
        &mut challenger,
        all_lookups,
        lookup_gadget,
    );

    if let Some(permutation) = &commitments_targets.permutation_targets {
        challenger.observe_slice(circuit, &permutation.to_observation_targets());
    }
    for terminal in lookup_terminals.iter().flatten() {
        challenger.observe_ext(circuit, *terminal);
    }

    let alpha = challenger.sample_ext(circuit);

    challenger.observe_slice(
        circuit,
        &commitments_targets
            .quotient_chunks_targets
            .to_observation_targets(),
    );
    if let Some(random_commit) = &commitments_targets.random_commit {
        challenger.observe_slice(circuit, &random_commit.to_observation_targets());
    }
    let zeta = challenger.sample_ext(circuit);

    let mut trace_domains = Vec::with_capacity(n_instances);
    let mut ext_trace_domains = Vec::with_capacity(n_instances);
    for &ext_db in degree_bits {
        let base_db = ext_db.checked_sub(config.is_zk()).ok_or_else(|| {
            VerificationError::InvalidProofShape(
                "Extended degree bits smaller than ZK adjustment".to_string(),
            )
        })?;
        trace_domains.push(pcs.natural_domain_for_degree(1 << base_db));
        ext_trace_domains.push(pcs.natural_domain_for_degree(1 << ext_db));
    }

    let mut coms_to_verify = Vec::with_capacity(5);

    if let Some(random_commit) = &commitments_targets.random_commit {
        let random_round = layout
            .matrices(CommitmentRole::Random)
            .map(|matrix| {
                let MatrixRoute::Random { instance } = matrix.route else {
                    unreachable!("random planner emits only random routes")
                };
                let random_vals = instances[instance]
                    .opened_values_no_lookups
                    .random_targets
                    .as_ref()
                    .ok_or(VerificationError::RandomizationError)?;
                Ok((
                    ext_trace_domains[instance],
                    vec![(zeta, random_vals.clone())],
                ))
            })
            .collect::<Result<Vec<_>, VerificationError>>()?;
        coms_to_verify.push((random_commit.clone(), random_round));
    }

    let trace_domain_generator =
        |trace_dom: &<SC::Pcs as Pcs<SC::Challenge, SC::Challenger>>::Domain| {
            let first_point = pcs.first_point(trace_dom);
            let next_point = trace_dom.next_point(first_point).ok_or_else(|| {
                VerificationError::InvalidProofShape(
                    "Trace domain does not provide next point".to_string(),
                )
            })?;
            Ok::<_, VerificationError>(next_point * first_point.inverse())
        };

    let trace_round: Vec<_> = layout
        .matrices(CommitmentRole::Trace)
        .map(|matrix| {
            let MatrixRoute::Trace { instance } = matrix.route else {
                unreachable!("trace planner emits only trace routes")
            };
            let inst = &instances[instance];
            let mut points = vec![(
                zeta,
                inst.opened_values_no_lookups.trace_local_targets.clone(),
            )];
            if matrix.point_count == 2 {
                let generator_const =
                    circuit.define_const(trace_domain_generator(&trace_domains[instance])?);
                let zeta_next = circuit.mul(zeta, generator_const);
                points.push((
                    zeta_next,
                    inst.opened_values_no_lookups.trace_next_targets.clone(),
                ));
            }
            Ok((ext_trace_domains[instance], points))
        })
        .collect::<Result<_, VerificationError>>()?;
    coms_to_verify.push((commitments_targets.trace_targets.clone(), trace_round));

    let quotient_domains: Vec<Vec<_>> = degree_bits
        .iter()
        .zip(ext_trace_domains.iter())
        .zip(log_quotient_degrees.iter())
        .map(
            |((&ext_db, ext_dom), &log_qd)| -> Result<Vec<_>, VerificationError> {
                let base_db = ext_db.checked_sub(config.is_zk()).ok_or_else(|| {
                    VerificationError::InvalidProofShape(
                        "Extended degree bits smaller than ZK adjustment".to_string(),
                    )
                })?;
                let q_domain =
                    ext_dom.create_disjoint_domain(1 << (base_db + log_qd + config.is_zk()));
                Ok(q_domain.split_domains(1 << (log_qd + config.is_zk())))
            },
        )
        .collect::<Result<Vec<_>, VerificationError>>()?;

    let randomized_quotient_domains: Vec<Vec<_>> = quotient_domains
        .iter()
        .map(|domains| {
            domains
                .iter()
                .map(|domain| pcs.natural_domain_for_degree(pcs.size(domain) << config.is_zk()))
                .collect()
        })
        .collect();

    let mut quotient_round = Vec::with_capacity(
        layout
            .instances
            .iter()
            .map(|instance| instance.quotient_chunks)
            .sum(),
    );
    for matrix in layout.matrices(CommitmentRole::Quotient) {
        let MatrixRoute::Quotient { instance, chunk } = matrix.route else {
            unreachable!("quotient planner emits only quotient routes")
        };
        let domain = randomized_quotient_domains[instance]
            .get(chunk)
            .ok_or_else(|| {
                VerificationError::InvalidProofShape(
                    "Quotient chunk count mismatch across domains".to_string(),
                )
            })?;
        let values = instances[instance]
            .opened_values_no_lookups
            .quotient_chunks_targets
            .get(chunk)
            .ok_or_else(|| {
                VerificationError::InvalidProofShape(
                    "Quotient chunk count mismatch across domains".to_string(),
                )
            })?;
        quotient_round.push((*domain, vec![(zeta, values.clone())]));
    }
    coms_to_verify.push((
        commitments_targets.quotient_chunks_targets.clone(),
        quotient_round,
    ));

    if let Some(global) = &common.preprocessed {
        let mut pre_round = Vec::with_capacity(global.matrix_to_instance.len());

        for matrix in layout.matrices(CommitmentRole::Preprocessed) {
            let MatrixRoute::Preprocessed {
                instance: inst_idx,
                matrix: matrix_index,
            } = matrix.route
            else {
                unreachable!("preprocessed planner emits only preprocessed routes")
            };
            let pre_w = preprocessed_widths[inst_idx];
            if pre_w == 0 {
                return Err(VerificationError::InvalidProofShape(
                    "Instance has preprocessed columns with zero width".to_string(),
                ));
            }

            let inst = &instances[inst_idx];
            let local = inst
                .opened_values_no_lookups
                .preprocessed_local_targets
                .as_ref()
                .ok_or_else(|| {
                    VerificationError::InvalidProofShape(
                        "Missing preprocessed local columns".to_string(),
                    )
                })?;
            let mut points = vec![(zeta, local.clone())];
            let ext_db = degree_bits[inst_idx];

            let meta = global.instances.instances[inst_idx]
                .as_ref()
                .ok_or_else(|| {
                    VerificationError::InvalidProofShape(
                        "Missing preprocessed instance metadata".to_string(),
                    )
                })?;
            if meta.matrix_index != matrix_index || meta.degree_bits != ext_db {
                return Err(VerificationError::InvalidProofShape(
                    "Preprocessed instance metadata mismatch".to_string(),
                ));
            }

            let pre_domain = pcs.natural_domain_for_degree(1 << meta.degree_bits);

            let trace_dom = &trace_domains[inst_idx];
            let generator_const = circuit.define_const(trace_domain_generator(trace_dom)?);
            let zeta_next = circuit.mul(zeta, generator_const);

            if matrix.point_count == 2 {
                let next = inst
                    .opened_values_no_lookups
                    .preprocessed_next_targets
                    .as_ref()
                    .ok_or_else(|| {
                        VerificationError::InvalidProofShape(
                            "Missing preprocessed next columns".to_string(),
                        )
                    })?;
                points.push((zeta_next, next.clone()));
            }

            pre_round.push((pre_domain, points));
        }

        coms_to_verify.push((global.commitment.clone(), pre_round));
    }

    if is_lookup {
        let permutation_commit = commitments_targets
            .permutation_targets
            .clone()
            .expect("We checked that the commitment exists");

        let mut permutation_round = Vec::with_capacity(ext_trace_domains.len());

        for matrix in layout.matrices(CommitmentRole::Permutation) {
            let MatrixRoute::Permutation { instance: i } = matrix.route else {
                unreachable!("permutation planner emits only permutation routes")
            };
            let ext_dom = &ext_trace_domains[i];
            let inst = &instances[i];
            let permutation_local = &inst.permutation_local_targets;
            let permutation_next = &inst.permutation_next_targets;
            let trace_dom = &trace_domains[i];
            let generator_const = circuit.define_const(trace_domain_generator(trace_dom)?);
            let zeta_next = circuit.mul(zeta, generator_const);
            permutation_round.push((
                *ext_dom,
                vec![
                    (zeta, permutation_local.clone()),
                    (zeta_next, permutation_next.clone()),
                ],
            ));
        }

        coms_to_verify.push((permutation_commit, permutation_round));
    }

    if SC::Pcs::PRE_OBSERVES_OPENED_VALUES {
        let fri_random_rounds = SC::Pcs::get_fri_random_opened_values(&proof_targets.opening_proof);
        let claims = collect_opened_values_circuit::<SC>(instances, fri_random_rounds, &layout);
        let seed = SC::Pcs::claims_transcript_seed(pcs_params, claimed_evaluation_counts(&claims));
        observe_claims_circuit::<SC, CP, WIDTH, RATE>(circuit, &mut challenger, &seed, &claims);
    }

    let pcs_challenges = SC::Pcs::get_challenges_circuit::<WIDTH, RATE, CP>(
        circuit,
        &mut challenger,
        &proof_targets.opening_proof,
        flattened,
        pcs_params,
    )?;

    let mmcs_op_ids = pcs.verify_circuit::<WIDTH, RATE, CP>(
        circuit,
        &pcs_challenges,
        &mut challenger,
        &coms_to_verify,
        opening_proof,
        pcs_params,
    )?;

    for i in 0..n_instances {
        let air = &airs[i];
        let inst = &instances[i];
        let trace_domain = &trace_domains[i];
        let public_values = &public_values[i];
        let domains = &quotient_domains[i];

        let quotient = recompose_quotient_from_chunks_circuit::<SC, _, _, _, _>(
            circuit,
            domains,
            &inst.opened_values_no_lookups.quotient_chunks_targets,
            zeta,
            pcs,
        );

        let aux_width = if all_lookups[i].is_empty() {
            0
        } else {
            all_lookups[i].len() + 1
        };

        let recompose = |circuit: &mut CircuitBuilder<SC::Challenge>,
                         flat: &[Target]|
         -> Result<Vec<Target>, VerificationError> {
            let ext_degree = SC::Challenge::DIMENSION;
            let expected = aux_width * ext_degree;
            if flat.len() != expected {
                return Err(VerificationError::InvalidProofShape(format!(
                    "flattened permutation opening length ({}) must equal aux_width ({}) * \
                     DIMENSION ({}) = {}",
                    flat.len(),
                    aux_width,
                    ext_degree,
                    expected
                )));
            }
            if aux_width == 0 {
                return Ok(vec![]);
            }
            Ok(flat
                .chunks_exact(ext_degree)
                .map(|coeffs| {
                    let mut sum = circuit.define_const(SC::Challenge::ZERO);
                    coeffs.iter().enumerate().for_each(|(j, &coeff)| {
                        let e_i = circuit.define_const(
                            SC::Challenge::ith_basis_element(j)
                                .expect("Basis element should exist"),
                        );
                        sum = circuit.mul_add(coeff, e_i, sum);
                    });
                    sum
                })
                .collect())
        };

        let local_permutation_values = recompose(circuit, &inst.permutation_local_targets)?;
        let next_permutation_values = recompose(circuit, &inst.permutation_next_targets)?;

        let local_prep_values = match inst
            .opened_values_no_lookups
            .preprocessed_local_targets
            .as_ref()
        {
            Some(v) => v.as_slice(),
            None => &[],
        };
        let next_prep_values = match inst
            .opened_values_no_lookups
            .preprocessed_next_targets
            .as_ref()
        {
            Some(v) => v.as_slice(),
            None => &[],
        };

        let permutation_values: Vec<Target> = lookup_terminals[i].into_iter().collect();
        let sels = pcs.selectors_at_point_circuit(circuit, trace_domain, &zeta);
        let periodic_columns = air.periodic_columns();
        let periodic_values = pcs.evaluate_periodic_columns_at_point_circuit(
            circuit,
            trace_domain,
            &periodic_columns,
            zeta,
        )?;
        let columns_targets = ColumnsTargets {
            challenges: &challenges_per_instance[i],
            public_values,
            permutation_local_values: &local_permutation_values,
            permutation_next_values: &next_permutation_values,
            permutation_values: &permutation_values,
            local_prep_values,
            next_prep_values,
            periodic_values: &periodic_values,
            local_values: &inst.opened_values_no_lookups.trace_local_targets,
            next_values: &inst.opened_values_no_lookups.trace_next_targets,
        };

        let lookup_metadata = LookupMetadata {
            contexts: &all_lookups[i],
        };
        let folded_constraints = air.eval_folded_circuit(
            circuit,
            &sels,
            &alpha,
            &lookup_metadata,
            columns_targets,
            lookup_gadget,
        );

        let folded_mul = circuit.mul(folded_constraints, sels.inv_vanishing);
        circuit.connect(folded_mul, quotient);
    }

    let present_terminals: Vec<Target> = lookup_terminals.iter().flatten().copied().collect();
    lookup_gadget.verify_terminal_sum_circuit(circuit, &present_terminals);

    Ok(mmcs_op_ids)
}

pub(crate) fn get_perm_challenges<
    SC: StarkGenericConfig,
    CP: ChallengerPermConfig,
    const WIDTH: usize,
    const RATE: usize,
    LG: LookupProtocol,
>(
    circuit: &mut CircuitBuilder<SC::Challenge>,
    challenger: &mut CircuitChallenger<WIDTH, RATE, CP>,
    all_lookups: &[Vec<Lookup<Val<SC>>>],
    lookup_gadget: &LG,
) -> Vec<Vec<Target>>
where
    Val<SC>: PrimeField64,
    SC::Challenge: ExtensionField<Val<SC>>,
{
    assert_eq!(
        lookup_gadget.num_challenges(),
        2,
        "single-pair bus-prefix challenge layout requires exactly two challenges per lookup"
    );

    if !all_lookups.iter().any(|contexts| !contexts.is_empty()) {
        return all_lookups.iter().map(|_| Vec::new()).collect();
    }

    let alpha = challenger.sample_ext(circuit);
    let beta = challenger.sample_ext(circuit);

    let mut global_index: HashMap<&str, usize> = HashMap::new();
    let mut next_bus = 0usize;
    let mut max_message_width = 1usize;
    let mut bus_ids: Vec<Vec<usize>> = Vec::with_capacity(all_lookups.len());
    for contexts in all_lookups {
        let mut instance_buses = Vec::with_capacity(contexts.len());
        for context in contexts {
            for tuple in &context.elements {
                max_message_width = max_message_width.max(tuple.len());
            }
            let bus = match &context.kind {
                Kind::Global(name) => *global_index.entry(name.as_str()).or_insert_with(|| {
                    let id = next_bus;
                    next_bus += 1;
                    id
                }),
                Kind::Local => {
                    let id = next_bus;
                    next_bus += 1;
                    id
                }
            };
            instance_buses.push(bus);
        }
        bus_ids.push(instance_buses);
    }

    let mut gamma = beta;
    for _ in 1..max_message_width {
        gamma = circuit.mul(gamma, beta);
    }

    let mut prefix = alpha;
    let bus_prefix: Vec<Target> = (0..next_bus)
        .map(|_| {
            prefix = circuit.add(prefix, gamma);
            prefix
        })
        .collect();

    bus_ids
        .iter()
        .map(|instance_buses| {
            instance_buses
                .iter()
                .flat_map(|&bus| [bus_prefix[bus], beta])
                .collect()
        })
        .collect()
}

#[allow(clippy::too_many_arguments)]
pub(crate) fn collect_opened_values_circuit<SC>(
    instances: &[OpenedValuesTargetsWithLookups<SC>],
    fri_random_rounds: &[Vec<Vec<Vec<Target>>>],
    layout: &NativeStarkLayout<'_>,
) -> Vec<Vec<Vec<Vec<Target>>>>
where
    SC: StarkGenericConfig,
{
    let mut claims: Vec<Vec<Vec<Vec<Target>>>> = Vec::new();
    let point = |original: &[Target], fri_random: Option<&Vec<Target>>| -> Vec<Target> {
        let mut values = original.to_vec();
        if let Some(rand_vals) = fri_random {
            values.extend_from_slice(rand_vals);
        }
        values
    };

    let mut round_idx: usize = 0;

    if layout.has_random {
        let rand_round = fri_random_rounds.get(round_idx);
        let mut round = Vec::new();
        for (mat_idx, matrix) in layout.matrices(CommitmentRole::Random).enumerate() {
            let mut matrix_points = Vec::new();
            let MatrixRoute::Random { instance } = matrix.route else {
                unreachable!("random planner emits only random routes")
            };
            if let Some(random_vals) = &instances[instance].opened_values_no_lookups.random_targets
            {
                let fri_rand = rand_round
                    .and_then(|r| r.get(mat_idx))
                    .and_then(|m| m.first());
                matrix_points.push(point(random_vals, fri_rand));
            }
            round.push(matrix_points);
        }
        claims.push(round);
        round_idx += 1;
    }

    {
        let rand_round = fri_random_rounds.get(round_idx);
        let mut round = Vec::new();
        for (mat_idx, matrix) in layout.matrices(CommitmentRole::Trace).enumerate() {
            let mut matrix_points = Vec::new();
            let MatrixRoute::Trace { instance } = matrix.route else {
                unreachable!("trace planner emits only trace routes")
            };
            let inst = &instances[instance];
            let fri_rand_local = rand_round
                .and_then(|r| r.get(mat_idx))
                .and_then(|m| m.first());
            let fri_rand_next = rand_round
                .and_then(|r| r.get(mat_idx))
                .and_then(|m| m.get(1));
            matrix_points.push(point(
                &inst.opened_values_no_lookups.trace_local_targets,
                fri_rand_local,
            ));
            if matrix.point_count == 2 {
                matrix_points.push(point(
                    &inst.opened_values_no_lookups.trace_next_targets,
                    fri_rand_next,
                ));
            }
            round.push(matrix_points);
        }
        claims.push(round);
        round_idx += 1;
    }

    {
        let rand_round = fri_random_rounds.get(round_idx);
        let mut round = Vec::new();
        for (mat_idx, matrix) in layout.matrices(CommitmentRole::Quotient).enumerate() {
            let mut matrix_points = Vec::new();
            let MatrixRoute::Quotient { instance, chunk } = matrix.route else {
                unreachable!("quotient planner emits only quotient routes")
            };
            let chunk_values = &instances[instance]
                .opened_values_no_lookups
                .quotient_chunks_targets[chunk];
            let fri_rand = rand_round
                .and_then(|r| r.get(mat_idx))
                .and_then(|m| m.first());
            matrix_points.push(point(chunk_values, fri_rand));
            round.push(matrix_points);
        }
        claims.push(round);
        round_idx += 1;
    }

    if layout.has_preprocessed {
        let rand_round = fri_random_rounds.get(round_idx);
        let mut round = Vec::new();
        for (mat_idx, matrix) in layout.matrices(CommitmentRole::Preprocessed).enumerate() {
            let mut matrix_points = Vec::new();
            let MatrixRoute::Preprocessed {
                instance: inst_idx, ..
            } = matrix.route
            else {
                unreachable!("preprocessed planner emits only preprocessed routes")
            };
            let inst = &instances[inst_idx];
            if let Some(prep_local) = &inst.opened_values_no_lookups.preprocessed_local_targets {
                let fri_rand_local = rand_round
                    .and_then(|r| r.get(mat_idx))
                    .and_then(|m| m.first());
                let fri_rand_next = rand_round
                    .and_then(|r| r.get(mat_idx))
                    .and_then(|m| m.get(1));
                matrix_points.push(point(prep_local, fri_rand_local));
                if matrix.point_count == 2 {
                    let prep_next = &inst.opened_values_no_lookups.preprocessed_next_targets;
                    if let Some(prep_next) = prep_next {
                        matrix_points.push(point(prep_next, fri_rand_next));
                    }
                }
            }
            round.push(matrix_points);
        }
        claims.push(round);
        round_idx += 1;
    }

    if layout.has_permutation {
        let rand_round = fri_random_rounds.get(round_idx);
        let mut round = Vec::new();
        for (mat_idx, matrix) in layout.matrices(CommitmentRole::Permutation).enumerate() {
            let mut matrix_points = Vec::new();
            let MatrixRoute::Permutation { instance } = matrix.route else {
                unreachable!("permutation planner emits only permutation routes")
            };
            let inst = &instances[instance];
            let fri_rand_local = rand_round
                .and_then(|r| r.get(mat_idx))
                .and_then(|m| m.first());
            let fri_rand_next = rand_round
                .and_then(|r| r.get(mat_idx))
                .and_then(|m| m.get(1));
            matrix_points.push(point(&inst.permutation_local_targets, fri_rand_local));
            matrix_points.push(point(&inst.permutation_next_targets, fri_rand_next));
            round.push(matrix_points);
        }
        claims.push(round);
    }

    claims
}

pub(crate) fn observe_claims_circuit<
    SC,
    CP: ChallengerPermConfig,
    const WIDTH: usize,
    const RATE: usize,
>(
    circuit: &mut CircuitBuilder<SC::Challenge>,
    challenger: &mut CircuitChallenger<WIDTH, RATE, CP>,
    seed: &[Val<SC>],
    claims: &[Vec<Vec<Vec<Target>>>],
) where
    SC: StarkGenericConfig,
    Val<SC>: PrimeField64,
    SC::Challenge: ExtensionField<Val<SC>>,
{
    challenger.observe_seed(circuit, seed);
    for values in claims.iter().flatten().flatten() {
        challenger.observe_ext_slice(circuit, values);
    }
}

pub(crate) fn claimed_evaluation_counts(claims: &[Vec<Vec<Vec<Target>>>]) -> Vec<Vec<Vec<usize>>> {
    claims
        .iter()
        .map(|round| {
            round
                .iter()
                .map(|matrix| matrix.iter().map(Vec::len).collect())
                .collect()
        })
        .collect()
}
