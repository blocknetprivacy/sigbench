use alloc::string::ToString;
use alloc::vec::Vec;
use alloc::{format, vec};
use core::marker::PhantomData;

use p3_challenger::{CanObserve, GrindingChallenger};
use p3_circuit::ops::PermConfig;
use p3_circuit::symbolic::RowSelectorsTargets;
use p3_circuit::{CircuitBuilder, CircuitBuilderError, NonPrimitiveOpId};
use p3_commit::{BatchOpening, ExtensionMmcs, Mmcs, OpenedValues, PolynomialSpace};
use p3_field::coset::TwoAdicMultiplicativeCoset;
use p3_field::{
    BasedVectorSpace, ExtensionField, Field, PackedValue, PrimeCharacteristicRing, PrimeField64,
    TwoAdicField,
};
use p3_fri::{BatchMultiOpening, CommitPhaseMultiStep, FriProof, HidingFriPcs, TwoAdicFriPcs};
use p3_merkle_tree::{MerkleTreeHidingMmcs, MerkleTreeMmcs, PrunedMerklePaths};
use p3_symmetric::{CryptographicHasher, MerkleCap, PseudoCompressionFunction};
use p3_uni_stark::{StarkGenericConfig, Val};
use rand::distr::{Distribution, StandardUniform};
use rand::{CryptoRng, Rng, SeedableRng};
use serde::de::DeserializeOwned;
use serde::{Deserialize, Serialize};

use super::context::{
    CheckedFriCommitment, CheckedFriOpening, ValidatedFriContext, validate_counted_fri_raw,
    validate_fri_context_with_caps, validate_fri_replacement_with_caps,
};
use super::{FriVerifierParams, NativeFriParams, verify_fri_circuit};
use crate::Target;
use crate::challenger::CircuitChallenger;
use crate::input_contract::FriOpeningLayout;
use crate::input_contract::fri::{
    FriCommitStepShape, FriInputBatchShape, FriShape, HidingFriShape, HidingOpeningAdviceShape,
    MerkleCapShape,
};
use crate::prepared::ConstrainConstantCommitment;
use crate::traits::{
    CheckedRecursive, ComsWithOpeningsTargets, PreparedRecursive, Recursive, RecursiveChallenger,
    RecursiveExtensionMmcs, RecursiveMmcs, RecursivePcs,
};
use crate::transcript::domain_separator_seed;
use crate::types::{OpenedValuesTargetsWithLookups, RecursiveLagrangeSelectors};
use crate::verifier::{
    InputResourceUsage, ObservableCommitment, VerificationError, VerifierLimits,
};

pub trait RecursiveMultiProofTargets<EF: Field>: Recursive<EF> {
    type MultiProof;

    fn new_for_query(
        circuit: &mut CircuitBuilder<EF>,
        proof: &Self::MultiProof,
        query: usize,
    ) -> Self;

    fn get_values_for_query(_proof: &Self::MultiProof, _query: usize) -> Vec<EF> {
        vec![]
    }

    fn get_private_values_for_query(_proof: &Self::MultiProof, _query: usize) -> Vec<EF> {
        vec![]
    }
}

pub trait PreparedRecursiveMultiProofTargets<EF: Field>: RecursiveMultiProofTargets<EF> {
    type Shape: Clone + PartialEq;

    fn multiproof_shape(
        proof: &Self::MultiProof,
        query_matrix_counts: &[usize],
    ) -> Result<Self::Shape, VerificationError>;

    fn validate_multiproof_raw<I>(
        proof: &Self::MultiProof,
        query_matrix_counts: I,
        required_salt_elems: Option<usize>,
    ) -> Result<(), VerificationError>
    where
        I: ExactSizeIterator<Item = usize>,
    {
        if required_salt_elems.is_some() {
            return Err(VerificationError::InvalidProofShape(
                "checked FRI salt validation is unsupported for this multiproof".into(),
            ));
        }
        let counts: Vec<_> = query_matrix_counts.collect();
        Self::multiproof_shape(proof, &counts).map(|_| ())
    }
}

mod sealed {
    pub trait FriPrivateAdvice {}
}

pub(crate) trait FriPrivateAdvice<EF: Field>:
    PreparedRecursiveMultiProofTargets<EF> + sealed::FriPrivateAdvice
{
    fn checked_private_values_len(proof: &Self::MultiProof) -> Result<usize, VerificationError>;

    fn add_private_resource_usage(
        proof: &Self::MultiProof,
        usage: &mut InputResourceUsage,
        limits: &VerifierLimits,
    ) -> Result<(), VerificationError>;

    fn compressed_frontier_hashes(proof: &Self::MultiProof) -> usize;
}

pub trait RecursiveFriInputOpenings<EF: Field>: Sized {
    type MultiOpenings;

    fn num_queries(input: &Self::MultiOpenings) -> Option<usize>;

    fn new_for_query(
        circuit: &mut CircuitBuilder<EF>,
        input: &Self::MultiOpenings,
        query: usize,
    ) -> Self;

    fn get_values_for_query(input: &Self::MultiOpenings, query: usize) -> Vec<EF>;

    fn get_private_values_for_query(input: &Self::MultiOpenings, query: usize) -> Vec<EF>;
}

pub trait PreparedRecursiveFriInputOpenings<EF: Field>: RecursiveFriInputOpenings<EF> {
    type Shape: Clone + PartialEq;

    fn openings_shape(input: &Self::MultiOpenings) -> Result<Self::Shape, VerificationError>;

    fn query_counts(input: &Self::MultiOpenings) -> Vec<usize>;

    fn validate_openings_raw(
        input: &Self::MultiOpenings,
    ) -> Result<Option<usize>, VerificationError> {
        let counts = Self::query_counts(input);
        if counts
            .first()
            .is_some_and(|first| counts.iter().any(|count| count != first))
        {
            return Err(VerificationError::InvalidProofShape(
                "FRI input query counts disagree".into(),
            ));
        }
        Self::openings_shape(input).map(|_| counts.first().copied())
    }
}

fn num_queries_from_counts(from_rounds: Option<usize>, from_batches: Option<usize>) -> usize {
    match (from_rounds, from_batches) {
        (Some(rounds), Some(batches)) => rounds.min(batches),
        (Some(count), None) | (None, Some(count)) => count,
        (None, None) => 0,
    }
}

pub(crate) fn fri_pcs_transcript_seed<F, EF>(
    claimed_evaluation_counts: Vec<Vec<Vec<usize>>>,
) -> Vec<F>
where
    F: PrimeField64,
    EF: ExtensionField<F>,
{
    domain_separator_seed(
        &p3_fri::PcsShape {
            claimed_evaluation_counts,
            batch_pow_bits: 0,
        }
        .domain_separator::<F, EF>(),
    )
}

pub(crate) fn fri_transcript_seed<F, EF>(
    params: &FriVerifierParams,
    log_arities: &[usize],
    num_queries: usize,
) -> Vec<F>
where
    F: PrimeField64,
    EF: ExtensionField<F>,
{
    let index_bits =
        log_arities.iter().sum::<usize>() + params.log_blowup() + params.log_final_poly_len();
    domain_separator_seed(
        &p3_fri::FriShape {
            log_arities: log_arities.to_vec(),
            final_poly_len: 1 << params.log_final_poly_len(),
            commit_pow_bits: params.commit_pow_bits(),
            query_pow_bits: params.query_pow_bits(),
            num_queries,
            index_bits,
            log_blowup: params.log_blowup(),
            max_log_arity: params.max_log_arity(),
        }
        .domain_separator::<F, EF>(),
    )
}

pub fn fri_proof_num_queries<F, EF, InputMmcs, FriMmcs, Witness>(
    proof: &FriProof<EF, FriMmcs, Witness, Vec<BatchMultiOpening<F, InputMmcs>>>,
) -> usize
where
    F: Field,
    EF: ExtensionField<F>,
    InputMmcs: Mmcs<F>,
    FriMmcs: Mmcs<EF>,
{
    num_queries_from_counts(
        proof
            .commit_phase_openings
            .iter()
            .map(|opening| opening.sibling_values.len())
            .min(),
        proof
            .input_openings
            .iter()
            .map(|batch| batch.opened_values.len())
            .min(),
    )
}

pub struct FriProofTargets<
    F: Field,
    EF: ExtensionField<F>,
    RecMmcs: RecursiveExtensionMmcs<F, EF>,
    InputProof: Recursive<EF>,
    Witness: Recursive<EF>,
> {
    pub commit_phase_commits: Vec<RecMmcs::Commitment>,
    pub commit_pow_witnesses: Vec<Witness>,
    pub query_proofs: Vec<QueryProofTargets<F, EF, InputProof, RecMmcs>>,
    pub final_poly: Vec<Target>,
    pub pow_witness: Witness,
    pub log_arities: Vec<usize>,
}

impl<
    F: Field,
    EF: ExtensionField<F>,
    RecMmcs: RecursiveExtensionMmcs<F, EF>,
    InputProof: Recursive<EF> + RecursiveFriInputOpenings<EF>,
    Witness: Recursive<EF>,
> FriProofTargets<F, EF, RecMmcs, InputProof, Witness>
{
    fn num_queries(
        input: &FriProof<EF, RecMmcs::Input, Witness::Input, InputProof::MultiOpenings>,
    ) -> usize {
        num_queries_from_counts(
            input
                .commit_phase_openings
                .iter()
                .map(|opening| opening.sibling_values.len())
                .min(),
            InputProof::num_queries(&input.input_openings),
        )
    }
}

impl<
    F: Field,
    EF: ExtensionField<F>,
    RecMmcs: RecursiveExtensionMmcs<F, EF>,
    InputProof: Recursive<EF> + RecursiveFriInputOpenings<EF>,
    Witness: Recursive<EF>,
> Recursive<EF> for FriProofTargets<F, EF, RecMmcs, InputProof, Witness>
where
    RecMmcs::Proof:
        RecursiveMultiProofTargets<EF, MultiProof = <RecMmcs::Input as Mmcs<EF>>::MultiProof>,
{
    type Input = FriProof<EF, RecMmcs::Input, Witness::Input, InputProof::MultiOpenings>;

    fn new(circuit: &mut CircuitBuilder<EF>, input: &Self::Input) -> Self {
        let commit_phase_commits = input
            .commit_phase_commits
            .iter()
            .map(|commitment| RecMmcs::Commitment::new(circuit, commitment))
            .collect();

        let commit_pow_witnesses = input
            .commit_pow_witnesses
            .iter()
            .map(|witness| Witness::new(circuit, witness))
            .collect();

        let query_proofs = (0..Self::num_queries(input))
            .map(|query| {
                QueryProofTargets::new_for_query(
                    circuit,
                    &input.input_openings,
                    &input.commit_phase_openings,
                    query,
                )
            })
            .collect();

        let final_poly = circuit
            .alloc_public_inputs(input.final_poly.len(), "FRI final polynomial coefficients");

        let log_arities = input
            .commit_phase_openings
            .iter()
            .map(|opening| super::sibling_log_arity(opening).unwrap_or(0))
            .collect();

        Self {
            commit_phase_commits,
            commit_pow_witnesses,
            query_proofs,
            final_poly,
            pow_witness: Witness::new(circuit, &input.query_pow_witness),
            log_arities,
        }
    }

    fn get_values(input: &Self::Input) -> Vec<EF> {
        let FriProof {
            batch_pow_witness: _,
            commit_phase_commits,
            commit_pow_witnesses,
            input_openings,
            commit_phase_openings,
            final_poly,
            query_pow_witness,
        } = input;

        commit_phase_commits
            .iter()
            .flat_map(|c| RecMmcs::Commitment::get_values(c))
            .chain(
                commit_pow_witnesses
                    .iter()
                    .flat_map(|w| Witness::get_values(w)),
            )
            .chain((0..Self::num_queries(input)).flat_map(|query| {
                QueryProofTargets::<F, EF, InputProof, RecMmcs>::get_values_for_query(
                    input_openings,
                    commit_phase_openings,
                    query,
                )
            }))
            .chain(final_poly.iter().copied())
            .chain(Witness::get_values(query_pow_witness))
            .collect()
    }

    fn get_private_values(input: &Self::Input) -> Vec<EF> {
        (0..Self::num_queries(input))
            .flat_map(|query| {
                QueryProofTargets::<F, EF, InputProof, RecMmcs>::get_private_values_for_query(
                    &input.input_openings,
                    &input.commit_phase_openings,
                    query,
                )
            })
            .collect()
    }
}

impl<
    F: Field,
    EF: ExtensionField<F>,
    RecMmcs: RecursiveExtensionMmcs<F, EF>,
    InputProof: Recursive<EF> + PreparedRecursiveFriInputOpenings<EF>,
    Witness: PreparedRecursive<EF>,
> PreparedRecursive<EF> for FriProofTargets<F, EF, RecMmcs, InputProof, Witness>
where
    RecMmcs::Commitment: PreparedRecursive<EF>,
    RecMmcs::Proof: PreparedRecursiveMultiProofTargets<
            EF,
            MultiProof = <RecMmcs::Input as Mmcs<EF>>::MultiProof,
        >,
{
    type Shape = FriShape<
        <RecMmcs::Commitment as PreparedRecursive<EF>>::Shape,
        InputProof::Shape,
        <RecMmcs::Proof as PreparedRecursiveMultiProofTargets<EF>>::Shape,
        Witness::Shape,
    >;

    fn input_shape(input: &Self::Input) -> Result<Self::Shape, VerificationError> {
        let FriProof {
            batch_pow_witness: _,
            commit_phase_commits,
            commit_pow_witnesses,
            input_openings,
            commit_phase_openings,
            final_poly,
            query_pow_witness,
        } = input;

        validate_fri_structure::<F, EF, RecMmcs, InputProof, Witness>(input)?;

        let mut counts = InputProof::query_counts(input_openings);
        counts.extend(
            commit_phase_openings
                .iter()
                .map(|step| step.sibling_values.len()),
        );
        if counts
            .first()
            .is_some_and(|first| counts.iter().any(|count| count != first))
        {
            return Err(VerificationError::InvalidProofShape(
                "FRI query counts disagree".into(),
            ));
        }

        let mut log_arities = Vec::with_capacity(commit_phase_openings.len());
        for step in commit_phase_openings {
            let log_arity = super::sibling_log_arity(step)
                .and_then(|log_arity| u8::try_from(log_arity).ok())
                .ok_or_else(|| {
                    VerificationError::InvalidProofShape("FRI sibling arity mismatch".into())
                })?;
            log_arities.push(log_arity);
        }

        Ok(FriShape {
            commit_phase_commits: commit_phase_commits
                .iter()
                .map(RecMmcs::Commitment::input_shape)
                .collect::<Result<_, _>>()?,
            commit_pow_witnesses: commit_pow_witnesses
                .iter()
                .map(Witness::input_shape)
                .collect::<Result<_, _>>()?,
            input_openings: InputProof::openings_shape(input_openings)?,
            commit_phase_openings: commit_phase_openings
                .iter()
                .zip(log_arities)
                .map(|(step, log_arity)| {
                    Ok(FriCommitStepShape {
                        log_arity,
                        sibling_values: step.sibling_values.iter().map(Vec::len).collect(),
                        opening_advice: RecMmcs::Proof::multiproof_shape(
                            &step.opening_proof,
                            &vec![1; step.sibling_values.len()],
                        )?,
                    })
                })
                .collect::<Result<_, VerificationError>>()?,
            final_poly: final_poly.len(),
            query_pow_witness: Witness::input_shape(query_pow_witness)?,
        })
    }
}

impl<
    F: Field,
    EF: ExtensionField<F>,
    RecMmcs: RecursiveExtensionMmcs<F, EF>,
    RI: RecursiveMmcs<F, EF>,
> CheckedRecursive<EF> for FriProofTargets<F, EF, RecMmcs, InputProofTargets<F, EF, RI>, Witness<F>>
where
    RecMmcs::Commitment: CheckedFriCommitment<EF, Input = <RecMmcs::Input as Mmcs<EF>>::Commitment>,
    RecMmcs::Proof: FriPrivateAdvice<EF, MultiProof = <RecMmcs::Input as Mmcs<EF>>::MultiProof>,
    RecMmcs::Input: NativeFriSaltWidth,
    RI::Input: NativeFriSaltWidth,
    RI::Proof: FriPrivateAdvice<EF, MultiProof = <RI::Input as Mmcs<F>>::MultiProof>,
{
    fn validate_input(input: &Self::Input) -> Result<(), VerificationError> {
        validate_counted_fri_raw::<F, EF, RI, RecMmcs>(
            input,
            None,
            <RI::Input as NativeFriSaltWidth>::SALT_ELEMS,
            <RecMmcs::Input as NativeFriSaltWidth>::SALT_ELEMS,
        )
        .map(|_| ())
    }
}

pub(crate) fn validate_fri_input<
    F: Field,
    EF: ExtensionField<F>,
    RecMmcs: RecursiveExtensionMmcs<F, EF>,
    InputProof: Recursive<EF> + PreparedRecursiveFriInputOpenings<EF>,
    Witness: Recursive<EF>,
>(
    input: &FriProof<EF, RecMmcs::Input, Witness::Input, InputProof::MultiOpenings>,
) -> Result<(), VerificationError>
where
    RecMmcs::Commitment: CheckedRecursive<EF>,
    RecMmcs::Proof: PreparedRecursiveMultiProofTargets<
            EF,
            MultiProof = <RecMmcs::Input as Mmcs<EF>>::MultiProof,
        >,
{
    validate_fri_structure::<F, EF, RecMmcs, InputProof, Witness>(input)?;
    for commitment in &input.commit_phase_commits {
        RecMmcs::Commitment::validate_input(commitment)?;
    }
    Ok(())
}

fn validate_fri_structure<
    F: Field,
    EF: ExtensionField<F>,
    RecMmcs: RecursiveExtensionMmcs<F, EF>,
    InputProof: Recursive<EF> + PreparedRecursiveFriInputOpenings<EF>,
    Witness: Recursive<EF>,
>(
    input: &FriProof<EF, RecMmcs::Input, Witness::Input, InputProof::MultiOpenings>,
) -> Result<(), VerificationError>
where
    RecMmcs::Proof: PreparedRecursiveMultiProofTargets<
            EF,
            MultiProof = <RecMmcs::Input as Mmcs<EF>>::MultiProof,
        >,
{
    let phases = input.commit_phase_commits.len();
    if phases != input.commit_phase_openings.len() {
        return Err(VerificationError::InvalidProofShape(
            "FRI commitment/opening round count mismatch".into(),
        ));
    }
    if phases != input.commit_pow_witnesses.len() {
        return Err(VerificationError::InvalidProofShape(
            "FRI commitment/PoW witness round count mismatch".into(),
        ));
    }
    if input.final_poly.is_empty() {
        return Err(VerificationError::InvalidProofShape(
            "FRI proof missing final polynomial".into(),
        ));
    }

    let mut query_count = InputProof::validate_openings_raw(&input.input_openings)?;
    for step in &input.commit_phase_openings {
        if super::sibling_log_arity(step).is_none() {
            return Err(VerificationError::InvalidProofShape(
                "FRI sibling arity mismatch".into(),
            ));
        }
        if let Some(expected) = query_count {
            if expected != step.sibling_values.len() {
                return Err(VerificationError::InvalidProofShape(
                    "FRI query counts disagree".into(),
                ));
            }
        } else {
            query_count = Some(step.sibling_values.len());
        }
        let matrix_counts = core::iter::repeat_n(1usize, step.sibling_values.len());
        RecMmcs::Proof::validate_multiproof_raw(&step.opening_proof, matrix_counts, None)?;
    }

    Ok(())
}

pub struct QueryProofTargets<
    F: Field,
    EF: ExtensionField<F>,
    InputProof: Recursive<EF>,
    RecMmcs: RecursiveExtensionMmcs<F, EF>,
> {
    pub input_proof: InputProof,
    pub commit_phase_openings: Vec<CommitPhaseProofStepTargets<F, EF, RecMmcs>>,
}

impl<
    F: Field,
    EF: ExtensionField<F>,
    InputProof: Recursive<EF> + RecursiveFriInputOpenings<EF>,
    RecMmcs: RecursiveExtensionMmcs<F, EF>,
> QueryProofTargets<F, EF, InputProof, RecMmcs>
where
    RecMmcs::Proof:
        RecursiveMultiProofTargets<EF, MultiProof = <RecMmcs::Input as Mmcs<EF>>::MultiProof>,
{
    fn new_for_query(
        circuit: &mut CircuitBuilder<EF>,
        input_openings: &InputProof::MultiOpenings,
        commit_phase_openings: &[CommitPhaseMultiStep<EF, RecMmcs::Input>],
        query: usize,
    ) -> Self {
        let input_proof = InputProof::new_for_query(circuit, input_openings, query);
        let commit_phase_openings = commit_phase_openings
            .iter()
            .map(|opening| CommitPhaseProofStepTargets::new_for_query(circuit, opening, query))
            .collect();
        Self {
            input_proof,
            commit_phase_openings,
        }
    }

    fn get_values_for_query(
        input_openings: &InputProof::MultiOpenings,
        commit_phase_openings: &[CommitPhaseMultiStep<EF, RecMmcs::Input>],
        query: usize,
    ) -> Vec<EF> {
        InputProof::get_values_for_query(input_openings, query)
            .into_iter()
            .chain(commit_phase_openings.iter().flat_map(|opening| {
                CommitPhaseProofStepTargets::<F, EF, RecMmcs>::get_values_for_query(opening, query)
            }))
            .collect()
    }

    fn get_private_values_for_query(
        input_openings: &InputProof::MultiOpenings,
        commit_phase_openings: &[CommitPhaseMultiStep<EF, RecMmcs::Input>],
        query: usize,
    ) -> Vec<EF> {
        InputProof::get_private_values_for_query(input_openings, query)
            .into_iter()
            .chain(commit_phase_openings.iter().flat_map(|opening| {
                CommitPhaseProofStepTargets::<F, EF, RecMmcs>::get_private_values_for_query(
                    opening, query,
                )
            }))
            .collect()
    }
}

pub struct CommitPhaseProofStepTargets<
    F: Field,
    EF: ExtensionField<F>,
    RecMmcs: RecursiveExtensionMmcs<F, EF>,
> {
    pub log_arity: usize,
    pub sibling_coefficients: Vec<Target>,
    pub opening_proof: RecMmcs::Proof,
    _phantom: PhantomData<(F, EF)>,
}

impl<F: Field, EF: ExtensionField<F> + BasedVectorSpace<F>, RecMmcs: RecursiveExtensionMmcs<F, EF>>
    CommitPhaseProofStepTargets<F, EF, RecMmcs>
{
    fn pack_one_sibling(coeffs: &[Target], circuit: &mut CircuitBuilder<EF>) -> Target {
        let basis: Vec<EF> = (0..EF::DIMENSION)
            .map(|i| EF::from_basis_coefficients_fn(|j| if i == j { F::ONE } else { F::ZERO }))
            .collect();

        let mut result = coeffs[0];
        for (i, &basis_elem) in basis.iter().enumerate().skip(1) {
            let basis_const = circuit.define_const(basis_elem);
            result = circuit.mul_add(coeffs[i], basis_const, result);
        }
        circuit.hint_ext_recompose_coeffs(result, coeffs);
        result
    }

    pub fn sibling_values_packed(&self, circuit: &mut CircuitBuilder<EF>) -> Vec<Target> {
        let d = EF::DIMENSION;
        self.sibling_coefficients
            .chunks_exact(d)
            .map(|chunk| Self::pack_one_sibling(chunk, circuit))
            .collect()
    }

    pub fn sibling_value_packed(&self, circuit: &mut CircuitBuilder<EF>) -> Target {
        debug_assert_eq!(
            self.log_arity, 1,
            "sibling_value_packed is for arity-2 only; use sibling_values_packed for higher arity"
        );
        Self::pack_one_sibling(&self.sibling_coefficients, circuit)
    }
}

impl<F: Field, EF: ExtensionField<F> + BasedVectorSpace<F>, RecMmcs: RecursiveExtensionMmcs<F, EF>>
    CommitPhaseProofStepTargets<F, EF, RecMmcs>
where
    RecMmcs::Proof:
        RecursiveMultiProofTargets<EF, MultiProof = <RecMmcs::Input as Mmcs<EF>>::MultiProof>,
{
    fn new_for_query(
        circuit: &mut CircuitBuilder<EF>,
        input: &CommitPhaseMultiStep<EF, RecMmcs::Input>,
        query: usize,
    ) -> Self {
        let log_arity = super::sibling_log_arity(input)
            .expect("FRI commit-phase rows were validated before target allocation");
        let arity = 1usize << log_arity;
        let num_siblings = arity - 1;
        let num_coeffs = num_siblings * EF::DIMENSION;
        let sibling_coefficients =
            circuit.alloc_private_inputs(num_coeffs, "FRI commit phase sibling coefficients");
        let opening_proof = RecMmcs::Proof::new_for_query(circuit, &input.opening_proof, query);
        Self {
            log_arity,
            sibling_coefficients,
            opening_proof,
            _phantom: PhantomData,
        }
    }

    fn get_values_for_query(
        input: &CommitPhaseMultiStep<EF, RecMmcs::Input>,
        query: usize,
    ) -> Vec<EF> {
        RecMmcs::Proof::get_values_for_query(&input.opening_proof, query)
    }

    fn get_private_values_for_query(
        input: &CommitPhaseMultiStep<EF, RecMmcs::Input>,
        query: usize,
    ) -> Vec<EF> {
        let mut values: Vec<EF> = Vec::new();
        for sibling_value in input.sibling_values.get(query).into_iter().flatten() {
            let coeffs = sibling_value.as_basis_coefficients_slice();
            values.extend(coeffs.iter().map(|&c| EF::from(c)));
        }
        values.extend(RecMmcs::Proof::get_private_values_for_query(
            &input.opening_proof,
            query,
        ));
        values
    }
}

pub struct BatchOpeningTargets<F: Field, EF: ExtensionField<F>, RecMmcs: RecursiveMmcs<F, EF>> {
    pub opened_values: Vec<Vec<Target>>,
    pub opening_proof: RecMmcs::Proof,
}

impl<F: Field, EF: ExtensionField<F>, Inner: RecursiveMmcs<F, EF>> Recursive<EF>
    for BatchOpeningTargets<F, EF, Inner>
{
    type Input = BatchOpening<F, Inner::Input>;

    fn new(circuit: &mut CircuitBuilder<EF>, input: &Self::Input) -> Self {
        let opened_values = input
            .opened_values
            .iter()
            .map(|values| circuit.alloc_private_inputs(values.len(), "batch opened values"))
            .collect();

        let opening_proof = Inner::Proof::new(circuit, &input.opening_proof);

        Self {
            opened_values,
            opening_proof,
        }
    }

    fn get_values(input: &Self::Input) -> Vec<EF> {
        Inner::Proof::get_values(&input.opening_proof)
    }

    fn get_private_values(input: &Self::Input) -> Vec<EF> {
        input
            .opened_values
            .iter()
            .flat_map(|inner| inner.iter().map(|v| EF::from(*v)))
            .chain(Inner::Proof::get_private_values(&input.opening_proof))
            .collect()
    }
}

impl<F: Field, EF: ExtensionField<F>, Inner: RecursiveMmcs<F, EF>> BatchOpeningTargets<F, EF, Inner>
where
    Inner::Proof:
        RecursiveMultiProofTargets<EF, MultiProof = <Inner::Input as Mmcs<F>>::MultiProof>,
{
    fn new_for_query(
        circuit: &mut CircuitBuilder<EF>,
        input: &BatchMultiOpening<F, Inner::Input>,
        query: usize,
    ) -> Self {
        let opened_values = input
            .opened_values
            .get(query)
            .map(|rows| {
                rows.iter()
                    .map(|values| circuit.alloc_private_inputs(values.len(), "batch opened values"))
                    .collect()
            })
            .unwrap_or_default();

        let opening_proof = Inner::Proof::new_for_query(circuit, &input.opening_proof, query);

        Self {
            opened_values,
            opening_proof,
        }
    }

    fn get_values_for_query(input: &BatchMultiOpening<F, Inner::Input>, query: usize) -> Vec<EF> {
        Inner::Proof::get_values_for_query(&input.opening_proof, query)
    }

    fn get_private_values_for_query(
        input: &BatchMultiOpening<F, Inner::Input>,
        query: usize,
    ) -> Vec<EF> {
        input
            .opened_values
            .get(query)
            .into_iter()
            .flatten()
            .flat_map(|inner| inner.iter().map(|v| EF::from(*v)))
            .chain(Inner::Proof::get_private_values_for_query(
                &input.opening_proof,
                query,
            ))
            .collect()
    }
}

#[derive(Clone)]
pub struct MerkleCapTargets<F, const DIGEST_ELEMS: usize> {
    pub cap_targets: Vec<[Target; DIGEST_ELEMS]>,
    _phantom: PhantomData<F>,
}

impl<F, const DIGEST_ELEMS: usize> ObservableCommitment for MerkleCapTargets<F, DIGEST_ELEMS> {
    fn to_observation_targets(&self) -> Vec<Target> {
        self.cap_targets
            .iter()
            .flat_map(|entry| entry.iter().copied())
            .collect()
    }
}

type ValMmcsCommitment<F, const DIGEST_ELEMS: usize> =
    MerkleCap<<F as PackedValue>::Value, [<F as PackedValue>::Value; DIGEST_ELEMS]>;

#[allow(dead_code, clippy::needless_pass_by_value)]
pub(crate) fn validate_merkle_cap_context<F, EF, const DIGEST_ELEMS: usize, I>(
    cap: &ValMmcsCommitment<F, DIGEST_ELEMS>,
    permutation_config: PermConfig,
    index_bit_len: usize,
    heights: I,
) -> Result<(), VerificationError>
where
    F: Field,
    EF: ExtensionField<F>,
    I: Iterator<Item = usize> + Clone,
{
    let roots = cap.num_roots();
    let mut max_height = 0usize;
    let mut has_height = false;
    let height_scan = heights.clone();
    for height in height_scan {
        if height == 0 {
            continue;
        }
        has_height = true;
        max_height = max_height.max(height);
    }
    if !has_height {
        return Err(VerificationError::InvalidProofShape(
            "MMCS commitment cap has no positive planned matrices".into(),
        ));
    }
    let (cap_height, path_bits) = if permutation_config.is_arity4_shape() {
        let path_bits = crate::pcs::mmcs::visit_arity4_path(heights, roots, |_| {})
            .map_err(|error| VerificationError::InvalidProofShape(error.to_string()))?;
        let cap_height = crate::pcs::mmcs::validate_commitment_cap_count(roots)
            .map_err(|error| VerificationError::InvalidProofShape(error.to_string()))?;
        (cap_height, path_bits)
    } else {
        let raw_heights = heights;
        for height in raw_heights {
            if height == 0 || !height.is_power_of_two() {
                return Err(VerificationError::InvalidProofShape(
                    "binary MMCS matrix heights must be positive powers of two".into(),
                ));
            }
        }
        let tree_height = max_height.trailing_zeros() as usize;
        let cap_height = crate::pcs::mmcs::validate_binary_cap_count(roots, tree_height)
            .map_err(|error| VerificationError::InvalidProofShape(error.to_string()))?;
        (cap_height, tree_height - cap_height)
    };
    if !permutation_config.is_arity4_shape() && cap_height > index_bit_len {
        return Err(VerificationError::InvalidProofShape(
            "binary MMCS cap needs more index bits than the checked query layout".into(),
        ));
    }
    let chunk_ext = if permutation_config.is_arity4_shape() {
        permutation_config.capacity_ext()
    } else {
        permutation_config.rate_ext()
    };
    validate_cap_packing::<DIGEST_ELEMS>(
        roots,
        chunk_ext,
        permutation_config.d() == 1 && EF::DIMENSION > 1,
        EF::DIMENSION,
        cap_height,
        path_bits,
    )?;
    Ok(())
}

fn validate_cap_packing<const DIGEST_ELEMS: usize>(
    roots: usize,
    chunk_ext: usize,
    lifted_d1: bool,
    extension_dimension: usize,
    cap_height: usize,
    path_bits: usize,
) -> Result<(), VerificationError> {
    if chunk_ext == 0 || extension_dimension == 0 {
        return Err(VerificationError::InvalidProofShape(
            "MMCS digest packing has a zero chunk or extension width".into(),
        ));
    }
    let expected_digest_elems = if lifted_d1 {
        chunk_ext
    } else {
        chunk_ext.checked_mul(extension_dimension).ok_or_else(|| {
            VerificationError::InvalidProofShape("MMCS digest width overflows".into())
        })?
    };
    if DIGEST_ELEMS != expected_digest_elems {
        return Err(VerificationError::InvalidProofShape(format!(
            "MMCS digest packing mismatch: expected {expected_digest_elems}, got {DIGEST_ELEMS}"
        )));
    }
    let flat_digest = roots.checked_mul(DIGEST_ELEMS).ok_or_else(|| {
        VerificationError::InvalidProofShape("MMCS cap digest count overflows".into())
    })?;
    let flat_chunk = roots.checked_mul(chunk_ext).ok_or_else(|| {
        VerificationError::InvalidProofShape("MMCS cap chunk count overflows".into())
    })?;
    let target_size = core::mem::size_of::<Target>();
    if roots
        .checked_mul(core::mem::size_of::<Vec<Target>>())
        .and_then(|bytes| (bytes <= isize::MAX as usize).then_some(bytes))
        .is_none()
    {
        return Err(VerificationError::InvalidProofShape(
            "MMCS cap outer target vector size overflows".into(),
        ));
    }
    for (label, elements) in [("digest", flat_digest), ("chunk", flat_chunk)] {
        if elements
            .checked_mul(target_size)
            .filter(|bytes| *bytes <= isize::MAX as usize)
            .is_none()
        {
            return Err(VerificationError::InvalidProofShape(format!(
                "MMCS cap {label} target size overflows"
            )));
        }
    }
    cap_height.checked_add(path_bits).ok_or_else(|| {
        VerificationError::InvalidProofShape("MMCS cap and path bits overflow".into())
    })?;
    Ok(())
}

impl<F: Field, EF: ExtensionField<F>, const DIGEST_ELEMS: usize> Recursive<EF>
    for MerkleCapTargets<F, DIGEST_ELEMS>
{
    type Input = ValMmcsCommitment<F, DIGEST_ELEMS>;

    fn new(circuit: &mut CircuitBuilder<EF>, input: &Self::Input) -> Self {
        let cap_targets = (0..input.num_roots())
            .map(|_| circuit.alloc_public_input_array("MMCS commitment cap entry"))
            .collect();
        Self {
            cap_targets,
            _phantom: PhantomData,
        }
    }

    fn get_values(input: &Self::Input) -> Vec<EF> {
        input
            .roots()
            .iter()
            .flat_map(|entry: &[<F as PackedValue>::Value; DIGEST_ELEMS]| {
                entry.iter().map(|v| EF::from(*v))
            })
            .collect()
    }
}

impl<F: Field, EF: ExtensionField<F>, const DIGEST_ELEMS: usize> ConstrainConstantCommitment<EF>
    for MerkleCapTargets<F, DIGEST_ELEMS>
{
    fn constrain_constant(
        &self,
        circuit: &mut CircuitBuilder<EF>,
        expected: &Self::Input,
    ) -> Result<(), VerificationError> {
        if self.cap_targets.len() != expected.num_roots() {
            return Err(VerificationError::InvalidProofShape(format!(
                "trusted preprocessing cap root count mismatch: targets {}, expected {}",
                self.cap_targets.len(),
                expected.num_roots()
            )));
        }
        let targets = self
            .cap_targets
            .iter()
            .flat_map(|entry| entry.iter().copied());
        let values = <Self as Recursive<EF>>::get_values(expected);
        let expected_limbs = self
            .cap_targets
            .len()
            .checked_mul(DIGEST_ELEMS)
            .ok_or_else(|| {
                VerificationError::InvalidProofShape(
                    "trusted preprocessing cap limb count overflows".into(),
                )
            })?;
        if values.len() != expected_limbs {
            return Err(VerificationError::InvalidProofShape(format!(
                "trusted preprocessing cap limb count mismatch: targets {expected_limbs}, expected {}",
                values.len()
            )));
        }
        for (target, value) in targets.zip(values) {
            let constant = circuit.alloc_const(value, "trusted child preprocessing");
            let difference = circuit.sub(target, constant);
            let negative = circuit.sub(Target::ZERO, target);
            let zero = circuit.add(target, negative);
            circuit.connect(difference, zero);
        }
        Ok(())
    }
}

impl<F: Field, EF: ExtensionField<F>, const DIGEST_ELEMS: usize> PreparedRecursive<EF>
    for MerkleCapTargets<F, DIGEST_ELEMS>
{
    type Shape = MerkleCapShape;

    fn input_shape(input: &Self::Input) -> Result<Self::Shape, VerificationError> {
        Ok(MerkleCapShape {
            roots: input.num_roots(),
        })
    }
}

impl<F: Field, EF: ExtensionField<F>, const DIGEST_ELEMS: usize> CheckedRecursive<EF>
    for MerkleCapTargets<F, DIGEST_ELEMS>
{
    fn validate_input(input: &Self::Input) -> Result<(), VerificationError> {
        let roots = input.num_roots();
        if roots == 0 || !roots.is_power_of_two() {
            return Err(VerificationError::InvalidProofShape(
                "MMCS commitment cap must have a non-empty power-of-two root count".into(),
            ));
        }
        Ok(())
    }
}

pub struct HashProofTargets<F, const DIGEST_ELEMS: usize> {
    pub hash_proof_targets: Vec<[Target; DIGEST_ELEMS]>,
    _phantom: PhantomData<F>,
}

type ValMmcsProof<PW, const DIGEST_ELEMS: usize> = Vec<[<PW as PackedValue>::Value; DIGEST_ELEMS]>;

impl<F: Field, EF: ExtensionField<F>, const DIGEST_ELEMS: usize> Recursive<EF>
    for HashProofTargets<F, DIGEST_ELEMS>
{
    type Input = ValMmcsProof<F, DIGEST_ELEMS>;

    fn new(_circuit: &mut CircuitBuilder<EF>, _input: &Self::Input) -> Self {
        Self {
            hash_proof_targets: vec![],
            _phantom: PhantomData,
        }
    }

    fn get_values(_input: &Self::Input) -> Vec<EF> {
        vec![]
    }
}

impl<F: Field, EF: ExtensionField<F>, const DIGEST_ELEMS: usize> RecursiveMultiProofTargets<EF>
    for HashProofTargets<F, DIGEST_ELEMS>
{
    type MultiProof = PrunedMerklePaths<<F as PackedValue>::Value, DIGEST_ELEMS>;

    fn new_for_query(
        _circuit: &mut CircuitBuilder<EF>,
        _proof: &Self::MultiProof,
        _query: usize,
    ) -> Self {
        Self {
            hash_proof_targets: vec![],
            _phantom: PhantomData,
        }
    }
}

impl<F: Field, EF: ExtensionField<F>, const DIGEST_ELEMS: usize>
    PreparedRecursiveMultiProofTargets<EF> for HashProofTargets<F, DIGEST_ELEMS>
{
    type Shape = ();

    fn multiproof_shape(
        _proof: &Self::MultiProof,
        _query_matrix_counts: &[usize],
    ) -> Result<Self::Shape, VerificationError> {
        Ok(())
    }

    fn validate_multiproof_raw<I>(
        _proof: &Self::MultiProof,
        _query_matrix_counts: I,
        required_salt_elems: Option<usize>,
    ) -> Result<(), VerificationError>
    where
        I: ExactSizeIterator<Item = usize>,
    {
        if required_salt_elems.is_some() {
            return Err(VerificationError::InvalidProofShape(
                "ordinary FRI multiproof cannot carry salts".into(),
            ));
        }
        Ok(())
    }
}

impl<F: Field, const DIGEST_ELEMS: usize> sealed::FriPrivateAdvice
    for HashProofTargets<F, DIGEST_ELEMS>
{
}

impl<F: Field, EF: ExtensionField<F>, const DIGEST_ELEMS: usize> FriPrivateAdvice<EF>
    for HashProofTargets<F, DIGEST_ELEMS>
{
    fn checked_private_values_len(_proof: &Self::MultiProof) -> Result<usize, VerificationError> {
        Ok(0)
    }

    fn add_private_resource_usage(
        _proof: &Self::MultiProof,
        _usage: &mut InputResourceUsage,
        _limits: &VerifierLimits,
    ) -> Result<(), VerificationError> {
        Ok(())
    }

    fn compressed_frontier_hashes(proof: &Self::MultiProof) -> usize {
        proof.sibling_hashes.len()
    }
}

pub struct Witness<F> {
    pub witness: Target,
    _phantom: PhantomData<F>,
}

impl<F: Field, EF: ExtensionField<F>> Recursive<EF> for Witness<F> {
    type Input = F;

    fn new(circuit: &mut CircuitBuilder<EF>, _input: &Self::Input) -> Self {
        Self {
            witness: circuit.alloc_public_input("FRI proof-of-work witness"),
            _phantom: PhantomData,
        }
    }

    fn get_values(input: &Self::Input) -> Vec<EF> {
        vec![EF::from(*input)]
    }
}

impl<F: Field, EF: ExtensionField<F>> PreparedRecursive<EF> for Witness<F> {
    type Shape = ();

    fn input_shape(_input: &Self::Input) -> Result<Self::Shape, VerificationError> {
        Ok(())
    }
}

pub struct RecValMmcs<F: Field, const DIGEST_ELEMS: usize, H, C>
where
    H: CryptographicHasher<F, [F; DIGEST_ELEMS]>
        + CryptographicHasher<F::Packing, [F::Packing; DIGEST_ELEMS]>
        + Sync,
{
    pub hash: H,
    pub compress: C,
    _phantom: PhantomData<F>,
}

impl<F: Field, EF: ExtensionField<F>, const DIGEST_ELEMS: usize, H, C> RecursiveMmcs<F, EF>
    for RecValMmcs<F, DIGEST_ELEMS, H, C>
where
    H: CryptographicHasher<F, [F; DIGEST_ELEMS]>
        + CryptographicHasher<F::Packing, [F::Packing; DIGEST_ELEMS]>
        + Sync,
    C: PseudoCompressionFunction<[F; DIGEST_ELEMS], 2>
        + PseudoCompressionFunction<[F::Packing; DIGEST_ELEMS], 2>
        + Sync,
    [F; DIGEST_ELEMS]: Serialize + for<'a> Deserialize<'a>,
{
    type Input = MerkleTreeMmcs<F::Packing, F::Packing, H, C, 2, DIGEST_ELEMS>;

    type Commitment = MerkleCapTargets<F, DIGEST_ELEMS>;

    type Proof = HashProofTargets<F, DIGEST_ELEMS>;
}

pub struct RecValMmcsArity4<F: Field, const DIGEST_ELEMS: usize, H, C>
where
    H: CryptographicHasher<F, [F; DIGEST_ELEMS]>
        + CryptographicHasher<F::Packing, [F::Packing; DIGEST_ELEMS]>
        + Sync,
{
    pub hash: H,
    pub compress: C,
    _phantom: PhantomData<F>,
}

impl<F: Field, EF: ExtensionField<F>, const DIGEST_ELEMS: usize, H, C> RecursiveMmcs<F, EF>
    for RecValMmcsArity4<F, DIGEST_ELEMS, H, C>
where
    H: CryptographicHasher<F, [F; DIGEST_ELEMS]>
        + CryptographicHasher<F::Packing, [F::Packing; DIGEST_ELEMS]>
        + Sync,
    C: PseudoCompressionFunction<[F; DIGEST_ELEMS], 4>
        + PseudoCompressionFunction<[F::Packing; DIGEST_ELEMS], 4>
        + Sync,
    [F; DIGEST_ELEMS]: Serialize + for<'a> Deserialize<'a>,
{
    type Input = MerkleTreeMmcs<F::Packing, F::Packing, H, C, 4, DIGEST_ELEMS>;

    type Commitment = MerkleCapTargets<F, DIGEST_ELEMS>;

    type Proof = HashProofTargets<F, DIGEST_ELEMS>;
}

pub struct RecExtensionValMmcs<
    F: Field,
    EF: ExtensionField<F>,
    const DIGEST_ELEMS: usize,
    MyMmcs: RecursiveMmcs<F, EF>,
> {
    _phantom: PhantomData<F>,
    _phantom_ef: PhantomData<EF>,
    _phantom_val: PhantomData<MyMmcs>,
}

impl<F: Field, EF: ExtensionField<F>, const DIGEST_ELEMS: usize, RecValMmcs: RecursiveMmcs<F, EF>>
    RecursiveExtensionMmcs<F, EF> for RecExtensionValMmcs<F, EF, DIGEST_ELEMS, RecValMmcs>
{
    type Input = ExtensionMmcs<F, EF, RecValMmcs::Input>;

    type Commitment = RecValMmcs::Commitment;

    type Proof = RecValMmcs::Proof;
}

pub struct RecExtensionValMmcsArity4<
    F: Field,
    EF: ExtensionField<F>,
    const DIGEST_ELEMS: usize,
    MyMmcs: RecursiveMmcs<F, EF>,
> {
    _phantom: PhantomData<F>,
    _phantom_ef: PhantomData<EF>,
    _phantom_val: PhantomData<MyMmcs>,
}

impl<F: Field, EF: ExtensionField<F>, const DIGEST_ELEMS: usize, RecValMmcs: RecursiveMmcs<F, EF>>
    RecursiveExtensionMmcs<F, EF> for RecExtensionValMmcsArity4<F, EF, DIGEST_ELEMS, RecValMmcs>
{
    type Input = ExtensionMmcs<F, EF, RecValMmcs::Input>;

    type Commitment = RecValMmcs::Commitment;

    type Proof = RecValMmcs::Proof;
}

pub trait MmcsProofTargets {
    fn salt_targets(&self) -> &[Vec<Target>];
}

impl<F, const DIGEST_ELEMS: usize> MmcsProofTargets for HashProofTargets<F, DIGEST_ELEMS> {
    fn salt_targets(&self) -> &[Vec<Target>] {
        &[]
    }
}

pub struct HidingHashProofTargets<F, const DIGEST_ELEMS: usize> {
    pub salts: Vec<Vec<Target>>,
    _phantom: PhantomData<F>,
}

type HidingValMmcsProof<F, const DIGEST_ELEMS: usize> = (
    Vec<Vec<<F as PackedValue>::Value>>,
    Vec<[<F as PackedValue>::Value; DIGEST_ELEMS]>,
);

impl<F: Field, EF: ExtensionField<F>, const DIGEST_ELEMS: usize> Recursive<EF>
    for HidingHashProofTargets<F, DIGEST_ELEMS>
{
    type Input = HidingValMmcsProof<F, DIGEST_ELEMS>;

    fn new(circuit: &mut CircuitBuilder<EF>, input: &Self::Input) -> Self {
        let salts = input
            .0
            .iter()
            .map(|salt| circuit.alloc_private_inputs(salt.len(), "hiding MMCS leaf salt"))
            .collect();
        Self {
            salts,
            _phantom: PhantomData,
        }
    }

    fn get_values(_input: &Self::Input) -> Vec<EF> {
        vec![]
    }

    fn get_private_values(input: &Self::Input) -> Vec<EF> {
        input
            .0
            .iter()
            .flat_map(|salt| salt.iter().map(|&v| EF::from(v)))
            .collect()
    }
}

impl<F, const DIGEST_ELEMS: usize> MmcsProofTargets for HidingHashProofTargets<F, DIGEST_ELEMS> {
    fn salt_targets(&self) -> &[Vec<Target>] {
        &self.salts
    }
}

type HidingValMmcsMultiProof<F, const DIGEST_ELEMS: usize> = (
    Vec<Vec<Vec<<F as PackedValue>::Value>>>,
    PrunedMerklePaths<<F as PackedValue>::Value, DIGEST_ELEMS>,
);

impl<F: Field, EF: ExtensionField<F>, const DIGEST_ELEMS: usize> RecursiveMultiProofTargets<EF>
    for HidingHashProofTargets<F, DIGEST_ELEMS>
{
    type MultiProof = HidingValMmcsMultiProof<F, DIGEST_ELEMS>;

    fn new_for_query(
        circuit: &mut CircuitBuilder<EF>,
        proof: &Self::MultiProof,
        query: usize,
    ) -> Self {
        let salts = proof
            .0
            .get(query)
            .map(|per_matrix| {
                per_matrix
                    .iter()
                    .map(|salt| circuit.alloc_private_inputs(salt.len(), "hiding MMCS leaf salt"))
                    .collect()
            })
            .unwrap_or_default();
        Self {
            salts,
            _phantom: PhantomData,
        }
    }

    fn get_private_values_for_query(proof: &Self::MultiProof, query: usize) -> Vec<EF> {
        proof
            .0
            .get(query)
            .into_iter()
            .flatten()
            .flat_map(|salt| salt.iter().map(|&v| EF::from(v)))
            .collect()
    }
}

impl<F: Field, EF: ExtensionField<F>, const DIGEST_ELEMS: usize>
    PreparedRecursiveMultiProofTargets<EF> for HidingHashProofTargets<F, DIGEST_ELEMS>
{
    type Shape = HidingOpeningAdviceShape;

    fn multiproof_shape(
        proof: &Self::MultiProof,
        query_matrix_counts: &[usize],
    ) -> Result<Self::Shape, VerificationError> {
        <Self as PreparedRecursiveMultiProofTargets<EF>>::validate_multiproof_raw(
            proof,
            query_matrix_counts.iter().copied(),
            None,
        )?;
        if proof.0.len() != query_matrix_counts.len()
            || proof
                .0
                .iter()
                .zip(query_matrix_counts)
                .any(|(matrices, &expected)| matrices.len() != expected)
        {
            return Err(VerificationError::InvalidProofShape(
                "hiding FRI salt query/matrix shape mismatch".into(),
            ));
        }
        Ok(HidingOpeningAdviceShape {
            salts: proof
                .0
                .iter()
                .map(|matrices| matrices.iter().map(Vec::len).collect())
                .collect(),
        })
    }

    fn validate_multiproof_raw<I>(
        proof: &Self::MultiProof,
        query_matrix_counts: I,
        required_salt_elems: Option<usize>,
    ) -> Result<(), VerificationError>
    where
        I: ExactSizeIterator<Item = usize>,
    {
        if proof.0.len() != query_matrix_counts.len() {
            return Err(VerificationError::InvalidProofShape(
                "hiding FRI salt query count mismatch".into(),
            ));
        }
        for (salts, expected) in proof.0.iter().zip(query_matrix_counts) {
            if salts.len() != expected {
                return Err(VerificationError::InvalidProofShape(
                    "hiding FRI salt matrix count mismatch".into(),
                ));
            }
            if let Some(salt_width) = required_salt_elems
                && salts.iter().any(|salt| salt.len() != salt_width)
            {
                return Err(VerificationError::InvalidProofShape(
                    "hiding FRI salt width mismatch".into(),
                ));
            }
        }
        Ok(())
    }
}

impl<F: Field, const DIGEST_ELEMS: usize> sealed::FriPrivateAdvice
    for HidingHashProofTargets<F, DIGEST_ELEMS>
{
}

impl<F: Field, EF: ExtensionField<F>, const DIGEST_ELEMS: usize> FriPrivateAdvice<EF>
    for HidingHashProofTargets<F, DIGEST_ELEMS>
{
    fn checked_private_values_len(proof: &Self::MultiProof) -> Result<usize, VerificationError> {
        let mut total = 0usize;
        for query in &proof.0 {
            for matrix in query {
                total = crate::pcs::fri::context::checked_add_len(
                    total,
                    matrix.len(),
                    "hiding MMCS salt advice",
                )?;
            }
        }
        Ok(total)
    }

    fn add_private_resource_usage(
        proof: &Self::MultiProof,
        usage: &mut InputResourceUsage,
        limits: &VerifierLimits,
    ) -> Result<(), VerificationError> {
        usage.add_metadata_entries(limits, proof.0.len())?;
        for query in &proof.0 {
            usage.add_metadata_entries(limits, query.len())?;
            for matrix in query {
                usage.check_matrix_width(limits, matrix.len())?;
                usage.add_scalar_elements(limits, matrix.len())?;
            }
        }
        Ok(())
    }

    fn compressed_frontier_hashes(proof: &Self::MultiProof) -> usize {
        proof.1.sibling_hashes.len()
    }
}

pub struct RecValHidingMmcs<F: Field, const DIGEST_ELEMS: usize, const SALT_ELEMS: usize, H, C, R>
where
    H: CryptographicHasher<F, [F; DIGEST_ELEMS]>
        + CryptographicHasher<F::Packing, [F::Packing; DIGEST_ELEMS]>
        + Sync,
{
    pub hash: H,
    pub compress: C,
    _phantom: PhantomData<(F, R)>,
}

impl<
    F: Field + Serialize + DeserializeOwned,
    EF: ExtensionField<F>,
    const DIGEST_ELEMS: usize,
    const SALT_ELEMS: usize,
    H,
    C,
    R,
> RecursiveMmcs<F, EF> for RecValHidingMmcs<F, DIGEST_ELEMS, SALT_ELEMS, H, C, R>
where
    H: CryptographicHasher<F, [F; DIGEST_ELEMS]>
        + CryptographicHasher<F::Packing, [F::Packing; DIGEST_ELEMS]>
        + Sync,
    C: PseudoCompressionFunction<[F; DIGEST_ELEMS], 2>
        + PseudoCompressionFunction<[F::Packing; DIGEST_ELEMS], 2>
        + Sync,
    R: Rng + Send + SeedableRng + CryptoRng,
    StandardUniform: Distribution<F>,
    [F; DIGEST_ELEMS]: Serialize + for<'a> Deserialize<'a>,
{
    type Input = MerkleTreeHidingMmcs<F::Packing, F::Packing, H, C, R, 2, DIGEST_ELEMS, SALT_ELEMS>;

    type Commitment = MerkleCapTargets<F, DIGEST_ELEMS>;

    type Proof = HidingHashProofTargets<F, DIGEST_ELEMS>;
}

pub type InputProofTargets<F, EF, Inner> = Vec<BatchOpeningTargets<F, EF, Inner>>;

pub(crate) trait NativeFriSaltWidth {
    const SALT_ELEMS: Option<usize>;
}

impl<P, PW, H, C, const ARITY: usize, const DIGEST_ELEMS: usize> NativeFriSaltWidth
    for MerkleTreeMmcs<P, PW, H, C, ARITY, DIGEST_ELEMS>
{
    const SALT_ELEMS: Option<usize> = None;
}

impl<P, PW, H, C, R, const ARITY: usize, const DIGEST_ELEMS: usize, const SALT_ELEMS: usize>
    NativeFriSaltWidth for MerkleTreeHidingMmcs<P, PW, H, C, R, ARITY, DIGEST_ELEMS, SALT_ELEMS>
{
    const SALT_ELEMS: Option<usize> = Some(SALT_ELEMS);
}

impl<F, EF, M: NativeFriSaltWidth> NativeFriSaltWidth for ExtensionMmcs<F, EF, M> {
    const SALT_ELEMS: Option<usize> = M::SALT_ELEMS;
}

pub type TwoAdicFriProofTargets<F, EF, RecMmcs, Inner> =
    FriProofTargets<F, EF, RecMmcs, InputProofTargets<F, EF, Inner>, Target>;

#[allow(clippy::type_complexity)]
pub(crate) fn validate_builtin_fri_raw<F, EF, RF, RI, W>(
    input: &FriProof<EF, RF::Input, W::Input, Vec<BatchMultiOpening<F, RI::Input>>>,
    input_salt_elems: Option<usize>,
    phase_salt_elems: Option<usize>,
) -> Result<(), VerificationError>
where
    F: Field,
    EF: ExtensionField<F>,
    RF: RecursiveExtensionMmcs<F, EF>,
    RI: RecursiveMmcs<F, EF>,
    W: Recursive<EF>,
    RI::Proof:
        PreparedRecursiveMultiProofTargets<EF, MultiProof = <RI::Input as Mmcs<F>>::MultiProof>,
    RF::Proof:
        PreparedRecursiveMultiProofTargets<EF, MultiProof = <RF::Input as Mmcs<EF>>::MultiProof>,
{
    if input.commit_phase_openings.is_empty() {
        return Err(VerificationError::InvalidProofShape(
            "FRI must have at least one fold phase".into(),
        ));
    }
    let query_count = InputProofTargets::<F, EF, RI>::validate_openings_raw(&input.input_openings)?;
    for batch in &input.input_openings {
        <RI::Proof as PreparedRecursiveMultiProofTargets<EF>>::validate_multiproof_raw(
            &batch.opening_proof,
            batch.opened_values.iter().map(Vec::len),
            input_salt_elems,
        )?;
    }
    for step in &input.commit_phase_openings {
        if query_count.is_some_and(|count| count != step.sibling_values.len()) {
            return Err(VerificationError::InvalidProofShape(
                "FRI query counts disagree".into(),
            ));
        }
        <RF::Proof as PreparedRecursiveMultiProofTargets<EF>>::validate_multiproof_raw(
            &step.opening_proof,
            core::iter::repeat_n(1usize, step.sibling_values.len()),
            phase_salt_elems,
        )?;
    }
    Ok(())
}

impl<F, EF, RF, RI> CheckedFriOpening<EF, RI::Commitment>
    for FriProofTargets<F, EF, RF, InputProofTargets<F, EF, RI>, Witness<F>>
where
    F: TwoAdicField + PrimeField64,
    EF: ExtensionField<F>,
    RF: RecursiveExtensionMmcs<F, EF>,
    RI: RecursiveMmcs<F, EF>,
    RI::Input: NativeFriSaltWidth,
    RF::Input: NativeFriSaltWidth,
    RI::Commitment: CheckedFriCommitment<EF, Input = <RI::Input as Mmcs<F>>::Commitment>,
    RF::Commitment: CheckedFriCommitment<EF, Input = <RF::Input as Mmcs<EF>>::Commitment>,
    RI::Proof: FriPrivateAdvice<EF, MultiProof = <RI::Input as Mmcs<F>>::MultiProof>,
    RF::Proof: FriPrivateAdvice<EF, MultiProof = <RF::Input as Mmcs<EF>>::MultiProof>,
{
    type PhaseCommitment = RF::Commitment;

    fn check_fri_resources(
        input: &Self::Input,
        limits: &VerifierLimits,
    ) -> Result<InputResourceUsage, VerificationError> {
        crate::pcs::fri::context::check_fri_resource_limits::<F, EF, RI, RF>(input, None, limits)
    }

    fn validate_fri_context(
        input: &Self::Input,
        native: &NativeFriParams,
        recursive: &FriVerifierParams,
        layout: FriOpeningLayout<'_>,
        input_caps: &[&<RI::Commitment as Recursive<EF>>::Input],
    ) -> Result<ValidatedFriContext, VerificationError> {
        validate_fri_context_with_caps::<F, EF, RI, RF>(
            input,
            native,
            recursive,
            layout,
            input_caps,
            <RI::Input as NativeFriSaltWidth>::SALT_ELEMS,
            <RF::Input as NativeFriSaltWidth>::SALT_ELEMS,
            None,
        )
    }

    fn validate_fri_replacement(
        input: &Self::Input,
        expected: &ValidatedFriContext,
        candidate_layout: FriOpeningLayout<'_>,
        input_caps: &[&<RI::Commitment as Recursive<EF>>::Input],
    ) -> Result<(), VerificationError> {
        validate_fri_replacement_with_caps::<F, EF, RI, RF>(
            input,
            &expected.native_params(),
            &expected.recursive_params(),
            expected,
            candidate_layout,
            input_caps,
            <RI::Input as NativeFriSaltWidth>::SALT_ELEMS,
            <RF::Input as NativeFriSaltWidth>::SALT_ELEMS,
            None,
        )
    }
}

impl<F, EF, RF, RI> CheckedFriOpening<EF, RI::Commitment>
    for HidingFriProofTargets<F, EF, RF, InputProofTargets<F, EF, RI>, Witness<F>>
where
    F: TwoAdicField + PrimeField64,
    EF: ExtensionField<F>,
    RF: RecursiveExtensionMmcs<F, EF>,
    RI: RecursiveMmcs<F, EF>,
    RI::Input: NativeFriSaltWidth,
    RF::Input: NativeFriSaltWidth,
    RI::Commitment: CheckedFriCommitment<EF, Input = <RI::Input as Mmcs<F>>::Commitment>,
    RF::Commitment: CheckedFriCommitment<EF, Input = <RF::Input as Mmcs<EF>>::Commitment>,
    RI::Proof: FriPrivateAdvice<EF, MultiProof = <RI::Input as Mmcs<F>>::MultiProof>,
    RF::Proof: FriPrivateAdvice<EF, MultiProof = <RF::Input as Mmcs<EF>>::MultiProof>,
{
    type PhaseCommitment = RF::Commitment;

    fn check_fri_resources(
        input: &Self::Input,
        limits: &VerifierLimits,
    ) -> Result<InputResourceUsage, VerificationError> {
        crate::pcs::fri::context::check_fri_resource_limits::<F, EF, RI, RF>(
            &input.1,
            Some(&input.0),
            limits,
        )
    }

    fn validate_fri_context(
        input: &Self::Input,
        native: &NativeFriParams,
        recursive: &FriVerifierParams,
        layout: FriOpeningLayout<'_>,
        input_caps: &[&<RI::Commitment as Recursive<EF>>::Input],
    ) -> Result<ValidatedFriContext, VerificationError> {
        validate_fri_context_with_caps::<F, EF, RI, RF>(
            &input.1,
            native,
            recursive,
            layout,
            input_caps,
            <RI::Input as NativeFriSaltWidth>::SALT_ELEMS,
            <RF::Input as NativeFriSaltWidth>::SALT_ELEMS,
            Some(&input.0),
        )
    }

    fn validate_fri_replacement(
        input: &Self::Input,
        expected: &ValidatedFriContext,
        candidate_layout: FriOpeningLayout<'_>,
        input_caps: &[&<RI::Commitment as Recursive<EF>>::Input],
    ) -> Result<(), VerificationError> {
        validate_fri_replacement_with_caps::<F, EF, RI, RF>(
            &input.1,
            &expected.native_params(),
            &expected.recursive_params(),
            expected,
            candidate_layout,
            input_caps,
            <RI::Input as NativeFriSaltWidth>::SALT_ELEMS,
            <RF::Input as NativeFriSaltWidth>::SALT_ELEMS,
            Some(&input.0),
        )
    }
}

impl<F: Field, EF: ExtensionField<F>, Inner: RecursiveMmcs<F, EF>> Recursive<EF>
    for InputProofTargets<F, EF, Inner>
{
    type Input = Vec<BatchOpening<F, Inner::Input>>;

    fn new(circuit: &mut CircuitBuilder<EF>, input: &Self::Input) -> Self {
        let num_batch_openings = input.len();
        let mut batch_openings = Self::with_capacity(num_batch_openings);
        for batch_opening in input.iter() {
            batch_openings.push(BatchOpeningTargets::new(circuit, batch_opening));
        }

        batch_openings
    }

    fn get_values(input: &Self::Input) -> Vec<EF> {
        input
            .iter()
            .flat_map(|batch_opening| {
                BatchOpeningTargets::<F, EF, Inner>::get_values(batch_opening)
            })
            .collect()
    }

    fn get_private_values(input: &Self::Input) -> Vec<EF> {
        input
            .iter()
            .flat_map(|batch_opening| {
                BatchOpeningTargets::<F, EF, Inner>::get_private_values(batch_opening)
            })
            .collect()
    }
}

impl<F: Field, EF: ExtensionField<F>, Inner: RecursiveMmcs<F, EF>> RecursiveFriInputOpenings<EF>
    for InputProofTargets<F, EF, Inner>
where
    Inner::Proof:
        RecursiveMultiProofTargets<EF, MultiProof = <Inner::Input as Mmcs<F>>::MultiProof>,
{
    type MultiOpenings = Vec<BatchMultiOpening<F, Inner::Input>>;

    fn num_queries(input: &Self::MultiOpenings) -> Option<usize> {
        input.iter().map(|batch| batch.opened_values.len()).min()
    }

    fn new_for_query(
        circuit: &mut CircuitBuilder<EF>,
        input: &Self::MultiOpenings,
        query: usize,
    ) -> Self {
        input
            .iter()
            .map(|batch| BatchOpeningTargets::new_for_query(circuit, batch, query))
            .collect()
    }

    fn get_values_for_query(input: &Self::MultiOpenings, query: usize) -> Vec<EF> {
        input
            .iter()
            .flat_map(|batch| {
                BatchOpeningTargets::<F, EF, Inner>::get_values_for_query(batch, query)
            })
            .collect()
    }

    fn get_private_values_for_query(input: &Self::MultiOpenings, query: usize) -> Vec<EF> {
        input
            .iter()
            .flat_map(|batch| {
                BatchOpeningTargets::<F, EF, Inner>::get_private_values_for_query(batch, query)
            })
            .collect()
    }
}

impl<F: Field, EF: ExtensionField<F>, Inner: RecursiveMmcs<F, EF>>
    PreparedRecursiveFriInputOpenings<EF> for InputProofTargets<F, EF, Inner>
where
    Inner::Proof:
        PreparedRecursiveMultiProofTargets<EF, MultiProof = <Inner::Input as Mmcs<F>>::MultiProof>,
{
    type Shape =
        Vec<FriInputBatchShape<<Inner::Proof as PreparedRecursiveMultiProofTargets<EF>>::Shape>>;

    fn openings_shape(input: &Self::MultiOpenings) -> Result<Self::Shape, VerificationError> {
        Self::validate_openings_raw(input)?;
        input
            .iter()
            .map(|batch| {
                let query_matrix_counts =
                    batch.opened_values.iter().map(Vec::len).collect::<Vec<_>>();
                Ok(FriInputBatchShape {
                    opened_values: batch
                        .opened_values
                        .iter()
                        .map(|matrices| matrices.iter().map(Vec::len).collect())
                        .collect(),
                    opening_advice: Inner::Proof::multiproof_shape(
                        &batch.opening_proof,
                        &query_matrix_counts,
                    )?,
                })
            })
            .collect()
    }

    fn query_counts(input: &Self::MultiOpenings) -> Vec<usize> {
        input
            .iter()
            .map(|batch| batch.opened_values.len())
            .collect()
    }

    fn validate_openings_raw(
        input: &Self::MultiOpenings,
    ) -> Result<Option<usize>, VerificationError> {
        let mut query_count = None;
        for batch in input {
            let count = batch.opened_values.len();
            if let Some(expected) = query_count {
                if expected != count {
                    return Err(VerificationError::InvalidProofShape(
                        "FRI input query counts disagree".into(),
                    ));
                }
            } else {
                query_count = Some(count);
            }
            Inner::Proof::validate_multiproof_raw(
                &batch.opening_proof,
                batch.opened_values.iter().map(Vec::len),
                None,
            )?;
        }
        Ok(query_count)
    }
}

type RecursiveFriProof<SC, RecursiveFriMmcs, RecursiveInputProof> = FriProofTargets<
    Val<SC>,
    <SC as StarkGenericConfig>::Challenge,
    RecursiveFriMmcs,
    RecursiveInputProof,
    Witness<Val<SC>>,
>;

impl<SC, Dft, Comm, InputMmcs, RecursiveInputMmcs, RecursiveFriMmcs, FriMmcs>
    RecursivePcs<
        SC,
        InputProofTargets<Val<SC>, SC::Challenge, RecursiveInputMmcs>,
        RecursiveFriProof<
            SC,
            RecursiveFriMmcs,
            InputProofTargets<Val<SC>, SC::Challenge, RecursiveInputMmcs>,
        >,
        Comm,
        TwoAdicMultiplicativeCoset<Val<SC>>,
    > for TwoAdicFriPcs<Val<SC>, Dft, InputMmcs, FriMmcs>
where
    SC: StarkGenericConfig,
    Val<SC>: TwoAdicField + PrimeField64,
    InputMmcs: Mmcs<Val<SC>>,
    FriMmcs: Mmcs<SC::Challenge>,
    Comm: Recursive<SC::Challenge> + ObservableCommitment,
    RecursiveInputMmcs: RecursiveMmcs<Val<SC>, SC::Challenge, Input = InputMmcs>,
    RecursiveInputMmcs::Proof: MmcsProofTargets
        + RecursiveMultiProofTargets<
            SC::Challenge,
            MultiProof = <InputMmcs as Mmcs<Val<SC>>>::MultiProof,
        >,
    RecursiveFriMmcs: RecursiveExtensionMmcs<Val<SC>, SC::Challenge, Input = FriMmcs>,
    RecursiveFriMmcs::Commitment: ObservableCommitment,
    RecursiveFriMmcs::Proof: MmcsProofTargets
        + RecursiveMultiProofTargets<
            SC::Challenge,
            MultiProof = <FriMmcs as Mmcs<SC::Challenge>>::MultiProof,
        >,
    SC::Challenger: GrindingChallenger + CanObserve<FriMmcs::Commitment>,
{
    type VerifierParams = FriVerifierParams;

    fn claims_transcript_seed(
        _params: &Self::VerifierParams,
        claimed_evaluation_counts: Vec<Vec<Vec<usize>>>,
    ) -> Vec<Val<SC>>
    where
        Val<SC>: PrimeField64,
        SC::Challenge: ExtensionField<Val<SC>>,
    {
        fri_pcs_transcript_seed::<Val<SC>, SC::Challenge>(claimed_evaluation_counts)
    }
    type RecursiveProof = RecursiveFriProof<
        SC,
        RecursiveFriMmcs,
        InputProofTargets<Val<SC>, SC::Challenge, RecursiveInputMmcs>,
    >;

    fn get_challenges_circuit<
        const WIDTH: usize,
        const RATE: usize,
        C: crate::ChallengerPermConfig,
    >(
        circuit: &mut CircuitBuilder<SC::Challenge>,
        challenger: &mut CircuitChallenger<WIDTH, RATE, C>,
        fri_proof: &RecursiveFriProof<
            SC,
            RecursiveFriMmcs,
            InputProofTargets<Val<SC>, SC::Challenge, RecursiveInputMmcs>,
        >,
        _opened_values: &OpenedValuesTargetsWithLookups<SC>,
        params: &Self::VerifierParams,
    ) -> Result<Vec<Target>, CircuitBuilderError>
    where
        Val<SC>: PrimeField64,
        SC::Challenge: ExtensionField<Val<SC>>,
    {

        let fri_alpha = challenger.sample_ext(circuit);

        challenger.observe_seed(
            circuit,
            &fri_transcript_seed::<Val<SC>, SC::Challenge>(
                params,
                &fri_proof.log_arities,
                fri_proof.query_proofs.len(),
            ),
        );

        let mut betas = Vec::with_capacity(fri_proof.commit_phase_commits.len());
        for (commit, pow) in fri_proof
            .commit_phase_commits
            .iter()
            .zip(fri_proof.commit_pow_witnesses.iter())
        {
            let commit_targets = commit.to_observation_targets();
            challenger.observe_slice(circuit, &commit_targets);
            challenger.check_pow_witness(circuit, params.commit_pow_bits(), pow.witness)?;
            let beta = challenger.sample_ext(circuit);
            betas.push(beta);
        }

        challenger.observe_ext_slice(circuit, &fri_proof.final_poly);

        challenger.check_pow_witness(
            circuit,
            params.query_pow_bits(),
            fri_proof.pow_witness.witness,
        )?;

        let mut challenges = Vec::with_capacity(1 + betas.len());
        challenges.push(fri_alpha);
        challenges.extend(betas);
        Ok(challenges)
    }

    fn verify_circuit<const WIDTH: usize, const RATE: usize, C: crate::ChallengerPermConfig>(
        &self,
        circuit: &mut CircuitBuilder<SC::Challenge>,
        challenges: &[Target],
        challenger: &mut CircuitChallenger<WIDTH, RATE, C>,
        commitments_with_opening_points: &ComsWithOpeningsTargets<
            Comm,
            TwoAdicMultiplicativeCoset<Val<SC>>,
        >,
        opening_proof: &Self::RecursiveProof,
        params: &Self::VerifierParams,
    ) -> Result<Vec<NonPrimitiveOpId>, VerificationError> {
        let log_blowup = params.log_blowup();
        let log_final_poly_len = params.log_final_poly_len();
        let required_num_queries = params.num_queries();
        let permutation_config = params.permutation_config();
        let num_betas = opening_proof.commit_phase_commits.len();
        let num_queries = opening_proof.query_proofs.len();

        if num_queries < required_num_queries {
            return Err(VerificationError::InvalidProofShape(format!(
                "FRI proof has {num_queries} queries but verifier params require at least {required_num_queries}"
            )));
        }

        let alpha = challenges[0];
        let betas = &challenges[1..1 + num_betas];

        let total_log_reduction: usize = opening_proof.log_arities.iter().sum();
        let log_max_height = total_log_reduction + log_final_poly_len + log_blowup;

        let max_query_index_bits = Val::<SC>::bits();
        if log_max_height > max_query_index_bits {
            return Err(VerificationError::InvalidProofShape(format!(
                "log_max_height {log_max_height} exceeds base field bit width {max_query_index_bits}"
            )));
        }

        let index_bits_per_query: Vec<Vec<Target>> = (0..num_queries)
            .map(|_| challenger.sample_bits(circuit, log_max_height))
            .collect::<Result<Vec<_>, _>>()?;

        verify_fri_circuit(
            circuit,
            opening_proof,
            alpha,
            betas,
            &index_bits_per_query,
            commitments_with_opening_points,
            log_blowup,
            permutation_config,
        )
    }

    fn selectors_at_point_circuit(
        &self,
        circuit: &mut CircuitBuilder<SC::Challenge>,
        domain: &TwoAdicMultiplicativeCoset<Val<SC>>,
        point: &Target,
    ) -> RecursiveLagrangeSelectors {
        let shift_inv =
            circuit.alloc_const(SC::Challenge::from(domain.shift_inverse()), "shift_inv");
        let one = circuit.alloc_const(SC::Challenge::from(Val::<SC>::ONE), "1");
        let subgroup_gen_inv = circuit.alloc_const(
            SC::Challenge::from(domain.subgroup_generator().inverse()),
            "subgroup_gen_inv",
        );

        let unshifted_point = circuit.alloc_mul(shift_inv, *point, "unshifted_point");
        let us_exp = circuit.exp_power_of_2(unshifted_point, domain.log_size());
        let z_h = circuit.alloc_sub(us_exp, one, "z_h");

        let us_minus_one = circuit.alloc_sub(unshifted_point, one, "us_minus_one");
        let us_minus_gen_inv =
            circuit.alloc_sub(unshifted_point, subgroup_gen_inv, "us_minus_gen_inv");

        let is_first_row = circuit.alloc_div(z_h, us_minus_one, "is_first_row");
        let is_last_row = circuit.alloc_div(z_h, us_minus_gen_inv, "is_last_row");
        let is_transition = us_minus_gen_inv;
        let inv_vanishing = circuit.alloc_div(one, z_h, "inv_vanishing");

        let row_selectors = RowSelectorsTargets {
            is_first_row,
            is_last_row,
            is_transition,
        };
        RecursiveLagrangeSelectors {
            row_selectors,
            inv_vanishing,
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
        trace_domain.first_point().into()
    }

    fn get_fri_random_opened_values(
        _proof: &RecursiveFriProof<
            SC,
            RecursiveFriMmcs,
            InputProofTargets<Val<SC>, SC::Challenge, RecursiveInputMmcs>,
        >,
    ) -> &[Vec<Vec<Vec<Target>>>] {
        &[]
    }
}

pub struct HidingOpenedValuesTargets<EF: Field> {
    pub rounds: Vec<Vec<Vec<Vec<Target>>>>,
    _phantom: PhantomData<EF>,
}

impl<EF: Field> Recursive<EF> for HidingOpenedValuesTargets<EF> {
    type Input = OpenedValues<EF>;

    fn new(circuit: &mut CircuitBuilder<EF>, input: &Self::Input) -> Self {
        let rounds = input
            .iter()
            .map(|round| {
                round
                    .iter()
                    .map(|matrix| {
                        matrix
                            .iter()
                            .map(|point_vals| {
                                circuit.alloc_private_inputs(
                                    point_vals.len(),
                                    "hiding random opened values",
                                )
                            })
                            .collect::<Vec<_>>()
                    })
                    .collect::<Vec<_>>()
            })
            .collect::<Vec<_>>();

        Self {
            rounds,
            _phantom: PhantomData,
        }
    }

    fn get_values(_input: &Self::Input) -> Vec<EF> {
        vec![]
    }

    fn get_private_values(input: &Self::Input) -> Vec<EF> {
        input
            .iter()
            .flat_map(|round| round.iter())
            .flat_map(|matrix| matrix.iter())
            .flat_map(|point_vals| point_vals.iter().copied())
            .collect()
    }
}

impl<EF: Field> PreparedRecursive<EF> for HidingOpenedValuesTargets<EF> {
    type Shape = Vec<Vec<Vec<usize>>>;

    fn input_shape(input: &Self::Input) -> Result<Self::Shape, VerificationError> {
        Ok(input
            .iter()
            .map(|round| {
                round
                    .iter()
                    .map(|matrix| matrix.iter().map(Vec::len).collect())
                    .collect()
            })
            .collect())
    }
}

pub struct HidingFriProofTargets<
    F: Field,
    EF: ExtensionField<F>,
    RecMmcs: RecursiveExtensionMmcs<F, EF>,
    InputProof: Recursive<EF>,
    PowWitness: Recursive<EF>,
> {
    pub random_opened_values: HidingOpenedValuesTargets<EF>,
    pub inner_proof: FriProofTargets<F, EF, RecMmcs, InputProof, PowWitness>,
}

impl<
    F: Field,
    EF: ExtensionField<F>,
    RecMmcs: RecursiveExtensionMmcs<F, EF>,
    InputProof: Recursive<EF> + RecursiveFriInputOpenings<EF>,
    PowWitness: Recursive<EF>,
> Recursive<EF> for HidingFriProofTargets<F, EF, RecMmcs, InputProof, PowWitness>
where
    RecMmcs::Proof:
        RecursiveMultiProofTargets<EF, MultiProof = <RecMmcs::Input as Mmcs<EF>>::MultiProof>,
{
    type Input = (
        OpenedValues<EF>,
        FriProof<EF, RecMmcs::Input, PowWitness::Input, InputProof::MultiOpenings>,
    );

    fn new(circuit: &mut CircuitBuilder<EF>, input: &Self::Input) -> Self {
        Self {
            random_opened_values: HidingOpenedValuesTargets::new(circuit, &input.0),
            inner_proof: FriProofTargets::new(circuit, &input.1),
        }
    }

    fn get_values(input: &Self::Input) -> Vec<EF> {
        FriProofTargets::<F, EF, RecMmcs, InputProof, PowWitness>::get_values(&input.1)
    }

    fn get_private_values(input: &Self::Input) -> Vec<EF> {
        HidingOpenedValuesTargets::<EF>::get_private_values(&input.0)
            .into_iter()
            .chain(
                FriProofTargets::<F, EF, RecMmcs, InputProof, PowWitness>::get_private_values(
                    &input.1,
                ),
            )
            .collect()
    }
}

impl<
    F: Field,
    EF: ExtensionField<F>,
    RecMmcs: RecursiveExtensionMmcs<F, EF>,
    InputProof: Recursive<EF> + PreparedRecursiveFriInputOpenings<EF>,
    PowWitness: PreparedRecursive<EF>,
> PreparedRecursive<EF> for HidingFriProofTargets<F, EF, RecMmcs, InputProof, PowWitness>
where
    RecMmcs::Commitment: PreparedRecursive<EF>,
    RecMmcs::Proof: PreparedRecursiveMultiProofTargets<
            EF,
            MultiProof = <RecMmcs::Input as Mmcs<EF>>::MultiProof,
        >,
{
    type Shape = HidingFriShape<
        <FriProofTargets<F, EF, RecMmcs, InputProof, PowWitness> as PreparedRecursive<EF>>::Shape,
    >;

    fn input_shape(input: &Self::Input) -> Result<Self::Shape, VerificationError> {
        let (random_opened_values, inner_proof) = input;
        Ok(HidingFriShape {
            random_openings: HidingOpenedValuesTargets::<EF>::input_shape(random_opened_values)?,
            inner: FriProofTargets::<F, EF, RecMmcs, InputProof, PowWitness>::input_shape(
                inner_proof,
            )?,
        })
    }
}

impl<
    F: Field,
    EF: ExtensionField<F>,
    RecMmcs: RecursiveExtensionMmcs<F, EF>,
    RI: RecursiveMmcs<F, EF>,
> CheckedRecursive<EF>
    for HidingFriProofTargets<F, EF, RecMmcs, InputProofTargets<F, EF, RI>, Witness<F>>
where
    RecMmcs::Commitment: CheckedFriCommitment<EF, Input = <RecMmcs::Input as Mmcs<EF>>::Commitment>,
    RecMmcs::Proof: FriPrivateAdvice<EF, MultiProof = <RecMmcs::Input as Mmcs<EF>>::MultiProof>,
    RecMmcs::Input: NativeFriSaltWidth,
    RI::Input: NativeFriSaltWidth,
    RI::Proof: FriPrivateAdvice<EF, MultiProof = <RI::Input as Mmcs<F>>::MultiProof>,
{
    fn validate_input(input: &Self::Input) -> Result<(), VerificationError> {
        validate_counted_fri_raw::<F, EF, RI, RecMmcs>(
            &input.1,
            Some(&input.0),
            <RI::Input as NativeFriSaltWidth>::SALT_ELEMS,
            <RecMmcs::Input as NativeFriSaltWidth>::SALT_ELEMS,
        )
        .map(|_| ())
    }
}

type RecursiveHidingFriProof<SC, RecursiveFriMmcs, RecursiveInputProof> = HidingFriProofTargets<
    Val<SC>,
    <SC as StarkGenericConfig>::Challenge,
    RecursiveFriMmcs,
    RecursiveInputProof,
    Witness<Val<SC>>,
>;

type HidingMergedCommitments<SC, Comm> = (
    Comm,
    Vec<(
        TwoAdicMultiplicativeCoset<Val<SC>>,
        Vec<(Target, Vec<Target>)>,
    )>,
);

fn merge_hiding_random_openings<SC, Comm>(
    commitments_with_opening_points: &ComsWithOpeningsTargets<
        Comm,
        TwoAdicMultiplicativeCoset<Val<SC>>,
    >,
    random_opened_values: &[Vec<Vec<Vec<Target>>>],
) -> Result<Vec<HidingMergedCommitments<SC, Comm>>, VerificationError>
where
    SC: StarkGenericConfig,
    Val<SC>: TwoAdicField,
    Comm: Clone,
{
    if commitments_with_opening_points.len() != random_opened_values.len() {
        return Err(VerificationError::InvalidProofShape(
            "Hiding FRI proof shape mismatch: random rounds count does not match commitments"
                .to_string(),
        ));
    }

    let mut merged = Vec::with_capacity(commitments_with_opening_points.len());

    for ((commitment, mats), rand_round) in commitments_with_opening_points
        .iter()
        .zip(random_opened_values.iter())
    {
        if mats.len() != rand_round.len() {
            return Err(VerificationError::InvalidProofShape(
                "Hiding FRI proof shape mismatch: random matrices count does not match".to_string(),
            ));
        }

        let mut merged_mats = Vec::with_capacity(mats.len());
        for ((domain, points), rand_mat) in mats.iter().zip(rand_round.iter()) {
            if points.len() != rand_mat.len() {
                return Err(VerificationError::InvalidProofShape(
                    "Hiding FRI proof shape mismatch: random points count does not match"
                        .to_string(),
                ));
            }

            let mut merged_points = Vec::with_capacity(points.len());
            for ((point, vals), rand_point) in points.iter().zip(rand_mat.iter()) {
                let mut merged_vals = vals.clone();
                merged_vals.extend(rand_point.iter().copied());
                merged_points.push((*point, merged_vals));
            }

            merged_mats.push((*domain, merged_points));
        }

        merged.push((commitment.clone(), merged_mats));
    }

    Ok(merged)
}

impl<SC, Dft, Comm, InputMmcs, RecursiveInputMmcs, RecursiveFriMmcs, FriMmcs, R>
    RecursivePcs<
        SC,
        InputProofTargets<Val<SC>, SC::Challenge, RecursiveInputMmcs>,
        RecursiveHidingFriProof<
            SC,
            RecursiveFriMmcs,
            InputProofTargets<Val<SC>, SC::Challenge, RecursiveInputMmcs>,
        >,
        Comm,
        TwoAdicMultiplicativeCoset<Val<SC>>,
    > for HidingFriPcs<Val<SC>, Dft, InputMmcs, FriMmcs, R>
where
    SC: StarkGenericConfig,
    Val<SC>: TwoAdicField + PrimeField64,
    InputMmcs: Mmcs<Val<SC>>,
    FriMmcs: Mmcs<SC::Challenge>,
    Comm: Recursive<SC::Challenge> + ObservableCommitment + Clone,
    RecursiveInputMmcs: RecursiveMmcs<Val<SC>, SC::Challenge, Input = InputMmcs>,
    RecursiveInputMmcs::Proof: MmcsProofTargets
        + RecursiveMultiProofTargets<
            SC::Challenge,
            MultiProof = <InputMmcs as Mmcs<Val<SC>>>::MultiProof,
        >,
    RecursiveFriMmcs: RecursiveExtensionMmcs<Val<SC>, SC::Challenge, Input = FriMmcs>,
    RecursiveFriMmcs::Commitment: ObservableCommitment,
    RecursiveFriMmcs::Proof: MmcsProofTargets
        + RecursiveMultiProofTargets<
            SC::Challenge,
            MultiProof = <FriMmcs as Mmcs<SC::Challenge>>::MultiProof,
        >,
    SC::Challenger: GrindingChallenger + CanObserve<FriMmcs::Commitment>,
{
    type VerifierParams = FriVerifierParams;

    fn claims_transcript_seed(
        _params: &Self::VerifierParams,
        claimed_evaluation_counts: Vec<Vec<Vec<usize>>>,
    ) -> Vec<Val<SC>>
    where
        Val<SC>: PrimeField64,
        SC::Challenge: ExtensionField<Val<SC>>,
    {
        fri_pcs_transcript_seed::<Val<SC>, SC::Challenge>(claimed_evaluation_counts)
    }
    type RecursiveProof = RecursiveHidingFriProof<
        SC,
        RecursiveFriMmcs,
        InputProofTargets<Val<SC>, SC::Challenge, RecursiveInputMmcs>,
    >;

    fn get_challenges_circuit<
        const WIDTH: usize,
        const RATE: usize,
        C: crate::ChallengerPermConfig,
    >(
        circuit: &mut CircuitBuilder<SC::Challenge>,
        challenger: &mut CircuitChallenger<WIDTH, RATE, C>,
        proof_targets: &Self::RecursiveProof,
        _opened_values: &OpenedValuesTargetsWithLookups<SC>,
        params: &Self::VerifierParams,
    ) -> Result<Vec<Target>, CircuitBuilderError>
    where
        Val<SC>: PrimeField64,
        SC::Challenge: ExtensionField<Val<SC>>,
    {
        let fri_proof = &proof_targets.inner_proof;

        let fri_alpha = challenger.sample_ext(circuit);
        challenger.observe_seed(
            circuit,
            &fri_transcript_seed::<Val<SC>, SC::Challenge>(
                params,
                &fri_proof.log_arities,
                fri_proof.query_proofs.len(),
            ),
        );

        let mut betas = Vec::with_capacity(fri_proof.commit_phase_commits.len());
        for (commit, pow) in fri_proof
            .commit_phase_commits
            .iter()
            .zip(fri_proof.commit_pow_witnesses.iter())
        {
            let commit_targets = commit.to_observation_targets();
            challenger.observe_slice(circuit, &commit_targets);
            challenger.check_pow_witness(circuit, params.commit_pow_bits(), pow.witness)?;
            let beta = challenger.sample_ext(circuit);
            betas.push(beta);
        }

        challenger.observe_ext_slice(circuit, &fri_proof.final_poly);

        challenger.check_pow_witness(
            circuit,
            params.query_pow_bits(),
            fri_proof.pow_witness.witness,
        )?;

        let mut challenges = Vec::with_capacity(1 + betas.len());
        challenges.push(fri_alpha);
        challenges.extend(betas);
        Ok(challenges)
    }

    fn verify_circuit<const WIDTH: usize, const RATE: usize, C: crate::ChallengerPermConfig>(
        &self,
        circuit: &mut CircuitBuilder<SC::Challenge>,
        challenges: &[Target],
        challenger: &mut CircuitChallenger<WIDTH, RATE, C>,
        commitments_with_opening_points: &ComsWithOpeningsTargets<
            Comm,
            TwoAdicMultiplicativeCoset<Val<SC>>,
        >,
        opening_proof: &Self::RecursiveProof,
        params: &Self::VerifierParams,
    ) -> Result<Vec<NonPrimitiveOpId>, VerificationError> {
        let log_blowup = params.log_blowup();
        let log_final_poly_len = params.log_final_poly_len();
        let required_num_queries = params.num_queries();
        let permutation_config = params.permutation_config();
        let fri_proof = &opening_proof.inner_proof;
        let num_betas = fri_proof.commit_phase_commits.len();
        let num_queries = fri_proof.query_proofs.len();

        if num_queries < required_num_queries {
            return Err(VerificationError::InvalidProofShape(format!(
                "FRI proof has {num_queries} queries but verifier params require at least {required_num_queries}"
            )));
        }

        let alpha = challenges[0];
        let betas = &challenges[1..1 + num_betas];

        let total_log_reduction: usize = fri_proof.log_arities.iter().sum();
        let log_max_height = total_log_reduction + log_final_poly_len + log_blowup;

        let max_query_index_bits = Val::<SC>::bits();
        if log_max_height > max_query_index_bits {
            return Err(VerificationError::InvalidProofShape(format!(
                "log_max_height {log_max_height} exceeds base field bit width {max_query_index_bits}"
            )));
        }

        let index_bits_per_query: Vec<Vec<Target>> = (0..num_queries)
            .map(|_| challenger.sample_bits(circuit, log_max_height))
            .collect::<Result<Vec<_>, _>>()?;

        let merged_commitments = merge_hiding_random_openings::<SC, Comm>(
            commitments_with_opening_points,
            &opening_proof.random_opened_values.rounds,
        )?;

        verify_fri_circuit(
            circuit,
            fri_proof,
            alpha,
            betas,
            &index_bits_per_query,
            &merged_commitments,
            log_blowup,
            permutation_config,
        )
    }

    fn selectors_at_point_circuit(
        &self,
        circuit: &mut CircuitBuilder<SC::Challenge>,
        domain: &TwoAdicMultiplicativeCoset<Val<SC>>,
        point: &Target,
    ) -> RecursiveLagrangeSelectors {
        let shift_inv =
            circuit.alloc_const(SC::Challenge::from(domain.shift_inverse()), "shift_inv");
        let one = circuit.alloc_const(SC::Challenge::from(Val::<SC>::ONE), "1");
        let subgroup_gen_inv = circuit.alloc_const(
            SC::Challenge::from(domain.subgroup_generator().inverse()),
            "subgroup_gen_inv",
        );

        let unshifted_point = circuit.alloc_mul(shift_inv, *point, "unshifted_point");
        let us_exp = circuit.exp_power_of_2(unshifted_point, domain.log_size());
        let z_h = circuit.alloc_sub(us_exp, one, "z_h");

        let us_minus_one = circuit.alloc_sub(unshifted_point, one, "us_minus_one");
        let us_minus_gen_inv =
            circuit.alloc_sub(unshifted_point, subgroup_gen_inv, "us_minus_gen_inv");

        let is_first_row = circuit.alloc_div(z_h, us_minus_one, "is_first_row");
        let is_last_row = circuit.alloc_div(z_h, us_minus_gen_inv, "is_last_row");
        let is_transition = us_minus_gen_inv;
        let inv_vanishing = circuit.alloc_div(one, z_h, "inv_vanishing");

        let row_selectors = RowSelectorsTargets {
            is_first_row,
            is_last_row,
            is_transition,
        };
        RecursiveLagrangeSelectors {
            row_selectors,
            inv_vanishing,
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
        trace_domain.first_point().into()
    }

    fn get_fri_random_opened_values(
        proof: &RecursiveHidingFriProof<
            SC,
            RecursiveFriMmcs,
            InputProofTargets<Val<SC>, SC::Challenge, RecursiveInputMmcs>,
        >,
    ) -> &[Vec<Vec<Vec<Target>>>] {
        &proof.random_opened_values.rounds
    }
}
