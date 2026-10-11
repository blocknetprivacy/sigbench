use alloc::vec;
use alloc::vec::Vec;
use core::marker::PhantomData;

use p3_batch_stark::common::PreprocessedInstanceMeta;
use p3_batch_stark::proof::OpenedValuesWithLookups;
use p3_batch_stark::{BatchCommitments, BatchOpenedValues, BatchProof, CommonData};
use p3_circuit::CircuitBuilder;
use p3_commit::Pcs;
use p3_field::{ExtensionField, Field, PrimeField64};
use p3_lookup::Lookup;
use p3_uni_stark::{OpenedValues, Proof, StarkGenericConfig, Val};

use crate::Target;
use crate::traits::{Recursive, RecursiveChallenger};

#[derive(Clone)]
pub struct ProofTargets<
    SC: StarkGenericConfig,
    Comm: Recursive<SC::Challenge>,
    OpeningProof: Recursive<SC::Challenge>,
> {
    pub commitments_targets: CommitmentTargets<SC::Challenge, Comm>,
    pub opened_values_targets: OpenedValuesTargets<SC>,
    pub opening_proof: OpeningProof,
    pub degree_bits: usize,
}

#[derive(Clone)]
pub struct BatchProofTargets<
    SC: StarkGenericConfig,
    Comm: Recursive<SC::Challenge>,
    OpeningProof: Recursive<SC::Challenge>,
> {
    pub commitments_targets: CommitmentTargets<SC::Challenge, Comm>,
    pub flattened_opened_values_targets: OpenedValuesTargetsWithLookups<SC>,
    pub(crate) opened_values_targets: BatchOpenedValuesTargets<SC>,
    pub opening_proof: OpeningProof,
    pub lookup_terminals: Vec<Option<Target>>,
    pub degree_bits: Vec<usize>,
}

#[derive(Clone)]
pub struct CommitmentTargets<F: Field, Comm: Recursive<F>> {
    pub trace_targets: Comm,
    pub permutation_targets: Option<Comm>,
    pub quotient_chunks_targets: Comm,
    pub random_commit: Option<Comm>,
    pub _phantom: PhantomData<F>,
}

pub struct OpenedValuesTargets<SC: StarkGenericConfig> {
    pub trace_local_targets: Vec<Target>,
    pub trace_next_targets: Vec<Target>,
    pub preprocessed_local_targets: Option<Vec<Target>>,
    pub preprocessed_next_targets: Option<Vec<Target>>,
    pub quotient_chunks_targets: Vec<Vec<Target>>,
    pub random_targets: Option<Vec<Target>>,
    pub _phantom: PhantomData<SC>,
}

impl<SC> Clone for OpenedValuesTargets<SC>
where
    SC: StarkGenericConfig,
{
    fn clone(&self) -> Self {
        Self {
            trace_local_targets: self.trace_local_targets.clone(),
            trace_next_targets: self.trace_next_targets.clone(),
            preprocessed_local_targets: self.preprocessed_local_targets.clone(),
            preprocessed_next_targets: self.preprocessed_next_targets.clone(),
            quotient_chunks_targets: self.quotient_chunks_targets.clone(),
            random_targets: self.random_targets.clone(),
            _phantom: PhantomData,
        }
    }
}

#[derive(Clone)]
pub struct OpenedValuesTargetsWithLookups<SC: StarkGenericConfig> {
    pub opened_values_no_lookups: OpenedValuesTargets<SC>,
    pub permutation_local_targets: Vec<Target>,
    pub permutation_next_targets: Vec<Target>,
}

#[derive(Clone)]
pub(crate) struct BatchOpenedValuesTargets<SC: StarkGenericConfig> {
    pub instances: Vec<OpenedValuesTargetsWithLookups<SC>>,
}

pub(crate) struct GlobalPreprocessedTargets<Comm> {
    pub commitment: Comm,
    pub instances: PreprocessedInstanceMetas,
    pub matrix_to_instance: Vec<usize>,
}

pub(crate) struct PreprocessedInstanceMetas {
    pub instances: Vec<Option<PreprocessedInstanceMeta>>,
}

pub struct CommonDataTargets<SC: StarkGenericConfig, Comm> {
    pub(crate) preprocessed: Option<GlobalPreprocessedTargets<Comm>>,
    pub lookups: Vec<Vec<Lookup<Val<SC>>>>,
}

impl<SC: StarkGenericConfig, Comm> CommonDataTargets<SC, Comm> {
    pub fn preprocessed_commitment(&self) -> Option<&Comm> {
        self.preprocessed.as_ref().map(|group| &group.commitment)
    }
}

impl<SC: StarkGenericConfig, Comm> Recursive<SC::Challenge> for CommonDataTargets<SC, Comm>
where
    Comm: Recursive<
            SC::Challenge,
            Input = <SC::Pcs as Pcs<SC::Challenge, SC::Challenger>>::Commitment,
        >,
{
    type Input = CommonData<SC>;

    fn new(circuit: &mut CircuitBuilder<SC::Challenge>, input: &Self::Input) -> Self {
        let preprocessed = input
            .preprocessed
            .as_ref()
            .map(|prep| GlobalPreprocessedTargets {
                commitment: Comm::new(circuit, &prep.commitment),
                instances: PreprocessedInstanceMetas {
                    instances: prep.instances.clone(),
                },
                matrix_to_instance: prep.matrix_to_instance.clone(),
            });

        Self {
            preprocessed,
            lookups: input.lookups.iter().map(|ls| ls.to_vec()).collect(),
        }
    }

    fn get_values(input: &Self::Input) -> Vec<SC::Challenge> {
        let mut values = vec![];
        if let Some(prep) = &input.preprocessed {
            values.extend(Comm::get_values(&prep.commitment));
        }

        values
    }
}

impl<SC: StarkGenericConfig> OpenedValuesTargetsWithLookups<SC> {
    pub fn observe<BF, EF>(
        &self,
        circuit: &mut CircuitBuilder<EF>,
        challenger: &mut impl RecursiveChallenger<BF, EF>,
    ) where
        BF: PrimeField64,
        EF: ExtensionField<BF>,
    {
        if let Some(random_vals) = &self.opened_values_no_lookups.random_targets {
            challenger.observe_ext_slice(circuit, random_vals);
        }

        challenger.observe_ext_slice(circuit, &self.opened_values_no_lookups.trace_local_targets);
        challenger.observe_ext_slice(circuit, &self.opened_values_no_lookups.trace_next_targets);

        for chunk_values in &self.opened_values_no_lookups.quotient_chunks_targets {
            challenger.observe_ext_slice(circuit, chunk_values);
        }

        if let Some(preprocessed_local_targets) =
            &self.opened_values_no_lookups.preprocessed_local_targets
        {
            challenger.observe_ext_slice(circuit, preprocessed_local_targets);
        }
        if let Some(preprocessed_next_targets) =
            &self.opened_values_no_lookups.preprocessed_next_targets
        {
            challenger.observe_ext_slice(circuit, preprocessed_next_targets);
        }
        if !self.permutation_local_targets.is_empty() {
            challenger.observe_ext_slice(circuit, &self.permutation_local_targets);
        }
        if !self.permutation_next_targets.is_empty() {
            challenger.observe_ext_slice(circuit, &self.permutation_next_targets);
        }
    }
}

impl<
    SC: StarkGenericConfig,
    Comm: Recursive<SC::Challenge, Input = <SC::Pcs as Pcs<SC::Challenge, SC::Challenger>>::Commitment>,
    OpeningProof: Recursive<SC::Challenge, Input = <SC::Pcs as Pcs<SC::Challenge, SC::Challenger>>::Proof>,
> Recursive<SC::Challenge> for ProofTargets<SC, Comm, OpeningProof>
{
    type Input = Proof<SC>;

    fn new(circuit: &mut CircuitBuilder<SC::Challenge>, input: &Self::Input) -> Self {
        let commitments_no_lookups = BatchCommitments {
            main: input.commitments.trace.clone(),
            permutation: None,
            quotient_chunks: input.commitments.quotient_chunks.clone(),
            random: input.commitments.random.clone(),
        };
        let commitments_targets = CommitmentTargets::new(circuit, &commitments_no_lookups);
        let opened_values_targets = OpenedValuesTargets::new(circuit, &input.opened_values);
        let opening_proof = OpeningProof::new(circuit, &input.opening_proof);

        Self {
            commitments_targets,
            opened_values_targets,
            opening_proof,
            degree_bits: input.degree_bits,
        }
    }

    fn get_values(input: &Self::Input) -> Vec<SC::Challenge> {
        let Proof {
            commitments,
            opened_values,
            opening_proof,
            degree_bits: _,
            ood_pow_witness: _,
        } = input;

        let commitments_no_lookups = BatchCommitments {
            main: commitments.trace.clone(),
            permutation: None,
            quotient_chunks: commitments.quotient_chunks.clone(),
            random: commitments.random.clone(),
        };
        CommitmentTargets::<SC::Challenge, Comm>::get_values(&commitments_no_lookups)
            .into_iter()
            .chain(OpenedValuesTargets::<SC>::get_values(opened_values))
            .chain(OpeningProof::get_values(opening_proof))
            .collect()
    }

    fn get_private_values(input: &Self::Input) -> Vec<SC::Challenge> {
        let mut values = vec![];
        values.extend(OpenedValuesTargets::<SC>::get_private_values(
            &input.opened_values,
        ));
        values.extend(OpeningProof::get_private_values(&input.opening_proof));
        values
    }
}

impl<
    SC: StarkGenericConfig,
    Comm: Recursive<SC::Challenge, Input = <SC::Pcs as Pcs<SC::Challenge, SC::Challenger>>::Commitment>,
    OpeningProof: Recursive<SC::Challenge, Input = <SC::Pcs as Pcs<SC::Challenge, SC::Challenger>>::Proof>,
> Recursive<SC::Challenge> for BatchProofTargets<SC, Comm, OpeningProof>
{
    type Input = BatchProof<SC>;

    fn new(circuit: &mut CircuitBuilder<SC::Challenge>, input: &Self::Input) -> Self {
        let num_instances = input.opened_values.instances.len();
        let mut aggregated_trace_local = Vec::with_capacity(num_instances);
        let mut aggregated_trace_next = Vec::with_capacity(num_instances);
        let mut aggregated_permutation_local = Vec::with_capacity(num_instances);
        let mut aggregated_permutation_next = Vec::with_capacity(num_instances);
        let mut aggregated_preprocessed_local = Vec::with_capacity(num_instances);
        let mut aggregated_preprocessed_next = Vec::with_capacity(num_instances);
        let mut aggregated_quotient_chunks = Vec::with_capacity(num_instances);
        let mut aggregated_random = Vec::with_capacity(num_instances);

        let commitments_targets = CommitmentTargets::new(circuit, &input.commitments);
        let opened_values_targets = BatchOpenedValuesTargets::new(circuit, &input.opened_values);
        let opening_proof = OpeningProof::new(circuit, &input.opening_proof);
        let lookup_terminals = input
            .lookup_terminals
            .iter()
            .map(|terminal| {
                terminal
                    .as_ref()
                    .map(|_| circuit.alloc_public_input("lookup terminal"))
            })
            .collect::<Vec<_>>();

        for instance in &opened_values_targets.instances {
            aggregated_trace_local.extend(&instance.opened_values_no_lookups.trace_local_targets);
            aggregated_trace_next.extend(&instance.opened_values_no_lookups.trace_next_targets);
            if let Some(prep_local) = &instance.opened_values_no_lookups.preprocessed_local_targets
            {
                aggregated_preprocessed_local.extend(prep_local);
            }
            if let Some(prep_next) = &instance.opened_values_no_lookups.preprocessed_next_targets {
                aggregated_preprocessed_next.extend(prep_next);
            }
            aggregated_permutation_local.extend(&instance.permutation_local_targets);
            aggregated_permutation_next.extend(&instance.permutation_next_targets);
            for chunk in &instance.opened_values_no_lookups.quotient_chunks_targets {
                aggregated_quotient_chunks.push(chunk.clone());
            }
            if let Some(random) = &instance.opened_values_no_lookups.random_targets {
                aggregated_random.extend(random);
            }
        }

        let flattened_opened_values_targets = OpenedValuesTargetsWithLookups {
            opened_values_no_lookups: OpenedValuesTargets {
                trace_local_targets: aggregated_trace_local,
                trace_next_targets: aggregated_trace_next,
                preprocessed_local_targets: if aggregated_preprocessed_local.is_empty() {
                    None
                } else {
                    Some(aggregated_preprocessed_local)
                },
                preprocessed_next_targets: if aggregated_preprocessed_next.is_empty() {
                    None
                } else {
                    Some(aggregated_preprocessed_next)
                },
                quotient_chunks_targets: aggregated_quotient_chunks,
                random_targets: if aggregated_random.is_empty() {
                    None
                } else {
                    Some(aggregated_random)
                },
                _phantom: PhantomData,
            },
            permutation_local_targets: aggregated_permutation_local,
            permutation_next_targets: aggregated_permutation_next,
        };

        Self {
            commitments_targets,
            opened_values_targets,
            flattened_opened_values_targets,
            opening_proof,
            lookup_terminals,
            degree_bits: input.degree_bits.clone(),
        }
    }

    fn get_values(input: &Self::Input) -> Vec<SC::Challenge> {
        let BatchProof {
            commitments,
            opened_values: _,
            opening_proof,
            lookup_terminals,
            degree_bits: _,
            lookup_pow_witness: _,
            ood_pow_witness: _,
        } = input;

        CommitmentTargets::<SC::Challenge, Comm>::get_values(commitments)
            .into_iter()
            .chain(OpeningProof::get_values(opening_proof))
            .chain(lookup_terminals.iter().flatten().map(|t| t.0))
            .collect()
    }

    fn get_private_values(input: &Self::Input) -> Vec<SC::Challenge> {
        let mut values = vec![];
        values.extend(BatchOpenedValuesTargets::<SC>::get_private_values(
            &input.opened_values,
        ));
        values.extend(OpeningProof::get_private_values(&input.opening_proof));
        values
    }
}

impl<F: Field, Comm> Recursive<F> for CommitmentTargets<F, Comm>
where
    Comm: Recursive<F>,
{
    type Input = BatchCommitments<Comm::Input>;

    fn new(circuit: &mut CircuitBuilder<F>, input: &Self::Input) -> Self {
        let trace_targets = Comm::new(circuit, &input.main);
        let permutation_targets = input
            .permutation
            .as_ref()
            .map(|perm| Comm::new(circuit, perm));
        let quotient_chunks_targets = Comm::new(circuit, &input.quotient_chunks);

        Self {
            trace_targets,
            permutation_targets,
            quotient_chunks_targets,
            random_commit: input.random.as_ref().map(|rand| Comm::new(circuit, rand)),
            _phantom: PhantomData,
        }
    }

    fn get_values(input: &Self::Input) -> Vec<F> {
        let BatchCommitments {
            main,
            permutation,
            quotient_chunks,
            random,
        } = input;

        let mut values = vec![];
        values.extend(Comm::get_values(main));
        if let Some(permutation) = permutation {
            values.extend(Comm::get_values(permutation));
        }
        values.extend(Comm::get_values(quotient_chunks));

        if let Some(random) = random {
            values.extend(Comm::get_values(random));
        }

        values
    }
}

impl<SC: StarkGenericConfig> Recursive<SC::Challenge> for OpenedValuesTargets<SC> {
    type Input = OpenedValues<SC::Challenge>;

    fn new(circuit: &mut CircuitBuilder<SC::Challenge>, input: &Self::Input) -> Self {
        let trace_local_len = input.trace_local.len();
        let trace_local_targets =
            circuit.alloc_private_inputs(trace_local_len, "trace local values");

        let trace_next_len = input.trace_next.as_ref().map_or(0, |v| v.len());
        let trace_next_targets = circuit.alloc_private_inputs(trace_next_len, "trace next values");

        let preprocessed_local_targets = input
            .preprocessed_local()
            .map(|prep| circuit.alloc_private_inputs(prep.len(), "local preprocessed values"));
        let preprocessed_next_targets = input
            .preprocessed_next()
            .map(|prep| circuit.alloc_private_inputs(prep.len(), "local preprocessed values"));

        let quotient_chunks_len = input.quotient_chunks.len();
        let mut quotient_chunks_targets = Vec::with_capacity(quotient_chunks_len);
        for quotient_chunk in input.quotient_chunks.iter() {
            let quotient_chunks_cols_len = quotient_chunk.len();
            let quotient_col =
                circuit.alloc_private_inputs(quotient_chunks_cols_len, "quotient chunk columns");
            quotient_chunks_targets.push(quotient_col);
        }

        let random_targets = input
            .random
            .as_ref()
            .map(|random| circuit.alloc_private_inputs(random.len(), "random values (ZK mode)"));

        Self {
            trace_local_targets,
            trace_next_targets,
            preprocessed_local_targets,
            preprocessed_next_targets,
            quotient_chunks_targets,
            random_targets,
            _phantom: PhantomData,
        }
    }

    fn get_values(_input: &Self::Input) -> Vec<SC::Challenge> {
        vec![]
    }

    fn get_private_values(input: &Self::Input) -> Vec<SC::Challenge> {
        let OpenedValues {
            trace_local,
            trace_next,
            preprocessed,
            quotient_chunks,
            random,
        } = input;
        let preprocessed_local = preprocessed.as_ref().map(|p| p.local.as_slice());
        let preprocessed_next = preprocessed.as_ref().and_then(|p| p.next.as_deref());

        let mut values = vec![];
        values.extend(trace_local);
        if let Some(trace_next) = trace_next {
            values.extend(trace_next);
        }
        if let Some(preprocessed_local) = preprocessed_local {
            values.extend(preprocessed_local);
        }
        if let Some(preprocessed_next) = preprocessed_next {
            values.extend(preprocessed_next);
        }
        for chunk in quotient_chunks {
            values.extend(chunk);
        }
        if let Some(random) = random {
            values.extend(random);
        }

        values
    }
}

impl<SC: StarkGenericConfig> Recursive<SC::Challenge> for OpenedValuesTargetsWithLookups<SC> {
    type Input = OpenedValuesWithLookups<SC::Challenge>;

    fn new(circuit: &mut CircuitBuilder<SC::Challenge>, input: &Self::Input) -> Self {
        let opened_values_no_lookups = OpenedValuesTargets::new(circuit, &input.base_opened_values);

        let permutation_local_targets = circuit.alloc_private_inputs(
            input.permutation_local.len(),
            "permutation local opened values",
        );
        let permutation_next_targets = circuit.alloc_private_inputs(
            input.permutation_next.len(),
            "permutation next opened values",
        );

        Self {
            opened_values_no_lookups,
            permutation_local_targets,
            permutation_next_targets,
        }
    }

    fn get_values(_input: &Self::Input) -> Vec<SC::Challenge> {
        vec![]
    }

    fn get_private_values(input: &Self::Input) -> Vec<SC::Challenge> {
        let OpenedValuesWithLookups {
            base_opened_values,
            permutation_local,
            permutation_next,
        } = input;

        let mut values = vec![];
        values.extend(OpenedValuesTargets::<SC>::get_private_values(
            base_opened_values,
        ));
        values.extend(permutation_local);
        values.extend(permutation_next);
        values
    }
}

impl<SC: StarkGenericConfig> Recursive<SC::Challenge> for BatchOpenedValuesTargets<SC> {
    type Input = BatchOpenedValues<SC::Challenge>;

    fn new(circuit: &mut CircuitBuilder<SC::Challenge>, input: &Self::Input) -> Self {
        let instances = input
            .instances
            .iter()
            .map(|instance| OpenedValuesTargetsWithLookups::new(circuit, instance))
            .collect();

        Self { instances }
    }

    fn get_values(_input: &Self::Input) -> Vec<SC::Challenge> {
        vec![]
    }

    fn get_private_values(input: &Self::Input) -> Vec<SC::Challenge> {
        let mut values = vec![];
        for instance in &input.instances {
            values.extend(OpenedValuesTargetsWithLookups::<SC>::get_private_values(
                instance,
            ));
        }
        values
    }
}
