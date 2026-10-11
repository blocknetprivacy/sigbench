use alloc::format;
use alloc::vec::Vec;

use p3_batch_stark::{BatchProof, CommonData};
use p3_circuit::CircuitBuilder;
use p3_commit::Pcs;
use p3_field::{BasedVectorSpace, Field, PrimeField64};
use p3_uni_stark::{Proof, StarkGenericConfig, Val};

use crate::input_contract::stark::{
    validate_batch_native, validate_batch_proof_native, validate_uni_native,
};
use crate::traits::{CheckedRecursive, Recursive};
use crate::{BatchProofTargets, CommonDataTargets, ProofTargets, VerificationError};

#[derive(Default)]
pub struct PublicInputBuilder<F: Field> {
    inputs: Vec<F>,
}

impl<F: Field> PublicInputBuilder<F> {
    pub const fn new() -> Self {
        Self { inputs: Vec::new() }
    }

    pub fn add_proof_values(&mut self, values: impl IntoIterator<Item = F>) -> &mut Self {
        self.inputs.extend(values);
        self
    }

    pub fn add_challenge(&mut self, challenge: F) -> &mut Self {
        self.inputs.push(challenge);
        self
    }

    pub fn add_challenges(&mut self, challenges: impl IntoIterator<Item = F>) -> &mut Self {
        self.inputs.extend(challenges);
        self
    }

    pub fn add_query_index(&mut self, index: F) -> &mut Self
    where
        F: PrimeField64,
    {
        let index_usize = index.as_canonical_u64() as usize;

        for k in 0..F::bits() {
            let bit = if (index_usize >> k) & 1 == 1 {
                F::ONE
            } else {
                F::ZERO
            };
            self.inputs.push(bit);
        }

        self
    }

    pub fn add_query_index_bits(&mut self, bits: impl IntoIterator<Item = F>) -> &mut Self {
        self.inputs.extend(bits);
        self
    }

    pub const fn len(&self) -> usize {
        self.inputs.len()
    }

    pub const fn is_empty(&self) -> bool {
        self.inputs.is_empty()
    }

    pub fn build(self) -> Vec<F> {
        self.inputs
    }
}

#[derive(Clone, Debug)]
pub struct CommitmentOpening<F: Field> {
    pub commitment: F,

    pub opened_points: Vec<(F, Vec<F>)>,
}

pub struct FriVerifierInputs<F: Field> {
    pub fri_proof_values: Vec<F>,

    pub alpha: F,

    pub betas: Vec<F>,

    pub query_index_bits: Vec<Vec<F>>,

    pub commitment_openings: Vec<CommitmentOpening<F>>,
}

impl<F: Field> FriVerifierInputs<F> {
    pub fn build(self) -> Vec<F> {
        let mut builder = PublicInputBuilder::new();

        builder.add_proof_values(self.fri_proof_values);

        builder.add_challenge(self.alpha);

        builder.add_challenges(self.betas);

        for bits in self.query_index_bits {
            debug_assert!(
                bits.len() <= F::bits(),
                "query index bit length exceeds limit"
            );

            builder.add_query_index_bits(bits);
        }

        for opening in self.commitment_openings {
            builder.add_challenge(opening.commitment);

            for (z, values) in opening.opened_points {
                builder.add_challenge(z);
                builder.add_proof_values(values);
            }
        }

        builder.build()
    }
}

pub struct StarkVerifierInputs<F, EF>
where
    F: Field + PrimeField64,
    EF: Field + BasedVectorSpace<F> + From<F>,
{
    pub air_public_values: Vec<F>,

    pub proof_values: Vec<EF>,

    pub preprocessed: Vec<EF>,
}

impl<F, EF> StarkVerifierInputs<F, EF>
where
    F: Field + PrimeField64,
    EF: Field + BasedVectorSpace<F> + From<F>,
{
    pub fn build(self) -> Vec<EF> {
        let mut builder = PublicInputBuilder::new();

        builder.add_proof_values(self.air_public_values.iter().map(|&v| v.into()));

        builder.add_proof_values(self.proof_values);

        builder.add_proof_values(self.preprocessed);

        builder.build()
    }
}

pub fn construct_batch_stark_verifier_inputs<F, EF>(
    air_public_values: &[Vec<F>],
    proof_values: &[EF],
    common_data: &[EF],
) -> Vec<EF>
where
    F: Field + PrimeField64,
    EF: Field + BasedVectorSpace<F> + From<F>,
{
    let mut builder = PublicInputBuilder::new();

    for instance_pv in air_public_values {
        builder.add_proof_values(instance_pv.iter().map(|&v| v.into()));
    }

    builder.add_proof_values(proof_values.iter().copied());

    builder.add_proof_values(common_data.iter().copied());

    builder.build()
}

pub struct StarkVerifierInputsBuilder<SC, Comm, OpeningProof>
where
    SC: StarkGenericConfig,
    Comm: Recursive<
            SC::Challenge,
            Input = <SC::Pcs as Pcs<SC::Challenge, SC::Challenger>>::Commitment,
        >,
    OpeningProof:
        Recursive<SC::Challenge, Input = <SC::Pcs as Pcs<SC::Challenge, SC::Challenger>>::Proof>,
{
    pub air_public_targets: Vec<crate::Target>,

    pub proof_targets: ProofTargets<SC, Comm, OpeningProof>,

    pub preprocessed_commit: Option<Comm>,
}

type Com<SC> = <<SC as StarkGenericConfig>::Pcs as Pcs<
    <SC as StarkGenericConfig>::Challenge,
    <SC as StarkGenericConfig>::Challenger,
>>::Commitment;

impl<SC, Comm, OpeningProof> StarkVerifierInputsBuilder<SC, Comm, OpeningProof>
where
    SC: StarkGenericConfig,
    Comm: Recursive<
            SC::Challenge,
            Input = <SC::Pcs as Pcs<SC::Challenge, SC::Challenger>>::Commitment,
        >,
    OpeningProof:
        Recursive<SC::Challenge, Input = <SC::Pcs as Pcs<SC::Challenge, SC::Challenger>>::Proof>,
{
    pub fn allocate(
        circuit: &mut CircuitBuilder<SC::Challenge>,
        proof: &Proof<SC>,
        preprocessed_commit: Option<&Com<SC>>,
        num_air_public_inputs: usize,
    ) -> Self {
        let air_public_targets = (0..num_air_public_inputs)
            .map(|_| circuit.public_input())
            .collect();

        let proof_targets = ProofTargets::new(circuit, proof);

        let preprocessed_commit = preprocessed_commit
            .as_ref()
            .map(|prep_comm| Comm::new(circuit, prep_comm));

        Self {
            air_public_targets,
            proof_targets,
            preprocessed_commit,
        }
    }

    pub fn try_allocate(
        circuit: &mut CircuitBuilder<SC::Challenge>,
        proof: &Proof<SC>,
        preprocessed_commit: Option<&Com<SC>>,
        num_air_public_inputs: usize,
    ) -> Result<Self, VerificationError>
    where
        Comm: CheckedRecursive<SC::Challenge>,
        OpeningProof: CheckedRecursive<SC::Challenge>,
    {
        validate_uni_native::<SC, Comm, OpeningProof>(proof, preprocessed_commit)?;
        Ok(Self::allocate(
            circuit,
            proof,
            preprocessed_commit,
            num_air_public_inputs,
        ))
    }

    pub fn pack_public_values(
        &self,
        air_public_values: &[Val<SC>],
        proof: &Proof<SC>,
        preprocessed_commit: &Option<Com<SC>>,
    ) -> Vec<SC::Challenge>
    where
        Val<SC>: PrimeField64,
        SC::Challenge: BasedVectorSpace<Val<SC>> + From<Val<SC>>,
    {
        let proof_values = ProofTargets::<SC, Comm, OpeningProof>::get_values(proof);

        let preprocessed = preprocessed_commit
            .as_ref()
            .map_or_else(Vec::new, |prep_comm| Comm::get_values(prep_comm));

        StarkVerifierInputs {
            air_public_values: air_public_values.to_vec(),
            proof_values: proof_values.to_vec(),
            preprocessed: preprocessed.to_vec(),
        }
        .build()
    }

    pub fn try_pack_public_values(
        &self,
        air_public_values: &[Val<SC>],
        proof: &Proof<SC>,
        preprocessed_commit: &Option<Com<SC>>,
    ) -> Result<Vec<SC::Challenge>, VerificationError>
    where
        Val<SC>: PrimeField64,
        SC::Challenge: BasedVectorSpace<Val<SC>> + From<Val<SC>>,
        Comm: CheckedRecursive<SC::Challenge>,
        OpeningProof: CheckedRecursive<SC::Challenge>,
    {
        validate_uni_native::<SC, Comm, OpeningProof>(proof, preprocessed_commit.as_ref())?;
        Ok(self.pack_public_values(air_public_values, proof, preprocessed_commit))
    }

    pub fn pack_private_values(&self, proof: &Proof<SC>) -> Vec<SC::Challenge>
    where
        Val<SC>: PrimeField64,
        SC::Challenge: BasedVectorSpace<Val<SC>> + From<Val<SC>>,
    {
        ProofTargets::<SC, Comm, OpeningProof>::get_private_values(proof)
    }

    pub fn try_pack_private_values(
        &self,
        proof: &Proof<SC>,
    ) -> Result<Vec<SC::Challenge>, VerificationError>
    where
        Val<SC>: PrimeField64,
        SC::Challenge: BasedVectorSpace<Val<SC>> + From<Val<SC>>,
        Comm: CheckedRecursive<SC::Challenge>,
        OpeningProof: CheckedRecursive<SC::Challenge>,
    {
        validate_uni_native::<SC, Comm, OpeningProof>(proof, None)?;
        Ok(self.pack_private_values(proof))
    }

    pub fn pack_values(
        &self,
        air_public_values: &[Val<SC>],
        proof: &Proof<SC>,
        preprocessed_commit: &Option<Com<SC>>,
    ) -> (Vec<SC::Challenge>, Vec<SC::Challenge>)
    where
        Val<SC>: PrimeField64,
        SC::Challenge: BasedVectorSpace<Val<SC>> + From<Val<SC>>,
    {
        let public_values = self.pack_public_values(air_public_values, proof, preprocessed_commit);
        let private_values = self.pack_private_values(proof);

        (public_values, private_values)
    }

    #[allow(clippy::type_complexity)]
    pub fn try_pack_values(
        &self,
        air_public_values: &[Val<SC>],
        proof: &Proof<SC>,
        preprocessed_commit: &Option<Com<SC>>,
    ) -> Result<(Vec<SC::Challenge>, Vec<SC::Challenge>), VerificationError>
    where
        Val<SC>: PrimeField64,
        SC::Challenge: BasedVectorSpace<Val<SC>> + From<Val<SC>>,
        Comm: CheckedRecursive<SC::Challenge>,
        OpeningProof: CheckedRecursive<SC::Challenge>,
    {
        validate_uni_native::<SC, Comm, OpeningProof>(proof, preprocessed_commit.as_ref())?;
        Ok(self.pack_values(air_public_values, proof, preprocessed_commit))
    }
}

pub struct BatchStarkVerifierInputsBuilder<SC, Comm, OpeningProof>
where
    SC: StarkGenericConfig,
    Comm: Recursive<
            SC::Challenge,
            Input = <SC::Pcs as Pcs<SC::Challenge, SC::Challenger>>::Commitment,
        >,
    OpeningProof:
        Recursive<SC::Challenge, Input = <SC::Pcs as Pcs<SC::Challenge, SC::Challenger>>::Proof>,
{
    pub air_public_targets: Vec<Vec<crate::Target>>,

    pub proof_targets: BatchProofTargets<SC, Comm, OpeningProof>,
    pub common_data: CommonDataTargets<SC, Comm>,
}

impl<SC, Comm, OpeningProof> BatchStarkVerifierInputsBuilder<SC, Comm, OpeningProof>
where
    SC: StarkGenericConfig,
    Comm: Recursive<
            SC::Challenge,
            Input = <SC::Pcs as Pcs<SC::Challenge, SC::Challenger>>::Commitment,
        >,
    OpeningProof:
        Recursive<SC::Challenge, Input = <SC::Pcs as Pcs<SC::Challenge, SC::Challenger>>::Proof>,
{
    pub fn allocate(
        circuit: &mut CircuitBuilder<SC::Challenge>,
        proof: &BatchProof<SC>,
        common_data: &CommonData<SC>,
        air_public_counts: &[usize],
    ) -> Result<Self, VerificationError> {
        let instances = proof.opened_values.instances.len();
        if instances == 0 {
            return Err(VerificationError::InvalidProofShape(
                "batch-STARK allocation requires at least one instance".into(),
            ));
        }
        if air_public_counts.len() != instances {
            return Err(VerificationError::InvalidProofShape(format!(
                "public input count for instances mismatch: expected {instances}, got {}",
                air_public_counts.len()
            )));
        }
        if proof.degree_bits.len() != instances {
            return Err(VerificationError::InvalidProofShape(format!(
                "degree bit count mismatch: expected {instances}, got {}",
                proof.degree_bits.len()
            )));
        }
        if proof.lookup_terminals.len() != instances {
            return Err(VerificationError::InvalidProofShape(format!(
                "lookup terminal count mismatch: expected {instances}, got {}",
                proof.lookup_terminals.len()
            )));
        }

        let air_public_targets = air_public_counts
            .iter()
            .map(|&count| (0..count).map(|_| circuit.public_input()).collect())
            .collect();

        let proof_targets = BatchProofTargets::new(circuit, proof);

        let common_data = CommonDataTargets::<SC, Comm>::new(circuit, common_data);

        Ok(Self {
            air_public_targets,
            proof_targets,
            common_data,
        })
    }

    pub fn try_allocate(
        circuit: &mut CircuitBuilder<SC::Challenge>,
        proof: &BatchProof<SC>,
        common_data: &CommonData<SC>,
        air_public_counts: &[usize],
    ) -> Result<Self, VerificationError>
    where
        Comm: CheckedRecursive<SC::Challenge>,
        OpeningProof: CheckedRecursive<SC::Challenge>,
    {
        validate_batch_native::<SC, Comm, OpeningProof>(proof, common_data, air_public_counts)?;
        Self::allocate(circuit, proof, common_data, air_public_counts)
    }

    pub fn pack_public_values(
        &self,
        air_public_values: &[Vec<Val<SC>>],
        proof: &BatchProof<SC>,
        common: &CommonData<SC>,
    ) -> Vec<SC::Challenge>
    where
        Val<SC>: PrimeField64,
        SC::Challenge: BasedVectorSpace<Val<SC>> + From<Val<SC>>,
    {
        let common_data = CommonDataTargets::<SC, Comm>::get_values(common);
        let proof_values = BatchProofTargets::<SC, Comm, OpeningProof>::get_values(proof);

        construct_batch_stark_verifier_inputs(air_public_values, &proof_values, &common_data)
    }

    pub fn try_pack_public_values(
        &self,
        air_public_values: &[Vec<Val<SC>>],
        proof: &BatchProof<SC>,
        common: &CommonData<SC>,
    ) -> Result<Vec<SC::Challenge>, VerificationError>
    where
        Val<SC>: PrimeField64,
        SC::Challenge: BasedVectorSpace<Val<SC>> + From<Val<SC>>,
        Comm: CheckedRecursive<SC::Challenge>,
        OpeningProof: CheckedRecursive<SC::Challenge>,
    {
        let air_public_counts = air_public_values.iter().map(Vec::len).collect::<Vec<_>>();
        validate_batch_native::<SC, Comm, OpeningProof>(proof, common, &air_public_counts)?;
        Ok(self.pack_public_values(air_public_values, proof, common))
    }

    pub fn pack_private_values(&self, proof: &BatchProof<SC>) -> Vec<SC::Challenge>
    where
        Val<SC>: PrimeField64,
        SC::Challenge: BasedVectorSpace<Val<SC>> + From<Val<SC>>,
    {
        BatchProofTargets::<SC, Comm, OpeningProof>::get_private_values(proof)
    }

    pub fn try_pack_private_values(
        &self,
        proof: &BatchProof<SC>,
    ) -> Result<Vec<SC::Challenge>, VerificationError>
    where
        Val<SC>: PrimeField64,
        SC::Challenge: BasedVectorSpace<Val<SC>> + From<Val<SC>>,
        Comm: CheckedRecursive<SC::Challenge>,
        OpeningProof: CheckedRecursive<SC::Challenge>,
    {
        validate_batch_proof_native::<SC, Comm, OpeningProof>(proof)?;
        Ok(self.pack_private_values(proof))
    }

    pub fn pack_values(
        &self,
        air_public_values: &[Vec<Val<SC>>],
        proof: &BatchProof<SC>,
        common: &CommonData<SC>,
    ) -> (Vec<SC::Challenge>, Vec<SC::Challenge>)
    where
        Val<SC>: PrimeField64,
        SC::Challenge: BasedVectorSpace<Val<SC>> + From<Val<SC>>,
    {
        let public_values = self.pack_public_values(air_public_values, proof, common);
        let private_values = self.pack_private_values(proof);

        (public_values, private_values)
    }

    #[allow(clippy::type_complexity)]
    pub fn try_pack_values(
        &self,
        air_public_values: &[Vec<Val<SC>>],
        proof: &BatchProof<SC>,
        common: &CommonData<SC>,
    ) -> Result<(Vec<SC::Challenge>, Vec<SC::Challenge>), VerificationError>
    where
        Val<SC>: PrimeField64,
        SC::Challenge: BasedVectorSpace<Val<SC>> + From<Val<SC>>,
        Comm: CheckedRecursive<SC::Challenge>,
        OpeningProof: CheckedRecursive<SC::Challenge>,
    {
        let public_values = self.try_pack_public_values(air_public_values, proof, common)?;
        let private_values = self.try_pack_private_values(proof)?;
        Ok((public_values, private_values))
    }
}
