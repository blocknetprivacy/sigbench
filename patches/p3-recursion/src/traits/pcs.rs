use alloc::vec::Vec;

use p3_circuit::{CircuitBuilder, CircuitBuilderError, NonPrimitiveOpId};
use p3_field::{ExtensionField, PrimeField64};
use p3_uni_stark::{StarkGenericConfig, Val};

use super::Recursive;
use crate::challenger_perm::ChallengerPermConfig;
use crate::types::{OpenedValuesTargetsWithLookups, RecursiveLagrangeSelectors};
use crate::verifier::VerificationError;
use crate::{CircuitChallenger, Target};

pub type ComsWithOpeningsTargets<Comm, Domain> =
    [(Comm, Vec<(Domain, Vec<(Target, Vec<Target>)>)>)];

pub trait RecursivePcs<
    SC: StarkGenericConfig,
    InputProof: Recursive<SC::Challenge>,
    OpeningProof: Recursive<SC::Challenge>,
    Comm: Recursive<SC::Challenge>,
    Domain,
>
{
    type VerifierParams;

    type RecursiveProof;

    const PRE_OBSERVES_OPENED_VALUES: bool = true;

    fn claims_transcript_seed(
        _params: &Self::VerifierParams,
        _claimed_evaluation_counts: Vec<Vec<Vec<usize>>>,
    ) -> Vec<Val<SC>>
    where
        Val<SC>: PrimeField64,
        SC::Challenge: ExtensionField<Val<SC>>,
    {
        Vec::new()
    }

    fn get_challenges_circuit<const WIDTH: usize, const RATE: usize, C: ChallengerPermConfig>(
        circuit: &mut CircuitBuilder<SC::Challenge>,
        challenger: &mut CircuitChallenger<WIDTH, RATE, C>,
        proof_targets: &OpeningProof,
        opened_values: &OpenedValuesTargetsWithLookups<SC>,
        params: &Self::VerifierParams,
    ) -> Result<Vec<Target>, CircuitBuilderError>;

    fn verify_circuit<const WIDTH: usize, const RATE: usize, C: ChallengerPermConfig>(
        &self,
        circuit: &mut CircuitBuilder<SC::Challenge>,
        challenges: &[Target],
        challenger: &mut CircuitChallenger<WIDTH, RATE, C>,
        commitments_with_opening_points: &ComsWithOpeningsTargets<Comm, Domain>,
        opening_proof: &OpeningProof,
        params: &Self::VerifierParams,
    ) -> Result<Vec<NonPrimitiveOpId>, VerificationError>;

    fn selectors_at_point_circuit(
        &self,
        circuit: &mut CircuitBuilder<SC::Challenge>,
        domain: &Domain,
        point: &Target,
    ) -> RecursiveLagrangeSelectors;

    fn evaluate_periodic_columns_at_point_circuit(
        &self,
        circuit: &mut CircuitBuilder<SC::Challenge>,
        domain: &Domain,
        periodic_columns: &[Vec<Val<SC>>],
        point: Target,
    ) -> Result<Vec<Target>, VerificationError>;

    fn create_disjoint_domain(&self, trace_domain: Domain, degree: usize) -> Domain;

    fn split_domains(&self, trace_domain: &Domain, degree: usize) -> Vec<Domain>;

    fn log_size(&self, trace_domain: &Domain) -> usize;

    fn size(&self, trace_domain: &Domain) -> usize {
        1 << self.log_size(trace_domain)
    }

    fn first_point(&self, trace_domain: &Domain) -> SC::Challenge;

    fn get_fri_random_opened_values(proof: &OpeningProof) -> &[Vec<Vec<Vec<Target>>>];
}
