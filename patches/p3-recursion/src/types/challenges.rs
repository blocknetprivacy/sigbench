use alloc::vec;
use alloc::vec::Vec;

use p3_circuit::CircuitBuilder;
use p3_field::{ExtensionField, PrimeCharacteristicRing, PrimeField64};
use p3_uni_stark::{StarkGenericConfig, Val};

use crate::Target;
use crate::traits::{Recursive, RecursiveChallenger};
use crate::types::ProofTargets;
use crate::verifier::ObservableCommitment;

#[derive(Debug, Clone)]
pub struct StarkChallenges {
    pub alpha: Target,
    pub zeta: Target,
    pub zeta_next: Target,
}

pub(crate) struct StarkChallengeParams<'a, SC: StarkGenericConfig, Comm> {
    pub transcript_seed: Vec<Val<SC>>,
    pub preprocessed_width: usize,
    pub preprocessed_commit: &'a Option<Comm>,
    pub trace_domain_generator: SC::Challenge,
}

impl StarkChallenges {
    pub(crate) fn allocate<SC, Comm, OpeningProof>(
        circuit: &mut CircuitBuilder<SC::Challenge>,
        challenger: &mut impl RecursiveChallenger<Val<SC>, SC::Challenge>,
        proof_targets: &ProofTargets<SC, Comm, OpeningProof>,
        public_values: &[Target],
        params: &StarkChallengeParams<'_, SC, Comm>,
    ) -> Self
    where
        SC: StarkGenericConfig,
        Val<SC>: PrimeField64,
        SC::Challenge: ExtensionField<Val<SC>> + PrimeCharacteristicRing,
        Comm: Recursive<SC::Challenge> + ObservableCommitment,
        OpeningProof: Recursive<SC::Challenge>,
    {
        let trace_comm_targets = proof_targets
            .commitments_targets
            .trace_targets
            .to_observation_targets();
        let quotient_comm_targets = proof_targets
            .commitments_targets
            .quotient_chunks_targets
            .to_observation_targets();
        let random_comm_targets = proof_targets
            .commitments_targets
            .random_commit
            .as_ref()
            .map(|c| c.to_observation_targets());
        let preprocessed_comm_targets = params
            .preprocessed_commit
            .as_ref()
            .map(|c| c.to_observation_targets());

        challenger.observe_seed(circuit, &params.transcript_seed);

        challenger.observe_slice(circuit, &trace_comm_targets);

        if params.preprocessed_width > 0
            && let Some(prep_comm) = &preprocessed_comm_targets
        {
            challenger.observe_slice(circuit, prep_comm);
        }

        challenger.observe_slice(circuit, public_values);

        let alpha = challenger.sample_ext(circuit);

        challenger.observe_slice(circuit, &quotient_comm_targets);

        if let Some(random_comm) = random_comm_targets {
            challenger.observe_slice(circuit, &random_comm);
        }

        let zeta = challenger.sample_ext(circuit);

        let generator_const = circuit.define_const(params.trace_domain_generator);
        let zeta_next = circuit.mul(zeta, generator_const);

        Self {
            alpha,
            zeta,
            zeta_next,
        }
    }

    pub fn to_vec(&self) -> Vec<Target> {
        vec![self.alpha, self.zeta, self.zeta_next]
    }

    pub const fn alpha(&self) -> Target {
        self.alpha
    }

    pub const fn zeta(&self) -> Target {
        self.zeta
    }

    pub const fn zeta_next(&self) -> Target {
        self.zeta_next
    }
}
