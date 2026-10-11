mod challenges;
mod proof;
mod selectors;

pub(crate) use challenges::StarkChallengeParams;
pub use challenges::StarkChallenges;
pub use proof::{
    BatchProofTargets, CommitmentTargets, CommonDataTargets, OpenedValuesTargets,
    OpenedValuesTargetsWithLookups, ProofTargets,
};
pub use selectors::RecursiveLagrangeSelectors;

pub type Target = p3_circuit::ExprId;
