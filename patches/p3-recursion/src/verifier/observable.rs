use alloc::vec;
use alloc::vec::Vec;

use crate::Target;

pub trait ObservableCommitment {
    fn to_observation_targets(&self) -> Vec<Target>;
}

impl ObservableCommitment for Target {
    fn to_observation_targets(&self) -> Vec<Target> {
        vec![*self]
    }
}
