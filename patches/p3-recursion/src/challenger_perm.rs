use p3_circuit::ops::{Poseidon1Config, Poseidon2Config};

pub trait ChallengerPermConfig: Send + Sync {
    fn extension_degree(&self) -> usize;

    fn as_poseidon2(&self) -> Option<&Poseidon2Config> {
        None
    }

    fn as_poseidon1(&self) -> Option<&Poseidon1Config> {
        None
    }
}

impl ChallengerPermConfig for Poseidon2Config {
    fn extension_degree(&self) -> usize {
        Self::d(*self)
    }

    fn as_poseidon2(&self) -> Option<&Poseidon2Config> {
        Some(self)
    }
}

impl ChallengerPermConfig for Poseidon1Config {
    fn extension_degree(&self) -> usize {
        Self::d(*self)
    }

    fn as_poseidon1(&self) -> Option<&Poseidon1Config> {
        Some(self)
    }
}
