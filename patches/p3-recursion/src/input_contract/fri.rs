use alloc::vec::Vec;

#[derive(Clone, PartialEq, Eq)]
pub struct MerkleCapShape {
    pub(crate) roots: usize,
}

#[derive(Clone, PartialEq, Eq)]
pub struct FriShape<C, I, M, W> {
    pub(crate) commit_phase_commits: Vec<C>,
    pub(crate) commit_pow_witnesses: Vec<W>,
    pub(crate) input_openings: I,
    pub(crate) commit_phase_openings: Vec<FriCommitStepShape<M>>,
    pub(crate) final_poly: usize,
    pub(crate) query_pow_witness: W,
}

#[derive(Clone, PartialEq, Eq)]
pub struct FriCommitStepShape<M> {
    pub(crate) log_arity: u8,
    pub(crate) sibling_values: Vec<usize>,
    pub(crate) opening_advice: M,
}

#[derive(Clone, PartialEq, Eq)]
pub struct FriInputBatchShape<M> {
    pub(crate) opened_values: Vec<Vec<usize>>,
    pub(crate) opening_advice: M,
}

#[derive(Clone, PartialEq, Eq)]
pub struct HidingOpeningAdviceShape {
    pub(crate) salts: Vec<Vec<usize>>,
}

#[derive(Clone, PartialEq, Eq)]
pub struct HidingFriShape<P> {
    pub(crate) random_openings: Vec<Vec<Vec<usize>>>,
    pub(crate) inner: P,
}
