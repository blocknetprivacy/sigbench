use p3_commit::Mmcs;
use p3_field::{ExtensionField, Field};

use super::Recursive;

pub trait RecursiveMmcs<F: Field, EF: ExtensionField<F>> {
    type Input: Mmcs<F>;

    type Commitment: Recursive<EF, Input = <Self::Input as Mmcs<F>>::Commitment>;

    type Proof: Recursive<EF, Input = <Self::Input as Mmcs<F>>::Proof>;
}

pub trait RecursiveExtensionMmcs<F: Field, EF: ExtensionField<F>> {
    type Input: Mmcs<EF>;

    type Commitment: Recursive<EF, Input = <Self::Input as Mmcs<EF>>::Commitment>;

    type Proof: Recursive<EF, Input = <Self::Input as Mmcs<EF>>::Proof>;
}
