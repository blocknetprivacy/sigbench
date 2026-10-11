use p3_circuit::symbolic::RowSelectorsTargets;

use crate::Target;

#[derive(Clone, Debug)]
pub struct RecursiveLagrangeSelectors {
    pub row_selectors: RowSelectorsTargets,
    pub inv_vanishing: Target,
}
