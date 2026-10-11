use alloc::vec::Vec;

use p3_sumcheck::layout::LayoutStrategy;
use p3_sumcheck::strategy::VariableOrder;
use p3_util::reverse_bits_len;
use p3_whir::parameters::FoldingFactor;
use thiserror::Error;

pub(crate) fn initial_layout_folding(strategy: &FoldingFactor) -> Option<usize> {
    match strategy {
        FoldingFactor::Constant(first) if *first > 0 => Some(*first),
        FoldingFactor::ConstantFromSecondRound(first, rest) if *first > 0 && *rest > 0 => {
            Some(*first)
        }
        FoldingFactor::PerRound(factors) if factors.iter().all(|&factor| factor > 0) => {
            factors.first().copied()
        }
        _ => None,
    }
}

pub(crate) const fn canonical_layout_strategy(order: VariableOrder) -> LayoutStrategy {
    match order {
        VariableOrder::Prefix => LayoutStrategy::new(true, VariableOrder::Prefix),
        VariableOrder::Suffix => LayoutStrategy::new(false, VariableOrder::Suffix),
    }
}

#[derive(Clone, Copy, Debug, Error, PartialEq, Eq)]
pub enum StackedArityError {
    #[error("stacked table arity {arity} cannot be shifted into a usize")]
    ShiftOverflow { arity: usize },
    #[error("stacked table width {width} times row size 2^{arity} overflows")]
    ProductOverflow { arity: usize, width: usize },
    #[error("stacked table sizes overflow while being summed")]
    SumOverflow,
    #[error("stacked polynomial size {total} has no representable next power of two")]
    RoundedDomainOverflow { total: usize },
    #[error("table arity {arity} exceeds stacked arity {stacked_num_variables}")]
    ArityExceedsStack {
        arity: usize,
        stacked_num_variables: usize,
    },
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PaddedArity(usize);

impl PaddedArity {
    pub const fn get(self) -> usize {
        self.0
    }
}

pub const fn padded_arity(log_height: usize, folding: usize) -> PaddedArity {
    PaddedArity(if log_height > folding {
        log_height
    } else {
        folding
    })
}

pub fn checked_stacked_num_variables<I>(shapes: I) -> Result<usize, StackedArityError>
where
    I: IntoIterator<Item = (PaddedArity, usize)>,
{
    let mut total = 0usize;
    for (arity, width) in shapes {
        if width == 0 {
            continue;
        }
        let arity = arity.get();
        let shift = u32::try_from(arity).map_err(|_| StackedArityError::ShiftOverflow { arity })?;
        let row_size = 1usize
            .checked_shl(shift)
            .ok_or(StackedArityError::ShiftOverflow { arity })?;
        let contribution = width
            .checked_mul(row_size)
            .ok_or(StackedArityError::ProductOverflow { arity, width })?;
        total = total
            .checked_add(contribution)
            .ok_or(StackedArityError::SumOverflow)?;
    }
    if total == 0 {
        return Ok(0);
    }
    let rounded = total
        .checked_next_power_of_two()
        .ok_or(StackedArityError::RoundedDomainOverflow { total })?;
    Ok(rounded.trailing_zeros() as usize)
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct StackedSelector {
    pub num_variables: usize,
    pub index: usize,
}

impl StackedSelector {
    pub const fn new(num_variables: usize, index: usize) -> Self {
        assert!(
            num_variables < usize::BITS as usize && index < (1usize << num_variables),
            "selector index out of range for its bit-width"
        );
        Self {
            num_variables,
            index,
        }
    }

    pub fn lift_prefix<F: Clone>(&self, local: &[F], zero: F, one: F) -> Vec<F> {
        self.lift_with_strategy(
            local,
            zero,
            one,
            canonical_layout_strategy(VariableOrder::Prefix),
        )
    }

    pub(crate) fn lift_with_strategy<F: Clone>(
        &self,
        local: &[F],
        zero: F,
        one: F,
        strategy: LayoutStrategy,
    ) -> Vec<F> {
        let mut out = Vec::with_capacity(local.len() + self.num_variables);
        if strategy.reverse_selectors {
            out.extend_from_slice(local);
        }
        for i in 0..self.num_variables {
            let bit = (self.index >> (self.num_variables - 1 - i)) & 1 == 1;
            out.push(if bit { one.clone() } else { zero.clone() });
        }
        if !strategy.reverse_selectors {
            out.extend_from_slice(local);
        }
        out
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct StackedPlacement {
    pub table_idx: usize,
    pub selectors: Vec<StackedSelector>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct StackedPlan {
    pub num_variables: usize,
    pub placements: Vec<StackedPlacement>,
}

impl StackedPlan {
    pub fn new(shapes: &[(PaddedArity, usize)]) -> Self {
        Self::try_new(shapes).expect("stacked geometry must fit in usize")
    }

    pub fn try_new(shapes: &[(PaddedArity, usize)]) -> Result<Self, StackedArityError> {
        Self::try_new_with_strategy(shapes, canonical_layout_strategy(VariableOrder::Prefix))
    }

    pub(crate) fn new_with_strategy(
        shapes: &[(PaddedArity, usize)],
        strategy: LayoutStrategy,
    ) -> Self {
        Self::try_new_with_strategy(shapes, strategy).expect("stacked geometry must fit in usize")
    }

    pub(crate) fn try_new_with_strategy(
        shapes: &[(PaddedArity, usize)],
        strategy: LayoutStrategy,
    ) -> Result<Self, StackedArityError> {
        let num_variables = checked_stacked_num_variables(shapes.iter().copied())?;
        let mut order: Vec<usize> = (0..shapes.len()).collect();
        order.sort_by_key(|&i| shapes[i].0.get());

        let mut offset = 0usize;
        let mut placements = Vec::with_capacity(shapes.len());
        for &table_idx in order.iter().rev() {
            let (arity, width) = shapes[table_idx];
            let arity = arity.get();
            if width == 0 {
                placements.push(StackedPlacement {
                    table_idx,
                    selectors: Vec::new(),
                });
                continue;
            }
            let shift =
                u32::try_from(arity).map_err(|_| StackedArityError::ShiftOverflow { arity })?;
            let slot_size = 1usize
                .checked_shl(shift)
                .ok_or(StackedArityError::ShiftOverflow { arity })?;
            let selector_variables =
                num_variables
                    .checked_sub(arity)
                    .ok_or(StackedArityError::ArityExceedsStack {
                        arity,
                        stacked_num_variables: num_variables,
                    })?;
            let selectors = (0..width)
                .map(|_| {
                    let raw_index = offset >> arity;
                    let index = if strategy.reverse_selectors {
                        reverse_bits_len(raw_index, selector_variables)
                    } else {
                        raw_index
                    };
                    let selector = StackedSelector::new(selector_variables, index);
                    offset += slot_size;
                    selector
                })
                .collect();
            placements.push(StackedPlacement {
                table_idx,
                selectors,
            });
        }

        Ok(Self {
            num_variables,
            placements,
        })
    }

    pub fn table_num_variables(&self, table_idx: usize) -> usize {
        let placement = self
            .placements
            .iter()
            .find(|p| p.table_idx == table_idx)
            .expect("every source table has a placement");
        let selector_variables = placement
            .selectors
            .first()
            .map(|s| s.num_variables)
            .unwrap_or(0);
        self.num_variables - selector_variables
    }
}
