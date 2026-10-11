use alloc::borrow::Cow;
use alloc::vec::Vec;

use hashbrown::HashMap;
use p3_air::symbolic::AirLayout;
use p3_air::{Air, SymbolicExpressionExt};
use p3_batch_stark::symbolic::{get_log_num_quotient_chunks, get_symbolic_constraints};
use p3_circuit::CircuitBuilder;
use p3_circuit::symbolic::{ColumnsTargets, SymbolicCompiler};
use p3_field::{Algebra, ExtensionField, Field};
use p3_lookup::symbolic::InteractionSymbolicBuilder;
use p3_lookup::{Lookup, LookupProtocol};
use p3_uni_stark::SymbolicExpression;

use crate::Target;
use crate::types::RecursiveLagrangeSelectors;

pub struct LookupMetadata<'a, F: Field> {
    pub contexts: &'a [Lookup<F>],
}
pub trait RecursiveAir<F: Field, EF: ExtensionField<F>, LG: LookupProtocol> {
    fn expected_public_input_count(&self) -> Option<usize> {
        None
    }

    fn width(&self) -> usize;

    fn num_periodic_columns(&self) -> usize;

    fn periodic_columns(&self) -> Cow<'_, [Vec<F>]>;

    fn eval_folded_circuit(
        &self,
        builder: &mut CircuitBuilder<EF>,
        sels: &RecursiveLagrangeSelectors,
        alpha: &Target,
        lookup_metadata: &LookupMetadata<'_, F>,
        columns: ColumnsTargets<'_>,
        lookup_gadget: &LG,
    ) -> Target;

    fn get_log_num_quotient_chunks(
        &self,
        preprocessed_width: usize,
        trace_len: usize,
        contexts: &[Lookup<F>],
        is_zk: usize,
        lookup_gadget: &LG,
    ) -> usize;

    fn declares_interactions(&self, preprocessed_width: usize) -> bool;

    fn opens_trace_next(&self) -> bool;

    fn opens_preprocessed_next(&self) -> bool {
        true
    }
}

impl<F: Field, EF: ExtensionField<F>, A, LG: LookupProtocol> RecursiveAir<F, EF, LG> for A
where
    A: Air<InteractionSymbolicBuilder<F, EF>>,
    SymbolicExpressionExt<F, EF>: Algebra<SymbolicExpression<F>> + Algebra<EF>,
{
    fn expected_public_input_count(&self) -> Option<usize> {
        Some(p3_air::BaseAir::<F>::num_public_values(self))
    }

    fn width(&self) -> usize {
        Self::width(self)
    }

    fn num_periodic_columns(&self) -> usize {
        p3_air::BaseAir::<F>::num_periodic_columns(self)
    }

    fn periodic_columns(&self) -> Cow<'_, [Vec<F>]> {
        p3_air::BaseAir::<F>::periodic_columns(self)
    }

    fn eval_folded_circuit(
        &self,
        builder: &mut CircuitBuilder<EF>,
        sels: &RecursiveLagrangeSelectors,
        alpha: &Target,
        lookup_metadata: &LookupMetadata<'_, F>,
        columns: ColumnsTargets<'_>,
        lookup_gadget: &LG,
    ) -> Target {
        builder.push_scope("eval_folded_circuit");

        let LookupMetadata { contexts } = lookup_metadata;

        let num_preprocessed = columns.local_prep_values.len();
        debug_assert_eq!(
            columns.periodic_values.len(),
            p3_air::BaseAir::<F>::num_periodic_columns(self),
            "periodic_values targets must match the AIR's declared periodic column count"
        );
        let num_permutation_values = usize::from(!contexts.is_empty());
        let layout = AirLayout {
            preprocessed_width: num_preprocessed,
            main_width: self.width(),
            num_public_values: self.num_public_values(),
            num_periodic_columns: p3_air::BaseAir::<F>::num_periodic_columns(self),
            num_permutation_values,
            ..Default::default()
        };
        let (base_symbolic_constraints, extension_symbolic_constraints) =
            get_symbolic_constraints(self, layout, contexts, lookup_gadget);

        let compiler = SymbolicCompiler::new(sels.row_selectors, &columns);
        let mut acc = builder.define_const(EF::ZERO);
        let mut base_cache = HashMap::new();
        for s_c in &base_symbolic_constraints {
            let constraints = compiler.compile_base(s_c, builder, &mut base_cache);
            acc = builder.mul_add(acc, *alpha, constraints);
        }

        let mut ext_cache = HashMap::new();
        for s_c in &extension_symbolic_constraints {
            let constraints = compiler.compile_ext(s_c, builder, &mut base_cache, &mut ext_cache);
            acc = builder.mul_add(acc, *alpha, constraints);
        }

        builder.pop_scope();
        acc
    }

    fn get_log_num_quotient_chunks(
        &self,
        preprocessed_width: usize,
        trace_len: usize,
        contexts: &[Lookup<F>],
        is_zk: usize,
        lookup_gadget: &LG,
    ) -> usize
    where
        F: Field,
        EF: ExtensionField<F>,
        SymbolicExpressionExt<F, EF>: Algebra<SymbolicExpression<F>>,
        LG: LookupProtocol,
    {
        let layout = AirLayout {
            preprocessed_width,
            main_width: self.width(),
            num_public_values: self.num_public_values(),
            num_periodic_columns: p3_air::BaseAir::<F>::num_periodic_columns(self),
            ..Default::default()
        };
        get_log_num_quotient_chunks(self, layout, trace_len, contexts, is_zk, lookup_gadget)
    }

    fn declares_interactions(&self, preprocessed_width: usize) -> bool {
        let layout = AirLayout {
            preprocessed_width,
            main_width: self.width(),
            num_public_values: self.num_public_values(),
            ..Default::default()
        };
        let mut builder = InteractionSymbolicBuilder::<F, EF>::new(layout);
        self.eval(&mut builder);
        !builder.global_interactions().is_empty() || !builder.local_interactions().is_empty()
    }

    fn opens_trace_next(&self) -> bool {
        !p3_air::BaseAir::<F>::main_next_row_columns(self).is_empty()
    }

    fn opens_preprocessed_next(&self) -> bool {
        !p3_air::BaseAir::<F>::preprocessed_next_row_columns(self).is_empty()
    }
}
