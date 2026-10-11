use alloc::boxed::Box;
use alloc::vec::Vec;

use p3_batch_stark::{StarkGenericConfig, Val};
use p3_circuit::ops::NpoTypeId;
use p3_circuit_prover::batch_stark_prover::{Blake3CompressProver, KeccakF1600Prover, TableProver};
use p3_circuit_prover::config::StarkField;
use p3_field::Algebra;
use p3_uni_stark::{SymbolicExpression, SymbolicExpressionExt};

fn hash_table_prover<SC>(op_type: &NpoTypeId, ext_degree: usize) -> Option<Box<dyn TableProver<SC>>>
where
    SC: StarkGenericConfig + 'static + Send + Sync,
    Val<SC>: StarkField,
    SymbolicExpressionExt<Val<SC>, SC::Challenge>:
        Algebra<SymbolicExpression<Val<SC>>> + Algebra<SC::Challenge>,
{
    macro_rules! by_degree {
        ($prover:ident) => {
            match ext_degree {
                1 => Some(Box::new($prover::<1>) as Box<dyn TableProver<SC>>),
                2 => Some(Box::new($prover::<2>)),
                4 => Some(Box::new($prover::<4>)),
                5 => Some(Box::new($prover::<5>)),
                8 => Some(Box::new($prover::<8>)),
                _ => None,
            }
        };
    }
    if *op_type == NpoTypeId::keccak_f1600() {
        by_degree!(KeccakF1600Prover)
    } else if *op_type == NpoTypeId::blake3_compress() {
        by_degree!(Blake3CompressProver)
    } else {
        None
    }
}

pub fn with_hash_table_input_provers<SC>(
    ext_degree: usize,
    op_types: &[NpoTypeId],
    provers: Vec<Box<dyn TableProver<SC>>>,
) -> Vec<Box<dyn TableProver<SC>>>
where
    SC: StarkGenericConfig + 'static + Send + Sync,
    Val<SC>: StarkField,
    SymbolicExpressionExt<Val<SC>, SC::Challenge>:
        Algebra<SymbolicExpression<Val<SC>>> + Algebra<SC::Challenge>,
{
    let is_hash =
        |op: &NpoTypeId| *op == NpoTypeId::keccak_f1600() || *op == NpoTypeId::blake3_compress();
    if !op_types.iter().any(is_hash) {
        return provers;
    }

    let backend_types: Vec<NpoTypeId> = provers
        .iter()
        .map(|p| TableProver::op_type(p.as_ref()))
        .collect();
    let rest_matches = op_types
        .iter()
        .filter(|op| !is_hash(op))
        .eq(backend_types.iter());
    let mut backend = provers.into_iter();
    let mut out = Vec::with_capacity(op_types.len());
    if !rest_matches {
        out.extend(backend);
        out.extend(
            op_types
                .iter()
                .filter(|op| is_hash(op))
                .filter_map(|op| hash_table_prover::<SC>(op, ext_degree)),
        );
        return out;
    }
    for op in op_types {
        if !is_hash(op) {
            out.extend(backend.next());
            continue;
        }
        match hash_table_prover::<SC>(op, ext_degree) {
            Some(prover) => out.push(prover),
            None => return out.into_iter().chain(backend).collect(),
        }
    }
    out
}
