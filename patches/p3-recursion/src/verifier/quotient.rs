use alloc::vec::Vec;

use itertools::Itertools;
use p3_circuit::CircuitBuilder;
use p3_field::{BasedVectorSpace, Field, PrimeCharacteristicRing};
use p3_uni_stark::StarkGenericConfig;

use crate::Target;
use crate::traits::{Recursive, RecursivePcs};

pub fn recompose_quotient_from_chunks_circuit<
    SC: StarkGenericConfig,
    InputProof: Recursive<SC::Challenge>,
    OpeningProof: Recursive<SC::Challenge>,
    Comm: Recursive<SC::Challenge>,
    Domain: Copy,
>(
    circuit: &mut CircuitBuilder<SC::Challenge>,
    quotient_chunks_domains: &[Domain],
    quotient_chunks: &[Vec<Target>],
    zeta: Target,
    pcs: &SC::Pcs,
) -> Target
where
    SC::Pcs: RecursivePcs<SC, InputProof, OpeningProof, Comm, Domain>,
    SC::Challenge: PrimeCharacteristicRing,
{
    let zps = compute_quotient_chunk_products::<SC, _, _, _, _>(
        circuit,
        quotient_chunks_domains,
        zeta,
        pcs,
    );

    compute_quotient_evaluation::<SC>(circuit, quotient_chunks, &zps)
}

fn vanishing_poly_at_point_native<
    SC: StarkGenericConfig,
    InputProof: Recursive<SC::Challenge>,
    OpeningProof: Recursive<SC::Challenge>,
    Comm: Recursive<SC::Challenge>,
    Domain,
>(
    pcs: &SC::Pcs,
    domain: &Domain,
    point: SC::Challenge,
) -> SC::Challenge
where
    SC::Pcs: RecursivePcs<SC, InputProof, OpeningProof, Comm, Domain>,
{
    let normalized = point * pcs.first_point(domain).inverse();

    let power = normalized.exp_power_of_2(pcs.log_size(domain));

    power - SC::Challenge::ONE
}

fn compute_quotient_chunk_products<
    SC: StarkGenericConfig,
    InputProof: Recursive<SC::Challenge>,
    OpeningProof: Recursive<SC::Challenge>,
    Comm: Recursive<SC::Challenge>,
    Domain: Copy,
>(
    circuit: &mut CircuitBuilder<SC::Challenge>,
    quotient_chunks_domains: &[Domain],
    zeta: Target,
    pcs: &SC::Pcs,
) -> Vec<Target>
where
    SC::Pcs: RecursivePcs<SC, InputProof, OpeningProof, Comm, Domain>,
    SC::Challenge: PrimeCharacteristicRing,
{
    if quotient_chunks_domains.is_empty() {
        return Vec::new();
    }

    let vp_zeta_values = quotient_chunks_domains
        .iter()
        .map(|&domain| {
            vanishing_poly_at_point_circuit::<SC, _, _, _, _>(pcs, &domain, zeta, circuit)
        })
        .collect_vec();

    let total_vp_zeta_product = circuit.mul_many(&vp_zeta_values);

    let den_constants = quotient_chunks_domains
        .iter()
        .enumerate()
        .map(|(i, &domain_i)| {
            let fp_i = pcs.first_point(&domain_i);
            quotient_chunks_domains
                    .iter()
                    .enumerate()
                    .filter(|&(j, _)| j != i)
                    .fold(SC::Challenge::ONE, |acc, (_, &domain_j)| {
                        acc * vanishing_poly_at_point_native::<
                            SC,
                            InputProof,
                            OpeningProof,
                            Comm,
                            Domain,
                        >(pcs, &domain_j, fp_i)
                    })
        })
        .collect_vec();

    let den_targets: Vec<_> = den_constants
        .iter()
        .map(|&c| circuit.define_const(c))
        .collect();

    vp_zeta_values
        .iter()
        .enumerate()
        .map(|(i, &vp_zeta_i)| {
            let num = circuit.div(total_vp_zeta_product, vp_zeta_i);

            let den = den_targets[i];

            circuit.div(num, den)
        })
        .collect()
}

fn compute_quotient_evaluation<SC: StarkGenericConfig>(
    circuit: &mut CircuitBuilder<SC::Challenge>,
    opened_quotient_chunks: &[Vec<Target>],
    zps: &[Target],
) -> Target
where
    SC::Challenge: PrimeCharacteristicRing,
{
    let d = SC::Challenge::DIMENSION;

    if d == 0 || opened_quotient_chunks.is_empty() {
        return circuit.define_const(SC::Challenge::ZERO);
    }

    let basis_targets: Vec<_> = (0..d)
        .map(|i| {
            let basis_elem =
                SC::Challenge::ith_basis_element(i).expect("Basis index should be in range [0, d)");
            circuit.define_const(basis_elem)
        })
        .collect();

    let chunk_evals = opened_quotient_chunks
        .iter()
        .map(|chunk| {
            debug_assert_eq!(
                chunk.len(),
                d,
                "Chunk length must match field extension degree"
            );

            circuit.inner_product(chunk, &basis_targets)
        })
        .collect_vec();

    circuit.inner_product(&chunk_evals, zps)
}

fn vanishing_poly_at_point_circuit<
    SC: StarkGenericConfig,
    InputProof: Recursive<SC::Challenge>,
    OpeningProof: Recursive<SC::Challenge>,
    Comm: Recursive<SC::Challenge>,
    Domain,
>(
    pcs: &SC::Pcs,
    domain: &Domain,
    point: Target,
    circuit: &mut CircuitBuilder<SC::Challenge>,
) -> Target
where
    SC::Pcs: RecursivePcs<SC, InputProof, OpeningProof, Comm, Domain>,
{
    let inv = circuit.define_const(pcs.first_point(domain).inverse());
    let mul = circuit.mul(point, inv);

    let exp = circuit.exp_power_of_2(mul, pcs.log_size(domain));

    let one = circuit.define_const(SC::Challenge::ONE);
    circuit.sub(exp, one)
}
