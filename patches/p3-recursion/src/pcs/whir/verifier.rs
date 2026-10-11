use alloc::vec;
use alloc::vec::Vec;

use p3_circuit::{CircuitBuilder, CircuitBuilderError, NonPrimitiveOpId};
use p3_field::{ExtensionField, PrimeField64, TwoAdicField};
use p3_matrix::Dimensions;
use p3_sumcheck::strategy::VariableOrder;

use super::params::WhirVerifierParams;
use crate::Target;
use crate::pcs::mmcs::{
    verify_batch_circuit_from_extension_opened, verify_whir_base_batch_circuit,
};
use crate::pcs::whir::gadgets::{
    ConstraintWeightData, eval_constraints_poly_circuit, eval_multilinear,
    eval_multilinear_batched, expand_from_univariate, horner_eval, multilinear_eq_weights,
    pow_const_base,
};
use crate::pcs::whir::sumcheck::verify_sumcheck_rounds;
use crate::pcs::whir::targets::{QueryOpeningTargets, WhirProofTargets};
use crate::traits::RecursiveChallenger;

fn stir_query_index_bits<BF, EF, Ch>(
    circuit: &mut CircuitBuilder<EF>,
    challenger: &mut Ch,
    raw_queries: usize,
    folded_domain_size: usize,
    query: usize,
) -> Result<Vec<Target>, CircuitBuilderError>
where
    BF: PrimeField64,
    EF: ExtensionField<BF>,
    Ch: RecursiveChallenger<BF, EF>,
{
    let domain_bits = p3_util::log2_strict_usize(folded_domain_size);
    if raw_queries < folded_domain_size {
        challenger.sample_bits(circuit, domain_bits)
    } else {
        Ok((0..domain_bits)
            .map(|bit| {
                circuit.define_const(if (query >> bit) & 1 == 0 {
                    EF::ZERO
                } else {
                    EF::ONE
                })
            })
            .collect())
    }
}

pub(crate) struct WhirMmcsCheck<'a> {
    config: p3_circuit::ops::PermConfig,
    cap: Vec<Vec<Target>>,
    dims: Vec<Dimensions>,
    index_bits: Vec<Target>,
    opening: &'a QueryOpeningTargets,
}

pub(crate) fn verify_deferred_whir_mmcs<BF, EF>(
    circuit: &mut CircuitBuilder<EF>,
    checks: Vec<WhirMmcsCheck<'_>>,
) -> Result<Vec<NonPrimitiveOpId>, CircuitBuilderError>
where
    BF: PrimeField64 + TwoAdicField,
    EF: ExtensionField<BF> + TwoAdicField,
{
    let mut op_ids = Vec::new();
    for check in checks {
        let ids = match check.opening {
            QueryOpeningTargets::Base { leaf_values } => verify_whir_base_batch_circuit::<BF, EF>(
                circuit,
                check.config,
                &check.cap,
                &check.dims,
                &check.index_bits,
                core::slice::from_ref(leaf_values),
            )?,
            QueryOpeningTargets::Extension { leaf_values } => {
                verify_batch_circuit_from_extension_opened::<BF, EF>(
                    circuit,
                    check.config,
                    &check.cap,
                    &check.dims,
                    &check.index_bits,
                    core::slice::from_ref(leaf_values),
                    None,
                )?
            }
        };
        op_ids.extend(ids);
    }
    Ok(op_ids)
}

#[allow(clippy::too_many_arguments)]
fn verify_whir_circuit_engine<'a, BF, EF, Ch>(
    circuit: &mut CircuitBuilder<EF>,
    challenger: &mut Ch,
    params: &WhirVerifierParams<BF>,
    proof: &'a WhirProofTargets,
    initial_commitment_cap: &[Vec<Target>],
    initial_constraint: ConstraintWeightData,
    initial_claimed_eval: Target,
    permutation_config: Option<p3_circuit::ops::PermConfig>,
) -> Result<Vec<WhirMmcsCheck<'a>>, CircuitBuilderError>
where
    BF: PrimeField64 + TwoAdicField,
    EF: ExtensionField<BF> + TwoAdicField,
    Ch: RecursiveChallenger<BF, EF>,
{
    let is_suffix = params.variable_order() == VariableOrder::Suffix;

    let mut mmcs_checks = Vec::new();
    let mut all_constraints: Vec<ConstraintWeightData> = vec![initial_constraint];
    let mut all_r: Vec<Target> = Vec::new();
    let mut claimed_eval = initial_claimed_eval;

    let (new_claim, initial_r) = verify_sumcheck_rounds::<BF, EF, Ch>(
        circuit,
        challenger,
        claimed_eval,
        &proof.initial_sumcheck.round_polys,
        &proof.initial_sumcheck.pow_witnesses,
        params.starting_folding_pow_bits(),
    )?;
    claimed_eval = new_claim;
    let mut last_r = initial_r.clone();
    all_r.extend_from_slice(&initial_r);

    let mut prev_cap: Vec<Vec<Target>> = initial_commitment_cap.to_vec();

    for (round_idx, rp) in params.round_params().iter().enumerate() {
        let round_proof = &proof.rounds[round_idx];

        let config = params.permutation_config();
        let digest_elems = if config.is_arity4_shape() {
            config.capacity_ext() * config.d()
        } else {
            config.rate_ext() * config.d()
        };
        for cap_entry in &round_proof.commitment_cap {
            if digest_elems.is_multiple_of(EF::DIMENSION) {
                challenger.observe_ext_slice(circuit, cap_entry);
            } else {
                challenger.observe_slice(circuit, cap_entry);
            }
        }

        let mut ood_eq_points: Vec<Vec<Target>> = Vec::with_capacity(rp.ood_samples());
        for i in 0..rp.ood_samples() {
            let ood_univ = challenger.sample_ext(circuit);
            let ood_pt = expand_from_univariate(circuit, ood_univ, rp.num_variables());
            challenger.observe_ext(circuit, round_proof.ood_answers[i]);
            ood_eq_points.push(ood_pt);
        }

        if rp.pow_bits() > 0 {
            challenger.check_pow_witness(circuit, rp.pow_bits(), round_proof.pow_witness)?;
        }

        let folded_domain_size = rp.domain_size() >> rp.folding_factor();
        let dims = vec![Dimensions {
            height: folded_domain_size,
            width: 1usize << rp.folding_factor(),
        }];

        let query_r: Vec<Target> = if is_suffix {
            last_r.iter().copied().rev().collect()
        } else {
            last_r.clone()
        };

        let mut sel_scalars: Vec<Target> = Vec::with_capacity(rp.num_query_openings());

        for q_idx in 0..rp.num_query_openings() {
            let index_bits = stir_query_index_bits::<BF, EF, Ch>(
                circuit,
                challenger,
                rp.num_queries(),
                folded_domain_size,
                q_idx,
            )?;

            let domain_pt = pow_const_base(circuit, rp.folded_domain_gen().into(), &index_bits);
            sel_scalars.push(domain_pt);

            let query_opening = &round_proof.queries[q_idx];
            if let Some(config) = permutation_config {
                mmcs_checks.push(WhirMmcsCheck {
                    config,
                    cap: prev_cap.clone(),
                    dims: dims.clone(),
                    index_bits,
                    opening: query_opening,
                });
            }
        }

        let gamma = challenger.sample_ext(circuit);
        let leaves: Vec<_> = round_proof
            .queries
            .iter()
            .map(|query| query.leaf_values())
            .collect();
        let mut combination = eval_multilinear_batched(circuit, &leaves, &query_r, gamma);
        for &answer in round_proof.ood_answers.iter().rev() {
            combination = circuit.mul_add(combination, gamma, answer);
        }
        let contrib = circuit.mul(combination, gamma);
        claimed_eval = circuit.add(claimed_eval, contrib);

        all_constraints.push(ConstraintWeightData {
            num_variables: rp.num_variables(),
            eq_points: ood_eq_points,
            sel_scalars,
            gamma,
            initial_power: 1,
        });

        let (new_claim, round_r) = verify_sumcheck_rounds::<BF, EF, Ch>(
            circuit,
            challenger,
            claimed_eval,
            &round_proof.sumcheck.round_polys,
            &round_proof.sumcheck.pow_witnesses,
            rp.folding_pow_bits(),
        )?;
        claimed_eval = new_claim;
        last_r = round_r.clone();
        all_r.extend_from_slice(&round_r);

        prev_cap = round_proof.commitment_cap.clone();
    }

    challenger.observe_ext_slice(circuit, &proof.final_poly);

    if params.final_pow_bits() > 0 {
        challenger.check_pow_witness(circuit, params.final_pow_bits(), proof.final_pow_witness)?;
    }

    let final_folded_size = params.final_domain_size() >> params.final_folding_factor();
    let final_dims = vec![Dimensions {
        height: final_folded_size,
        width: 1usize << params.final_folding_factor(),
    }];

    let final_query_r: Vec<Target> = if is_suffix {
        last_r.iter().copied().rev().collect()
    } else {
        last_r
    };

    let final_weights = (params.final_folding_factor() >= 2 && params.final_query_openings() >= 3)
        .then(|| multilinear_eq_weights(circuit, &final_query_r));

    for q_idx in 0..params.final_query_openings() {
        let index_bits = stir_query_index_bits::<BF, EF, Ch>(
            circuit,
            challenger,
            params.final_queries(),
            final_folded_size,
            q_idx,
        )?;

        let domain_scalar = pow_const_base(
            circuit,
            params.final_folded_domain_gen().into(),
            &index_bits,
        );

        let query_opening = &proof.final_queries[q_idx];
        let leaf_vals = query_opening.leaf_values();
        let fold = match &final_weights {
            Some(weights) => circuit.inner_product(weights, leaf_vals),
            None => eval_multilinear(circuit, leaf_vals, &final_query_r),
        };

        let expected = horner_eval(circuit, &proof.final_poly, domain_scalar);
        circuit.connect(fold, expected);

        if let Some(config) = permutation_config {
            mmcs_checks.push(WhirMmcsCheck {
                config,
                cap: prev_cap.clone(),
                dims: final_dims.clone(),
                index_bits,
                opening: query_opening,
            });
        }
    }

    let final_sumcheck_r = if params.final_sumcheck_rounds() > 0
        && let Some(ref final_sc) = proof.final_sumcheck
    {
        let (new_claim, final_r) = verify_sumcheck_rounds::<BF, EF, Ch>(
            circuit,
            challenger,
            claimed_eval,
            &final_sc.round_polys,
            &final_sc.pow_witnesses,
            params.final_folding_pow_bits(),
        )?;
        claimed_eval = new_claim;
        all_r.extend_from_slice(&final_r);
        final_r
    } else {
        Vec::new()
    };

    let eval_weights = eval_constraints_poly_circuit(circuit, &all_r, &all_constraints, is_suffix);

    let final_r_local: Vec<Target> = if is_suffix {
        final_sumcheck_r.iter().copied().rev().collect()
    } else {
        final_sumcheck_r
    };
    let final_value = eval_multilinear(circuit, &proof.final_poly, &final_r_local);

    let expected = circuit.mul(eval_weights, final_value);
    circuit.connect(claimed_eval, expected);

    Ok(mmcs_checks)
}

pub fn verify_whir_circuit<BF, EF, Ch>(
    circuit: &mut CircuitBuilder<EF>,
    challenger: &mut Ch,
    params: &WhirVerifierParams<BF>,
    proof: &WhirProofTargets,
    initial_commitment_cap: &[Vec<Target>],
    initial_constraint: ConstraintWeightData,
    initial_claimed_eval: Target,
) -> Result<Vec<NonPrimitiveOpId>, CircuitBuilderError>
where
    BF: PrimeField64 + TwoAdicField,
    EF: ExtensionField<BF> + TwoAdicField,
    Ch: RecursiveChallenger<BF, EF>,
{
    let checks = verify_whir_circuit_deferred(
        circuit,
        challenger,
        params,
        proof,
        initial_commitment_cap,
        initial_constraint,
        initial_claimed_eval,
    )?;
    verify_deferred_whir_mmcs::<BF, EF>(circuit, checks)
}

#[allow(clippy::too_many_arguments)]
pub(crate) fn verify_whir_circuit_deferred<'a, BF, EF, Ch>(
    circuit: &mut CircuitBuilder<EF>,
    challenger: &mut Ch,
    params: &WhirVerifierParams<BF>,
    proof: &'a WhirProofTargets,
    initial_commitment_cap: &[Vec<Target>],
    initial_constraint: ConstraintWeightData,
    initial_claimed_eval: Target,
) -> Result<Vec<WhirMmcsCheck<'a>>, CircuitBuilderError>
where
    BF: PrimeField64 + TwoAdicField,
    EF: ExtensionField<BF> + TwoAdicField,
    Ch: RecursiveChallenger<BF, EF>,
{
    verify_whir_circuit_engine(
        circuit,
        challenger,
        params,
        proof,
        initial_commitment_cap,
        initial_constraint,
        initial_claimed_eval,
        Some(params.permutation_config()),
    )
}
