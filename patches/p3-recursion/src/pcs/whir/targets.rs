use alloc::vec::Vec;

use p3_circuit::CircuitBuilder;
use p3_field::{ExtensionField, Field};

use crate::Target;
pub use crate::pcs::whir::gadgets::ConstraintWeightData;

pub struct SumcheckDataTargets {
    pub round_polys: Vec<[Target; 2]>,
    pub pow_witnesses: Vec<Target>,
}

impl SumcheckDataTargets {
    pub fn alloc<EF: Field>(
        circuit: &mut CircuitBuilder<EF>,
        num_rounds: usize,
        pow_bits: usize,
        label: &'static str,
    ) -> Self {
        let round_polys = (0..num_rounds)
            .map(|_| circuit.alloc_public_input_array(label))
            .collect();
        let pow_witnesses = if pow_bits > 0 {
            circuit.alloc_public_inputs(num_rounds, label)
        } else {
            Vec::new()
        };
        Self {
            round_polys,
            pow_witnesses,
        }
    }

    pub fn get_values<F: Field, EF: ExtensionField<F>>(
        data: &p3_sumcheck::SumcheckData<F, EF>,
    ) -> Vec<EF> {
        let mut vals: Vec<EF> = Vec::new();
        for &[c0, cinf] in data.polynomial_evaluations() {
            vals.push(c0);
            vals.push(cinf);
        }
        for &w in &data.pow_witnesses {
            vals.push(w.into());
        }
        vals
    }
}

pub enum QueryOpeningTargets {
    Base {
        leaf_values: Vec<Target>,
    },
    Extension {
        leaf_values: Vec<Target>,
    },
}

impl QueryOpeningTargets {
    pub fn alloc_base<EF: Field>(circuit: &mut CircuitBuilder<EF>, leaf_len: usize) -> Self {
        Self::Base {
            leaf_values: circuit.alloc_private_inputs(leaf_len, "WHIR base query leaf"),
        }
    }

    pub fn alloc_extension<EF: Field>(circuit: &mut CircuitBuilder<EF>, leaf_len: usize) -> Self {
        Self::Extension {
            leaf_values: circuit.alloc_private_inputs(leaf_len, "WHIR extension query leaf"),
        }
    }

    pub fn leaf_values(&self) -> &[Target] {
        match self {
            Self::Base { leaf_values } | Self::Extension { leaf_values } => leaf_values,
        }
    }

    pub fn private_values_base<F: Field, EF: ExtensionField<F>>(values: &[F]) -> Vec<EF> {
        values.iter().map(|&v| v.into()).collect()
    }

    pub fn private_values_extension<EF: Copy>(values: &[EF]) -> Vec<EF> {
        values.to_vec()
    }
}

pub struct WhirRoundProofTargets {
    pub commitment_cap: Vec<Vec<Target>>,
    pub ood_answers: Vec<Target>,
    pub pow_witness: Target,
    pub queries: Vec<QueryOpeningTargets>,
    pub sumcheck: SumcheckDataTargets,
}

impl WhirRoundProofTargets {
    #[allow(clippy::too_many_arguments)]
    pub fn alloc<EF: Field>(
        circuit: &mut CircuitBuilder<EF>,
        ood_samples: usize,
        num_queries: usize,
        folding_factor: usize,
        folding_pow_bits: usize,
        cap_entries: usize,
        cap_entry_len: usize,
        is_base_round: bool,
    ) -> Self {
        Self::alloc_with_sumcheck_rounds(
            circuit,
            ood_samples,
            num_queries,
            folding_factor,
            folding_factor,
            folding_pow_bits,
            cap_entries,
            cap_entry_len,
            is_base_round,
        )
    }

    #[allow(clippy::too_many_arguments)]
    fn alloc_with_sumcheck_rounds<EF: Field>(
        circuit: &mut CircuitBuilder<EF>,
        ood_samples: usize,
        num_queries: usize,
        leaf_folding_factor: usize,
        num_sumcheck_rounds: usize,
        folding_pow_bits: usize,
        cap_entries: usize,
        cap_entry_len: usize,
        is_base_round: bool,
    ) -> Self {
        let commitment_cap = (0..cap_entries)
            .map(|_| circuit.alloc_public_inputs(cap_entry_len, "WHIR round commitment cap entry"))
            .collect();
        let ood_answers = circuit.alloc_public_inputs(ood_samples, "WHIR round OOD answers");
        let pow_witness = circuit.alloc_public_input("WHIR round PoW witness");
        let leaf_len = 1usize << leaf_folding_factor;
        let queries = if is_base_round {
            (0..num_queries)
                .map(|_| QueryOpeningTargets::alloc_base(circuit, leaf_len))
                .collect()
        } else {
            (0..num_queries)
                .map(|_| QueryOpeningTargets::alloc_extension(circuit, leaf_len))
                .collect()
        };
        let sumcheck = SumcheckDataTargets::alloc(
            circuit,
            num_sumcheck_rounds,
            folding_pow_bits,
            "WHIR round sumcheck",
        );
        Self {
            commitment_cap,
            ood_answers,
            pow_witness,
            queries,
            sumcheck,
        }
    }
}

pub struct WhirProofTargets {
    pub initial_ood_answers: Vec<Target>,
    pub initial_sumcheck: SumcheckDataTargets,
    pub rounds: Vec<WhirRoundProofTargets>,
    pub final_poly: Vec<Target>,
    pub final_pow_witness: Target,
    pub final_queries: Vec<QueryOpeningTargets>,
    pub final_sumcheck: Option<SumcheckDataTargets>,
}

impl WhirProofTargets {
    pub fn alloc<F: Field, EF: ExtensionField<F>>(
        circuit: &mut CircuitBuilder<EF>,
        params: &super::params::WhirVerifierParams<F>,
        cap_entries: usize,
        cap_entry_len: usize,
    ) -> Self {
        let initial_ood_answers = circuit
            .alloc_public_inputs(params.commitment_ood_samples(), "WHIR initial OOD answers");

        let initial_folding_factor = if params.n_rounds() > 0 {
            params.round_params()[0].folding_factor()
        } else {
            params.final_folding_factor()
        };
        let initial_sumcheck = SumcheckDataTargets::alloc(
            circuit,
            initial_folding_factor,
            params.starting_folding_pow_bits(),
            "WHIR initial sumcheck",
        );

        let rounds = params
            .round_params()
            .iter()
            .enumerate()
            .map(|(i, rp)| {
                WhirRoundProofTargets::alloc_with_sumcheck_rounds(
                    circuit,
                    rp.ood_samples(),
                    rp.num_query_openings(),
                    rp.folding_factor(),
                    params.round_folding_factor(i + 1),
                    rp.folding_pow_bits(),
                    cap_entries,
                    cap_entry_len,
                    i == 0,
                )
            })
            .collect();

        let final_poly_len = 1usize << params.final_poly_num_variables();
        let final_poly =
            circuit.alloc_public_inputs(final_poly_len, "WHIR final polynomial evaluations");
        let final_pow_witness = circuit.alloc_public_input("WHIR final PoW witness");

        let final_leaf_len = 1usize << params.final_folding_factor();
        let final_queries = (0..params.final_query_openings())
            .map(|_| {
                if params.n_rounds() == 0 {
                    QueryOpeningTargets::alloc_base(circuit, final_leaf_len)
                } else {
                    QueryOpeningTargets::alloc_extension(circuit, final_leaf_len)
                }
            })
            .collect();

        let final_sumcheck = if params.final_sumcheck_rounds() > 0 {
            Some(SumcheckDataTargets::alloc(
                circuit,
                params.final_sumcheck_rounds(),
                params.final_folding_pow_bits(),
                "WHIR final sumcheck",
            ))
        } else {
            None
        };

        Self {
            initial_ood_answers,
            initial_sumcheck,
            rounds,
            final_poly,
            final_pow_witness,
            final_queries,
            final_sumcheck,
        }
    }
}

pub struct WhirPcsProofTargets {
    pub whir: WhirProofTargets,
    pub evals: Vec<Vec<Target>>,
}

impl WhirPcsProofTargets {
    pub fn alloc<F: Field, EF: ExtensionField<F>>(
        circuit: &mut CircuitBuilder<EF>,
        params: &super::params::WhirVerifierParams<F>,
        cap_entries: usize,
        cap_entry_len: usize,
        batch_evals: &[usize],
    ) -> Self {
        let whir = WhirProofTargets::alloc(circuit, params, cap_entries, cap_entry_len);
        let evals = batch_evals
            .iter()
            .map(|&n| circuit.alloc_public_inputs(n, "WHIR opening evals"))
            .collect();
        Self { whir, evals }
    }
}
