use p3_air::symbolic::AirLayout;
use p3_air::{Air, BaseAir};
use p3_batch_stark::symbolic::{get_max_constraint_degree, get_symbolic_constraints};
use p3_field::PrimeField64;
use p3_lookup::logup::LogUpGadget;
use p3_lookup::InteractionSymbolicBuilder;
use p3_security::fri::FriRegime;
use p3_security::logup::{security_term, LogUpAir};
use p3_security::report::SecurityTerm;
use p3_security::shape::{InstanceShape, StarkAirParams};
use p3_security::stark::{conjectured_security_report, proven_security_report};
use p3_security::GrindingSites;
use p3_uni_stark::OpeningShape;

pub struct TableShape {
    pub degree_bits: usize,
    pub main_width: usize,
    pub main_next: bool,
    pub preprocessed_width: usize,
    pub preprocessed_next: bool,
    pub quotient_chunks: usize,
    pub num_lookups: usize,
    pub interactions_per_row: usize,
    pub max_message_width: usize,
    pub num_constraints: usize,
    pub max_constraint_degree: usize,
}

pub struct FriShapeBits {
    pub log_blowup: usize,
    pub max_log_arity: usize,
    pub log_final_poly_len: usize,
    pub num_queries: usize,
    pub commit_pow_bits: usize,
    pub query_pow_bits: usize,
    pub batch_pow_bits: usize,
    pub lookup_pow_bits: usize,
    pub ood_pow_bits: usize,
}

pub struct Report {
    pub tables: usize,
    pub log_domain: usize,
    pub batched_functions: usize,
    pub constraints: usize,
    pub max_degree: usize,
    pub modulus_bits: usize,
    pub collision_bits: usize,
    pub udr_bits: f64,
    pub udr_binding: &'static str,
    pub ldr_bits: f64,
    pub ldr_binding: &'static str,
    pub conjectured_bits: f64,
    pub conjectured_binding: &'static str,
}

impl Report {
    pub fn proven_bits(&self) -> f64 {
        self.udr_bits.max(self.ldr_bits)
    }
}

pub fn table_shape<F, EF, A>(
    air: &A,
    lookups: &[p3_lookup::Lookup<F>],
    degree_bits: usize,
    main_next: bool,
    preprocessed_width: usize,
    preprocessed_next: bool,
    quotient_chunks: usize,
) -> TableShape
where
    F: p3_field::Field,
    EF: p3_field::ExtensionField<F>,
    A: Air<InteractionSymbolicBuilder<F, EF>> + BaseAir<F>,
    p3_air::symbolic::SymbolicExpressionExt<F, EF>: p3_field::Algebra<EF>,
{
    let gadget = LogUpGadget::new();
    let layout = AirLayout::from_air(air);
    let (base, ext) = get_symbolic_constraints::<F, EF, A, _>(air, layout, lookups, &gadget);
    let max_constraint_degree =
        get_max_constraint_degree::<F, EF, A, _>(air, layout, 1 << degree_bits, lookups, &gadget);
    TableShape {
        degree_bits,
        main_width: layout.main_width,
        main_next,
        preprocessed_width,
        preprocessed_next,
        quotient_chunks,
        num_lookups: lookups.len(),
        interactions_per_row: lookups.iter().map(|l| l.elements.len()).sum(),
        max_message_width: lookups
            .iter()
            .flat_map(|l| l.elements.iter().map(|e| e.len()))
            .max()
            .unwrap_or(0),
        num_constraints: base.len() + ext.len(),
        max_constraint_degree,
    }
}

pub fn report<F: PrimeField64>(
    tables: &[TableShape],
    fri: &FriShapeBits,
    challenge_degree: usize,
    digest_elems: usize,
) -> Report {
    let field_bits = (F::ORDER_U64 as f64).log2();
    let modulus_bits = (challenge_degree as f64 * field_bits).floor() as usize;
    let collision_bits = (digest_elems as f64 * field_bits / 2.0).floor() as usize;
    let log_domain = tables.iter().map(|t| t.degree_bits).max().unwrap_or(0);
    let batched_functions: usize = tables
        .iter()
        .map(|t| {
            p3_batch_stark::num_batched_openings(
                t.main_width,
                t.main_next,
                t.preprocessed_width,
                t.preprocessed_next,
                t.quotient_chunks,
                t.num_lookups,
                challenge_degree,
                OpeningShape::new(),
            )
        })
        .sum();
    let constraints: usize = tables.iter().map(|t| t.num_constraints).sum();
    let max_degree = tables.iter().map(|t| t.max_constraint_degree).max().unwrap_or(0);
    let quotient_chunks = tables.iter().map(|t| t.quotient_chunks).max().unwrap_or(1);
    let any_next = tables.iter().any(|t| t.main_next || t.preprocessed_next);

    let regime = FriRegime {
        log_blowup: fri.log_blowup,
        num_queries: fri.num_queries,
        log_final_poly_len: fri.log_final_poly_len,
        max_log_arity: fri.max_log_arity,
        commit_pow_bits: fri.commit_pow_bits,
        query_pow_bits: fri.query_pow_bits,
    };
    let air = StarkAirParams {
        num_constraints: constraints,
        max_constraint_degree: max_degree,
        num_quotient_chunks: quotient_chunks,
        max_combo: if any_next { 2 } else { 1 },
    };
    let shape = InstanceShape {
        log_trace_length: log_domain,
        modulus_bits,
        collision_resistance: collision_bits,
        num_batched_functions: batched_functions,
    };
    let grinding = GrindingSites {
        out_of_domain: fri.ood_pow_bits,
        batch_combination: fri.batch_pow_bits,
        lookup_challenge: fri.lookup_pow_bits,
        ..GrindingSites::NONE
    };
    let logup = LogUpAir {
        num_interactions: tables.iter().map(|t| t.interactions_per_row).sum(),
        max_message_width: tables.iter().map(|t| t.max_message_width).max().unwrap_or(0),
    };
    let extras: Vec<SecurityTerm> = security_term(&logup, &shape, &grinding).into_iter().collect();

    let proven = proven_security_report(&regime, &air, &shape, &extras, &grinding);
    let conj = conjectured_security_report(&regime, &air, &shape, &extras, &grinding);
    let (ldr_bits, ldr_binding) = proven
        .ldr
        .as_ref()
        .map(|r| (r.security_bits(), r.binding().label))
        .unwrap_or((0.0, "none"));
    Report {
        tables: tables.len(),
        log_domain,
        batched_functions,
        constraints,
        max_degree,
        modulus_bits,
        collision_bits,
        udr_bits: proven.udr.security_bits(),
        udr_binding: proven.udr.binding().label,
        ldr_bits,
        ldr_binding,
        conjectured_bits: conj.security_bits(),
        conjectured_binding: conj.binding().label,
    }
}
