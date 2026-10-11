use alloc::vec::Vec;
use core::fmt;

use p3_challenger::{FieldChallenger, GrindingChallenger};
use p3_circuit::ops::PermConfig;
use p3_field::{ExtensionField, Field, TwoAdicField};
use p3_sumcheck::strategy::VariableOrder;
use p3_whir::parameters::{RoundConfig, WhirConfig, WhirConfigError};
use p3_whir::transcript::WhirShape;
use thiserror::Error;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum WhirPhase {
    Round(usize),
    Final,
}

impl fmt::Display for WhirPhase {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Round(i) => write!(f, "round {i}"),
            Self::Final => write!(f, "final phase"),
        }
    }
}

#[derive(Debug, Error)]
pub enum WhirVerifierParamsError {
    #[error("invalid WHIR configuration: {0}")]
    InvalidConfig(#[from] WhirConfigError),
    #[error("WHIR recursive verifier requires a positive native folding strategy")]
    UnsupportedFoldingFactor,
    #[error("WHIR stacked univariate adapter cannot use variable order {variable_order:?}")]
    UnsupportedVariableOrder { variable_order: VariableOrder },
    #[error("stacked WHIR arity {arity} cannot form an initial domain with rate {rate}")]
    InvalidStackedArity { arity: usize, rate: usize },
    #[error("WHIR rate arithmetic overflows while deriving round {round}")]
    RateArithmeticOverflow { round: usize },
    #[error("invalid WHIR rate policy: {0}")]
    InvalidRatePolicy(&'static str),
    #[error("WHIR derived configuration is inconsistent in {component}")]
    InconsistentDerivedConfig { component: &'static str },
    #[error(
        "{phase}: num_queries ({num_queries}) >= folded_domain_size ({folded_domain_size}); \
         saturating STIR query counts are not yet supported in-circuit"
    )]
    SaturatingQueryCountUnsupported {
        phase: WhirPhase,
        num_queries: usize,
        folded_domain_size: usize,
    },
    #[error("WHIR recursive verifier does not support stratified query sampling")]
    UnsupportedStratifiedQueries,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct WhirRoundParams<F> {
    ood_samples: usize,
    num_queries: usize,
    pow_bits: usize,
    folding_pow_bits: usize,
    folding_factor: usize,
    domain_size: usize,
    folded_domain_gen: F,
    num_variables: usize,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct WhirVerifierParams<F> {
    num_variables: usize,
    commitment_ood_samples: usize,
    starting_folding_pow_bits: usize,
    round_params: Vec<WhirRoundParams<F>>,
    final_poly_num_variables: usize,
    final_queries: usize,
    final_pow_bits: usize,
    final_sumcheck_rounds: usize,
    final_folding_factor: usize,
    final_folding_pow_bits: usize,
    variable_order: VariableOrder,
    final_domain_size: usize,
    final_folded_domain_gen: F,
    transcript_shape: WhirTranscriptShape,
    permutation_config: PermConfig,
}

#[derive(Clone, Debug)]
pub struct WhirTranscriptShape(WhirShape);

impl PartialEq for WhirTranscriptShape {
    fn eq(&self, other: &Self) -> bool {
        alloc::format!("{:?}", self.0) == alloc::format!("{:?}", other.0)
    }
}

impl Eq for WhirTranscriptShape {}

impl WhirTranscriptShape {
    #[must_use]
    pub fn for_claims(&self, num_opening_claims: usize) -> WhirShape {
        WhirShape {
            num_opening_claims,
            ..self.0.clone()
        }
    }
}

impl<F: Field> WhirVerifierParams<F> {
    const fn round_config_matches(a: &RoundConfig, b: &RoundConfig) -> bool {
        a.pow_bits == b.pow_bits
            && a.folding_pow_bits == b.folding_pow_bits
            && a.num_queries == b.num_queries
            && a.ood_samples == b.ood_samples
            && a.num_variables == b.num_variables
            && a.folding_factor == b.folding_factor
            && a.log_inv_rate == b.log_inv_rate
            && a.domain_size == b.domain_size
            && a.log_folded_domain_size == b.log_folded_domain_size
    }

    pub fn from_config<EF, Ch>(
        config: &WhirConfig<EF, F, Ch>,
        variable_order: VariableOrder,
        permutation_config: impl Into<PermConfig>,
    ) -> Result<Self, WhirVerifierParamsError>
    where
        F: TwoAdicField,
        EF: ExtensionField<F> + TwoAdicField,
        Ch: FieldChallenger<F> + GrindingChallenger<Witness = F>,
    {
        crate::pcs::whir::uni::recursive_pcs::validate_round_config_inputs(
            config.num_variables(),
            config.params(),
        )?;
        let canonical =
            WhirConfig::<EF, F, Ch>::new(config.num_variables(), config.params().clone())?;
        if config.num_variables() != canonical.num_variables()
            || config.folding_schedule() != canonical.folding_schedule()
            || config.commitment_ood_samples() != canonical.commitment_ood_samples()
            || config.starting_folding_pow_bits() != canonical.starting_folding_pow_bits()
            || config.terminal() != canonical.terminal()
            || config.final_sumcheck_rounds() != canonical.final_sumcheck_rounds()
            || config.final_folding_pow_bits() != canonical.final_folding_pow_bits()
            || config.round_parameters().len() != canonical.round_parameters().len()
            || config
                .round_parameters()
                .iter()
                .zip(canonical.round_parameters())
                .any(|(a, b)| !Self::round_config_matches(a, b))
        {
            return Err(WhirVerifierParamsError::InconsistentDerivedConfig {
                component: "derived round schedule",
            });
        }

        let supplied_shape = WhirShape::new(config, 0);
        let canonical_shape = WhirShape::new(&canonical, 0);
        if supplied_shape.stratified_queries {
            return Err(WhirVerifierParamsError::UnsupportedStratifiedQueries);
        }
        if supplied_shape.domain_id != canonical_shape.domain_id {
            return Err(WhirVerifierParamsError::InconsistentDerivedConfig {
                component: "transcript domain",
            });
        }

        let config = &canonical;
        let n_rounds = config.n_rounds();
        let round_params = (0..n_rounds)
            .map(|i| {
                let rp = &config.round_parameters()[i];
                WhirRoundParams {
                    ood_samples: rp.ood_samples,
                    num_queries: rp.num_queries,
                    pow_bits: rp.pow_bits,
                    folding_pow_bits: rp.folding_pow_bits,
                    folding_factor: rp.folding_factor,
                    domain_size: rp.domain_size,
                    folded_domain_gen: F::two_adic_generator(rp.log_folded_domain_size),
                    num_variables: rp.num_variables,
                }
            })
            .collect();

        let final_round_config = config.final_round_config();
        let terminal = config.terminal();
        Ok(Self {
            num_variables: config.num_variables(),
            commitment_ood_samples: config.commitment_ood_samples(),
            starting_folding_pow_bits: config.starting_folding_pow_bits(),
            round_params,
            final_poly_num_variables: final_round_config.num_variables,
            final_queries: terminal.num_queries,
            final_pow_bits: terminal.pow_bits,
            final_sumcheck_rounds: config.final_sumcheck_rounds(),
            final_folding_factor: final_round_config.folding_factor,
            final_folding_pow_bits: config.final_folding_pow_bits(),
            variable_order,
            final_domain_size: final_round_config.domain_size,
            final_folded_domain_gen: F::two_adic_generator(
                final_round_config.log_folded_domain_size,
            ),
            transcript_shape: WhirTranscriptShape(canonical_shape),
            permutation_config: permutation_config.into(),
        })
    }

    pub const fn n_rounds(&self) -> usize {
        self.round_params.len()
    }

    pub fn round_folding_factor(&self, round: usize) -> usize {
        if round < self.n_rounds() {
            self.round_params[round].folding_factor
        } else {
            self.final_folding_factor
        }
    }

    pub const fn num_variables(&self) -> usize {
        self.num_variables
    }
    pub const fn commitment_ood_samples(&self) -> usize {
        self.commitment_ood_samples
    }
    pub const fn starting_folding_pow_bits(&self) -> usize {
        self.starting_folding_pow_bits
    }
    pub fn round_params(&self) -> &[WhirRoundParams<F>] {
        &self.round_params
    }
    pub const fn final_poly_num_variables(&self) -> usize {
        self.final_poly_num_variables
    }
    pub const fn final_queries(&self) -> usize {
        self.final_queries
    }
    pub const fn final_query_openings(&self) -> usize {
        let folded = self.final_domain_size >> self.final_folding_factor;
        if self.final_queries < folded {
            self.final_queries
        } else {
            folded
        }
    }
    pub const fn final_pow_bits(&self) -> usize {
        self.final_pow_bits
    }
    pub const fn final_sumcheck_rounds(&self) -> usize {
        self.final_sumcheck_rounds
    }
    pub const fn final_folding_factor(&self) -> usize {
        self.final_folding_factor
    }
    pub const fn final_folding_pow_bits(&self) -> usize {
        self.final_folding_pow_bits
    }
    pub const fn variable_order(&self) -> VariableOrder {
        self.variable_order
    }
    pub const fn final_domain_size(&self) -> usize {
        self.final_domain_size
    }
    pub const fn final_folded_domain_gen(&self) -> F {
        self.final_folded_domain_gen
    }
    pub const fn permutation_config(&self) -> PermConfig {
        self.permutation_config
    }
    pub const fn transcript_shape(&self) -> &WhirTranscriptShape {
        &self.transcript_shape
    }
}

impl<F> WhirRoundParams<F> {
    pub const fn ood_samples(&self) -> usize {
        self.ood_samples
    }
    pub const fn num_queries(&self) -> usize {
        self.num_queries
    }
    pub const fn num_query_openings(&self) -> usize {
        let folded = self.domain_size >> self.folding_factor;
        if self.num_queries < folded {
            self.num_queries
        } else {
            folded
        }
    }
    pub const fn pow_bits(&self) -> usize {
        self.pow_bits
    }
    pub const fn folding_pow_bits(&self) -> usize {
        self.folding_pow_bits
    }
    pub const fn folding_factor(&self) -> usize {
        self.folding_factor
    }
    pub const fn domain_size(&self) -> usize {
        self.domain_size
    }
    pub const fn folded_domain_gen(&self) -> F
    where
        F: Copy,
    {
        self.folded_domain_gen
    }
    pub const fn num_variables(&self) -> usize {
        self.num_variables
    }
}
