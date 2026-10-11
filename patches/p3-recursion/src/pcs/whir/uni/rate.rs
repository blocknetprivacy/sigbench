use p3_whir::parameters::ProtocolParameters;

use crate::pcs::whir::params::WhirVerifierParamsError;
use crate::pcs::whir::uni::plan::initial_layout_folding;
use crate::pcs::whir::uni::recursive_pcs::validate_round_config_inputs;

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub enum WhirRatePolicy {
    #[default]
    Native,
    FirstRoundReduction(usize),
}

impl WhirRatePolicy {
    pub(crate) fn validate(
        self,
        protocol: &ProtocolParameters,
    ) -> Result<(), WhirVerifierParamsError> {
        if let Self::FirstRoundReduction(bits) = self {
            if !protocol.round_log_inv_rates.is_empty() {
                return Err(WhirVerifierParamsError::InvalidRatePolicy(
                    "an adaptive policy cannot be combined with explicit round rates",
                ));
            }
            let first = initial_layout_folding(&protocol.folding_factor)
                .ok_or(WhirVerifierParamsError::UnsupportedFoldingFactor)?;
            let max = protocol
                .starting_log_inv_rate
                .checked_add(first)
                .ok_or(WhirVerifierParamsError::RateArithmeticOverflow { round: 0 })?;
            if bits == 0 || bits >= max {
                return Err(WhirVerifierParamsError::InvalidRatePolicy(
                    "first domain reduction must be positive and leave a positive inverse rate",
                ));
            }
        }
        Ok(())
    }

    pub(crate) fn resolve(
        self,
        arity: usize,
        protocol: &ProtocolParameters,
    ) -> Result<ProtocolParameters, WhirVerifierParamsError> {
        self.validate(protocol)?;
        validate_round_config_inputs(arity, protocol)?;
        let mut resolved = protocol.clone();
        if let Self::FirstRoundReduction(bits) = self {
            let schedule = protocol
                .folding_factor
                .compute_folding_schedule(arity)
                .map_err(p3_whir::parameters::WhirConfigError::FoldingFactor)?;
            let mut rate = protocol.starting_log_inv_rate;
            for (round, &fold) in schedule.iter().take(schedule.len() - 1).enumerate() {
                rate = rate
                    .checked_add(fold)
                    .and_then(|rate| rate.checked_sub(if round == 0 { bits } else { 1 }))
                    .ok_or(WhirVerifierParamsError::RateArithmeticOverflow { round })?;
                resolved.round_log_inv_rates.push(rate);
            }
        }
        Ok(resolved)
    }
}
