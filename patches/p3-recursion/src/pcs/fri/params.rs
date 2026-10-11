use p3_circuit::ops::PermConfig;
use p3_field::{PrimeField64, TwoAdicField};
use p3_fri::FriParameters;
use thiserror::Error;

#[derive(Clone, Copy, Debug, Eq, Error, PartialEq)]
pub enum FriInputError {
    #[error("native FRI must require at least one query")]
    ZeroQueries,
    #[error("native FRI max folding arity must be positive")]
    ZeroMaxLogArity,
    #[error("native FRI log_blowup must be positive for soundness")]
    ZeroBlowup,
    #[error("native FRI log parameter {name} is not representable")]
    LogNotRepresentable { name: &'static str },
    #[error("native FRI height logs overflow")]
    HeightOverflow,
    #[error("native FRI height cannot be represented by the machine word")]
    HeightExceedsWord,
    #[error("native FRI height exceeds field two-adicity")]
    HeightExceedsTwoAdicity,
    #[error("native FRI max arity exceeds field two-adicity")]
    MaxArityExceedsTwoAdicity,
    #[error("native FRI {name} proof-of-work bits are not supported by the field/word limits")]
    PowBitsOutOfRange { name: &'static str },
    #[error(
        "native FRI batch-phase proof of work ({bits} bits) is not supported by the recursive verifier"
    )]
    UnsupportedBatchPow { bits: usize },
    #[error("native FRI scalar {name} does not match recursive parameters")]
    ScalarMismatch { name: &'static str },
    #[error("native FRI has {native} queries but recursive verifier requires {minimum}")]
    QueryFloor { native: usize, minimum: usize },
}

#[derive(Clone, Copy, Debug, Eq, Error, PartialEq)]
pub enum FriVerifierParamsError {
    #[error("FRI verifier requires at least one query")]
    ZeroQueries,
    #[error("FRI verifier max folding arity must be positive")]
    ZeroMaxLogArity,
    #[error("FRI verifier log parameter {name} is not representable")]
    LogNotRepresentable { name: &'static str },
    #[error("FRI verifier fold/domain exponent sum overflows usize")]
    HeightOverflow,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct NativeFriParams {
    log_blowup: usize,
    log_final_poly_len: usize,
    max_log_arity: usize,
    num_queries: usize,
    commit_pow_bits: usize,
    query_pow_bits: usize,
}

impl NativeFriParams {
    pub fn try_from_native<F, M>(params: &FriParameters<M>) -> Result<Self, FriInputError>
    where
        F: PrimeField64 + TwoAdicField,
    {
        if params.num_queries == 0 {
            return Err(FriInputError::ZeroQueries);
        }
        if params.max_log_arity == 0 {
            return Err(FriInputError::ZeroMaxLogArity);
        }
        if params.log_blowup == 0 {
            return Err(FriInputError::ZeroBlowup);
        }
        if params.batch_proof_of_work_bits != 0 {
            return Err(FriInputError::UnsupportedBatchPow {
                bits: params.batch_proof_of_work_bits,
            });
        }
        for (name, value) in [
            ("log_blowup", params.log_blowup),
            ("log_final_poly_len", params.log_final_poly_len),
            ("max_log_arity", params.max_log_arity),
        ] {
            if value >= usize::BITS as usize || u32::try_from(value).is_err() {
                return Err(FriInputError::LogNotRepresentable { name });
            }
        }
        for (name, bits) in [
            ("commit", params.commit_proof_of_work_bits),
            ("query", params.query_proof_of_work_bits),
        ] {
            if bits >= usize::BITS as usize
                || (bits != 0
                    && (1u64.checked_shl(bits as u32).is_none()
                        || 1u64.checked_shl(bits as u32).unwrap() >= F::ORDER_U64))
            {
                return Err(FriInputError::PowBitsOutOfRange { name });
            }
        }
        let snapshot = Self {
            log_blowup: params.log_blowup,
            log_final_poly_len: params.log_final_poly_len,
            max_log_arity: params.max_log_arity,
            num_queries: params.num_queries,
            commit_pow_bits: params.commit_proof_of_work_bits,
            query_pow_bits: params.query_proof_of_work_bits,
        };
        snapshot.validate_field::<F>()?;
        Ok(snapshot)
    }

    pub const fn log_blowup(&self) -> usize {
        self.log_blowup
    }

    pub const fn log_final_poly_len(&self) -> usize {
        self.log_final_poly_len
    }

    pub const fn max_log_arity(&self) -> usize {
        self.max_log_arity
    }

    pub const fn num_queries(&self) -> usize {
        self.num_queries
    }

    pub const fn commit_pow_bits(&self) -> usize {
        self.commit_pow_bits
    }

    pub const fn query_pow_bits(&self) -> usize {
        self.query_pow_bits
    }

    pub fn validate_field<F>(&self) -> Result<(), FriInputError>
    where
        F: PrimeField64 + TwoAdicField,
    {
        for (name, value) in [
            ("log_blowup", self.log_blowup),
            ("log_final_poly_len", self.log_final_poly_len),
            ("max_log_arity", self.max_log_arity),
        ] {
            if value >= usize::BITS as usize || u32::try_from(value).is_err() {
                return Err(FriInputError::LogNotRepresentable { name });
            }
        }
        let height = self
            .log_blowup
            .checked_add(self.log_final_poly_len)
            .ok_or(FriInputError::HeightOverflow)?;
        if height >= usize::BITS as usize {
            return Err(FriInputError::HeightExceedsWord);
        }
        if height > F::TWO_ADICITY {
            return Err(FriInputError::HeightExceedsTwoAdicity);
        }
        if self.max_log_arity > F::TWO_ADICITY {
            return Err(FriInputError::MaxArityExceedsTwoAdicity);
        }
        for (name, bits) in [
            ("commit", self.commit_pow_bits),
            ("query", self.query_pow_bits),
        ] {
            if bits >= usize::BITS as usize
                || (bits != 0
                    && (1u64.checked_shl(bits as u32).is_none()
                        || 1u64.checked_shl(bits as u32).unwrap() >= F::ORDER_U64))
            {
                return Err(FriInputError::PowBitsOutOfRange { name });
            }
        }
        Ok(())
    }

    pub fn validate_recursive(&self, recursive: &FriVerifierParams) -> Result<(), FriInputError> {
        for (name, native, recursive) in [
            ("log_blowup", self.log_blowup, recursive.log_blowup),
            (
                "log_final_poly_len",
                self.log_final_poly_len,
                recursive.log_final_poly_len,
            ),
            ("max_log_arity", self.max_log_arity, recursive.max_log_arity),
            (
                "commit_pow_bits",
                self.commit_pow_bits,
                recursive.commit_pow_bits,
            ),
            (
                "query_pow_bits",
                self.query_pow_bits,
                recursive.query_pow_bits,
            ),
        ] {
            if native != recursive {
                return Err(FriInputError::ScalarMismatch { name });
            }
        }
        if self.num_queries < recursive.num_queries {
            return Err(FriInputError::QueryFloor {
                native: self.num_queries,
                minimum: recursive.num_queries,
            });
        }
        Ok(())
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct FriVerifierParams {
    log_blowup: usize,
    log_final_poly_len: usize,
    max_log_arity: usize,
    commit_pow_bits: usize,
    query_pow_bits: usize,
    num_queries: usize,
    permutation_config: PermConfig,
}

impl FriVerifierParams {
    pub fn try_with_mmcs(
        log_blowup: usize,
        log_final_poly_len: usize,
        max_log_arity: usize,
        commit_pow_bits: usize,
        query_pow_bits: usize,
        num_queries: usize,
        permutation_config: impl Into<PermConfig>,
    ) -> Result<Self, FriVerifierParamsError> {
        if num_queries == 0 {
            return Err(FriVerifierParamsError::ZeroQueries);
        }
        for (name, value) in [
            ("log_blowup", log_blowup),
            ("log_final_poly_len", log_final_poly_len),
            ("max_log_arity", max_log_arity),
            ("commit_pow_bits", commit_pow_bits),
            ("query_pow_bits", query_pow_bits),
        ] {
            if value >= usize::BITS as usize || u32::try_from(value).is_err() {
                return Err(FriVerifierParamsError::LogNotRepresentable { name });
            }
        }
        let height = log_blowup
            .checked_add(log_final_poly_len)
            .ok_or(FriVerifierParamsError::HeightOverflow)?;
        if height >= usize::BITS as usize {
            return Err(FriVerifierParamsError::HeightOverflow);
        }
        if max_log_arity == 0 {
            return Err(FriVerifierParamsError::ZeroMaxLogArity);
        }
        Ok(Self {
            log_blowup,
            log_final_poly_len,
            max_log_arity,
            commit_pow_bits,
            query_pow_bits,
            num_queries,
            permutation_config: permutation_config.into(),
        })
    }

    pub fn with_mmcs(
        log_blowup: usize,
        log_final_poly_len: usize,
        max_log_arity: usize,
        commit_pow_bits: usize,
        query_pow_bits: usize,
        num_queries: usize,
        permutation_config: impl Into<PermConfig>,
    ) -> Self {
        Self::try_with_mmcs(
            log_blowup,
            log_final_poly_len,
            max_log_arity,
            commit_pow_bits,
            query_pow_bits,
            num_queries,
            permutation_config,
        )
        .expect("invalid production FRI verifier parameters")
    }

    pub const fn log_blowup(&self) -> usize {
        self.log_blowup
    }
    pub const fn log_final_poly_len(&self) -> usize {
        self.log_final_poly_len
    }
    pub const fn max_log_arity(&self) -> usize {
        self.max_log_arity
    }
    pub const fn commit_pow_bits(&self) -> usize {
        self.commit_pow_bits
    }
    pub const fn query_pow_bits(&self) -> usize {
        self.query_pow_bits
    }
    pub const fn num_queries(&self) -> usize {
        self.num_queries
    }
    pub const fn permutation_config(&self) -> PermConfig {
        self.permutation_config
    }
}
