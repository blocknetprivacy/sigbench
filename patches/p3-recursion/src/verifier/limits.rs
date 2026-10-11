use crate::verifier::VerificationError;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct VerifierLimits {
    pub max_instances: usize,
    pub max_rounds: usize,
    pub max_queries_per_round: usize,
    pub max_log_domain_or_degree: usize,
    pub max_matrix_width: usize,
    pub max_final_poly_evaluations: usize,
    pub max_cap_roots: usize,
    pub max_total_scalar_elements: usize,
    pub max_metadata_entries: usize,
    pub max_metadata_string_bytes: usize,
    pub max_compressed_frontier_hashes: usize,
    pub max_restored_authentication_path_hashes: usize,
}

impl Default for VerifierLimits {
    fn default() -> Self {
        Self {
            max_instances: 4096,
            max_rounds: 64,
            max_queries_per_round: 4096,
            max_log_domain_or_degree: 32,
            max_matrix_width: 1 << 20,
            max_final_poly_evaluations: 1 << 20,
            max_cap_roots: 1 << 16,
            max_total_scalar_elements: 1 << 24,
            max_metadata_entries: 1 << 16,
            max_metadata_string_bytes: 1 << 20,
            max_compressed_frontier_hashes: 1 << 20,
            max_restored_authentication_path_hashes: 1 << 22,
        }
    }
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct InputResourceUsage {
    pub instances: usize,
    pub rounds: usize,
    pub queries: usize,
    pub scalar_elements: usize,
    pub metadata_entries: usize,
    pub metadata_string_bytes: usize,
    pub compressed_frontier_hashes: usize,
    pub restored_authentication_path_hashes: usize,
    pub cap_roots: usize,
    pub final_poly_evaluations: usize,
    #[doc(hidden)]
    pub max_whir_opening_width_sum: usize,
}

impl InputResourceUsage {
    pub fn checked_add(
        component: &'static str,
        current: usize,
        value: usize,
    ) -> Result<usize, VerificationError> {
        current
            .checked_add(value)
            .ok_or(VerificationError::ResourceArithmeticOverflow { component })
    }

    pub fn check(self, limits: &VerifierLimits) -> Result<(), VerificationError> {
        let checks = [
            ("instances", self.instances, limits.max_instances),
            ("rounds", self.rounds, limits.max_rounds),
            (
                "scalar elements",
                self.scalar_elements,
                limits.max_total_scalar_elements,
            ),
            (
                "metadata entries",
                self.metadata_entries,
                limits.max_metadata_entries,
            ),
            (
                "metadata string bytes",
                self.metadata_string_bytes,
                limits.max_metadata_string_bytes,
            ),
            (
                "compressed frontier hashes",
                self.compressed_frontier_hashes,
                limits.max_compressed_frontier_hashes,
            ),
            (
                "restored authentication-path hashes",
                self.restored_authentication_path_hashes,
                limits.max_restored_authentication_path_hashes,
            ),
            ("cap roots", self.cap_roots, limits.max_cap_roots),
            (
                "final polynomial evaluations",
                self.final_poly_evaluations,
                limits.max_final_poly_evaluations,
            ),
        ];
        for (component, actual, limit) in checks {
            if actual > limit {
                return Err(VerificationError::ResourceLimitExceeded {
                    component,
                    actual,
                    limit,
                });
            }
        }
        Ok(())
    }

    pub fn add_query_round(
        &mut self,
        limits: &VerifierLimits,
        count: usize,
    ) -> Result<(), VerificationError> {
        if count > limits.max_queries_per_round {
            return Err(VerificationError::ResourceLimitExceeded {
                component: "queries per round",
                actual: count,
                limit: limits.max_queries_per_round,
            });
        }
        self.queries = Self::checked_add("aggregate query rows", self.queries, count)?;
        Ok(())
    }

    pub fn add_rounds(
        &mut self,
        limits: &VerifierLimits,
        count: usize,
    ) -> Result<(), VerificationError> {
        self.rounds = Self::checked_add("rounds", self.rounds, count)?;
        self.check_component("rounds", self.rounds, limits.max_rounds)
    }

    pub fn add_instances(
        &mut self,
        limits: &VerifierLimits,
        count: usize,
    ) -> Result<(), VerificationError> {
        self.instances = Self::checked_add("instances", self.instances, count)?;
        self.check_component("instances", self.instances, limits.max_instances)
    }

    pub fn add_metadata_entries(
        &mut self,
        limits: &VerifierLimits,
        count: usize,
    ) -> Result<(), VerificationError> {
        self.metadata_entries =
            Self::checked_add("metadata entries", self.metadata_entries, count)?;
        self.check_component(
            "metadata entries",
            self.metadata_entries,
            limits.max_metadata_entries,
        )
    }

    pub fn add_metadata_string_bytes(
        &mut self,
        limits: &VerifierLimits,
        count: usize,
    ) -> Result<(), VerificationError> {
        self.metadata_string_bytes =
            Self::checked_add("metadata string bytes", self.metadata_string_bytes, count)?;
        self.check_component(
            "metadata string bytes",
            self.metadata_string_bytes,
            limits.max_metadata_string_bytes,
        )
    }

    pub fn add_scalar_elements(
        &mut self,
        limits: &VerifierLimits,
        count: usize,
    ) -> Result<(), VerificationError> {
        self.scalar_elements = Self::checked_add("scalar elements", self.scalar_elements, count)?;
        self.check_component(
            "scalar elements",
            self.scalar_elements,
            limits.max_total_scalar_elements,
        )
    }

    pub fn add_cap_roots(
        &mut self,
        limits: &VerifierLimits,
        count: usize,
    ) -> Result<(), VerificationError> {
        self.cap_roots = Self::checked_add("cap roots", self.cap_roots, count)?;
        self.check_component("cap roots", self.cap_roots, limits.max_cap_roots)
    }

    pub fn add_final_poly_evaluations(
        &mut self,
        limits: &VerifierLimits,
        count: usize,
    ) -> Result<(), VerificationError> {
        if count > limits.max_final_poly_evaluations {
            return Err(VerificationError::ResourceLimitExceeded {
                component: "final polynomial evaluations",
                actual: count,
                limit: limits.max_final_poly_evaluations,
            });
        }
        self.final_poly_evaluations = self.final_poly_evaluations.max(count);
        Ok(())
    }

    pub fn add_compressed_frontier_hashes(
        &mut self,
        limits: &VerifierLimits,
        count: usize,
    ) -> Result<(), VerificationError> {
        self.compressed_frontier_hashes = Self::checked_add(
            "compressed frontier hashes",
            self.compressed_frontier_hashes,
            count,
        )?;
        self.check_component(
            "compressed frontier hashes",
            self.compressed_frontier_hashes,
            limits.max_compressed_frontier_hashes,
        )
    }

    pub fn add_restored_authentication_path_hashes(
        &mut self,
        limits: &VerifierLimits,
        queries: usize,
        depth: usize,
    ) -> Result<(), VerificationError> {
        let count =
            queries
                .checked_mul(depth)
                .ok_or(VerificationError::ResourceArithmeticOverflow {
                    component: "restored authentication-path hashes",
                })?;
        self.restored_authentication_path_hashes = Self::checked_add(
            "restored authentication-path hashes",
            self.restored_authentication_path_hashes,
            count,
        )?;
        self.check_component(
            "restored authentication-path hashes",
            self.restored_authentication_path_hashes,
            limits.max_restored_authentication_path_hashes,
        )
    }

    pub const fn check_matrix_width(
        &self,
        limits: &VerifierLimits,
        width: usize,
    ) -> Result<(), VerificationError> {
        self.check_component("matrix or row width", width, limits.max_matrix_width)
    }

    pub const fn check_log_degree(
        &self,
        limits: &VerifierLimits,
        value: usize,
    ) -> Result<(), VerificationError> {
        self.check_component(
            "log domain or degree",
            value,
            limits.max_log_domain_or_degree,
        )
    }

    pub fn merge(&mut self, limits: &VerifierLimits, other: Self) -> Result<(), VerificationError> {
        self.add_instances(limits, other.instances)?;
        self.add_rounds(limits, other.rounds)?;
        self.queries = Self::checked_add("aggregate query rows", self.queries, other.queries)?;
        self.add_scalar_elements(limits, other.scalar_elements)?;
        self.add_metadata_entries(limits, other.metadata_entries)?;
        self.add_metadata_string_bytes(limits, other.metadata_string_bytes)?;
        self.add_compressed_frontier_hashes(limits, other.compressed_frontier_hashes)?;
        self.restored_authentication_path_hashes = Self::checked_add(
            "restored authentication-path hashes",
            self.restored_authentication_path_hashes,
            other.restored_authentication_path_hashes,
        )?;
        self.check_component(
            "restored authentication-path hashes",
            self.restored_authentication_path_hashes,
            limits.max_restored_authentication_path_hashes,
        )?;
        self.add_cap_roots(limits, other.cap_roots)?;
        self.add_final_poly_evaluations(limits, other.final_poly_evaluations)?;
        self.max_whir_opening_width_sum = self
            .max_whir_opening_width_sum
            .max(other.max_whir_opening_width_sum);
        Ok(())
    }

    const fn check_component(
        &self,
        component: &'static str,
        actual: usize,
        limit: usize,
    ) -> Result<(), VerificationError> {
        if actual > limit {
            Err(VerificationError::ResourceLimitExceeded {
                component,
                actual,
                limit,
            })
        } else {
            Ok(())
        }
    }
}
