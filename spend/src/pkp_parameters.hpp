#ifndef SDSIGN_PKP_PARAMETERS_HPP
#define SDSIGN_PKP_PARAMETERS_HPP

#include "pkp_optimal_encoding.hpp"
#include "vole_parameters.hpp"

#include <array>
#include <cstddef>
#include <utility>

namespace sdsign
{

enum class pkp_domain_model
{
    hamming_ball,
    exact_weight,
    optimal,
};

template <secpar S, std::size_t PARAM_SET = 0> struct pkp_table_parameters;

// Canonical d=3 optimal representative sets.  The PKP instance parameters are
// the ones selected in Section 4 of the paper.
template <> struct pkp_table_parameters<secpar::L1, 0>
{
    constexpr static std::size_t security_bits = 143;
    constexpr static std::size_t q_bits = 11;
    constexpr static std::size_t n = 62;
    constexpr static std::size_t m = 26;
    constexpr static std::size_t eta = 7;
    constexpr static std::size_t degree = 3;
    constexpr static std::size_t representative_capacity = 62;
    constexpr static std::size_t membership_polynomials = 2;
    constexpr static pkp_domain_model domain_model = pkp_domain_model::optimal;
};

template <> struct pkp_table_parameters<secpar::L3, 0>
{
    constexpr static std::size_t security_bits = 207;
    constexpr static std::size_t q_bits = 11;
    constexpr static std::size_t n = 90;
    constexpr static std::size_t m = 42;
    constexpr static std::size_t eta = 8;
    constexpr static std::size_t degree = 3;
    constexpr static std::size_t representative_capacity = 90;
    constexpr static std::size_t membership_polynomials = 3;
    constexpr static pkp_domain_model domain_model = pkp_domain_model::optimal;
};

template <> struct pkp_table_parameters<secpar::L5, 0>
{
    constexpr static std::size_t security_bits = 272;
    constexpr static std::size_t q_bits = 11;
    constexpr static std::size_t n = 118;
    constexpr static std::size_t m = 59;
    constexpr static std::size_t eta = 9;
    constexpr static std::size_t degree = 3;
    constexpr static std::size_t representative_capacity = 128;
    constexpr static std::size_t membership_polynomials = 3;
    constexpr static pkp_domain_model domain_model = pkp_domain_model::optimal;
};

template <secpar S, std::size_t TAU = 0, prg VOLE_PRG = prg::aes_ctr,
          prg TREE_PRG = prg::aes_ctr, leaf_hash LEAF_HASH = leaf_hash::crh,
          std::size_t ZERO_BITS_IN_DELTA = 0,
          std::pair<bavc, std::size_t> BAVC = std::pair<bavc, std::size_t>{bavc::ggm_forest, 0},
          std::size_t PARAM_SET = 0,
          quicksilver_term QS_TERM = quicksilver_term::leading>
struct pkp_owf_parameter_set
{
    using table = pkp_table_parameters<S, PARAM_SET>;

    constexpr static secpar secpar_v = S;
    constexpr static std::size_t tau_v = TAU;
    constexpr static owf owf_v = owf::pkp;
    constexpr static std::size_t param_set_v = PARAM_SET;
    constexpr static elementary_encoding elementary_encoding_v = elementary_encoding::optimal;
    constexpr static quicksilver_term quicksilver_term_v = QS_TERM;
    constexpr static prg prg_v = VOLE_PRG;
    constexpr static prg vole_prg_v = VOLE_PRG;
    constexpr static prg tree_prg_v = TREE_PRG;
    constexpr static leaf_hash leaf_hash_v = LEAF_HASH;
    constexpr static std::size_t zero_bits_in_delta_v = ZERO_BITS_IN_DELTA;
    constexpr static std::size_t secpar_bits = secpar_to_bits(S);
    constexpr static std::size_t secpar_bytes = secpar_to_bytes(S);
    constexpr static std::size_t delta_bits_v = secpar_bits - zero_bits_in_delta_v;

    constexpr static std::size_t pkp_q_bits = table::q_bits;
    constexpr static std::size_t pkp_q = std::size_t{1} << pkp_q_bits;
    constexpr static std::size_t pkp_n = table::n;
    constexpr static std::size_t pkp_m = table::m;
    constexpr static pkp_domain_model domain_model = table::domain_model;
    constexpr static std::size_t encoding_eta = table::eta;
    constexpr static std::size_t representative_capacity = table::representative_capacity;
    constexpr static std::size_t membership_constraints_per_subvector =
        table::membership_polynomials;
    constexpr static bool is_optimal_encoding = domain_model == pkp_domain_model::optimal;
    constexpr static std::size_t num_var_blocks = 1;
    constexpr static std::array<std::size_t, num_var_blocks> block_sizes = {encoding_eta};
    constexpr static std::array<std::size_t, num_var_blocks> block_wts = {0};

    static_assert(is_optimal_encoding);
    static_assert(pkp_n <= representative_capacity);
    static_assert(representative_capacity ==
                  pkp_optimal::representative_set<encoding_eta>::capacity);
    static_assert(table::degree == pkp_optimal::representative_set<encoding_eta>::degree);
    static_assert(membership_constraints_per_subvector ==
                  pkp_optimal::polynomial_data<encoding_eta, pkp_n>::membership_count);

    constexpr static std::size_t input_reduced_bits = []
    {
        return encoding_eta;
    }();
    constexpr static std::size_t witness_rows = pkp_n;
    constexpr static std::size_t witness_raw_bits = witness_rows * input_reduced_bits;
    constexpr static std::size_t witness_bits = ((witness_raw_bits + 7) / 8) * 8;
    constexpr static std::size_t witness_bytes = witness_bits / 8;
    constexpr static std::size_t witness_extended_subvector_bits = []
    {
        return encoding_eta;
    }();
    constexpr static std::size_t witness_extended_bits =
        witness_rows * witness_extended_subvector_bits;
    constexpr static std::size_t witness_extended_bytes = (witness_extended_bits + 7) / 8;

    constexpr static std::size_t public_vector_bits = pkp_n * pkp_q_bits;
    constexpr static std::size_t public_vector_bytes = (public_vector_bits + 7) / 8;
    constexpr static std::size_t y_vector_len =
        (public_vector_bits + secpar_bits - 1) / secpar_bits;
    constexpr static std::size_t prg_seed_bytes = secpar_bytes;
    constexpr static std::size_t packed_public_key_bytes = prg_seed_bytes + public_vector_bytes;
    constexpr static std::size_t unpacked_public_key_bytes =
        prg_seed_bytes + y_vector_len * secpar_bytes;
    constexpr static std::size_t public_key_bytes = packed_public_key_bytes;
    constexpr static std::size_t secret_seed_bytes = secpar_bytes;
    constexpr static std::size_t unpacked_secret_key_bytes =
        unpacked_public_key_bytes + secret_seed_bytes + witness_bytes;
    constexpr static std::size_t packed_secret_key_bytes =
        packed_public_key_bytes + secret_seed_bytes + witness_bytes;

    constexpr static std::size_t ncr(std::size_t n, std::size_t r)
    {
        if (r > n)
            return 0;
        if (r == 0 || r == n)
            return 1;
        const std::size_t k = (r < n - r) ? r : n - r;
        std::size_t result = 1;
        for (std::size_t i = 1; i <= k; ++i)
            result = (result * (n - k + i)) / i;
        return result;
    }

    constexpr static std::size_t pkp_membership_constraints =
        pkp_n * membership_constraints_per_subvector;
    constexpr static std::size_t pkp_permutation_constraints = pkp_n;
    constexpr static std::size_t pkp_equation_constraints = pkp_m * pkp_q_bits;
    constexpr static std::size_t qs_extra_challenges = 0;
    constexpr static std::size_t deg = table::degree;
    constexpr static std::size_t owf_num_constraints =
        pkp_membership_constraints + pkp_permutation_constraints + pkp_equation_constraints;

    using OWF_CONSTS = SDSIGN_OWF_CONSTANTS<S, witness_bits, deg, owf_num_constraints, 0, 0, 0>;
    using CONSTS = SDSIGN_CONSTANTS<
        pkp_owf_parameter_set<S, TAU, VOLE_PRG, TREE_PRG, LEAF_HASH, ZERO_BITS_IN_DELTA, BAVC,
                              PARAM_SET, QS_TERM>>;

    constexpr static std::size_t PRG_VOLE_BLOCK_SIZE_SHIFT = []
    {
        if constexpr (VOLE_PRG == prg::aes_secpar_fixed_key_ctr && S == secpar::L5)
            return 1;
        else
            return 0;
    }();
    constexpr static std::size_t PRG_VOLE_BLOCKS_SHIFT =
        VOLE_BLOCK_SHIFT - PRG_VOLE_BLOCK_SIZE_SHIFT;
    constexpr static std::size_t VOLE_WIDTH_SHIFT =
        AES_PREFERRED_WIDTH_SHIFT - PRG_VOLE_BLOCKS_SHIFT;

    using prg_t = prg_type_t<S, VOLE_PRG>;
    using leaf_hash_t = leaf_hash_type_t<S, tau_v, LEAF_HASH>;
    using tree_prg_t = prg_type_t<S, TREE_PRG>;
    using vole_prg_t = prg_type_t<S, VOLE_PRG>;
    using seed_block_t = block_secpar<S>;
    using digest_block_t = block_2secpar<S>;
    using field_t = poly_secpar<S>;
    using wide_field_t = poly_2secpar<S>;
    using bavc_t = bavc_type_t<S, tau_v, delta_bits_v, TREE_PRG, LEAF_HASH, VOLE_WIDTH_SHIFT,
                               BAVC.first, BAVC.second>;

    constexpr static bool use_grinding =
        (zero_bits_in_delta_v > 0) || (BAVC.first != bavc::ggm_forest);
    constexpr static std::size_t grinding_counter_size = use_grinding ? 4 : 0;
    constexpr static std::size_t salt_bytes = CONSTS::SALT_BYTES;
    constexpr static std::size_t digest_bytes = CONSTS::DIGEST_BYTES;
    constexpr static std::size_t commitment_bytes = CONSTS::COMMITMENT_BYTES;
    constexpr static std::size_t response_bytes = CONSTS::RESPONSE_BYTES;
};

using pkp_128 = pkp_owf_parameter_set<secpar::L1>;
using pkp_192 = pkp_owf_parameter_set<secpar::L3>;
using pkp_256 = pkp_owf_parameter_set<secpar::L5>;

using pkp_128_s = pkp_owf_parameter_set<secpar::L1, 11, prg::aes_ctr, prg::aes_ctr,
                                        leaf_hash::crh, 7,
                                        std::pair<bavc, std::size_t>{bavc::one_tree, 106}>;
using pkp_128_f = pkp_owf_parameter_set<secpar::L1, 16, prg::aes_ctr, prg::aes_ctr,
                                        leaf_hash::crh, 7,
                                        std::pair<bavc, std::size_t>{bavc::one_tree, 110}>;
using pkp_192_s = pkp_owf_parameter_set<secpar::L3, 16, prg::aes_ctr, prg::aes_ctr,
                                        leaf_hash::crh, 8,
                                        std::pair<bavc, std::size_t>{bavc::one_tree, 166}>;
using pkp_192_f = pkp_owf_parameter_set<secpar::L3, 24, prg::aes_ctr, prg::aes_ctr,
                                        leaf_hash::crh, 8,
                                        std::pair<bavc, std::size_t>{bavc::one_tree, 166}>;
using pkp_256_s = pkp_owf_parameter_set<secpar::L5, 22, prg::aes_ctr, prg::aes_ctr,
                                        leaf_hash::crh, 6,
                                        std::pair<bavc, std::size_t>{bavc::one_tree, 222}>;
using pkp_256_f = pkp_owf_parameter_set<secpar::L5, 32, prg::aes_ctr, prg::aes_ctr,
                                        leaf_hash::crh, 6,
                                        std::pair<bavc, std::size_t>{bavc::one_tree, 220}>;

#define ALL_PKP_OWF_INSTANCES pkp_128_s, pkp_128_f, pkp_192_s, pkp_192_f, pkp_256_s, pkp_256_f

} // namespace sdsign

#endif
