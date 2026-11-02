#ifndef SDSIGN_RSD_PARAMETERS_HPP
#define SDSIGN_RSD_PARAMETERS_HPP

#include "vole_parameters.hpp"
#include "optimal_encoding.hpp"

#include <array>
#include <cstddef>
#include <limits>
#include <type_traits>

namespace sdsign
{

template <typename Params, std::size_t Eta, typename = void> struct selected_optimal_encoding
{
    using type = optimal_encoding_detail::encoding<Eta>;
};

template <typename Params, std::size_t Eta>
struct selected_optimal_encoding<Params, Eta, std::void_t<typename Params::optimal_encoding_t>>
{
    using type = typename Params::optimal_encoding_t;
};

template <secpar S, std::size_t PARAM_SET = 0> struct rsd_table_parameters;

// =============================================================================
// P0: Optimal parameters
// =============================================================================

template <> struct rsd_table_parameters<secpar::L1, 0>
{
    constexpr static elementary_encoding elementary_encoding_v =
        elementary_encoding::optimal;
    constexpr static std::size_t encoding_eta = 10;
    constexpr static std::size_t rsd_n = 16896;
    constexpr static std::size_t rsd_w = 44;
    constexpr static std::size_t rsd_codim = 392;
    constexpr static std::size_t num_var_blocks = 1;
    constexpr static std::array<std::size_t, num_var_blocks> block_sizes = {10};
    constexpr static std::array<std::size_t, num_var_blocks> block_wts = {0};
    constexpr static std::size_t deg = 4;
};

template <> struct rsd_table_parameters<secpar::L3, 0>
{
    constexpr static elementary_encoding elementary_encoding_v =
        elementary_encoding::optimal;
    constexpr static std::size_t encoding_eta = 11;
    constexpr static std::size_t rsd_n = 31900;
    constexpr static std::size_t rsd_w = 58;
    constexpr static std::size_t rsd_codim = 536;
    constexpr static std::size_t num_var_blocks = 1;
    constexpr static std::array<std::size_t, num_var_blocks> block_sizes = {11};
    constexpr static std::array<std::size_t, num_var_blocks> block_wts = {0};
    constexpr static std::size_t deg = 4;
};

template <> struct rsd_table_parameters<secpar::L5, 0>
{
    constexpr static elementary_encoding elementary_encoding_v =
        elementary_encoding::optimal;
    constexpr static std::size_t encoding_eta = 12;
    constexpr static std::size_t rsd_n = 26255;
    constexpr static std::size_t rsd_w = 89;
    constexpr static std::size_t rsd_codim = 736;
    constexpr static std::size_t num_var_blocks = 1;
    constexpr static std::array<std::size_t, num_var_blocks> block_sizes = {12};
    constexpr static std::array<std::size_t, num_var_blocks> block_wts = {0};
    constexpr static std::size_t deg = 3;
};

// =============================================================================
// P1: Hamming-ball parameters
// =============================================================================

template <> struct rsd_table_parameters<secpar::L1, 1>
{
    constexpr static elementary_encoding elementary_encoding_v = elementary_encoding::hamming_ball;
    constexpr static std::size_t rsd_n = 16940;
    constexpr static std::size_t rsd_w = 44;
    constexpr static std::size_t rsd_codim = 384;
    constexpr static std::size_t num_var_blocks = 2;
    constexpr static std::array<std::size_t, num_var_blocks> block_sizes = {2, 9};
    constexpr static std::array<std::size_t, num_var_blocks> block_wts = {1, 3};
    constexpr static std::size_t deg = 4;
};

template <> struct rsd_table_parameters<secpar::L3, 1>
{
    constexpr static elementary_encoding elementary_encoding_v = elementary_encoding::hamming_ball;
    constexpr static std::size_t rsd_n = 24245;
    constexpr static std::size_t rsd_w = 65;
    constexpr static std::size_t rsd_codim = 576;
    constexpr static std::size_t num_var_blocks = 2;
    constexpr static std::array<std::size_t, num_var_blocks> block_sizes = {2, 9};
    constexpr static std::array<std::size_t, num_var_blocks> block_wts = {1, 3};
    constexpr static std::size_t deg = 4;
};

template <> struct rsd_table_parameters<secpar::L5, 1>
{
    constexpr static elementary_encoding elementary_encoding_v = elementary_encoding::hamming_ball;
    constexpr static std::size_t rsd_n = 25392;
    constexpr static std::size_t rsd_w = 92;
    constexpr static std::size_t rsd_codim = 752;
    constexpr static std::size_t num_var_blocks = 2;
    constexpr static std::array<std::size_t, num_var_blocks> block_sizes = {2, 8};
    constexpr static std::array<std::size_t, num_var_blocks> block_wts = {1, 3};
    constexpr static std::size_t deg = 4;
};

// =============================================================================

template <secpar S, std::size_t TAU, owf OWF = owf::rsd, prg VOLE_PRG = prg::aes_ctr,
          prg TREE_PRG = prg::aes_ctr, leaf_hash LEAF_HASH = leaf_hash::crh,
          std::size_t ZERO_BITS_IN_DELTA = 0,
          std::pair<bavc, std::size_t> BAVC = std::pair<bavc, std::size_t>{bavc::ggm_forest, 0},
          std::size_t PARAM_SET = 0, quicksilver_term QS_TERM = quicksilver_term::leading,
          proof_system_set PROOF_SYSTEM_SET = proof_system_set::set0>
struct sdsign_parameter_set
{
    using rsd_params = rsd_table_parameters<S, PARAM_SET>;

    constexpr static secpar secpar_v = S;
    constexpr static std::size_t tau_v = TAU;
    constexpr static owf owf_v = OWF;
    constexpr static std::size_t param_set_v = PARAM_SET;
    constexpr static proof_system_set proof_system_set_v = PROOF_SYSTEM_SET;
    constexpr static elementary_encoding elementary_encoding_v =
        rsd_params::elementary_encoding_v;
    constexpr static quicksilver_term quicksilver_term_v = QS_TERM;
    constexpr static prg prg_v = VOLE_PRG;
    constexpr static prg vole_prg_v = VOLE_PRG;
    constexpr static prg tree_prg_v = TREE_PRG;
    constexpr static leaf_hash leaf_hash_v = LEAF_HASH;
    constexpr static std::size_t zero_bits_in_delta_v = ZERO_BITS_IN_DELTA;

    constexpr static std::size_t secpar_bits = secpar_to_bits(S);
    constexpr static std::size_t secpar_bytes = secpar_to_bytes(S);
    constexpr static std::size_t delta_bits_v = secpar_bits - zero_bits_in_delta_v;

    constexpr static std::size_t rsd_n = rsd_params::rsd_n;
    constexpr static std::size_t rsd_w = rsd_params::rsd_w;
    constexpr static std::size_t rsd_codim = rsd_params::rsd_codim;
    constexpr static std::size_t num_var_blocks = rsd_params::num_var_blocks;
    constexpr static std::array<std::size_t, num_var_blocks> block_sizes =
        rsd_params::block_sizes;
    constexpr static std::array<std::size_t, num_var_blocks> block_wts = rsd_params::block_wts;
    constexpr static std::size_t deg = rsd_params::deg;
    constexpr static bool is_optimal_encoding =
        elementary_encoding_v == elementary_encoding::optimal;
    constexpr static std::size_t encoding_eta = []
    {
        if constexpr (is_optimal_encoding)
            return rsd_params::encoding_eta;
        else
            return std::size_t{0};
    }();
    using optimal_encoding_t =
        typename selected_optimal_encoding<rsd_params, encoding_eta>::type;

    constexpr static std::size_t input_reduced_bits = []
    {
        if constexpr (is_optimal_encoding)
            return encoding_eta;
        std::size_t total = 0;
        for (std::size_t b = 0; b < num_var_blocks; ++b)
            total += block_sizes[b];
        return total;
    }();

    constexpr static std::size_t witness_rows = rsd_w;
    constexpr static std::size_t witness_raw_bits = rsd_w * input_reduced_bits;
    constexpr static std::size_t witness_bits = ((witness_raw_bits + 7) / 8) * 8;
    constexpr static std::size_t witness_bytes = witness_bits / 8;

    constexpr static std::size_t witness_extended_subvector_bits = []
    {
        if constexpr (is_optimal_encoding)
            return encoding_eta;
        std::size_t total = 0;
        for (std::size_t b = 0; b < num_var_blocks; ++b)
            total += block_sizes[b];
        return total;
    }();
    constexpr static std::size_t witness_extended_bits = rsd_w * witness_extended_subvector_bits;
    constexpr static std::size_t witness_extended_bytes = (witness_extended_bits + 7) / 8;

    constexpr static std::size_t prg_seed_bytes = secpar_bytes;
    constexpr static std::size_t y_vector_len =
        (rsd_params::rsd_codim + secpar_bits - 1) / secpar_bits;
    constexpr static std::size_t qs_extra_challenges = y_vector_len;
    constexpr static std::size_t packed_public_key_bytes =
        rsd_params::rsd_codim / 8 + prg_seed_bytes;
    constexpr static std::size_t unpacked_public_key_bytes =
        y_vector_len * secpar_bytes + prg_seed_bytes;
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
        const std::size_t k = (r < (n - r)) ? r : (n - r);
        std::size_t result = 1;
        for (std::size_t i = 1; i <= k; ++i)
            result = (result * (n - k + i)) / i;
        return result;
    }

    constexpr static std::size_t elementary_vector_len = rsd_n / rsd_w;

    constexpr static std::size_t sum_block_choose = []
    {
        std::size_t total = 0;
        for (std::size_t i = 0; i < num_var_blocks; ++i)
            total += ncr(block_sizes[i], block_wts[i] + 1);
        return total;
    }();

    constexpr static std::size_t membership_constraints_per_subvector = []
    {
        if constexpr (is_optimal_encoding)
            return optimal_encoding_t::membership_count;
        else
            return sum_block_choose;
    }();

    constexpr static std::size_t owf_mul_block_M(std::size_t block_idx)
    {
        std::size_t total = 0;
        for (std::size_t t = 0; t <= block_wts[block_idx]; ++t)
            total += ncr(block_sizes[block_idx], t);
        return total;
    }

    constexpr static std::size_t elementary_domain_size = []
    {
        if constexpr (is_optimal_encoding)
            return optimal_encoding_t::domain_size;
        std::size_t total = 1;
        for (std::size_t b = 0; b < num_var_blocks; ++b)
            total *= owf_mul_block_M(b);
        return total;
    }();

    static_assert(rsd_n % rsd_w == 0, "rsd_n must be divisible by rsd_w.");
    static_assert(elementary_vector_len <= elementary_domain_size,
                  "Actual elementary-vector segment length must fit in the block domain.");

    constexpr static std::size_t owf_mul_block_L(std::size_t block_idx)
    {
        std::size_t total = 0;
        for (std::size_t t = 1; t <= block_wts[block_idx]; ++t)
            total += ncr(block_sizes[block_idx], t);
        return total;
    }

    constexpr static std::size_t owf_mul_c_pre = []
    {
        if constexpr (is_optimal_encoding)
            return optimal_encoding_t::monomial_count - encoding_eta - 1;
        std::size_t total = 0;
        for (std::size_t b = 0; b < num_var_blocks; ++b)
            for (std::size_t t = 2; t <= block_wts[b] + 1; ++t)
                total += ncr(block_sizes[b], t);
        return total;
    }();

    constexpr static std::size_t
    owf_mul_c_ip_for_order(const std::array<std::size_t, num_var_blocks>& order)
    {
        std::size_t total = 0;
        std::size_t prefix_w_sum = 0;
        for (std::size_t m = 0; m < num_var_blocks; ++m)
        {
            std::size_t suffix_M_prod = 1;
            for (std::size_t r = m + 1; r < num_var_blocks; ++r)
                suffix_M_prod *= owf_mul_block_M(order[r]);

            total += suffix_M_prod * (1 + prefix_w_sum) * owf_mul_block_L(order[m]);
            prefix_w_sum += block_wts[order[m]];
        }
        return total;
    }

    constexpr static std::size_t
    owf_mul_c_ip_min_impl(std::array<std::size_t, num_var_blocks>& order,
                          std::array<bool, num_var_blocks>& used, std::size_t depth,
                          std::size_t best_so_far,
                          std::array<std::size_t, num_var_blocks>& best_order)
    {
        if (depth == num_var_blocks)
        {
            const std::size_t c = owf_mul_c_ip_for_order(order);
            if (c < best_so_far)
            {
                best_order = order;
                return c;
            }
            return (c < best_so_far) ? c : best_so_far;
        }

        for (std::size_t b = 0; b < num_var_blocks; ++b)
        {
            if (used[b])
                continue;
            used[b] = true;
            order[depth] = b;
            best_so_far = owf_mul_c_ip_min_impl(order, used, depth + 1, best_so_far, best_order);
            used[b] = false;
        }
        return best_so_far;
    }

    constexpr static std::array<std::size_t, num_var_blocks> owf_mul_best_order = []
    {
        std::array<std::size_t, num_var_blocks> order{};
        std::array<bool, num_var_blocks> used{};
        std::array<std::size_t, num_var_blocks> best_order{};
        (void)owf_mul_c_ip_min_impl(order, used, 0, std::numeric_limits<std::size_t>::max(),
                                    best_order);
        return best_order;
    }();

    constexpr static std::array<std::size_t, num_var_blocks> FOLD_ORDER = owf_mul_best_order;
    constexpr static std::size_t owf_mul_c_ip = []
    {
        if constexpr (is_optimal_encoding)
            return elementary_domain_size - 1;
        else
            return owf_mul_c_ip_for_order(FOLD_ORDER);
    }();
    constexpr static std::size_t owf_mul_c_total = owf_mul_c_pre + owf_mul_c_ip;
    constexpr static std::size_t owf_num_constraints =
        y_vector_len + rsd_w * membership_constraints_per_subvector;

    using OWF_CONSTS = SDSIGN_OWF_CONSTANTS<S, witness_bits, deg, owf_num_constraints,
                                            owf_mul_c_pre, owf_mul_c_ip, owf_mul_c_total>;
    using CONSTS =
        SDSIGN_CONSTANTS<sdsign_parameter_set<S, TAU, OWF, VOLE_PRG, TREE_PRG, LEAF_HASH,
                                              ZERO_BITS_IN_DELTA, BAVC, PARAM_SET, QS_TERM>>;

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

    using bavc_t = bavc_type_t<S, tau_v, delta_bits_v, TREE_PRG, LEAF_HASH, VOLE_WIDTH_SHIFT,
                               BAVC.first, BAVC.second>;

    constexpr static bool use_grinding =
        (zero_bits_in_delta_v > 0) || (BAVC.first != bavc::ggm_forest);
    constexpr static std::size_t grinding_counter_size = use_grinding ? 4 : 0;

    constexpr static std::size_t salt_bytes = CONSTS::SALT_BYTES;
    constexpr static std::size_t digest_bytes = CONSTS::DIGEST_BYTES;
    constexpr static std::size_t commitment_bytes = CONSTS::COMMITMENT_BYTES;
    constexpr static std::size_t response_bytes = CONSTS::RESPONSE_BYTES;

    using prg_t = prg_type_t<S, VOLE_PRG>;
    using leaf_hash_t = leaf_hash_type_t<S, tau_v, LEAF_HASH>;
    using tree_prg_t = prg_type_t<S, TREE_PRG>;
    using vole_prg_t = prg_type_t<S, VOLE_PRG>;
    using seed_block_t = block_secpar<S>;
    using digest_block_t = block_2secpar<S>;
    using field_t = poly_secpar<S>;
    using wide_field_t = poly_2secpar<S>;
};

template <secpar S, proof_system_variant V, proof_system_set SET = proof_system_set::set0,
          std::size_t PARAM_SET = 0, quicksilver_term QS_TERM = quicksilver_term::leading>
using sdsign_rsd_parameter_set =
    sdsign_parameter_set<S, proof_system_parameters<S, V, SET>::tau, owf::rsd, prg::aes_ctr,
                         prg::aes_ctr, proof_system_parameters<S, V, SET>::leaf_hash_v,
                         proof_system_parameters<S, V, SET>::vole_width_shift,
                         proof_system_parameters<S, V, SET>::bavc_param, PARAM_SET, QS_TERM, SET>;

using sdsign_128_s =
    sdsign_rsd_parameter_set<secpar::L1, proof_system_variant::s, proof_system_set::set0>;
using sdsign_128_f =
    sdsign_rsd_parameter_set<secpar::L1, proof_system_variant::f, proof_system_set::set0>;
using sdsign_192_s =
    sdsign_rsd_parameter_set<secpar::L3, proof_system_variant::s, proof_system_set::set0>;
using sdsign_192_f =
    sdsign_rsd_parameter_set<secpar::L3, proof_system_variant::f, proof_system_set::set0>;
using sdsign_256_s =
    sdsign_rsd_parameter_set<secpar::L5, proof_system_variant::s, proof_system_set::set0>;
using sdsign_256_f =
    sdsign_rsd_parameter_set<secpar::L5, proof_system_variant::f, proof_system_set::set0>;

#define ALL_SDSIGN_INSTANCES                                                                       \
    sdsign_128_s, sdsign_128_f, sdsign_192_s, sdsign_192_f, sdsign_256_s, sdsign_256_f

} // namespace sdsign

#endif
