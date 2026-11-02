#ifndef SDSIGN_RING_SIGNATURE_CONSTRAINTS_INC
#define SDSIGN_RING_SIGNATURE_CONSTRAINTS_INC

#include "ring_signature/constraints.hpp"
#include "ring_signature/profile.hpp"
#include "../sd_owf_proof.inc"

#include <algorithm>
#include <array>
#include <cstddef>
#include <cstring>

namespace sdsign::ring::detail
{

template <typename QS, std::size_t Eta>
using qs_bit_array = std::array<quicksilver_gf2<QS, 1>, Eta>;

template <typename QS, std::size_t Eta>
struct ball_cache
{
    static constexpr std::size_t indicator_count = radius_two_ball_size(Eta);
    qs_bit_array<QS, Eta> bits{};
    std::array<quicksilver_gf2<QS, 2>, Eta * Eta> pairs{};
    std::array<quicksilver_gf2<QS, 2>, indicator_count> indicators{};

    const quicksilver_gf2<QS, 2>& pair(std::size_t i, std::size_t j) const
    {
        return pairs[i * Eta + j];
    }
};

template <typename QS, std::size_t Eta>
ball_cache<QS, Eta> make_ball_cache(QS* state, const qs_bit_array<QS, Eta>& bits)
{
    ball_cache<QS, Eta> cache;
    cache.bits = bits;
    for (std::size_t i = 0; i < Eta; ++i)
        for (std::size_t j = i + 1; j < Eta; ++j)
            cache.pairs[i * Eta + j] = bits[i] * bits[j];

    auto empty = quicksilver_gf2<QS, 2>(poly1::set_all(1), state);
    for (std::size_t i = 0; i < Eta; ++i)
        empty += quicksilver_gf2<QS, 2>(bits[i]);
    for (std::size_t i = 0; i < Eta; ++i)
        for (std::size_t j = i + 1; j < Eta; ++j)
            empty += cache.pair(i, j);
    cache.indicators[0] = empty;

    for (std::size_t i = 0; i < Eta; ++i)
    {
        auto singleton = quicksilver_gf2<QS, 2>(bits[i]);
        for (std::size_t j = 0; j < i; ++j)
            singleton += cache.pair(j, i);
        for (std::size_t j = i + 1; j < Eta; ++j)
            singleton += cache.pair(i, j);
        cache.indicators[1 + i] = singleton;
    }
    std::size_t rank = 1 + Eta;
    for (std::size_t i = 0; i < Eta; ++i)
        for (std::size_t j = i + 1; j < Eta; ++j)
            cache.indicators[rank++] = cache.pair(i, j);
    return cache;
}

template <typename QS, std::size_t Eta>
void rebind_ball_cache(ball_cache<QS, Eta>& cache, QS* state)
{
    if constexpr (QS::is_verifier)
    {
        for (auto& bit : cache.bits)
            bit.delta_powers = &state->delta_powers;
        for (auto& pair : cache.pairs)
            pair.delta_powers = &state->delta_powers;
        for (auto& indicator : cache.indicators)
            indicator.delta_powers = &state->delta_powers;
    }
}

template <typename QS, std::size_t Eta>
void add_radius_two_membership(QS* state, const ball_cache<QS, Eta>& cache)
{
    for (std::size_t i = 0; i < Eta; ++i)
        for (std::size_t j = i + 1; j < Eta; ++j)
            for (std::size_t k = j + 1; k < Eta; ++k)
                state->add_constraint(
                    quicksilver_gfsecpar<QS, 3>(cache.pair(i, j) * cache.bits[k]));
}

template <typename RP, typename QS>
auto load_selector(QS* state)
{
    using selector = selector_encoding<RP::ring_size>;
    using SP = typename selector::params;
    qs_bit_array<QS, SP::eta_left> left{};
    qs_bit_array<QS, SP::eta_right> right{};
    for (std::size_t bit = 0; bit < SP::eta_left; ++bit)
        left[bit] = state->get_witness_bit(RP::selector_extended_offset + bit);
    for (std::size_t bit = 0; bit < SP::eta_right; ++bit)
        right[bit] =
            state->get_witness_bit(RP::selector_extended_offset + SP::eta_left + bit);
    return std::pair{left, right};
}

template <typename RP, typename QS, typename LeftCache, typename RightCache>
void add_selector_constraints(QS* state, const LeftCache& left, const RightCache& right)
{
    using selector = selector_encoding<RP::ring_size>;
    add_radius_two_membership(state, left);
    add_radius_two_membership(state, right);

    constexpr std::size_t full_left_rows = RP::ring_size / selector::right_size;
    constexpr std::size_t partial_right = RP::ring_size % selector::right_size;
    static_assert(partial_right != 0, "the boundary formula expects a partial final row");

    // Invalid = all representatives after the partial row, plus the unused
    // suffix of that row.  Ball membership makes the indicators one-hot.
    auto invalid_left = quicksilver_gf2<QS, 2>(poly1::set_zero(), state);
    for (std::size_t rank = full_left_rows + 1; rank < selector::left_size; ++rank)
        invalid_left += left.indicators[rank];
    const auto& partial_left = left.indicators[full_left_rows];
    auto invalid_right = quicksilver_gf2<QS, 2>(poly1::set_zero(), state);
    for (std::size_t rank = partial_right; rank < selector::right_size; ++rank)
        invalid_right += right.indicators[rank];
    state->add_constraint(
        quicksilver_gfsecpar<QS, 4>(invalid_left) + partial_left * invalid_right);
}

template <typename RP, bool Verifier, typename QS, typename LeftCache, typename RightCache>
quicksilver_gfsecpar<QS, 4>
fold_selected_syndrome_verifier(
    QS* state, const public_ring<typename RP::base_parameter, RP::ring_size>& ring,
    const LeftCache& left, const RightCache& right)
{
    static_assert(Verifier);
    using Base = typename RP::base_parameter;
    using selector = selector_encoding<RP::ring_size>;
    using field_t = poly_secpar<RP::secpar_v>;
    constexpr std::size_t base_challenge_bytes =
        (3 * secpar_to_bits(RP::secpar_v) + 64) / 8;

    std::array<field_t, Base::y_vector_len> alpha{};
    for (std::size_t row = 0; row < Base::y_vector_len; ++row)
        alpha[row] = field_t::load_dup(state->challenge_bytes + base_challenge_bytes +
                                       row * RP::secpar_bytes);

    auto selected = quicksilver_gfsecpar<QS, 4>(poly1::set_zero(), state);
    for (std::size_t left_rank = 0; left_rank < selector::left_size; ++left_rank)
    {
        const std::size_t row_start = left_rank * selector::right_size;
        const std::size_t right_limit =
            row_start >= RP::ring_size
                ? 0
                : std::min(selector::right_size, RP::ring_size - row_start);
        if (right_limit == 0)
            continue;

        std::array<polysecpar_dot_accumulator<RP::secpar_v>, Base::y_vector_len> row_acc;
        for (std::size_t right_rank = 0; right_rank < right_limit; ++right_rank)
        {
            const std::size_t member = row_start + right_rank;
            const auto& indicator_mac = right.indicators[right_rank].mac;
            for (std::size_t row = 0; row < Base::y_vector_len; ++row)
                row_acc[row].add(field_t::load_dup(&ring.syndromes[member][row]), indicator_mac);
        }

        polysecpar_dot_accumulator<RP::secpar_v> alpha_acc;
        for (std::size_t row = 0; row < Base::y_vector_len; ++row)
            alpha_acc.add(alpha[row], row_acc[row].reduced());
        auto right_contraction = quicksilver_gfsecpar<QS, 2>(poly1::set_zero(), state);
        right_contraction.mac = alpha_acc.reduced();
        right_contraction.delta_powers = &state->delta_powers;
        selected += left.indicators[left_rank] * right_contraction;
    }
    return selected;
}

template <typename RP, bool Verifier, typename QS, typename LeftCache, typename RightCache>
quicksilver_gfsecpar<QS, 4>
fold_selected_syndrome(QS* state,
                       const public_ring<typename RP::base_parameter, RP::ring_size>& ring,
                       const LeftCache& left, const RightCache& right,
                       const std::array<block_secpar<RP::secpar_v>,
                                        RP::y_vector_len>* signer_syndrome,
                       std::size_t signer_index, bool* signer_matches)
{
    using Base = typename RP::base_parameter;
    using selector = selector_encoding<RP::ring_size>;
    using field_t = poly_secpar<RP::secpar_v>;
    constexpr std::size_t base_challenge_bytes =
        (3 * secpar_to_bits(RP::secpar_v) + 64) / 8;

    std::array<field_t, Base::y_vector_len> alpha{};
    for (std::size_t row = 0; row < Base::y_vector_len; ++row)
        alpha[row] = field_t::load_dup(state->challenge_bytes + base_challenge_bytes +
                                       row * RP::secpar_bytes);

    // Tensor contraction: first contract every public row with the right
    // degree-2 indicators, then perform only left_size degree-2 x degree-2
    // secret products.  No N-entry selector vector is materialized.
    auto selected = quicksilver_gfsecpar<QS, 4>(poly1::set_zero(), state);
    std::array<field_t, Base::y_vector_len> selected_public_syndrome{};
    for (std::size_t left_rank = 0; left_rank < selector::left_size; ++left_rank)
    {
        const std::size_t row_start = left_rank * selector::right_size;
        const std::size_t right_limit =
            row_start >= RP::ring_size
                ? 0
                : std::min(selector::right_size, RP::ring_size - row_start);
        if (right_limit == 0)
            continue;

        auto right_contraction = quicksilver_gfsecpar<QS, 2>(poly1::set_zero(), state);
        polysecpar_dot_accumulator<RP::secpar_v> right_acc0;
        polysecpar_dot_accumulator<RP::secpar_v> right_acc1;
        field_t right_value = field_t::set_zero();
        const auto accumulate_coefficient =
            [&](std::size_t right_rank, const field_t& coefficient)
        {
            const auto& indicator = right.indicators[right_rank];
            if constexpr (QS::is_verifier)
            {
                right_acc0.add(coefficient, indicator.mac);
            }
            else
            {
                right_acc0.add(coefficient, indicator.mac.coeffs[0]);
                right_acc1.add(coefficient, indicator.mac.coeffs[1]);
                add_mul_poly1_mask_polysecpar<RP::secpar_v>(
                    right_value, ::sdsign::detail::poly1_to_bit_mask(indicator.value()),
                    coefficient);
            }
        };

        std::size_t right_rank = 0;
        for (; right_rank + 1 < right_limit; right_rank += 2)
        {
            const std::size_t member0 = row_start + right_rank;
            const std::size_t member1 = member0 + 1;
            polysecpar_dot_accumulator<RP::secpar_v> public_acc0;
            polysecpar_dot_accumulator<RP::secpar_v> public_acc1;
            clmul_block signer_mask0{};
            clmul_block signer_mask1{};
            if constexpr (!Verifier)
            {
                signer_mask0 = ::sdsign::detail::poly1_to_bit_mask(
                    poly1::set_all(ct_equal_size(member0, signer_index)));
                signer_mask1 = ::sdsign::detail::poly1_to_bit_mask(
                    poly1::set_all(ct_equal_size(member1, signer_index)));
            }
            for (std::size_t row = 0; row < Base::y_vector_len; ++row)
            {
                const field_t syndrome0 = field_t::load_dup(&ring.syndromes[member0][row]);
                const field_t syndrome1 = field_t::load_dup(&ring.syndromes[member1][row]);
                public_acc0.add(alpha[row], syndrome0);
                public_acc1.add(alpha[row], syndrome1);
                if constexpr (!Verifier)
                {
                    add_mul_poly1_mask_polysecpar<RP::secpar_v>(
                        selected_public_syndrome[row], signer_mask0, syndrome0);
                    add_mul_poly1_mask_polysecpar<RP::secpar_v>(
                        selected_public_syndrome[row], signer_mask1, syndrome1);
                }
            }
            accumulate_coefficient(right_rank, public_acc0.reduced());
            accumulate_coefficient(right_rank + 1, public_acc1.reduced());
        }
        if (right_rank < right_limit)
        {
            const std::size_t member = row_start + right_rank;
            polysecpar_dot_accumulator<RP::secpar_v> public_acc;
            clmul_block signer_mask{};
            if constexpr (!Verifier)
                signer_mask = ::sdsign::detail::poly1_to_bit_mask(
                    poly1::set_all(ct_equal_size(member, signer_index)));
            for (std::size_t row = 0; row < Base::y_vector_len; ++row)
            {
                const field_t syndrome = field_t::load_dup(&ring.syndromes[member][row]);
                public_acc.add(alpha[row], syndrome);
                if constexpr (!Verifier)
                    add_mul_poly1_mask_polysecpar<RP::secpar_v>(
                        selected_public_syndrome[row], signer_mask, syndrome);
            }
            accumulate_coefficient(right_rank, public_acc.reduced());
        }
        if constexpr (QS::is_verifier)
        {
            right_contraction.mac = right_acc0.reduced();
            right_contraction.delta_powers = &state->delta_powers;
        }
        else
        {
            right_contraction.mac.coeffs[0] = right_acc0.reduced();
            right_contraction.mac.coeffs[1] = right_acc1.reduced();
            right_contraction.value() = right_value;
        }
        selected += left.indicators[left_rank] * right_contraction;
    }
    if constexpr (!Verifier)
    {
        SDSIGN_ASSERT(signer_syndrome != nullptr && signer_matches != nullptr);
        uint8_t mismatch = 0;
        const auto* expected = reinterpret_cast<const uint8_t*>(signer_syndrome->data());
        const auto* actual = reinterpret_cast<const uint8_t*>(selected_public_syndrome.data());
        constexpr std::size_t syndrome_bytes = Base::y_vector_len * RP::secpar_bytes;
        for (std::size_t byte = 0; byte < syndrome_bytes; ++byte)
            mismatch |= static_cast<uint8_t>(expected[byte] ^ actual[byte]);
        *signer_matches = mismatch == 0;
    }
    return selected;
}

} // namespace sdsign::ring::detail

namespace sdsign::ring
{

template <typename RP, bool Verifier>
void constraints(quicksilver_state<RP::secpar_v, Verifier, RP::OWF_CONSTS::QS_DEGREE,
                                   RP::quicksilver_term_v>* state,
                 const public_ring<typename RP::base_parameter, RP::ring_size>* ring,
                 uint8_t* folded_poly_coeffs_out,
                 const std::array<block_secpar<RP::secpar_v>,
                                  RP::y_vector_len>* signer_syndrome,
                 std::size_t signer_index, bool* signer_matches)
{
    using QS = quicksilver_state<RP::secpar_v, Verifier, RP::OWF_CONSTS::QS_DEGREE,
                                 RP::quicksilver_term_v>;
    using field_t = poly_secpar<RP::secpar_v>;
    constexpr std::size_t base_explicit =
        RP::rsd_w * RP::membership_constraints_per_subvector;
    constexpr std::size_t padding = RP::y_vector_len;
    static_assert(RP::OWF_CONSTS::OWF_NUM_CONSTRAINTS ==
                  base_explicit + RP::selector_constraints + padding);

    static thread_local std::array<field_t, RP::rsd_n> folded_h_row;
    {
        profile::scope timer(profile::FOLD_H, Verifier);
        sdsign_detail::sdsign_fold_expanded_h_rows_field<RP, Verifier>(
            folded_h_row.data(), folded_h_row.size(), ring->seed_pk, state);
    }

    QS rest_state = *state;
    auto folded_constraint = quicksilver_gfsecpar<QS, 4>(0, &rest_state);
    {
        profile::scope timer(profile::BASE_CONSTRAINTS, Verifier);
        for (std::size_t subvec = 0; subvec < RP::rsd_w; ++subvec)
            add_subvector_constraints_and_folded_ip<RP>(
                state, &rest_state, subvec, subvec * RP::witness_extended_subvector_bits,
                folded_h_row.data(), folded_h_row.size(), folded_constraint);
    }

    const auto [left_bits, right_bits] = detail::load_selector<RP>(state);
    auto selector_caches = [&]()
    {
        profile::scope timer(profile::SELECTOR_CONSTRAINTS, Verifier);
        auto left_cache = detail::make_ball_cache(state, left_bits);
        auto right_cache = detail::make_ball_cache(state, right_bits);
        detail::add_selector_constraints<RP>(state, left_cache, right_cache);
        return std::pair{left_cache, right_cache};
    }();
    auto& left_cache = selector_caches.first;
    auto& right_cache = selector_caches.second;
    // The folded polynomial is accumulated in the copied state.  The cache
    // values are identical, so reuse them; verifier objects only need their
    // delta-powers owner rebound to the copied state.
    {
        profile::scope timer(profile::RING_SYNDROME_CONTRACTION, Verifier);
        detail::rebind_ball_cache(left_cache, &rest_state);
        detail::rebind_ball_cache(right_cache, &rest_state);
        if constexpr (Verifier)
            folded_constraint += detail::fold_selected_syndrome_verifier<RP, Verifier>(
                &rest_state, *ring, left_cache, right_cache);
        else
            folded_constraint += detail::fold_selected_syndrome<RP, Verifier>(
                &rest_state, *ring, left_cache, right_cache, signer_syndrome,
                signer_index, signer_matches);
    }

    if (folded_poly_coeffs_out != nullptr)
    {
        if constexpr (!Verifier)
        {
            for (std::size_t i = 0; i < QS::max_degree; ++i)
            {
                constexpr bool constant = QS::term_v == quicksilver_term::constant;
                const std::size_t coeff = constant ? i + 1 : i;
                folded_constraint.mac.coeffs[coeff].store1(
                    folded_poly_coeffs_out + i * RP::secpar_bytes);
            }
        }
        else
        {
            auto eval = folded_constraint.mac;
            if constexpr (QS::term_v == quicksilver_term::constant)
                eval = mul_polysecpar_reduce<RP::secpar_v>(eval, state->high_coeff_eval_scale);
            eval.store1(folded_poly_coeffs_out);
            std::memset(folded_poly_coeffs_out + RP::secpar_bytes, 0,
                        (QS::max_degree - 1) * RP::secpar_bytes);
        }
    }

    const auto seed = quicksilver_gfsecpar<QS>(state->get_witness_bit(0));
    const auto same = quicksilver_gfsecpar<QS, 4>(seed);
    const auto zero = same + same;
    for (std::size_t i = 0; i < padding; ++i)
        state->add_constraint(zero);
}

} // namespace sdsign::ring

#endif
