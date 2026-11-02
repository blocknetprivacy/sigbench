#ifndef SDSIGN_RING_SIGNATURE_SELECTOR_HPP
#define SDSIGN_RING_SIGNATURE_SELECTOR_HPP

#include "ring_signature/parameters.hpp"

#include <array>
#include <bit>
#include <cstddef>
#include <cstdint>
#include <limits>
#include <utility>

namespace sdsign::ring
{

constexpr std::size_t radius_two_ball_size(std::size_t eta)
{
    return 1 + eta + eta * (eta - 1) / 2;
}

constexpr uint8_t ct_equal_size(std::size_t x, std::size_t y)
{
    constexpr std::size_t top_bit = std::numeric_limits<std::size_t>::digits - 1;
    const std::size_t difference = x ^ y;
    return static_cast<uint8_t>(1u ^ ((difference | (std::size_t{0} - difference)) >> top_bit));
}

// Divide a secret numerator by a public compile-time divisor with a fixed
// schedule.  The restoring division loop count depends only on the public
// maximum bit length.  It uses the subtraction borrow bit instead of a branch
// or a secret-indexed lookup.
template <std::size_t Divisor, std::size_t Bits>
constexpr std::pair<std::size_t, std::size_t> ct_divmod_public(std::size_t numerator)
{
    static_assert(Divisor > 0);
    static_assert(Bits > 0 && Bits < std::numeric_limits<std::size_t>::digits);
    constexpr std::size_t top_bit = std::numeric_limits<std::size_t>::digits - 1;
    std::size_t quotient = 0;
    std::size_t remainder = 0;
    for (std::size_t bit = Bits; bit-- > 0;)
    {
        remainder = (remainder << 1) | ((numerator >> bit) & 1u);
        const std::size_t difference = remainder - Divisor;
        const std::size_t ge = 1u ^ (difference >> top_bit);
        const std::size_t mask = std::size_t{0} - ge;
        remainder = (difference & mask) | (remainder & ~mask);
        quotient |= ge << bit;
    }
    return {quotient, remainder};
}

// Rank order: empty set, singletons in coordinate order, then pairs in
// lexicographic coordinate order.  The scan is fixed by eta; rank is never
// used as an array index and never controls a branch.
template <std::size_t Eta>
constexpr std::array<uint8_t, Eta> radius_two_unrank_ct(std::size_t rank)
{
    static_assert(Eta > 0);
    std::array<uint8_t, Eta> out{};
    std::size_t candidate = 1;

    for (std::size_t i = 0; i < Eta; ++i, ++candidate)
    {
        const uint8_t match = ct_equal_size(rank, candidate);
        out[i] ^= match;
    }
    for (std::size_t i = 0; i < Eta; ++i)
        for (std::size_t j = i + 1; j < Eta; ++j, ++candidate)
        {
            const uint8_t match = ct_equal_size(rank, candidate);
            out[i] ^= match;
            out[j] ^= match;
        }
    return out;
}

template <std::size_t RingSize> struct selector_encoding
{
    using params = selector_parameters<RingSize>;
    static constexpr std::size_t left_size = radius_two_ball_size(params::eta_left);
    static constexpr std::size_t right_size = radius_two_ball_size(params::eta_right);
    static constexpr std::size_t capacity = left_size * right_size;

    static_assert(RingSize <= capacity);

    struct representative
    {
        std::array<uint8_t, params::eta_left> left{};
        std::array<uint8_t, params::eta_right> right{};
    };

    // Fixed-schedule encoding.  In particular, there is no secret-indexed
    // lookup of a ring member.  The canonical representative of index i has
    // flat rank i in the Cartesian product of the two balls.
    static constexpr representative encode(std::size_t signer_index)
    {
        constexpr std::size_t index_bits = std::bit_width(RingSize - 1);
        const auto [selected_left_rank, selected_right_rank] =
            ct_divmod_public<right_size, index_bits>(signer_index);
        return representative{
            radius_two_unrank_ct<params::eta_left>(selected_left_rank),
            radius_two_unrank_ct<params::eta_right>(selected_right_rank),
        };
    }

    template <std::size_t Eta>
    static constexpr uint8_t ball_indicator(const std::array<uint8_t, Eta>& bits,
                                            std::size_t rank)
    {
        if (rank == 0)
        {
            uint8_t value = 1;
            for (std::size_t i = 0; i < Eta; ++i)
                value ^= bits[i];
            for (std::size_t i = 0; i < Eta; ++i)
                for (std::size_t j = i + 1; j < Eta; ++j)
                    value ^= static_cast<uint8_t>(bits[i] & bits[j]);
            return static_cast<uint8_t>(value & 1);
        }

        if (rank <= Eta)
        {
            const std::size_t selected = rank - 1;
            uint8_t value = bits[selected];
            for (std::size_t j = 0; j < Eta; ++j)
                if (j != selected)
                    value ^= static_cast<uint8_t>(bits[selected] & bits[j]);
            return static_cast<uint8_t>(value & 1);
        }

        std::size_t candidate = Eta + 1;
        uint8_t value = 0;
        for (std::size_t i = 0; i < Eta; ++i)
            for (std::size_t j = i + 1; j < Eta; ++j, ++candidate)
                value ^= static_cast<uint8_t>((rank == candidate) & bits[i] & bits[j]);
        return static_cast<uint8_t>(value & 1);
    }

    // z_i = u_a v_b.  The loop bounds and memory accesses depend only on the
    // public member index.  The same decomposition is used later for folded
    // syndrome contraction, so z is not materialized in the signing path.
    static constexpr uint8_t indicator(const representative& rep, std::size_t member_index)
    {
        const std::size_t left_rank = member_index / right_size;
        const std::size_t right_rank = member_index % right_size;
        return static_cast<uint8_t>(
            ball_indicator(rep.left, left_rank) & ball_indicator(rep.right, right_rank));
    }

    template <std::size_t Eta>
    static constexpr bool block_is_member(const std::array<uint8_t, Eta>& bits)
    {
        std::size_t weight = 0;
        for (uint8_t bit : bits)
        {
            if (bit > 1)
                return false;
            weight += bit;
        }
        return weight <= 2;
    }

    static constexpr bool is_valid(const representative& rep)
    {
        if (!block_is_member(rep.left) || !block_is_member(rep.right))
            return false;
        uint8_t selected = 0;
        for (std::size_t i = 0; i < RingSize; ++i)
            selected ^= indicator(rep, i);
        return selected == 1;
    }
};

} // namespace sdsign::ring

#endif
