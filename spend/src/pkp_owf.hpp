#ifndef SDSIGN_PKP_OWF_HPP
#define SDSIGN_PKP_OWF_HPP

#include "pkp_parameters.hpp"
#include "polynomials.hpp"

#include <array>
#include <cassert>
#include <cstddef>
#include <cstdint>
#include <cstring>

namespace sdsign
{

constexpr std::size_t pkp_ncr(std::size_t n, std::size_t r)
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

constexpr std::size_t pkp_block_domain_size(std::size_t n, std::size_t r,
                                            pkp_domain_model model)
{
    if (model == pkp_domain_model::exact_weight)
        return pkp_ncr(n, r);

    std::size_t total = 0;
    for (std::size_t w = 0; w <= r; ++w)
        total += pkp_ncr(n, w);
    return total;
}

template <typename P> constexpr std::size_t pkp_domain_size()
{
    if constexpr (P::domain_model == pkp_domain_model::optimal)
        return P::representative_capacity;
    std::size_t total = 1;
    for (std::size_t b = 0; b < P::num_var_blocks; ++b)
        total *= pkp_block_domain_size(P::block_sizes[b], P::block_wts[b], P::domain_model);
    return total;
}

template <std::size_t q_bits> struct pkp_field_reduction;

template <> struct pkp_field_reduction<11>
{
    // x^11 + x^2 + 1
    constexpr static uint16_t low_poly = 0x005;
};

template <> struct pkp_field_reduction<12>
{
    // x^12 + x^6 + x^4 + x + 1
    constexpr static uint16_t low_poly = 0x053;
};

template <std::size_t q_bits> struct pkp_binary_field
{
    static_assert(q_bits == 11 || q_bits == 12, "PKP supports q in {2^11, 2^12}.");

    using elem_t = uint16_t;
    constexpr static elem_t mask = static_cast<elem_t>((std::size_t{1} << q_bits) - 1);
    constexpr static elem_t low_poly = pkp_field_reduction<q_bits>::low_poly;

    static constexpr elem_t add(elem_t a, elem_t b) { return static_cast<elem_t>((a ^ b) & mask); }

    static constexpr elem_t mul(elem_t a, elem_t b)
    {
        elem_t aa = static_cast<elem_t>(a & mask);
        elem_t bb = static_cast<elem_t>(b & mask);
        elem_t res = 0;
        for (std::size_t i = 0; i < q_bits; ++i)
        {
            if ((bb & 1u) != 0)
                res ^= aa;
            bb = static_cast<elem_t>(bb >> 1);
            const bool carry = (aa & (elem_t{1} << (q_bits - 1))) != 0;
            aa = static_cast<elem_t>((aa << 1) & mask);
            if (carry)
                aa ^= low_poly;
        }
        return static_cast<elem_t>(res & mask);
    }

    // Fixed-schedule multiplication for secret field elements.  In
    // particular, this is used when key generation combines the public
    // systematic matrix with secret kernel coefficients.  Do not replace the
    // masks with secret-indexed tables.
    static constexpr elem_t mul_consttime(elem_t a, elem_t b)
    {
        elem_t aa = static_cast<elem_t>(a & mask);
        elem_t bb = static_cast<elem_t>(b & mask);
        elem_t res = 0;
        for (std::size_t i = 0; i < q_bits; ++i)
        {
            const elem_t bit_mask = static_cast<elem_t>(0u - (bb & 1u));
            res ^= static_cast<elem_t>(aa & bit_mask);
            bb = static_cast<elem_t>(bb >> 1);

            const elem_t carry = static_cast<elem_t>((aa >> (q_bits - 1)) & 1u);
            const elem_t carry_mask = static_cast<elem_t>(0u - carry);
            aa = static_cast<elem_t>((aa << 1) & mask);
            aa ^= static_cast<elem_t>(low_poly & carry_mask);
        }
        return static_cast<elem_t>(res & mask);
    }

    static constexpr elem_t square(elem_t a) { return mul(a, a); }

    static constexpr elem_t pow(elem_t a, std::size_t e)
    {
        elem_t result = 1;
        elem_t base = static_cast<elem_t>(a & mask);
        while (e != 0)
        {
            if ((e & 1u) != 0)
                result = mul(result, base);
            e >>= 1;
            if (e != 0)
                base = square(base);
        }
        return result;
    }

    static constexpr elem_t inv(elem_t a)
    {
        return a == 0 ? 0 : pow(a, (std::size_t{1} << q_bits) - 2);
    }
};

template <typename P> using pkp_gfq = pkp_binary_field<P::pkp_q_bits>;

template <typename P>
void pkp_compute_hpx(uint16_t* out_m, const uint16_t* h_col_major, const uint16_t* x,
                     const uint16_t* permutation)
{
    using F = pkp_gfq<P>;
    static_assert(P::owf_v == owf::pkp, "pkp_compute_hpx expects a PKP parameter set.");
    static_assert(pkp_domain_size<P>() >= P::pkp_n, "PKP encoding domain must cover n.");

    std::memset(out_m, 0, P::pkp_m * sizeof(uint16_t));
    for (std::size_t i = 0; i < P::pkp_n; ++i)
    {
        const std::size_t col = permutation[i];
        assert(col < P::pkp_n);
        if (col >= P::pkp_n)
            continue;
        const uint16_t xi = static_cast<uint16_t>(x[i] & F::mask);
        if (xi == 0)
            continue;

        const uint16_t* h_col = h_col_major + col * P::pkp_m;
        for (std::size_t row = 0; row < P::pkp_m; ++row)
            out_m[row] ^= F::mul(h_col[row], xi);
    }
}

template <typename P>
void pkp_precompute_scaled_h_columns(uint16_t* scaled_i_col_row, const uint16_t* h_col_major,
                                     const uint16_t* x)
{
    using F = pkp_gfq<P>;
    static_assert(P::owf_v == owf::pkp, "pkp_precompute_scaled_h_columns expects PKP params.");

    for (std::size_t i = 0; i < P::pkp_n; ++i)
    {
        const uint16_t xi = static_cast<uint16_t>(x[i] & F::mask);
        std::array<uint16_t, std::size_t{1} << P::pkp_q_bits> multiples{};
        uint16_t basis = xi;
        for (std::size_t bit = 0; bit < P::pkp_q_bits; ++bit)
        {
            const std::size_t step = std::size_t{1} << bit;
            for (std::size_t lower = 0; lower < step; ++lower)
                multiples[step + lower] = static_cast<uint16_t>(multiples[lower] ^ basis);

            const bool carry = (basis & (uint16_t{1} << (P::pkp_q_bits - 1))) != 0;
            basis = static_cast<uint16_t>((basis << 1) & F::mask);
            if (carry)
                basis ^= F::low_poly;
        }
        for (std::size_t col = 0; col < P::pkp_n; ++col)
        {
            uint16_t* dst = scaled_i_col_row + (i * P::pkp_n + col) * P::pkp_m;
            const uint16_t* h_col = h_col_major + col * P::pkp_m;
            for (std::size_t row = 0; row < P::pkp_m; ++row)
                dst[row] = multiples[h_col[row] & F::mask];
        }
    }
}

template <typename P>
void pkp_compute_hpx_from_scaled(uint16_t* out_m, const uint16_t* scaled_i_col_row,
                                 const uint16_t* permutation)
{
    static_assert(P::owf_v == owf::pkp,
                  "pkp_compute_hpx_from_scaled expects a PKP parameter set.");

    std::memset(out_m, 0, P::pkp_m * sizeof(uint16_t));
    for (std::size_t i = 0; i < P::pkp_n; ++i)
    {
        const std::size_t col = permutation[i];
        assert(col < P::pkp_n);
        if (col >= P::pkp_n)
            continue;
        const uint16_t* src = scaled_i_col_row + (i * P::pkp_n + col) * P::pkp_m;
        for (std::size_t row = 0; row < P::pkp_m; ++row)
            out_m[row] ^= src[row];
    }
}

template <typename P>
bool pkp_hpx_is_zero(const uint16_t* h_col_major, const uint16_t* x, const uint16_t* permutation)
{
    std::array<uint16_t, P::pkp_m> hpx{};
    pkp_compute_hpx<P>(hpx.data(), h_col_major, x, permutation);
    for (const uint16_t v : hpx)
        if (v != 0)
            return false;
    return true;
}

} // namespace sdsign

#endif
