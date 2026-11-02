#ifndef SDSIGN_RING_SIGNATURE_PARAMETERS_HPP
#define SDSIGN_RING_SIGNATURE_PARAMETERS_HPP

#include <cstddef>

#include "../rsd_parameters.hpp"

#include <array>

namespace sdsign::ring
{

// Ring-only RSD representative set for the reduction-compensated L1
// parameters (w, mu, n, d, eta, codim, t) =
// (47, 540, 25380, 4, 11, 432, 4).
//
// Start from the degree-four eta=11 construction, then exclude the disjoint
// supports of X0 X1 X2 and X3 X6 X7.  The first support contains 11
// representatives and the second contains 9, so the resulting public set has
// 560 - 11 - 9 = 540 representatives.  Together with the two original
// membership equations, these two cubic equations give t=4.  Coordinate bits
// retain the ordering used by optimal_encoding_detail::encoding<11>.
namespace reduction_compensated_detail
{
    using base = optimal_encoding_detail::encoding<11>;
    inline constexpr std::size_t domain_size = 540;
    inline constexpr uint16_t excluded_monomial_0 = 0x0007; // X0 X1 X2
    inline constexpr uint16_t excluded_monomial_1 = 0x00c8; // X3 X6 X7

    constexpr bool extra_memberships_vanish(uint16_t point)
    {
        return (point & excluded_monomial_0) != excluded_monomial_0 &&
               (point & excluded_monomial_1) != excluded_monomial_1;
    }
    constexpr bool contains(uint16_t point)
    {
        return base::contains(point) && extra_memberships_vanish(point);
    }
    constexpr std::size_t count_points()
    {
        std::size_t count = 0;
        for (std::size_t point = 0; point < base::universe_size; ++point)
            count += contains(static_cast<uint16_t>(point)) ? 1 : 0;
        return count;
    }
    static_assert(count_points() == domain_size);

    constexpr std::array<uint16_t, domain_size> make_points()
    {
        std::array<uint16_t, domain_size> out{};
        std::size_t pos = 0;
        for (std::size_t point = 0; point < base::universe_size; ++point)
            if (contains(static_cast<uint16_t>(point)))
                out[pos++] = static_cast<uint16_t>(point);
        return out;
    }
    inline constexpr std::array<uint16_t, domain_size> points = make_points();

    constexpr std::array<uint16_t, domain_size> make_base_indices()
    {
        std::array<uint16_t, domain_size> out{};
        std::size_t j = 0;
        for (std::size_t i = 0; i < domain_size; ++i)
        {
            while (base::points[j] < points[i])
                ++j;
            out[i] = static_cast<uint16_t>(j);
        }
        return out;
    }
    inline constexpr std::array<uint16_t, domain_size> base_indices = make_base_indices();

    constexpr std::array<uint8_t, base::monomial_count> make_phi_packed()
    {
        auto out = base::phi_packed;
        out[base::monomial_ranks[excluded_monomial_0]] |= uint8_t{1u << 2};
        out[base::monomial_ranks[excluded_monomial_1]] |= uint8_t{1u << 3};
        return out;
    }
    inline constexpr std::array<uint8_t, base::monomial_count> phi_packed = make_phi_packed();
} // namespace reduction_compensated_detail

struct reduction_compensated_encoding : optimal_encoding_detail::encoding<11>
{
    using base = optimal_encoding_detail::encoding<11>;
    constexpr static std::size_t domain_size = reduction_compensated_detail::domain_size;
    constexpr static std::size_t membership_count = 4;
    constexpr static bool generic_membership_verifier = true;
    constexpr static uint16_t excluded_monomial_0 =
        reduction_compensated_detail::excluded_monomial_0;
    constexpr static uint16_t excluded_monomial_1 =
        reduction_compensated_detail::excluded_monomial_1;
    constexpr static auto points = reduction_compensated_detail::points;
    constexpr static auto base_indices = reduction_compensated_detail::base_indices;
    constexpr static auto phi_packed = reduction_compensated_detail::phi_packed;

    constexpr static bool contains(uint16_t point)
    {
        return reduction_compensated_detail::contains(point);
    }

    template <std::size_t ActivePoints, typename T>
    static void reconstruct_compact_fixed(const T* point_values, T* coeffs)
    {
        constexpr std::size_t used = ActivePoints < domain_size ? ActivePoints : domain_size;
        std::array<T, base::domain_size> expanded{};
        const T zero = T::set_zero();
        expanded.fill(zero);
        for (std::size_t i = 0; i < used; ++i)
            expanded[base_indices[i]] = point_values[i];
        base::template reconstruct_compact_fixed<base::domain_size>(expanded.data(), coeffs);
    }

    template <typename T>
    static void reconstruct_compact(const T* point_values, std::size_t active_points, T* coeffs)
    {
        std::array<T, base::domain_size> expanded{};
        const T zero = T::set_zero();
        expanded.fill(zero);
        const std::size_t used = active_points < domain_size ? active_points : domain_size;
        for (std::size_t i = 0; i < used; ++i)
            expanded[base_indices[i]] = point_values[i];
        base::reconstruct_compact(expanded.data(), base::domain_size, coeffs);
    }

    template <typename T>
    static void reconstruct_anf(const T* point_values, std::size_t active_points, T* coeffs)
    {
        const T zero = T::set_zero();
        for (std::size_t mask = 0; mask < universe_size; ++mask)
            coeffs[mask] = zero;
        std::array<T, monomial_count> compact{};
        reconstruct_compact(point_values, active_points, compact.data());
        for (std::size_t rank = 0; rank < monomial_count; ++rank)
            coeffs[monomials[rank]] = compact[rank];
    }
};

} // namespace sdsign::ring

namespace sdsign
{

// This specialization is declared only with the ring-signature component.  It
// is deliberately absent from the ordinary SD parameter catalogue and API.
template <> struct rsd_table_parameters<secpar::L1, 1000>
{
    constexpr static elementary_encoding elementary_encoding_v = elementary_encoding::optimal;
    using optimal_encoding_t = ring::reduction_compensated_encoding;
    constexpr static std::size_t encoding_eta = 11;
    constexpr static std::size_t rsd_n = 25380;
    constexpr static std::size_t rsd_w = 47;
    constexpr static std::size_t rsd_codim = 432;
    constexpr static std::size_t num_var_blocks = 1;
    constexpr static std::array<std::size_t, num_var_blocks> block_sizes = {11};
    constexpr static std::array<std::size_t, num_var_blocks> block_wts = {0};
    constexpr static std::size_t deg = 4;
};

} // namespace sdsign

namespace sdsign::ring
{

using reduction_compensated_l1_short_set1_base = sdsign_rsd_parameter_set<
    secpar::L1, proof_system_variant::s, proof_system_set::set1, 1000>;

// Ring parameters are intentionally separate from rsd_table_parameters and
// pkp_table_parameters.  Adding a ring size therefore cannot change an
// existing SD/PKP parameter set or its test vectors.
template <std::size_t RingSize> struct selector_parameters;

template <> struct selector_parameters<64>
{
    static constexpr std::size_t ring_size = 64;
    static constexpr std::size_t eta_left = 3;
    static constexpr std::size_t eta_right = 4;
    static constexpr std::size_t selector_bits = eta_left + eta_right;
    static constexpr std::size_t degree = 4;
};

template <> struct selector_parameters<1024>
{
    static constexpr std::size_t ring_size = 1024;
    static constexpr std::size_t eta_left = 7;
    static constexpr std::size_t eta_right = 8;
    static constexpr std::size_t selector_bits = eta_left + eta_right;
    static constexpr std::size_t degree = 4;
};

#define SDSIGN_RING_SELECTOR_PARAMS(N, LEFT, RIGHT)                                                \
    template <> struct selector_parameters<N>                                                     \
    {                                                                                              \
        static constexpr std::size_t ring_size = N;                                               \
        static constexpr std::size_t eta_left = LEFT;                                             \
        static constexpr std::size_t eta_right = RIGHT;                                           \
        static constexpr std::size_t selector_bits = eta_left + eta_right;                         \
        static constexpr std::size_t degree = 4;                                                  \
    }

SDSIGN_RING_SELECTOR_PARAMS(4096, 11, 11);
SDSIGN_RING_SELECTOR_PARAMS(16384, 15, 16);
SDSIGN_RING_SELECTOR_PARAMS(65536, 22, 23);
SDSIGN_RING_SELECTOR_PARAMS(262144, 31, 32);
SDSIGN_RING_SELECTOR_PARAMS(1048576, 45, 45);
SDSIGN_RING_SELECTOR_PARAMS(2097152, 53, 54);

#undef SDSIGN_RING_SELECTOR_PARAMS

constexpr std::size_t choose3(std::size_t n)
{
    return n < 3 ? 0 : n * (n - 1) * (n - 2) / 6;
}

// A distinct proof parameter type is required because the selector extends
// both the committed witness and the constraint count.  Inheriting the SD
// table values keeps its optimized reconstruction machinery available while
// the overrides below remain local to the ring protocol.
template <typename Base, std::size_t RingSize> struct parameter_set : Base
{
    using base_parameter = Base;
    using selector = selector_parameters<RingSize>;
    static constexpr std::size_t ring_size = RingSize;
    static constexpr std::size_t selector_bits = selector::selector_bits;
    static constexpr std::size_t selector_witness_offset = Base::witness_bits;
    static constexpr std::size_t selector_extended_offset = Base::witness_extended_bits;

    static constexpr std::size_t witness_raw_bits = Base::witness_bits + selector_bits;
    static constexpr std::size_t witness_bits = ((witness_raw_bits + 7) / 8) * 8;
    static constexpr std::size_t witness_bytes = witness_bits / 8;
    static constexpr std::size_t witness_extended_bits =
        Base::witness_extended_bits + selector_bits;
    static constexpr std::size_t witness_extended_bytes = (witness_extended_bits + 7) / 8;

    static constexpr std::size_t selector_constraints =
        choose3(selector::eta_left) + choose3(selector::eta_right) + 1;
    static constexpr std::size_t owf_num_constraints =
        Base::owf_num_constraints + selector_constraints;
    using OWF_CONSTS =
        SDSIGN_OWF_CONSTANTS<Base::secpar_v, witness_bits, 4, owf_num_constraints,
                             Base::OWF_CONSTS::OWF_MUL_C_PRE,
                             Base::OWF_CONSTS::OWF_MUL_C_IP,
                             Base::OWF_CONSTS::OWF_MUL_C_TOTAL>;
    using CONSTS = SDSIGN_CONSTANTS<parameter_set<Base, RingSize>>;

    static_assert(Base::OWF_CONSTS::QS_DEGREE <= 4);
};

} // namespace sdsign::ring

#endif
