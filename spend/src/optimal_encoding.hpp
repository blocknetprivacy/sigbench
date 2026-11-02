#ifndef SDSIGN_OPTIMAL_ENCODING_HPP
#define SDSIGN_OPTIMAL_ENCODING_HPP

#include <array>
#include <bit>
#include <cstddef>
#include <cstdint>
#include <utility>

namespace sdsign::optimal_encoding_detail
{

template <std::size_t Eta> struct encoding
{
    static_assert(Eta == 10 || Eta == 11,
                  "The clean optimal encoding is currently specified only for eta=10,11.");

    constexpr static std::size_t eta = Eta;
    constexpr static std::size_t degree = 4;
    constexpr static std::size_t membership_count = 2;
    constexpr static bool generic_membership_verifier = false;
    constexpr static std::size_t universe_size = std::size_t{1} << eta;
    constexpr static std::size_t x_size = eta - 9;
    constexpr static uint16_t u_mask = 0x000f;
    constexpr static uint16_t x_mask =
        static_cast<uint16_t>(((std::size_t{1} << x_size) - 1) << 4);
    constexpr static std::size_t domain_size = (eta == 10) ? 384 : 560;
    constexpr static std::size_t monomial_count =
        1 + eta + eta * (eta - 1) / 2 + eta * (eta - 1) * (eta - 2) / 6 +
        eta * (eta - 1) * (eta - 2) * (eta - 3) / 24;

    constexpr static bool is_vx(uint16_t point)
    {
        return (point & static_cast<uint16_t>(~x_mask)) == 0;
    }
    constexpr static bool is_deleted(uint16_t point) { return is_vx(point) || point == u_mask; }
    constexpr static bool is_inserted(uint16_t point)
    {
        const uint16_t remainder = point ^ u_mask;
        return (point & u_mask) == u_mask && remainder != 0 && is_vx(remainder);
    }
    constexpr static bool contains(uint16_t point)
    {
        return (static_cast<std::size_t>(std::popcount(point)) <= degree && !is_deleted(point)) ||
               is_inserted(point);
    }
    constexpr static std::array<uint16_t, domain_size> make_points()
    {
        std::array<uint16_t, domain_size> out{};
        std::size_t pos = 0;
        for (std::size_t point = 0; point < universe_size; ++point)
            if (contains(static_cast<uint16_t>(point)))
                out[pos++] = static_cast<uint16_t>(point);
        return out;
    }
    constexpr static std::size_t count_points()
    {
        std::size_t count = 0;
        for (std::size_t point = 0; point < universe_size; ++point)
            count += contains(static_cast<uint16_t>(point)) ? 1 : 0;
        return count;
    }
    static_assert(count_points() == domain_size);
    constexpr static std::array<uint16_t, domain_size> points = make_points();
    // Monomials are enumerated by increasing total degree, and by increasing
    // mask within each degree.  The ordering is an implementation detail: every
    // consumer addresses monomials through `monomial_ranks`, and every schedule
    // below is derived from this array, so the choice is semantically neutral.
    // Grouping by degree lets the hot loops walk one degree bucket at a time
    // and gives the product schedule long dependency chains to overlap.
    constexpr static std::array<uint16_t, monomial_count> make_monomials()
    {
        std::array<uint16_t, monomial_count> out{};
        std::size_t pos = 0;
        for (std::size_t d = 0; d <= degree; ++d)
            for (std::size_t mask = 0; mask < universe_size; ++mask)
                if (static_cast<std::size_t>(std::popcount(mask)) == d)
                    out[pos++] = static_cast<uint16_t>(mask);
        return out;
    }
    constexpr static std::array<uint16_t, monomial_count> monomials = make_monomials();

    // degree_offsets[d] .. degree_offsets[d + 1] is the rank range of the
    // monomials of total degree d.
    constexpr static std::array<uint16_t, degree + 2> make_degree_offsets()
    {
        std::array<uint16_t, degree + 2> out{};
        std::size_t pos = 0;
        for (std::size_t d = 0; d <= degree; ++d)
        {
            out[d] = static_cast<uint16_t>(pos);
            for (std::size_t mask = 0; mask < universe_size; ++mask)
                pos += (static_cast<std::size_t>(std::popcount(mask)) == d) ? 1 : 0;
        }
        out[degree + 1] = static_cast<uint16_t>(pos);
        return out;
    }
    constexpr static std::array<uint16_t, degree + 2> degree_offsets = make_degree_offsets();
    static_assert(degree_offsets[degree + 1] == monomial_count);
    static_assert(degree_offsets[0] == 0 && degree_offsets[1] == 1);

    constexpr static uint16_t invalid_rank = UINT16_MAX;
    constexpr static std::array<uint16_t, universe_size> make_monomial_ranks()
    {
        std::array<uint16_t, universe_size> out{};
        out.fill(invalid_rank);
        for (std::size_t rank = 0; rank < monomial_count; ++rank)
            out[monomials[rank]] = static_cast<uint16_t>(rank);
        return out;
    }
    constexpr static std::array<uint16_t, universe_size> monomial_ranks =
        make_monomial_ranks();
    constexpr static std::array<uint8_t, monomial_count> make_monomial_degrees()
    {
        std::array<uint8_t, monomial_count> out{};
        for (std::size_t rank = 0; rank < monomial_count; ++rank)
            out[rank] = static_cast<uint8_t>(std::popcount(monomials[rank]));
        return out;
    }
    constexpr static std::array<uint8_t, monomial_count> monomial_degrees =
        make_monomial_degrees();
    constexpr static bool degrees_are_grouped()
    {
        for (std::size_t d = 0; d <= degree; ++d)
            for (std::size_t rank = degree_offsets[d]; rank < degree_offsets[d + 1]; ++rank)
                if (monomial_degrees[rank] != d)
                    return false;
        return true;
    }
    static_assert(degrees_are_grouped());

    struct degree_rank_schedule_t
    {
        std::array<uint16_t, degree + 2> offsets{};
        std::array<uint16_t, monomial_count> ranks{};
    };
    constexpr static degree_rank_schedule_t make_degree_rank_schedule()
    {
        degree_rank_schedule_t out{};
        std::size_t pos = 0;
        for (std::size_t d = 0; d <= degree; ++d)
        {
            out.offsets[d] = static_cast<uint16_t>(pos);
            for (std::size_t rank = 0; rank < monomial_count; ++rank)
                if (monomial_degrees[rank] == d)
                    out.ranks[pos++] = static_cast<uint16_t>(rank);
        }
        out.offsets[degree + 1] = static_cast<uint16_t>(pos);
        return out;
    }
    constexpr static degree_rank_schedule_t degree_rank_schedule =
        make_degree_rank_schedule();

    constexpr static std::size_t product_count = monomial_count - 1 - eta;
    struct product_schedule_t
    {
        std::array<uint16_t, product_count> destinations{};
        std::array<uint16_t, product_count> left_sources{};
        std::array<uint16_t, product_count> right_sources{};
    };
    constexpr static product_schedule_t make_product_schedule()
    {
        product_schedule_t out{};
        std::size_t pos = 0;
        for (std::size_t rank = 0; rank < monomial_count; ++rank)
        {
            const uint16_t mask = monomials[rank];
            if (monomial_degrees[rank] < 2)
                continue;
            uint16_t high_bit = 1;
            while (static_cast<uint16_t>(high_bit << 1) <= mask)
                high_bit = static_cast<uint16_t>(high_bit << 1);
            out.destinations[pos] = static_cast<uint16_t>(rank);
            out.left_sources[pos] = monomial_ranks[static_cast<uint16_t>(mask ^ high_bit)];
            out.right_sources[pos] = monomial_ranks[high_bit];
            ++pos;
        }
        return out;
    }
    constexpr static product_schedule_t product_schedule = make_product_schedule();

    // In-place Horner circuit for an arbitrary eta-variate multilinear
    // polynomial truncated at `degree`.  Processing variables from high to
    // low transforms coefficient[prefix] into the value of its suffix
    // subtree.  The circuit has exactly monomial_count - 1 multiplications.
    constexpr static std::size_t horner_edge_count = monomial_count - 1;
    struct horner_schedule_t
    {
        std::array<uint16_t, eta + 1> offsets{};
        std::array<uint16_t, horner_edge_count> destinations{};
        std::array<uint16_t, horner_edge_count> sources{};
    };
    constexpr static horner_schedule_t make_horner_schedule()
    {
        horner_schedule_t out{};
        std::size_t pos = 0;
        for (std::size_t bit = 0; bit < eta; ++bit)
        {
            out.offsets[bit] = static_cast<uint16_t>(pos);
            const uint16_t singleton = static_cast<uint16_t>(uint16_t{1} << bit);
            const uint16_t lower_mask = static_cast<uint16_t>(singleton - 1);
            for (std::size_t rank = 0; rank < monomial_count; ++rank)
            {
                const uint16_t prefix = monomials[rank];
                if ((prefix & static_cast<uint16_t>(~lower_mask)) != 0 ||
                    monomial_degrees[rank] >= degree)
                    continue;
                out.destinations[pos] = static_cast<uint16_t>(rank);
                out.sources[pos] =
                    monomial_ranks[static_cast<uint16_t>(prefix | singleton)];
                ++pos;
            }
        }
        out.offsets[eta] = static_cast<uint16_t>(pos);
        return out;
    }
    constexpr static horner_schedule_t horner_schedule = make_horner_schedule();
    static_assert(horner_schedule.offsets[eta] == horner_edge_count,
                  "Horner schedule must cover every non-constant monomial exactly once");

    constexpr static bool phi0(uint16_t monomial)
    {
        constexpr uint16_t z_mask =
            static_cast<uint16_t>((universe_size - 1) & ~x_mask);
        return (monomial & static_cast<uint16_t>(~z_mask)) == 0 &&
               static_cast<std::size_t>(std::popcount(monomial)) <= degree;
    }
    constexpr static bool phi1(uint16_t monomial)
    {
        return phi0(monomial) ^
               (static_cast<std::size_t>(std::popcount(monomial)) <= degree) ^
               (monomial == u_mask);
    }

    // The two public membership polynomials, evaluated once at compile time and
    // packed into bits 0 and 1 of one byte per monomial rank.
    constexpr static std::array<uint8_t, monomial_count> make_phi_packed()
    {
        std::array<uint8_t, monomial_count> out{};
        for (std::size_t rank = 0; rank < monomial_count; ++rank)
            out[rank] = static_cast<uint8_t>((phi0(monomials[rank]) ? 1u : 0u) |
                                             (phi1(monomials[rank]) ? 2u : 0u));
        return out;
    }
    constexpr static std::array<uint8_t, monomial_count> phi_packed = make_phi_packed();

    constexpr static std::size_t choose(std::size_t n, std::size_t k)
    {
        if (k > n)
            return 0;
        std::size_t result = 1;
        for (std::size_t i = 1; i <= k; ++i)
            result = result * (n - k + i) / i;
        return result;
    }

    constexpr static bool l_value(uint16_t b, uint16_t point)
    {
        if ((b & static_cast<uint16_t>(~point)) != 0)
            return false;
        const std::size_t b_weight = std::popcount(b);
        const std::size_t remaining = std::popcount(point) - b_weight;
        std::size_t parity = 0;
        for (std::size_t j = 0; j <= degree - b_weight; ++j)
            parity ^= choose(remaining, j) & 1u;
        return parity != 0;
    }

    // Compile the canonical reconstruction formula into a compact scatter
    // schedule.  This is derived solely from the descriptor above: it does
    // not assume a particular eta beyond the construction's stated scope.
    constexpr static std::size_t scatter_count = []
    {
        std::size_t count = 0;
        for (uint16_t point : points)
        {
            ++count;
            if (!is_inserted(point))
                for (uint16_t r = x_mask; r != 0;
                     r = static_cast<uint16_t>((r - 1) & x_mask))
                    count += l_value(point, static_cast<uint16_t>(u_mask | r)) ? 1 : 0;
        }
        return count;
    }();

    struct scatter_schedule_t
    {
        std::array<uint16_t, domain_size + 1> offsets{};
        std::array<uint16_t, scatter_count> destinations{};
    };

    constexpr static scatter_schedule_t make_scatter_schedule()
    {
        scatter_schedule_t out{};
        std::size_t pos = 0;
        for (std::size_t point_idx = 0; point_idx < domain_size; ++point_idx)
        {
            out.offsets[point_idx] = static_cast<uint16_t>(pos);
            const uint16_t point = points[point_idx];
            const uint16_t primary = is_inserted(point) ? static_cast<uint16_t>(point ^ u_mask)
                                                        : point;
            out.destinations[pos++] = monomial_ranks[primary];
            if (!is_inserted(point))
                for (uint16_t r = x_mask; r != 0;
                     r = static_cast<uint16_t>((r - 1) & x_mask))
                    if (l_value(point, static_cast<uint16_t>(u_mask | r)))
                        out.destinations[pos++] = monomial_ranks[r];
        }
        out.offsets[domain_size] = static_cast<uint16_t>(pos);
        return out;
    }
    constexpr static scatter_schedule_t scatter_schedule = make_scatter_schedule();

    // Every point contributes exactly one "primary" destination, and those
    // destinations are pairwise distinct: a point that is not inserted maps to
    // itself (never a vx-value, since vx-values are deleted), and an inserted
    // point maps to a distinct nonzero vx-value.  Splitting them off lets the
    // reconstruction store the primaries instead of accumulating into a
    // pre-zeroed array.
    constexpr static std::size_t secondary_count = scatter_count - domain_size;
    struct split_scatter_t
    {
        std::array<uint16_t, domain_size> primary_dest{};
        std::array<uint16_t, domain_size + 1> secondary_offsets{};
        std::array<uint16_t, secondary_count> secondary_dest{};
    };
    constexpr static split_scatter_t make_split_scatter()
    {
        split_scatter_t out{};
        std::size_t pos = 0;
        for (std::size_t point_idx = 0; point_idx < domain_size; ++point_idx)
        {
            const std::size_t begin = scatter_schedule.offsets[point_idx];
            const std::size_t end = scatter_schedule.offsets[point_idx + 1];
            out.primary_dest[point_idx] = scatter_schedule.destinations[begin];
            out.secondary_offsets[point_idx] = static_cast<uint16_t>(pos);
            for (std::size_t i = begin + 1; i < end; ++i)
                out.secondary_dest[pos++] = scatter_schedule.destinations[i];
        }
        out.secondary_offsets[domain_size] = static_cast<uint16_t>(pos);
        return out;
    }
    constexpr static split_scatter_t split_scatter = make_split_scatter();
    constexpr static bool primaries_are_distinct()
    {
        std::array<bool, monomial_count> seen{};
        for (std::size_t i = 0; i < domain_size; ++i)
        {
            if (seen[split_scatter.primary_dest[i]])
                return false;
            seen[split_scatter.primary_dest[i]] = true;
        }
        return true;
    }
    static_assert(primaries_are_distinct(),
                  "Primary scatter destinations must be pairwise distinct");

    constexpr static std::size_t clamp_active(std::size_t active_points)
    {
        return active_points < domain_size ? active_points : domain_size;
    }
    template <std::size_t ActivePoints> constexpr static std::size_t count_uncovered()
    {
        std::array<bool, monomial_count> covered{};
        for (std::size_t i = 0; i < clamp_active(ActivePoints); ++i)
            covered[split_scatter.primary_dest[i]] = true;
        std::size_t n = 0;
        for (std::size_t rank = 0; rank < monomial_count; ++rank)
            n += covered[rank] ? 0u : 1u;
        return n;
    }
    template <std::size_t ActivePoints>
    constexpr static std::array<uint16_t, count_uncovered<ActivePoints>()> make_uncovered()
    {
        std::array<uint16_t, count_uncovered<ActivePoints>()> out{};
        std::array<bool, monomial_count> covered{};
        for (std::size_t i = 0; i < clamp_active(ActivePoints); ++i)
            covered[split_scatter.primary_dest[i]] = true;
        std::size_t pos = 0;
        for (std::size_t rank = 0; rank < monomial_count; ++rank)
            if (!covered[rank])
                out[pos++] = static_cast<uint16_t>(rank);
        return out;
    }
    template <std::size_t ActivePoints>
    constexpr static std::array<uint16_t, count_uncovered<ActivePoints>()> uncovered_ranks =
        make_uncovered<ActivePoints>();

    constexpr static std::size_t zeta_edge_count = []
    {
        std::size_t count = 0;
        for (uint16_t mask : monomials)
            count += std::popcount(mask);
        return count;
    }();

    struct zeta_schedule_t
    {
        std::array<uint16_t, eta + 1> offsets{};
        std::array<uint16_t, zeta_edge_count> destinations{};
        std::array<uint16_t, zeta_edge_count> sources{};
    };

    constexpr static zeta_schedule_t make_zeta_schedule()
    {
        zeta_schedule_t out{};
        std::size_t pos = 0;
        for (std::size_t bit = 0; bit < eta; ++bit)
        {
            out.offsets[bit] = static_cast<uint16_t>(pos);
            const uint16_t singleton = static_cast<uint16_t>(std::size_t{1} << bit);
            for (uint16_t mask : monomials)
                if ((mask & singleton) != 0)
                {
                    out.destinations[pos] = monomial_ranks[mask];
                    out.sources[pos] = monomial_ranks[static_cast<uint16_t>(mask ^ singleton)];
                    ++pos;
                }
        }
        out.offsets[eta] = static_cast<uint16_t>(pos);
        return out;
    }
    constexpr static zeta_schedule_t zeta_schedule = make_zeta_schedule();

    template <typename T>
    static void reconstruct_compact(const T* point_values, std::size_t active_points, T* coeffs)
    {
        const T zero = T::set_zero();
        for (std::size_t rank = 0; rank < monomial_count; ++rank)
            coeffs[rank] = zero;

        const std::size_t used = active_points < domain_size ? active_points : domain_size;
        for (std::size_t point_idx = 0; point_idx < used; ++point_idx)
        {
            const T value = point_values[point_idx];
            for (std::size_t pos = scatter_schedule.offsets[point_idx];
                 pos < scatter_schedule.offsets[point_idx + 1]; ++pos)
                coeffs[scatter_schedule.destinations[pos]] += value;
        }

        zeta_transform(coeffs);
    }

    // Same result as reconstruct_compact(point_values, ActivePoints, coeffs),
    // but the number of active points is a compile-time constant, so the
    // primary scatter destinations can be stored directly and only the ranks
    // that no primary covers have to be cleared first.  Control flow and
    // memory accesses are identical for every input.
    template <std::size_t ActivePoints, typename T>
    static void reconstruct_compact_fixed(const T* point_values, T* coeffs)
    {
        constexpr std::size_t used = clamp_active(ActivePoints);
        const T zero = T::set_zero();
        for (uint16_t rank : uncovered_ranks<ActivePoints>)
            coeffs[rank] = zero;
        for (std::size_t point_idx = 0; point_idx < used; ++point_idx)
            coeffs[split_scatter.primary_dest[point_idx]] = point_values[point_idx];
        for (std::size_t point_idx = 0; point_idx < used; ++point_idx)
        {
            const T value = point_values[point_idx];
            for (std::size_t pos = split_scatter.secondary_offsets[point_idx];
                 pos < split_scatter.secondary_offsets[point_idx + 1]; ++pos)
                coeffs[split_scatter.secondary_dest[pos]] += value;
        }

        zeta_transform(coeffs);
    }

    template <typename T> static void zeta_transform(T* coeffs)
    {
        for (std::size_t bit = 0; bit < eta; ++bit)
            for (std::size_t pos = zeta_schedule.offsets[bit];
                 pos < zeta_schedule.offsets[bit + 1]; ++pos)
                coeffs[zeta_schedule.destinations[pos]] += coeffs[zeta_schedule.sources[pos]];
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

// Dense optimal (eta,d)=(12,3) construction.  Unlike the eta=10,11
// degree-four family above, its reconstruction map is generated by
// deterministic binary Gaussian elimination.  The matrices are public data
// initialized once before main; signing and verification only execute the
// compiled scatter schedule below.
template <std::size_t Eta> struct dense_d3_encoding
{
    static_assert(Eta == 12);
    constexpr static std::size_t eta = Eta;
    constexpr static std::size_t degree = 3;
    constexpr static std::size_t membership_count = 3;
    constexpr static bool generic_membership_verifier = true;
    constexpr static std::size_t universe_size = std::size_t{1} << eta;
    constexpr static std::size_t domain_size = 296;
    constexpr static std::size_t monomial_count = 299;

    constexpr static std::array<uint16_t, 145> c1 = {
        0,    3,    4,    5,    12,   13,   18,   19,   20,   21,   25,   26,   32,
        36,   37,   38,   40,   41,   42,   44,   49,   52,   67,   68,   72,   74,
        76,   81,   82,   84,   97,   100,  128,  131,  133,  140,  148,  164,  168,
        176,  192,  208,  258,  260,  262,  266,  268,  273,  274,  288,  289,  290,
        292,  320,  322,  336,  352,  385,  388,  416,  513,  514,  515,  516,  521,
        528,  532,  544,  548,  552,  560,  577,  580,  592,  640,  641,  642,  644,
        704,  770,  772,  800,  896,  1025, 1026, 1034, 1040, 1041, 1042, 1056, 1058,
        1060, 1072, 1088, 1104, 1120, 1153, 1156, 1160, 1168, 1184, 1216, 1280, 1282,
        1296, 1408, 1538, 1552, 1568, 1600, 2048, 2049, 2050, 2051, 2056, 2057, 2058,
        2080, 2081, 2084, 2088, 2114, 2120, 2128, 2144, 2180, 2184, 2192, 2240, 2306,
        2308, 2320, 2368, 2432, 2560, 2568, 2576, 2624, 2816, 3073, 3076, 3088, 3104,
        3136, 3584};

    constexpr static std::array<uint16_t, 152> c2 = {
        0,    1,    3,    4,    5,    6,    7,    10,   11,   12,   13,   17,   26,
        32,   33,   34,   37,   38,   40,   41,   42,   48,   56,   66,   69,   73,
        74,   76,   80,   81,   82,   96,   98,   100,  104,  112,  133,  137,  138,
        140,  144,  148,  152,  161,  164,  176,  192,  194,  196,  200,  208,  224,
        256,  258,  260,  264,  272,  276,  321,  324,  328,  336,  385,  386,  392,
        416,  513,  514,  516,  517,  518,  520,  522,  530,  536,  545,  546,  548,
        577,  592,  608,  641,  642,  644,  672,  769,  770,  772,  800,  832,  1024,
        1032, 1033, 1034, 1042, 1044, 1060, 1064, 1088, 1090, 1092, 1096, 1104, 1120,
        1152, 1154, 1168, 1216, 1281, 1284, 1296, 1312, 1344, 1408, 1538, 1540, 1544,
        1552, 1568, 2050, 2051, 2052, 2056, 2060, 2066, 2082, 2088, 2096, 2112, 2113,
        2114, 2116, 2176, 2178, 2184, 2192, 2208, 2240, 2304, 2305, 2308, 2368, 2432,
        2561, 2564, 2576, 2592, 3076, 3104, 3136, 3328, 3584};

    constexpr static std::array<uint16_t, 161> c3 = {
        4,    6,    7,    8,    9,    11,   14,   16,   20,   21,   22,   32,   33,
        34,   35,   36,   37,   41,   44,   56,   64,   66,   67,   73,   74,   80,
        81,   88,   97,   98,   100,  104,  128,  131,  133,  136,  137,  138,  144,
        146,  148,  152,  160,  162,  164,  176,  192,  194,  200,  224,  258,  260,
        261,  262,  265,  268,  274,  280,  288,  296,  304,  336,  352,  400,  416,
        448,  513,  514,  515,  517,  521,  528,  529,  530,  532,  536,  544,  548,
        552,  580,  584,  608,  640,  642,  644,  656,  672,  768,  770,  772,  776,
        784,  800,  1025, 1026, 1027, 1032, 1033, 1041, 1042, 1056, 1058, 1060, 1064,
        1072, 1089, 1090, 1096, 1120, 1152, 1156, 1160, 1168, 1184, 1216, 1288, 1296,
        1312, 1536, 1537, 1538, 1568, 1600, 1664, 1792, 2048, 2049, 2051, 2052, 2053,
        2056, 2060, 2064, 2065, 2072, 2081, 2084, 2112, 2113, 2114, 2128, 2144, 2177,
        2184, 2240, 2308, 2320, 2336, 2560, 2564, 2624, 2688, 3072, 3074, 3076, 3080,
        3088, 3104, 3136, 3328, 3584};

    template <std::size_t N>
    constexpr static bool valid_mask_set(const std::array<uint16_t, N>& masks)
    {
        for (std::size_t i = 0; i < N; ++i)
        {
            if (masks[i] >= universe_size ||
                static_cast<std::size_t>(std::popcount(masks[i])) > degree)
                return false;
            if (i != 0 && masks[i - 1] >= masks[i])
                return false;
        }
        return true;
    }
    static_assert(valid_mask_set(c1) && valid_mask_set(c2) && valid_mask_set(c3));

    template <std::size_t N>
    constexpr static bool mask_set_contains(const std::array<uint16_t, N>& masks, uint16_t mask)
    {
        for (uint16_t candidate : masks)
            if (candidate == mask)
                return true;
        return false;
    }
    constexpr static std::array<uint8_t, universe_size> make_membership_table()
    {
        std::array<uint8_t, universe_size> out{};
        for (uint16_t mask : c1)
            out[mask] ^= 1u;
        for (uint16_t mask : c2)
            out[mask] ^= 2u;
        for (uint16_t mask : c3)
            out[mask] ^= 4u;
        // Boolean zeta transform: after bit i, out[x] is the XOR of all
        // coefficients indexed by submasks of x on the processed variables.
        for (std::size_t bit = 0; bit < eta; ++bit)
            for (std::size_t point = 0; point < universe_size; ++point)
                if ((point & (std::size_t{1} << bit)) != 0)
                    out[point] ^= out[point ^ (std::size_t{1} << bit)];
        return out;
    }
    constexpr static std::array<uint8_t, universe_size> membership_table =
        make_membership_table();
    constexpr static uint8_t membership_label(uint16_t point) { return membership_table[point]; }
    constexpr static bool contains(uint16_t point) { return membership_label(point) == 0; }
    constexpr static bool phi0(uint16_t monomial) { return mask_set_contains(c1, monomial); }
    constexpr static bool phi1(uint16_t monomial) { return mask_set_contains(c2, monomial); }
    constexpr static bool phi2(uint16_t monomial) { return mask_set_contains(c3, monomial); }

    constexpr static std::array<std::size_t, 8> make_fiber_sizes()
    {
        std::array<std::size_t, 8> out{};
        for (std::size_t point = 0; point < universe_size; ++point)
            ++out[membership_label(static_cast<uint16_t>(point))];
        return out;
    }
    constexpr static std::array<std::size_t, 8> fiber_sizes = make_fiber_sizes();
    static_assert(fiber_sizes == std::array<std::size_t, 8>{296, 524, 556, 520, 552, 548, 524,
                                                            576});

    constexpr static std::array<uint16_t, domain_size> make_points()
    {
        std::array<uint16_t, domain_size> out{};
        std::size_t pos = 0;
        for (std::size_t point = 0; point < universe_size; ++point)
            if (contains(static_cast<uint16_t>(point)))
                out[pos++] = static_cast<uint16_t>(point);
        return out;
    }
    constexpr static std::array<uint16_t, domain_size> points = make_points();

    // The specification requires increasing integer-mask order, rather than
    // the degree-grouped internal order used by the eta=10,11 construction.
    constexpr static std::array<uint16_t, monomial_count> make_monomials()
    {
        std::array<uint16_t, monomial_count> out{};
        std::size_t pos = 0;
        for (std::size_t mask = 0; mask < universe_size; ++mask)
            if (static_cast<std::size_t>(std::popcount(mask)) <= degree)
                out[pos++] = static_cast<uint16_t>(mask);
        return out;
    }
    constexpr static std::array<uint16_t, monomial_count> monomials = make_monomials();
    constexpr static uint16_t invalid_rank = UINT16_MAX;
    constexpr static std::array<uint16_t, universe_size> make_monomial_ranks()
    {
        std::array<uint16_t, universe_size> out{};
        out.fill(invalid_rank);
        for (std::size_t rank = 0; rank < monomial_count; ++rank)
            out[monomials[rank]] = static_cast<uint16_t>(rank);
        return out;
    }
    constexpr static std::array<uint16_t, universe_size> monomial_ranks = make_monomial_ranks();
    constexpr static std::array<uint8_t, monomial_count> make_monomial_degrees()
    {
        std::array<uint8_t, monomial_count> out{};
        for (std::size_t rank = 0; rank < monomial_count; ++rank)
            out[rank] = static_cast<uint8_t>(std::popcount(monomials[rank]));
        return out;
    }
    constexpr static std::array<uint8_t, monomial_count> monomial_degrees =
        make_monomial_degrees();

    struct degree_rank_schedule_t
    {
        std::array<uint16_t, degree + 2> offsets{};
        std::array<uint16_t, monomial_count> ranks{};
    };
    constexpr static degree_rank_schedule_t make_degree_rank_schedule()
    {
        degree_rank_schedule_t out{};
        std::size_t pos = 0;
        for (std::size_t d = 0; d <= degree; ++d)
        {
            out.offsets[d] = static_cast<uint16_t>(pos);
            for (std::size_t rank = 0; rank < monomial_count; ++rank)
                if (monomial_degrees[rank] == d)
                    out.ranks[pos++] = static_cast<uint16_t>(rank);
        }
        out.offsets[degree + 1] = static_cast<uint16_t>(pos);
        return out;
    }
    constexpr static degree_rank_schedule_t degree_rank_schedule =
        make_degree_rank_schedule();

    constexpr static std::array<uint8_t, monomial_count> make_phi_packed()
    {
        std::array<uint8_t, monomial_count> out{};
        for (std::size_t rank = 0; rank < monomial_count; ++rank)
            out[rank] = static_cast<uint8_t>((phi0(monomials[rank]) ? 1u : 0u) |
                                             (phi1(monomials[rank]) ? 2u : 0u) |
                                             (phi2(monomials[rank]) ? 4u : 0u));
        return out;
    }
    constexpr static std::array<uint8_t, monomial_count> phi_packed = make_phi_packed();

    constexpr static bool coefficient_rows_independent()
    {
        for (uint8_t combination = 1; combination < (1u << membership_count); ++combination)
        {
            bool nonzero = false;
            for (uint8_t packed : phi_packed)
                nonzero |= (std::popcount(static_cast<unsigned>(packed & combination)) & 1u) != 0;
            if (!nonzero)
                return false;
        }
        return true;
    }
    static_assert(coefficient_rows_independent());

    constexpr static std::size_t product_count = monomial_count - 1 - eta;
    struct product_schedule_t
    {
        std::array<uint16_t, product_count> destinations{};
        std::array<uint16_t, product_count> left_sources{};
        std::array<uint16_t, product_count> right_sources{};
    };
    constexpr static product_schedule_t make_product_schedule()
    {
        product_schedule_t out{};
        std::size_t pos = 0;
        for (std::size_t rank = 0; rank < monomial_count; ++rank)
        {
            const uint16_t mask = monomials[rank];
            if (monomial_degrees[rank] < 2)
                continue;
            const uint16_t high_bit = static_cast<uint16_t>(uint16_t{1} <<
                                                            (std::bit_width(mask) - 1));
            out.destinations[pos] = static_cast<uint16_t>(rank);
            out.left_sources[pos] = monomial_ranks[static_cast<uint16_t>(mask ^ high_bit)];
            out.right_sources[pos] = monomial_ranks[high_bit];
            ++pos;
        }
        return out;
    }
    constexpr static product_schedule_t product_schedule = make_product_schedule();

    constexpr static std::size_t horner_edge_count = monomial_count - 1;
    struct horner_schedule_t
    {
        std::array<uint16_t, eta + 1> offsets{};
        std::array<uint16_t, horner_edge_count> destinations{};
        std::array<uint16_t, horner_edge_count> sources{};
    };
    constexpr static horner_schedule_t make_horner_schedule()
    {
        horner_schedule_t out{};
        std::size_t pos = 0;
        for (std::size_t bit = 0; bit < eta; ++bit)
        {
            out.offsets[bit] = static_cast<uint16_t>(pos);
            const uint16_t singleton = static_cast<uint16_t>(uint16_t{1} << bit);
            const uint16_t lower_mask = static_cast<uint16_t>(singleton - 1);
            for (std::size_t rank = 0; rank < monomial_count; ++rank)
            {
                const uint16_t prefix = monomials[rank];
                if ((prefix & static_cast<uint16_t>(~lower_mask)) != 0 ||
                    monomial_degrees[rank] >= degree)
                    continue;
                out.destinations[pos] = static_cast<uint16_t>(rank);
                out.sources[pos] = monomial_ranks[static_cast<uint16_t>(prefix | singleton)];
                ++pos;
            }
        }
        out.offsets[eta] = static_cast<uint16_t>(pos);
        return out;
    }
    constexpr static horner_schedule_t horner_schedule = make_horner_schedule();
    static_assert(horner_schedule.offsets[eta] == horner_edge_count);

    constexpr static std::size_t zeta_edge_count = []
    {
        std::size_t count = 0;
        for (uint16_t mask : monomials)
            count += std::popcount(mask);
        return count;
    }();
    struct zeta_schedule_t
    {
        std::array<uint16_t, eta + 1> offsets{};
        std::array<uint16_t, zeta_edge_count> destinations{};
        std::array<uint16_t, zeta_edge_count> sources{};
    };
    constexpr static zeta_schedule_t make_zeta_schedule()
    {
        zeta_schedule_t out{};
        std::size_t pos = 0;
        for (std::size_t bit = 0; bit < eta; ++bit)
        {
            out.offsets[bit] = static_cast<uint16_t>(pos);
            const uint16_t singleton = static_cast<uint16_t>(uint16_t{1} << bit);
            for (uint16_t mask : monomials)
                if ((mask & singleton) != 0)
                {
                    out.destinations[pos] = monomial_ranks[mask];
                    out.sources[pos] = monomial_ranks[static_cast<uint16_t>(mask ^ singleton)];
                    ++pos;
                }
        }
        out.offsets[eta] = static_cast<uint16_t>(pos);
        return out;
    }
    constexpr static zeta_schedule_t zeta_schedule = make_zeta_schedule();

    constexpr static std::size_t point_word_count = (domain_size + 63) / 64;
    constexpr static std::size_t monomial_word_count = (monomial_count + 63) / 64;
    using point_bits = std::array<uint64_t, point_word_count>;
    using monomial_bits = std::array<uint64_t, monomial_word_count>;

    template <std::size_t N>
    constexpr static bool get_bit(const std::array<uint64_t, N>& bits, std::size_t bit)
    {
        return ((bits[bit / 64] >> (bit % 64)) & 1u) != 0;
    }
    template <std::size_t N>
    constexpr static void set_bit(std::array<uint64_t, N>& bits, std::size_t bit)
    {
        bits[bit / 64] |= uint64_t{1} << (bit % 64);
    }
    template <std::size_t N>
    constexpr static void xor_bits(std::array<uint64_t, N>& dst,
                                   const std::array<uint64_t, N>& src)
    {
        for (std::size_t word = 0; word < N; ++word)
            dst[word] ^= src[word];
    }

    constexpr static point_bits evaluation_column(uint16_t monomial)
    {
        point_bits out{};
        for (std::size_t row = 0; row < domain_size; ++row)
            if ((points[row] & monomial) == monomial)
                set_bit(out, row);
        return out;
    }
    constexpr static monomial_bits evaluation_row(uint16_t point)
    {
        monomial_bits out{};
        for (std::size_t rank = 0; rank < monomial_count; ++rank)
            if ((point & monomials[rank]) == monomials[rank])
                set_bit(out, rank);
        return out;
    }

    struct pivot_columns_t
    {
        std::array<uint16_t, domain_size> columns{};
        std::size_t rank = 0;
    };
    struct raw_point_bits
    {
        uint64_t w0 = 0;
        uint64_t w1 = 0;
        uint64_t w2 = 0;
        uint64_t w3 = 0;
        uint64_t w4 = 0;
    };
    constexpr static bool raw_get_bit(const raw_point_bits& bits, std::size_t bit)
    {
        switch (bit / 64)
        {
        case 0:
            return ((bits.w0 >> (bit % 64)) & 1u) != 0;
        case 1:
            return ((bits.w1 >> (bit % 64)) & 1u) != 0;
        case 2:
            return ((bits.w2 >> (bit % 64)) & 1u) != 0;
        case 3:
            return ((bits.w3 >> (bit % 64)) & 1u) != 0;
        default:
            return ((bits.w4 >> (bit % 64)) & 1u) != 0;
        }
    }
    constexpr static void raw_set_bit(raw_point_bits& bits, std::size_t bit)
    {
        const uint64_t value = uint64_t{1} << (bit % 64);
        switch (bit / 64)
        {
        case 0:
            bits.w0 |= value;
            break;
        case 1:
            bits.w1 |= value;
            break;
        case 2:
            bits.w2 |= value;
            break;
        case 3:
            bits.w3 |= value;
            break;
        default:
            bits.w4 |= value;
            break;
        }
    }
    constexpr static void raw_xor(raw_point_bits& dst, const raw_point_bits& src)
    {
        dst.w0 ^= src.w0;
        dst.w1 ^= src.w1;
        dst.w2 ^= src.w2;
        dst.w3 ^= src.w3;
        dst.w4 ^= src.w4;
    }
    constexpr static raw_point_bits raw_evaluation_column(uint16_t monomial)
    {
        raw_point_bits out{};
        for (std::size_t row = 0; row < domain_size; ++row)
            if ((points[row] & monomial) == monomial)
                raw_set_bit(out, row);
        return out;
    }
    constexpr static std::array<raw_point_bits, monomial_count> make_raw_evaluation_columns()
    {
        std::array<raw_point_bits, monomial_count> out{};
        for (std::size_t column = 0; column < monomial_count; ++column)
            out[column] = raw_evaluation_column(monomials[column]);
        return out;
    }
    // Keep construction of G separate from elimination.  Besides mirroring
    // Sections 5 and 6 of the specification, this keeps each constexpr
    // calculation comfortably within conservative compiler step limits.
    constexpr static std::array<raw_point_bits, monomial_count> raw_evaluation_columns =
        make_raw_evaluation_columns();
    constexpr static pivot_columns_t select_pivot_columns()
    {
        pivot_columns_t out{};
        std::array<raw_point_bits, domain_size> basis{};
        std::array<bool, domain_size> occupied{};
        for (std::size_t column = 0; column < monomial_count; ++column)
        {
            raw_point_bits candidate = raw_evaluation_columns[column];
            for (std::size_t row = 0; row < domain_size; ++row)
            {
                if (!raw_get_bit(candidate, row))
                    continue;
                if (occupied[row])
                    raw_xor(candidate, basis[row]);
                else
                {
                    basis[row] = candidate;
                    occupied[row] = true;
                    out.columns[out.rank++] = static_cast<uint16_t>(column);
                    break;
                }
            }
        }
        return out;
    }
    // These elimination products are initialized once, before main.  Keeping
    // the finite F2 elimination executable (instead of embedding a generated
    // opaque table) makes the mandated construction directly auditable on
    // every platform and avoids compiler-specific constexpr step limits.
    inline static const pivot_columns_t pivot_columns = select_pivot_columns();

    constexpr static std::size_t augmented_word_count = (2 * domain_size + 63) / 64;
    using augmented_row = std::array<uint64_t, augmented_word_count>;
    using augmented_matrix = std::array<augmented_row, domain_size>;
    struct elimination_state_t
    {
        augmented_matrix rows{};
        bool invertible = true;
    };
    struct inverse_t
    {
        std::array<point_bits, domain_size> rows{};
        bool invertible = true;
    };
    constexpr static augmented_matrix make_augmented_matrix()
    {
        augmented_matrix matrix{};
        for (std::size_t row = 0; row < domain_size; ++row)
        {
            for (std::size_t column = 0; column < domain_size; ++column)
            {
                const uint16_t monomial = monomials[pivot_columns.columns[column]];
                if ((points[row] & monomial) == monomial)
                    set_bit(matrix[row], column);
            }
            set_bit(matrix[row], domain_size + row);
        }
        return matrix;
    }
    inline static const augmented_matrix initial_augmented_matrix = make_augmented_matrix();

    constexpr static elimination_state_t forward_eliminate()
    {
        elimination_state_t out{initial_augmented_matrix, true};
        for (std::size_t column = 0; column < domain_size; ++column)
        {
            std::size_t pivot = column;
            while (pivot < domain_size && !get_bit(out.rows[pivot], column))
                ++pivot;
            if (pivot == domain_size)
            {
                out.invertible = false;
                return out;
            }
            if (pivot != column)
                std::swap(out.rows[pivot], out.rows[column]);
            for (std::size_t row = column + 1; row < domain_size; ++row)
                if (get_bit(out.rows[row], column))
                    xor_bits(out.rows[row], out.rows[column]);
        }
        return out;
    }
    inline static const elimination_state_t forward_state = forward_eliminate();

    constexpr static elimination_state_t backward_eliminate()
    {
        elimination_state_t out = forward_state;
        for (std::size_t column = domain_size; column-- > 0;)
            for (std::size_t row = 0; row < column; ++row)
                if (get_bit(out.rows[row], column))
                    xor_bits(out.rows[row], out.rows[column]);
        return out;
    }
    inline static const elimination_state_t reduced_state = backward_eliminate();

    constexpr static inverse_t extract_pivot_inverse()
    {
        inverse_t out{};
        for (std::size_t row = 0; row < domain_size; ++row)
            for (std::size_t column = 0; column < domain_size; ++column)
                if (get_bit(reduced_state.rows[row], domain_size + column))
                    set_bit(out.rows[row], column);
        return out;
    }
    inline static const inverse_t pivot_inverse = extract_pivot_inverse();

    constexpr static std::array<point_bits, monomial_count> make_reconstruction_rows()
    {
        std::array<point_bits, monomial_count> out{};
        for (std::size_t row = 0; row < domain_size; ++row)
            out[pivot_columns.columns[row]] = pivot_inverse.rows[row];
        return out;
    }
    // A_rec in the mandated 299 x 296 orientation and integer-mask order.
    inline static const std::array<point_bits, monomial_count> reconstruction_rows =
        make_reconstruction_rows();

    constexpr static std::array<monomial_bits, domain_size> make_reconstruction_columns()
    {
        std::array<monomial_bits, domain_size> out{};
        for (std::size_t rank = 0; rank < monomial_count; ++rank)
            for (std::size_t column = 0; column < domain_size; ++column)
                if (get_bit(reconstruction_rows[rank], column))
                    set_bit(out[column], rank);
        return out;
    }
    inline static const std::array<monomial_bits, domain_size> reconstruction_columns =
        make_reconstruction_columns();
    static bool right_inverse_is_valid()
    {
        for (std::size_t row = 0; row < domain_size; ++row)
        {
            const monomial_bits g_row = evaluation_row(points[row]);
            for (std::size_t column = 0; column < domain_size; ++column)
            {
                unsigned parity = 0;
                for (std::size_t word = 0; word < monomial_word_count; ++word)
                    parity ^= std::popcount(g_row[word] & reconstruction_columns[column][word]) &
                              1u;
                if ((parity != 0) != (row == column))
                    return false;
            }
        }
        return true;
    }
    constexpr static std::size_t clamp_active(std::size_t active_points)
    {
        return active_points < domain_size ? active_points : domain_size;
    }
    template <typename T>
    static void reconstruct_compact(const T* point_values, std::size_t active_points, T* coeffs)
    {
        const std::size_t used = clamp_active(active_points);
        for (std::size_t rank = 0; rank < monomial_count; ++rank)
        {
            T value = T::set_zero();
            for (std::size_t source = 0; source < used; ++source)
                if (get_bit(reconstruction_rows[rank], source))
                    value += point_values[source];
            coeffs[rank] = value;
        }
    }
    template <std::size_t ActivePoints, typename T>
    static void reconstruct_compact_fixed(const T* point_values, T* coeffs)
    {
        constexpr std::size_t used = clamp_active(ActivePoints);
        // M4RM-style multiplication by the public binary reconstruction
        // matrix.  Six adjacent input values are expanded into all 64 XOR
        // combinations with 63 additions, after which every output consumes
        // one public-indexed combination.  This is generic in the matrix
        // dimensions and T, and all control flow/table indices depend only on
        // public reconstruction data (never on point_values).
        constexpr std::size_t group_bits = 6;
        constexpr std::size_t table_size = std::size_t{1} << group_bits;
        const T zero = T::set_zero();
        for (std::size_t rank = 0; rank < monomial_count; ++rank)
            coeffs[rank] = zero;
        for (std::size_t group_begin = 0; group_begin < used; group_begin += group_bits)
        {
            const std::size_t group_size =
                (used - group_begin < group_bits) ? used - group_begin : group_bits;
            const std::size_t combinations = std::size_t{1} << group_size;
            std::array<T, table_size> table;
            table[0] = zero;
            for (std::size_t mask = 1; mask < combinations; ++mask)
            {
                const std::size_t bit = static_cast<std::size_t>(std::countr_zero(mask));
                table[mask] = table[mask & (mask - 1)];
                table[mask] += point_values[group_begin + bit];
            }
            const std::size_t word = group_begin / 64;
            const std::size_t shift = group_begin % 64;
            const uint64_t pattern_mask = (uint64_t{1} << group_size) - 1;
            for (std::size_t rank = 0; rank < monomial_count; ++rank)
            {
                uint64_t pattern = reconstruction_rows[rank][word] >> shift;
                if (shift + group_size > 64)
                    pattern |= reconstruction_rows[rank][word + 1] << (64 - shift);
                coeffs[rank] += table[pattern & pattern_mask];
            }
        }
    }
    template <typename T> static void zeta_transform(T* coeffs)
    {
        for (std::size_t bit = 0; bit < eta; ++bit)
            for (std::size_t pos = zeta_schedule.offsets[bit];
                 pos < zeta_schedule.offsets[bit + 1]; ++pos)
                coeffs[zeta_schedule.destinations[pos]] += coeffs[zeta_schedule.sources[pos]];
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

template <> struct encoding<12> : dense_d3_encoding<12>
{};

static_assert(encoding<10>::points.size() == 384);
static_assert(encoding<11>::points.size() == 560);
static_assert(encoding<12>::points.size() == 296);

} // namespace sdsign::optimal_encoding_detail

#endif
