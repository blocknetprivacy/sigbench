#ifndef SDSIGN_PKP_OPTIMAL_ENCODING_HPP
#define SDSIGN_PKP_OPTIMAL_ENCODING_HPP

#include <array>
#include <bit>
#include <cstddef>
#include <cstdint>

namespace sdsign::pkp_optimal
{

constexpr bool bit(uint16_t x, std::size_t i) { return ((x >> i) & 1u) != 0; }

constexpr bool binomial_is_odd(std::size_t n, std::size_t k)
{
    return (k & ~n) == 0;
}

template <std::size_t Eta> struct representative_set;

// Coordinates, from least- to most-significant bit, are
// (z1,z2,z3,z4,z5,z6,y), exactly as in Section 2.
template <> struct representative_set<7>
{
    constexpr static std::size_t eta = 7;
    constexpr static std::size_t degree = 3;
    constexpr static std::size_t capacity = 62;
    constexpr static std::size_t membership_count = 2;

    static constexpr uint8_t membership(uint16_t point)
    {
        const bool z1 = bit(point, 0);
        const bool z2 = bit(point, 1);
        const bool z3 = bit(point, 2);
        const bool z4 = bit(point, 3);
        const bool z5 = bit(point, 4);
        const bool z6 = bit(point, 5);
        const bool y = bit(point, 6);

        const unsigned w = std::popcount(static_cast<unsigned>((point >> 1) & 0x1fu));
        const bool a = (w & 1u) != 0;
        const bool b = ((w >> 1) & 1u) != 0;
        const bool L = z3 && (z2 ^ z4 ^ z5);
        const bool q1 = (a && b) ^ L ^ (y && (true ^ a ^ b ^ L));
        const bool q2 = (z1 && b) ^ (z4 && z5 && z6) ^ (z2 && z3) ^
                        (y && ((z1 && !a) ^ (z2 && z3)));
        return static_cast<uint8_t>(q1 | (static_cast<uint8_t>(q2) << 1));
    }

    static constexpr bool contains(uint16_t point) { return membership(point) == 0; }
};

// Coordinates are A=(0,1,2), B=(3,4,5), alpha=6, beta=7.
// Q_U is evaluated in its block-Pascal form from Equation (24), without an
// expanded ANF or a point table.
template <> struct representative_set<8>
{
    constexpr static std::size_t eta = 8;
    constexpr static std::size_t degree = 3;
    constexpr static std::size_t capacity = 90;
    constexpr static std::size_t membership_count = 3;

    constexpr static uint16_t A = 0x007u;
    constexpr static uint16_t B = 0x038u;
    constexpr static uint16_t alpha = 0x040u;
    constexpr static uint16_t beta = 0x080u;
    constexpr static uint16_t full = 0x0ffu;
    constexpr static std::array<uint16_t, 6> U = {
        A | B | alpha,
        A | B | beta,
        A | alpha | beta,
        B | alpha | beta,
        A | B,
        full,
    };

    static constexpr bool pascal_q(uint16_t point, uint16_t u)
    {
        point &= full;
        if ((point & static_cast<uint16_t>(full ^ u)) != 0)
            return false;

        const std::size_t missing =
            std::popcount(static_cast<unsigned>(static_cast<uint16_t>(u & ~point)));
        const std::size_t max_degree = std::popcount(static_cast<unsigned>(u)) - 5;
        bool value = false;
        for (std::size_t j = 0; j <= max_degree; ++j)
            value ^= binomial_is_odd(missing, j);
        return value;
    }

    static constexpr uint8_t membership(uint16_t point)
    {
        std::array<bool, 6> Q{};
        for (std::size_t i = 0; i < Q.size(); ++i)
            Q[i] = pascal_q(point, U[i]);
        const bool q1 = Q[0] ^ Q[2];
        const bool q2 = Q[1] ^ Q[3];
        const bool q3 = Q[2] ^ Q[3] ^ Q[4] ^ Q[5];
        return static_cast<uint8_t>(q1 | (static_cast<uint8_t>(q2) << 1) |
                                    (static_cast<uint8_t>(q3) << 2));
    }

    static constexpr bool contains(uint16_t point)
    {
        point &= full;
        const bool in_D = point == 0 || point == (A | alpha) || point == (B | beta);
        bool removed_external = false;
        for (const uint16_t u : U)
            removed_external |= point == u;
        const bool outside_hamming_basis = std::popcount(static_cast<unsigned>(point)) >= 5;
        return in_D || (outside_hamming_basis && !removed_external);
    }
};

// Coordinates, from least- to most-significant bit, are
// (x0,x1,x2,y0,y1,y2,t,z1,z2), exactly as in Section 4.
template <> struct representative_set<9>
{
    constexpr static std::size_t eta = 9;
    constexpr static std::size_t degree = 3;
    constexpr static std::size_t capacity = 128;
    constexpr static std::size_t membership_count = 2;

    static constexpr uint8_t cyclic_bit(uint16_t point, std::size_t base, std::size_t i)
    {
        return static_cast<uint8_t>(bit(point, base + (i % 3)));
    }

    static constexpr uint8_t membership(uint16_t point)
    {
        const bool t = bit(point, 6);
        bool F1 = bit(point, 3) && bit(point, 4) && bit(point, 5);
        bool F2 = false;
        for (std::size_t i = 0; i < 3; ++i)
        {
            const bool xi = cyclic_bit(point, 0, i);
            const bool xi1 = cyclic_bit(point, 0, i + 1);
            const bool xi2 = cyclic_bit(point, 0, i + 2);
            const bool yi = cyclic_bit(point, 3, i);
            const bool yi1 = cyclic_bit(point, 3, i + 1);
            F1 ^= xi && xi1 && (yi != t);
            F2 ^= yi && ((xi1 && (xi2 != yi1)) != (t && xi2));
        }
        const bool q1 = bit(point, 7) != F1;
        const bool q2 = bit(point, 8) != F2;
        return static_cast<uint8_t>(q1 | (static_cast<uint8_t>(q2) << 1));
    }

    static constexpr bool contains(uint16_t point)
    {
        const uint16_t base = static_cast<uint16_t>(point & 0x07fu);
        const uint16_t graph_bits = static_cast<uint16_t>(point & 0x180u);
        const uint16_t expected = static_cast<uint16_t>(membership(base) << 7);
        return graph_bits == expected;
    }
};

template <std::size_t Eta> constexpr std::size_t count_members()
{
    std::size_t count = 0;
    for (uint16_t point = 0; point < (uint16_t{1} << Eta); ++point)
        count += representative_set<Eta>::contains(point) ? 1 : 0;
    return count;
}

template <std::size_t Eta> consteval auto enumerate_members()
{
    using set = representative_set<Eta>;
    std::array<uint16_t, set::capacity> points{};
    std::size_t out = 0;
    for (uint16_t point = 0; point < (uint16_t{1} << Eta); ++point)
    {
        if (set::contains(point))
            points[out++] = point;
    }
    return points;
}

template <std::size_t Eta>
constexpr std::size_t degree3_monomial_count =
    1 + Eta + (Eta * (Eta - 1)) / 2 + (Eta * (Eta - 1) * (Eta - 2)) / 6;

template <std::size_t Eta> consteval auto degree3_monomials()
{
    std::array<uint16_t, degree3_monomial_count<Eta>> masks{};
    std::size_t out = 0;
    masks[out++] = 0;
    for (std::size_t i = 0; i < Eta; ++i)
        masks[out++] = static_cast<uint16_t>(uint16_t{1} << i);
    for (std::size_t i = 0; i < Eta; ++i)
        for (std::size_t j = i + 1; j < Eta; ++j)
            masks[out++] = static_cast<uint16_t>((uint16_t{1} << i) | (uint16_t{1} << j));
    for (std::size_t i = 0; i < Eta; ++i)
        for (std::size_t j = i + 1; j < Eta; ++j)
            for (std::size_t k = j + 1; k < Eta; ++k)
                masks[out++] = static_cast<uint16_t>((uint16_t{1} << i) |
                                                     (uint16_t{1} << j) |
                                                     (uint16_t{1} << k));
    return masks;
}

template <std::size_t Eta>
constexpr std::size_t degree3_monomial_rank(uint16_t mask)
{
    constexpr auto monomials = degree3_monomials<Eta>();
    for (std::size_t rank = 0; rank < monomials.size(); ++rank)
        if (monomials[rank] == mask)
            return rank;
    return monomials.size();
}

// Packed ANF programs for the three genuinely different canonical membership
// constructions. Bit j of an entry is the coefficient of that monomial in
// membership equation j. The programs share the reconstruction monomial cache,
// but their construction-specific formulas are kept separate here.
template <std::size_t Eta> struct canonical_membership_program;

template <> struct canonical_membership_program<7>
{
    constexpr static std::size_t equation_count = 2;

    static consteval std::array<uint8_t, degree3_monomial_count<7>> make()
    {
        std::array<uint8_t, degree3_monomial_count<7>> out{};
        const auto add = [&](std::size_t equation, uint16_t mask) {
            out[degree3_monomial_rank<7>(mask)] ^= static_cast<uint8_t>(1u << equation);
        };
        constexpr uint16_t y = uint16_t{1} << 6;

        // q1 = E3 + L + y(1 + E1 + E2 + L), with
        // E_j in (z2,...,z6) and L=z3(z2+z4+z5).
        for (std::size_t i = 1; i <= 5; ++i)
            for (std::size_t j = i + 1; j <= 5; ++j)
                for (std::size_t k = j + 1; k <= 5; ++k)
                    add(0, static_cast<uint16_t>((1u << i) | (1u << j) | (1u << k)));
        add(0, static_cast<uint16_t>((1u << 2) | (1u << 1)));
        add(0, static_cast<uint16_t>((1u << 2) | (1u << 3)));
        add(0, static_cast<uint16_t>((1u << 2) | (1u << 4)));
        add(0, y);
        for (std::size_t i = 1; i <= 5; ++i)
            add(0, static_cast<uint16_t>(y | (1u << i)));
        for (std::size_t i = 1; i <= 5; ++i)
            for (std::size_t j = i + 1; j <= 5; ++j)
                add(0, static_cast<uint16_t>(y | (1u << i) | (1u << j)));
        add(0, static_cast<uint16_t>(y | (1u << 2) | (1u << 1)));
        add(0, static_cast<uint16_t>(y | (1u << 2) | (1u << 3)));
        add(0, static_cast<uint16_t>(y | (1u << 2) | (1u << 4)));

        // q2 = z1 E2 + z4 z5 z6 + z2 z3
        //      + y(z1(1+E1) + z2 z3).
        for (std::size_t i = 1; i <= 5; ++i)
            for (std::size_t j = i + 1; j <= 5; ++j)
                add(1, static_cast<uint16_t>(1u | (1u << i) | (1u << j)));
        add(1, static_cast<uint16_t>((1u << 3) | (1u << 4) | (1u << 5)));
        add(1, static_cast<uint16_t>((1u << 1) | (1u << 2)));
        add(1, static_cast<uint16_t>(y | 1u));
        for (std::size_t i = 1; i <= 5; ++i)
            add(1, static_cast<uint16_t>(y | 1u | (1u << i)));
        add(1, static_cast<uint16_t>(y | (1u << 1) | (1u << 2)));
        return out;
    }

};

template <> struct canonical_membership_program<8>
{
    constexpr static std::size_t equation_count = 3;

    static consteval std::array<uint8_t, degree3_monomial_count<8>> make()
    {
        using set = representative_set<8>;
        constexpr std::array<uint8_t, 6> equation_masks = {
            0x1u, 0x2u, 0x5u, 0x6u, 0x4u, 0x4u,
        };
        std::array<uint8_t, degree3_monomial_count<8>> out{};
        for (std::size_t q = 0; q < set::U.size(); ++q)
        {
            std::array<uint8_t, 256> anf{};
            for (std::size_t point = 0; point < anf.size(); ++point)
                anf[point] = static_cast<uint8_t>(set::pascal_q(
                    static_cast<uint16_t>(point), set::U[q]));
            for (std::size_t bit_idx = 0; bit_idx < 8; ++bit_idx)
                for (std::size_t mask = 0; mask < anf.size(); ++mask)
                    if ((mask & (std::size_t{1} << bit_idx)) != 0)
                        anf[mask] ^= anf[mask ^ (std::size_t{1} << bit_idx)];
            for (std::size_t mask = 0; mask < anf.size(); ++mask)
                if (anf[mask] != 0)
                    out[degree3_monomial_rank<8>(static_cast<uint16_t>(mask))] ^=
                        equation_masks[q];
        }
        return out;
    }

};

template <> struct canonical_membership_program<9>
{
    constexpr static std::size_t equation_count = 2;

    static consteval std::array<uint8_t, degree3_monomial_count<9>> make()
    {
        std::array<uint8_t, degree3_monomial_count<9>> out{};
        const auto add = [&](std::size_t equation, uint16_t mask) {
            out[degree3_monomial_rank<9>(mask)] ^= static_cast<uint8_t>(1u << equation);
        };
        add(0, uint16_t{1} << 7); // z1
        add(0, static_cast<uint16_t>((1u << 3) | (1u << 4) | (1u << 5)));
        for (std::size_t i = 0; i < 3; ++i)
        {
            const std::size_t i1 = (i + 1) % 3;
            const std::size_t i2 = (i + 2) % 3;
            add(0, static_cast<uint16_t>((1u << i) | (1u << i1) | (1u << (3 + i))));
            add(0, static_cast<uint16_t>((1u << i) | (1u << i1) | (1u << 6)));

            add(1, static_cast<uint16_t>((1u << (3 + i)) | (1u << i1) | (1u << i2)));
            add(1, static_cast<uint16_t>((1u << (3 + i)) | (1u << i1) |
                                         (1u << (3 + i1))));
            add(1, static_cast<uint16_t>((1u << (3 + i)) | (1u << 6) | (1u << i2)));
        }
        add(1, uint16_t{1} << 8); // z2
        return out;
    }

};

template <std::size_t Eta, std::size_t Rows> consteval auto make_reconstruction_coefficients()
{
    constexpr auto points = enumerate_members<Eta>();
    constexpr auto monomials = degree3_monomials<Eta>();
    constexpr std::size_t K = monomials.size();
    static_assert(Rows <= points.size());

    std::array<std::array<uint8_t, K>, Rows> out{};
    constexpr std::size_t augmented_columns = K + Rows;
    constexpr std::size_t augmented_words = (augmented_columns + 63) / 64;
    std::array<std::array<uint64_t, augmented_words>, Rows> matrix{};
    for (std::size_t row = 0; row < Rows; ++row)
    {
        for (std::size_t col = 0; col < K; ++col)
            if ((points[row] & monomials[col]) == monomials[col])
                matrix[row][col / 64] |= uint64_t{1} << (col % 64);
        const std::size_t identity_col = K + row;
        matrix[row][identity_col / 64] |= uint64_t{1} << (identity_col % 64);
    }

    std::array<std::size_t, Rows> pivots{};
    std::size_t pivot_row = 0;
    for (std::size_t col = 0; col < K && pivot_row < Rows; ++col)
    {
        std::size_t selected = pivot_row;
        while (selected < Rows &&
               ((matrix[selected][col / 64] >> (col % 64)) & 1u) == 0)
            ++selected;
        if (selected == Rows)
            continue;
        if (selected != pivot_row)
        {
            const auto tmp = matrix[pivot_row];
            matrix[pivot_row] = matrix[selected];
            matrix[selected] = tmp;
        }
        for (std::size_t row = 0; row < Rows; ++row)
        {
            if (row == pivot_row ||
                ((matrix[row][col / 64] >> (col % 64)) & 1u) == 0)
                continue;
            for (std::size_t word = 0; word < augmented_words; ++word)
                matrix[row][word] ^= matrix[pivot_row][word];
        }
        pivots[pivot_row++] = col;
    }
    if (pivot_row != Rows)
        throw "canonical representative set does not have full reconstruction rank";

    for (std::size_t coordinate = 0; coordinate < Rows; ++coordinate)
        for (std::size_t row = 0; row < Rows; ++row)
        {
            const std::size_t transform_col = K + coordinate;
            out[coordinate][pivots[row]] =
                static_cast<uint8_t>((matrix[row][transform_col / 64] >>
                                      (transform_col % 64)) &
                                     1u);
        }
    return out;
}

template <std::size_t Eta, std::size_t UsedPoints> struct polynomial_data
{
    using set = representative_set<Eta>;
    constexpr static std::size_t monomial_count = degree3_monomial_count<Eta>;
    constexpr static bool is_restricted = UsedPoints < set::capacity;
    constexpr static std::size_t membership_count =
        set::membership_count + (is_restricted ? 1 : 0);
    std::array<std::array<uint8_t, monomial_count>, UsedPoints> reconstruction{};
    std::array<std::array<uint8_t, monomial_count>, membership_count> membership{};
};

template <std::size_t Eta, std::size_t UsedPoints> constexpr auto make_restriction_coefficients()
{
    using set = representative_set<Eta>;
    constexpr auto points = enumerate_members<Eta>();
    constexpr auto monomials = degree3_monomials<Eta>();
    constexpr std::size_t K = monomials.size();
    constexpr std::size_t Rows = set::capacity;
    constexpr std::size_t augmented_words = (K + 1 + 63) / 64;
    std::array<std::array<uint64_t, augmented_words>, Rows> matrix{};
    for (std::size_t row = 0; row < Rows; ++row)
    {
        for (std::size_t col = 0; col < K; ++col)
            if ((points[row] & monomials[col]) == monomials[col])
                matrix[row][col / 64] |= uint64_t{1} << (col % 64);
        if (row >= UsedPoints)
            matrix[row][K / 64] |= uint64_t{1} << (K % 64);
    }

    std::array<std::size_t, Rows> pivots{};
    std::size_t pivot_row = 0;
    for (std::size_t col = 0; col < K && pivot_row < Rows; ++col)
    {
        std::size_t selected = pivot_row;
        while (selected < Rows &&
               ((matrix[selected][col / 64] >> (col % 64)) & 1u) == 0)
            ++selected;
        if (selected == Rows)
            continue;
        if (selected != pivot_row)
        {
            const auto tmp = matrix[pivot_row];
            matrix[pivot_row] = matrix[selected];
            matrix[selected] = tmp;
        }
        for (std::size_t row = 0; row < Rows; ++row)
        {
            if (row == pivot_row ||
                ((matrix[row][col / 64] >> (col % 64)) & 1u) == 0)
                continue;
            for (std::size_t word = 0; word < augmented_words; ++word)
                matrix[row][word] ^= matrix[pivot_row][word];
        }
        pivots[pivot_row++] = col;
    }
    if (pivot_row != Rows)
        throw "canonical representative set does not support the requested restriction";

    std::array<uint8_t, K> out{};
    for (std::size_t row = 0; row < Rows; ++row)
        out[pivots[row]] = static_cast<uint8_t>((matrix[row][K / 64] >> (K % 64)) & 1u);
    return out;
}

// Compile the canonical set description into degree-three ANF coefficients.
// The point list and the interpolation matrix are derived here; neither is a
// hand-written table.  For Category V, UsedPoints=118 selects the first 118
// canonical representatives in coordinate order from the 128-point graph and
// adds the degree-three restriction polynomial excluding the remaining 10.
template <std::size_t Eta, std::size_t UsedPoints> constexpr auto make_polynomial_data()
{
    using set = representative_set<Eta>;
    constexpr auto monomials = degree3_monomials<Eta>();
    static_assert(UsedPoints <= set::capacity);

    polynomial_data<Eta, UsedPoints> out{};
    out.reconstruction = make_reconstruction_coefficients<Eta, UsedPoints>();

    constexpr std::size_t truth_size = std::size_t{1} << Eta;
    for (std::size_t equation = 0; equation < set::membership_count; ++equation)
    {
        std::array<uint8_t, truth_size> anf{};
        for (std::size_t point = 0; point < truth_size; ++point)
            anf[point] = static_cast<uint8_t>((set::membership(point) >> equation) & 1u);
        for (std::size_t bit_idx = 0; bit_idx < Eta; ++bit_idx)
            for (std::size_t mask = 0; mask < truth_size; ++mask)
                if ((mask & (std::size_t{1} << bit_idx)) != 0)
                    anf[mask] ^= anf[mask ^ (std::size_t{1} << bit_idx)];

        for (std::size_t mask = 0; mask < truth_size; ++mask)
        {
            if (anf[mask] == 0)
                continue;
            if (std::popcount(mask) > 3)
                throw "membership map exceeds degree three";
            std::size_t col = 0;
            while (monomials[col] != mask)
                ++col;
            out.membership[equation][col] = 1;
        }
    }

    if constexpr (UsedPoints < set::capacity)
    {
        // Interpolate the public function which is zero on the retained prefix
        // and one on every omitted representative. Together with the canonical
        // equations it cuts out exactly UsedPoints.
        constexpr auto restriction_coefficients =
            make_restriction_coefficients<Eta, UsedPoints>();
        constexpr std::size_t restriction = set::membership_count;
        out.membership[restriction] = restriction_coefficients;
    }
    return out;
}

template <std::size_t Eta, std::size_t UsedPoints> struct reconstruction_support_data
{
    constexpr static std::size_t monomial_count = degree3_monomial_count<Eta>;
    std::array<std::array<uint16_t, UsedPoints>, monomial_count> columns{};
    std::array<uint16_t, monomial_count> counts{};
};

// Sparse, compile-time transpose of the derived reconstruction matrix.  This
// is an execution schedule, not a separately specified point or coefficient
// table: it is regenerated from the canonical representative construction.
template <std::size_t Eta, std::size_t UsedPoints>
consteval auto make_reconstruction_supports()
{
    constexpr auto polynomial_data = make_polynomial_data<Eta, UsedPoints>();
    reconstruction_support_data<Eta, UsedPoints> out{};
    for (std::size_t monomial = 0; monomial < out.monomial_count; ++monomial)
        for (std::size_t col = 0; col < UsedPoints; ++col)
            if (polynomial_data.reconstruction[col][monomial] != 0)
                out.columns[monomial][out.counts[monomial]++] = static_cast<uint16_t>(col);
    return out;
}

static_assert(count_members<7>() == representative_set<7>::capacity);
static_assert(count_members<8>() == representative_set<8>::capacity);
static_assert(count_members<9>() == representative_set<9>::capacity);

} // namespace sdsign::pkp_optimal

#endif
