#ifndef SDSIGN_TX_AES_ZK_INC
#define SDSIGN_TX_AES_ZK_INC

#include "../aes_defs.hpp"
#include "../quicksilver.hpp"

#include <algorithm>
#include <array>
#include <cstddef>
#include <cstdint>

namespace sdsign::tx::zk
{

inline constexpr std::size_t AES_BLOCK = 16;
inline constexpr std::size_t AES_R = 10;
inline constexpr std::size_t AES_COLS = 4;
inline constexpr std::size_t KS_SBOXES = 40;
inline constexpr std::size_t KEY_WITNESS_BITS = 128 + 8 * KS_SBOXES;
inline constexpr std::size_t ENC_WITNESS_BITS = 8 * (AES_BLOCK * AES_R * 3 / 4 - AES_BLOCK);
inline constexpr std::size_t KEY_CONSTRAINTS = 2 * KS_SBOXES + 1;
inline constexpr std::size_t ENC_CONSTRAINTS = 3 * AES_BLOCK * AES_R / 2;
inline constexpr std::size_t RK_BITS = 8 * AES_BLOCK * (AES_R + 1);
inline constexpr std::size_t RK_BYTES = AES_BLOCK * (AES_R + 1);

template <typename QS> using bits128 = std::array<quicksilver_gf2<QS>, 128>;

template <typename QS> struct round_key
{
    std::array<quicksilver_gf2<QS>, RK_BITS> bits;
    std::array<quicksilver_gfsecpar<QS>, RK_BYTES> bytes;
    std::array<quicksilver_gfsecpar<QS, 2>, RK_BYTES> bytes_sq;
};

template <typename QS, std::size_t deg>
inline void square_8_bits(quicksilver_gf2<QS, deg>* y, const quicksilver_gf2<QS, deg>* x)
{
    y[7] = x[6] + x[7];
    y[0] = x[0] + x[4] + x[6];
    y[1] = x[4] + y[7];
    y[2] = x[1] + x[5];
    y[3] = x[4] + x[5] + y[7];
    y[4] = x[2] + x[4] + x[7];
    y[5] = x[5] + x[6];
    y[6] = x[3] + x[5];
}

template <std::size_t N, typename QS, std::size_t deg>
inline void gf256_gf2_conjugates(const QS* qs, std::array<quicksilver_gfsecpar<QS, deg>, N>& y,
                                 const std::array<quicksilver_gf2<QS, deg>, 8>& x)
{
    static_assert(N > 1 && N <= 8);
    auto t = qs->template const_gf2_2d_array<8, 2, deg>();
    y[0] = quicksilver_gfsecpar<QS, deg>::combine_8_bits(x.data());
    square_8_bits(t[0].data(), x.data());
    for (std::size_t i = 0; i < N - 1; ++i)
    {
        y[i + 1] = quicksilver_gfsecpar<QS, deg>::combine_8_bits(t[i & 1].data());
        square_8_bits(t[(i & 1) ^ 1].data(), t[i & 1].data());
    }
    y[N - 1] = quicksilver_gfsecpar<QS, deg>::combine_8_bits(t[N & 1].data());
}

template <typename QS, std::size_t deg>
inline void decompress_gf16_subfield(std::array<quicksilver_gf2<QS, deg>, 8>& y,
                                     const std::array<quicksilver_gf2<QS, deg>, 4>& x)
{
    y[0] = x[0];
    y[1] = quicksilver_gf2<QS, deg>(poly1::set_zero(), x[0]);
    y[2] = x[3];
    y[3] = x[3];
    y[4] = x[1] + x[2];
    y[5] = x[2];
    y[6] = x[1];
    y[7] = x[2];
}

constexpr std::size_t shift_rows_perm(std::size_t row, std::size_t col)
{
    return 4 * ((col + row) % AES_COLS) + row;
}

constexpr std::size_t inverse_shift_rows_perm(std::size_t row, std::size_t col)
{
    return 4 * ((col + AES_COLS - row) % AES_COLS) + row;
}

template <bool square, typename QS, std::size_t deg>
inline quicksilver_gfsecpar<QS, deg>
sbox_affine(const std::array<quicksilver_gfsecpar<QS, deg>, 8>& in)
{
    constexpr auto S = QS::secpar_v;
    constexpr std::size_t t = square ? 1 : 0;
    constexpr std::array<std::array<uint8_t, 9>, 2> coefficients = {{
        {0x05, 0x09, 0xf9, 0x25, 0xf4, 0x01, 0xb5, 0x8f, 0x63},
        {0x11, 0x41, 0x07, 0x7d, 0x56, 0x01, 0xfc, 0xcf, 0xc2},
    }};
    constexpr auto C = coefficients[t];
    return poly_secpar<S>::from_8_byte(C[0]) * in[0 + t] +
           poly_secpar<S>::from_8_byte(C[1]) * in[1 + t] +
           poly_secpar<S>::from_8_byte(C[2]) * in[2 + t] +
           poly_secpar<S>::from_8_byte(C[3]) * in[3 + t] +
           poly_secpar<S>::from_8_byte(C[4]) * in[4 + t] +
           poly_secpar<S>::from_8_byte(C[5]) * in[5 + t] +
           poly_secpar<S>::from_8_byte(C[6]) * in[6 + t] +
           poly_secpar<S>::from_8_byte(C[7]) * in[(7 + t) % 8] +
           quicksilver_gfsecpar<QS, deg>(poly_secpar<S>::from_8_byte(C[8]), in[0]);
}

template <bool square, typename QS, std::size_t deg, std::size_t deg2>
inline void mix_columns_and_add_roundkey(const QS* qs,
                                         std::array<quicksilver_gfsecpar<QS, deg>, AES_BLOCK>& st,
                                         const quicksilver_gfsecpar<QS, deg2>* rk)
{
    constexpr auto S = QS::secpar_v;
    const poly_secpar<S> c_two =
        square ? poly_secpar<S>::from_8_byte(0x04) : poly_secpar<S>::from_8_byte(0x02);
    const poly_secpar<S> c_three =
        square ? poly_secpar<S>::from_8_byte(0x05) : poly_secpar<S>::from_8_byte(0x03);
    auto col = qs->template const_gfsecpar_array<4, deg>();
    for (std::size_t c = 0; c < AES_COLS; ++c)
    {
        std::copy_n(&st[c * 4], 4, col.data());
        for (std::size_t r = 0; r < 4; ++r)
            st[c * 4 + r] = c_two * col[r] + c_three * col[(r + 1) % 4] + col[(r + 2) % 4] +
                            col[(r + 3) % 4] + rk[c * 4 + r];
    }
}

template <typename QS, std::size_t deg>
inline void bitwise_mix_columns_and_add_roundkey(
    const QS* qs, std::array<std::array<quicksilver_gf2<QS, deg>, 8>, AES_BLOCK>& st,
    const quicksilver_gf2<QS, deg>* rk)
{
    auto a = qs->template const_gf2_2d_array<8, 4, deg>();
    auto b = qs->template const_gf2_2d_array<8, 4, deg>();
    for (std::size_t c = 0; c < AES_COLS; ++c)
    {
        const std::size_t byte_off = c * 4;
        const std::size_t bit_off = c * 32;
        std::copy_n(&st[byte_off], 4, a.begin());
        for (std::size_t r = 0; r < 4; ++r)
        {
            b[r][0] = a[r][7];
            b[r][1] = a[r][0] + a[r][7];
            b[r][2] = a[r][1];
            b[r][3] = a[r][2] + a[r][7];
            b[r][4] = a[r][3] + a[r][7];
            b[r][5] = a[r][4];
            b[r][6] = a[r][5];
            b[r][7] = a[r][6];
        }
        for (std::size_t i = 0; i < 8; ++i)
        {
            st[byte_off][i] = rk[bit_off + i] + b[0][i] + a[3][i] + a[2][i] + b[1][i] + a[1][i];
            st[byte_off + 1][i] =
                rk[bit_off + i + 8] + b[1][i] + a[0][i] + a[3][i] + b[2][i] + a[2][i];
            st[byte_off + 2][i] =
                rk[bit_off + i + 16] + b[2][i] + a[1][i] + a[0][i] + b[3][i] + a[3][i];
            st[byte_off + 3][i] =
                rk[bit_off + i + 24] + b[3][i] + a[2][i] + a[1][i] + b[0][i] + a[0][i];
        }
    }
}

template <typename QS, std::size_t deg>
inline void bitwise_inverse_shift_rows_and_sbox_affine(
    const QS* qs, std::array<std::array<quicksilver_gf2<QS, deg>, 8>, AES_BLOCK>& out,
    const std::array<std::array<quicksilver_gf2<QS, deg>, 8>, AES_BLOCK>& in)
{
    const auto c_zero = quicksilver_gf2<QS>(poly1::set_zero(), qs);
    const auto c_one = quicksilver_gf2<QS>(poly1::set_one(), qs);
    for (std::size_t c = 0; c < AES_COLS; ++c)
        for (std::size_t r = 0; r < 4; ++r)
        {
            const auto& x = in[c * 4 + r];
            auto& y = out[shift_rows_perm(r, c)];
            for (std::size_t i = 0; i < 8; ++i)
            {
                const auto c_i = (i & 0b101) ? c_zero : c_one;
                y[i] = x[(i + 7) % 8] + x[(i + 5) % 8] + x[(i + 2) % 8] + c_i;
            }
        }
}

template <typename QS> void key_constraints(QS* qs, std::size_t off, round_key<QS>& key)
{
    {
        const auto k0 = quicksilver_gfsecpar<QS>(qs->get_witness_bit(off));
        const auto k1 = quicksilver_gfsecpar<QS>(qs->get_witness_bit(off + 1));
        qs->add_constraint(k0 * k1);
    }

    auto& rk = key.bits;
    for (std::size_t i = 0; i < 128; ++i)
        rk[i] = qs->get_witness_bit(off + i);
    std::size_t wd = off + 128;
    for (std::size_t w = 4; w < 4 * (AES_R + 1); ++w)
    {
        if (w % 4 == 0)
        {
            for (std::size_t i = 0; i < 32; ++i)
                rk[32 * w + i] = qs->get_witness_bit(wd + i);
            wd += 32;
        }
        else
            for (std::size_t i = 0; i < 32; ++i)
                rk[32 * w + i] = rk[32 * (w - 4) + i] + rk[32 * (w - 1) + i];
    }

    auto inv_bits = qs->template const_gf2_array<8 * KS_SBOXES>();
    {
        std::size_t iw = 0;
        std::size_t rcon = 0;
        for (std::size_t j = 0; j < KS_SBOXES; ++j)
        {
            auto so = qs->template const_gf2_array<8>();
            for (std::size_t i = 0; i < 8; ++i)
                so[i] = qs->get_witness_bit(off + 128 + j * 8 + i) + rk[iw + 8 * (j % 4) + i];
            if (j % 4 == 0)
            {
                for (std::size_t i = 0; i < 8; ++i)
                    if ((aes_round_constants[rcon] >> i) & 1)
                        so[i] = so[i] + quicksilver_gf2<QS>(poly1::set_one(), qs);
                ++rcon;
            }
            auto* io = &inv_bits[8 * j];
            for (std::size_t i = 0; i < 8; ++i)
                io[(i + 1) % 8] = so[i];
            for (std::size_t i = 0; i < 8; ++i)
                io[(i + 3) % 8] = io[(i + 3) % 8] + so[i];
            for (std::size_t i = 0; i < 8; ++i)
                io[(i + 6) % 8] = io[(i + 6) % 8] + so[i];
            io[0] = io[0] + quicksilver_gf2<QS>(poly1::set_one(), qs);
            io[2] = io[2] + quicksilver_gf2<QS>(poly1::set_one(), qs);
            if (j % 4 == 3)
                iw += 128;
        }
    }

    for (std::size_t b = 0; b < RK_BYTES; ++b)
    {
        key.bytes[b] = quicksilver_gfsecpar<QS>::combine_8_bits(&rk[8 * b]);
        key.bytes_sq[b] = key.bytes[b] * key.bytes[b];
    }

    auto inv = qs->template const_gfsecpar_array<KS_SBOXES>();
    auto inv_sq = qs->template const_gfsecpar_array<KS_SBOXES>();
    {
        auto sq = qs->template const_gf2_array<8>();
        for (std::size_t j = 0; j < KS_SBOXES; ++j)
        {
            square_8_bits(sq.data(), &inv_bits[8 * j]);
            inv[j] = quicksilver_gfsecpar<QS>::combine_8_bits(&inv_bits[8 * j]);
            inv_sq[j] = quicksilver_gfsecpar<QS>::combine_8_bits(sq.data());
        }
    }

    std::size_t iw = 4 * 3;
    auto sq = qs->template const_gf2_array<8>();
    for (std::size_t j = 0; j < KS_SBOXES / 4; ++j)
    {
        for (std::size_t r = 0; r < 4; ++r)
        {
            square_8_bits(sq.data(), &rk[8 * (iw + r)]);
            const auto x = key.bytes[iw + r];
            const auto x_sq = quicksilver_gfsecpar<QS>::combine_8_bits(sq.data());
            const auto y = inv[4 * j + (r + 3) % 4];
            const auto y_sq = inv_sq[4 * j + (r + 3) % 4];
            qs->add_constraint(x_sq * y + x);
            qs->add_constraint(x * y_sq + y);
        }
        iw += 16;
    }
}

template <typename QS>
void enc_constraints(QS* qs, std::size_t off, const round_key<QS>& key, const bits128<QS>& in,
                     const bits128<QS>& out)
{
    auto state_bits = qs->template const_gf2_2d_array<8, AES_BLOCK>();
    auto state_bits_2 = qs->template const_gf2_2d_array<8, AES_BLOCK>();
    auto cinv = qs->template const_gf2_array<4>();
    auto dinv = qs->template const_gf2_array<8>();
    auto inv_conj = qs->template const_gfsecpar_2d_array<4, AES_BLOCK>();
    auto st_conj = qs->template const_gfsecpar_2d_array<8, AES_BLOCK>();
    auto st_inv_conj = qs->template const_gfsecpar_2d_array<8, AES_BLOCK, 2>();
    auto st_sq = qs->template const_gfsecpar_2d_array<AES_BLOCK, 2, 2>();

    for (std::size_t b = 0; b < AES_BLOCK; ++b)
        for (std::size_t i = 0; i < 8; ++i)
            state_bits[b][i] = key.bits[8 * b + i] + in[8 * b + i];

    for (std::size_t r = 0; r < AES_R / 2; ++r)
    {
        for (std::size_t b = 0; b < AES_BLOCK; ++b)
        {
            for (std::size_t i = 0; i < 4; ++i)
                cinv[i] = qs->get_witness_bit(off + i);
            off += 4;
            decompress_gf16_subfield(dinv, cinv);
            gf256_gf2_conjugates<4>(qs, inv_conj[b], dinv);
            gf256_gf2_conjugates<8>(qs, st_conj[b], state_bits[b]);
            qs->add_constraint(inv_conj[b][0] * st_conj[b][1] * st_conj[b][4] + st_conj[b][0]);
            for (std::size_t i = 0; i < 8; ++i)
                st_inv_conj[b][i] = st_conj[b][(i + 4) % 8] * inv_conj[b][i % 4];
        }

        for (std::size_t row = 0; row < 4; ++row)
            for (std::size_t col = 0; col < AES_COLS; ++col)
            {
                const auto in_index = 4 * col + row;
                const auto out_index = inverse_shift_rows_perm(row, col);
                st_sq[0][out_index] = sbox_affine<false>(st_inv_conj[in_index]);
                st_sq[1][out_index] = sbox_affine<true>(st_inv_conj[in_index]);
            }

        const auto rk_index = (2 * r + 1) * AES_BLOCK;
        mix_columns_and_add_roundkey<false>(qs, st_sq[0], &key.bytes[rk_index]);
        mix_columns_and_add_roundkey<true>(qs, st_sq[1], &key.bytes_sq[rk_index]);

        if (r == AES_R / 2 - 1)
        {
            const auto* last = &key.bits[8 * AES_BLOCK * AES_R];
            for (std::size_t b = 0; b < AES_BLOCK; ++b)
                for (std::size_t i = 0; i < 8; ++i)
                    state_bits[b][i] = last[8 * b + i] + out[8 * b + i];
        }
        else
        {
            for (std::size_t b = 0; b < AES_BLOCK; ++b)
            {
                for (std::size_t i = 0; i < 8; ++i)
                    state_bits[b][i] = qs->get_witness_bit(off + i);
                off += 8;
            }
        }

        bitwise_inverse_shift_rows_and_sbox_affine(qs, state_bits_2, state_bits);

        for (std::size_t b = 0; b < AES_BLOCK; ++b)
        {
            auto sqb = qs->template const_gf2_array<8>();
            square_8_bits(sqb.data(), state_bits_2[b].data());
            const auto x = quicksilver_gfsecpar<QS>::combine_8_bits(state_bits_2[b].data());
            const auto x_sq = quicksilver_gfsecpar<QS>::combine_8_bits(sqb.data());
            const auto y = st_sq[0][b];
            const auto y_sq = st_sq[1][b];
            qs->add_constraint(x_sq * y + x);
            qs->add_constraint(x * y_sq + y);
        }

        if (r != AES_R / 2 - 1)
            bitwise_mix_columns_and_add_roundkey(qs, state_bits,
                                                 &key.bits[(2 * r + 2) * 8 * AES_BLOCK]);
    }
}

template <typename QS> bits128<QS> witness_bits128(const QS* qs, std::size_t off)
{
    bits128<QS> out;
    for (std::size_t i = 0; i < 128; ++i)
        out[i] = qs->get_witness_bit(off + i);
    return out;
}

template <typename QS> bits128<QS> const_bits128(const QS* qs, const uint8_t* bytes)
{
    bits128<QS> out;
    for (std::size_t i = 0; i < 128; ++i)
        out[i] = quicksilver_gf2<QS>(poly1::load_offset8(&bytes[i / 8], i % 8), qs);
    return out;
}

} // namespace sdsign::tx::zk

#endif
