#ifndef GFSMALL_IMPL_HPP
#define GFSMALL_IMPL_HPP

#include "block.hpp"
#include "util.hpp"
#include <cassert>
#include <cstdint>

#include <cstring>

namespace sdsign
{

// Reduction of a polynomial of degree at most 63 modulo the GF(256) polynomial.
inline block128 gf256_barret_reduce_64(block128 x)
{
    // SDSIGN_ASSERT that the upper 64 bits are zero.
    SDSIGN_ASSERT(x.get_high64() == 0);
    // The modulus polynomial.
    const auto q8 = block128::set_low64(0b100011011);
    // X^64 // q8
    const auto m = block128::set_low64(0x11a59bcec98e023);
    return x ^ block128::clmul_hl(block128::clmul_ll(x, m), q8);
}

// Reduction of a polynomial of degree at most 119 modulo the GF(256) polynomial.
// (high 64 bits of the result might contain garbage)
inline block128 gf256_barret_reduce_120(block128 x)
{
    // SDSIGN_ASSERT that the upper 8 bits are zero.
    SDSIGN_ASSERT((x.get_high64() & 0xff00000000000000) == 0);
    // The modulus polynomial.
    const auto q8 = block128::set_low64(0b100011011);
    // X^64 // q8
    const auto m = block128::set_low64(0x11a59bcec98e023);
    // X^64 mod q8
    const auto r = block128::set_low64(0b01001101);
    const auto y = x ^ block128::clmul_hl(x, r);
    return y ^ block128::clmul_hl(block128::clmul_ll(y, m), q8);
}

inline uint8_t gf256_compress_gf16_subfield(uint8_t x)
{
    // 0, 6, 7, 2
    uint8_t y = 0;
    y |= x & 1;
    y |= (x >> 5) & 6;
    y |= (x << 1) & 8;
    return y;
}

inline block128 gf256_batch_compress_gf16_subfield(block128 x)
{
    // 0, 6, 7, 2
    const uint16x8_t data = vreinterpretq_u16_u32(x.data);
    const uint16x8_t mask_1 = vdupq_n_u16(0x0101);
    const uint16x8_t mask_6 = vdupq_n_u16(0x0606);
    const uint16x8_t mask_8 = vdupq_n_u16(0x0808);
    const uint16x8_t output =
        vorrq_u16(vorrq_u16(vandq_u16(data, mask_1),
                            vandq_u16(vshrq_n_u16(data, 5), mask_6)),
                  vandq_u16(vshlq_n_u16(data, 1), mask_8));
    return {vreinterpretq_u32_u16(output)};
}

inline uint8_t gf256_decompress_gf16_subfield(uint8_t x)
{
    // basis: [1, W^6 + W^4, W^7 + W^5 + W^4, W^3 + W^2]
    uint8_t y = 0;
    y |= x & 0b0001;
    y |= (x & 0b1000) >> 1;
    y |= x & 0b1000;
    y |= ((x & 0b0010) << 3) ^ ((x & 0b0100) << 2);
    y |= (x & 0b0100) << 3;
    y |= (x & 0b0010) << 5;
    y |= (x & 0b0100) << 5;
    return y;
}

inline uint8_t gf256_gf16_norm(uint8_t in)
{
    const auto x = block128::set_low32(in);     //   7
    const auto x2 = block128::clmul_ll(x, x);   //  14
    const auto x4 = block128::clmul_ll(x2, x2); //  28
    const auto x8 = block128::clmul_ll(x4, x4); //  56
    const auto x9 = block128::clmul_ll(x, x8);  //  63
    // const auto x16 = block128::clmul_ll(x8, x8);                           // 112
    const auto x17 = block128::clmul_ll(x8, x9); // 119
    const auto y = gf256_barret_reduce_120(x17);
    uint8_t out;
    memcpy(&out, &y, 1);
    return out;
}

inline block128 gf256_batch_compressed_gf16_inverse(block128 x)
{
    constexpr std::array<uint64_t, 2> lut_data = {0x090506080a0f0100, 0x020b0c0d0e030704};
    const uint8x16_t output =
        vqtbl1q_u8(vreinterpretq_u8_u64(vld1q_u64(lut_data.data())),
                   vreinterpretq_u8_u32(x.data));
    return {vreinterpretq_u32_u8(output)};
}

inline block128 compress_gf16_vector(block128 x)
{
    const uint8x16_t data = vreinterpretq_u8_u32(x.data);
    const uint8x16_t compressed =
        vorrq_u8(data, vreinterpretq_u8_u16(vshrq_n_u16(vreinterpretq_u16_u8(data), 4)));
    constexpr std::array<uint64_t, 2> shuffle_data = {0x0e0c0a0806040200,
                                                      0x8080808080808080};
    const block128 y = {vreinterpretq_u32_u8(
        vqtbl1q_u8(compressed, vreinterpretq_u8_u64(vld1q_u64(shuffle_data.data()))))};
    // SDSIGN_ASSERT that the upper 64 bits are zero.
    SDSIGN_ASSERT(y.get_high64() == 0);
    return y;
}

inline uint8_t gf256_gf16_invnorm(uint8_t in)
{
    const auto x = block128::set_low32(in);                                //  8
    const auto x2 = block128::clmul_ll(x, x);                              // 16
    const auto x4 = block128::clmul_ll(x2, x2);                            // 32
    const auto x8 = gf256_barret_reduce_64(block128::clmul_ll(x4, x4));    //  8
    const auto x16 = block128::clmul_ll(x8, x8);                           // 16
    const auto x32 = block128::clmul_ll(x16, x16);                         // 32
    const auto x64 = gf256_barret_reduce_64(block128::clmul_ll(x32, x32)); //  8
    const auto x128 = block128::clmul_ll(x64, x64);                        // 16
    const auto x36 = gf256_barret_reduce_64(block128::clmul_ll(x4, x32));  //  8
    const auto x10 = block128::clmul_ll(x2, x8);                           // 24
    const auto x191 = block128::clmul_ll(x64, x128);                       // 24
    const auto x46 = block128::clmul_ll(x36, x10);                         // 32
    const auto x238 = block128::clmul_ll(x46, x191);                       // 56
    const auto y = gf256_barret_reduce_64(x238);
    uint8_t out;
    memcpy(&out, &y, 1);
    return out;
}

template <size_t n> inline void gf256_gf16_batch_invnorm(uint8_t* out, const uint8_t* in)
{
    SDSIGN_ASSERT(n % 2 == 0);

    std::array<uint8_t, 16> buf;
    block128 block;
    constexpr auto complete_blocks = n / 16;
    for (size_t i = 0; i < complete_blocks; ++i, in += 16, out += 8)
    {
        memcpy(buf.data(), in, buf.size());
        // compute norms -> GF(16) subfield
        for (size_t j = 0; j < 16; ++j)
            buf[j] = gf256_gf16_norm(buf[j]);
        memcpy(&block, buf.data(), sizeof(block));
        // compress to 4 bits
        block = gf256_batch_compress_gf16_subfield(block);
        // invert in GF(16)
        block = gf256_batch_compressed_gf16_inverse(block);
        // write into output
        block = compress_gf16_vector(block);
        memcpy(out, &block, sizeof(block) / 2);
    }
    if constexpr (constexpr auto remainder = n % 16)
    {
        memcpy(buf.data(), in, remainder);
        // compute norms -> GF(16) subfield
        for (size_t j = 0; j < remainder; ++j)
            buf[j] = gf256_gf16_norm(buf[j]);
        memcpy(&block, buf.data(), sizeof(block));
        // compress to 4 bits
        block = gf256_batch_compress_gf16_subfield(block);
        // invert in GF(16)
        block = gf256_batch_compressed_gf16_inverse(block);
        // write into output
        block = compress_gf16_vector(block);
        memcpy(out, &block, remainder / 2);
    }
}

} // namespace sdsign

#endif
