#ifndef SDSIGN_TX_WITNESS_HPP
#define SDSIGN_TX_WITNESS_HPP

#include "../aes_defs.hpp"

#include <array>
#include <cstddef>
#include <cstdint>
#include <cstring>

namespace sdsign::tx::native
{

constexpr uint8_t gf_mul(uint8_t a, uint8_t b)
{
    uint8_t p = 0;
    for (int i = 0; i < 8; ++i)
    {
        if (b & 1)
            p ^= a;
        const bool hi = a & 0x80;
        a = static_cast<uint8_t>(a << 1);
        if (hi)
            a ^= 0x1b;
        b >>= 1;
    }
    return p;
}

constexpr uint8_t gf_pow(uint8_t a, unsigned e)
{
    uint8_t r = 1;
    while (e)
    {
        if (e & 1)
            r = gf_mul(r, a);
        a = gf_mul(a, a);
        e >>= 1;
    }
    return r;
}

constexpr std::array<uint8_t, 256> make_sbox()
{
    std::array<uint8_t, 256> s{};
    for (unsigned x = 0; x < 256; ++x)
    {
        const uint8_t inv = x ? gf_pow(static_cast<uint8_t>(x), 254) : 0;
        uint8_t y = inv;
        for (int i = 1; i < 5; ++i)
            y ^= static_cast<uint8_t>((inv << i) | (inv >> (8 - i)));
        s[x] = static_cast<uint8_t>(y ^ 0x63);
    }
    return s;
}

inline constexpr std::array<uint8_t, 256> sbox = make_sbox();

struct key_schedule
{
    std::array<std::array<uint8_t, 16>, 11> rk;
};

inline key_schedule expand(const uint8_t* key)
{
    key_schedule ks;
    uint8_t w[176];
    std::memcpy(w, key, 16);
    for (std::size_t i = 4; i < 44; ++i)
    {
        uint8_t t[4];
        std::memcpy(t, &w[4 * (i - 1)], 4);
        if (i % 4 == 0)
        {
            const uint8_t t0 = t[0];
            t[0] = static_cast<uint8_t>(sbox[t[1]] ^ aes_round_constants[i / 4 - 1]);
            t[1] = sbox[t[2]];
            t[2] = sbox[t[3]];
            t[3] = sbox[t0];
        }
        for (std::size_t b = 0; b < 4; ++b)
            w[4 * i + b] = static_cast<uint8_t>(w[4 * (i - 4) + b] ^ t[b]);
    }
    for (std::size_t r = 0; r < 11; ++r)
        std::memcpy(ks.rk[r].data(), &w[16 * r], 16);
    return ks;
}

inline void sub_shift(uint8_t* out, const uint8_t* in)
{
    for (std::size_t c = 0; c < 4; ++c)
        for (std::size_t r = 0; r < 4; ++r)
            out[4 * c + r] = sbox[in[4 * ((c + r) % 4) + r]];
}

inline void mix(uint8_t* s)
{
    for (std::size_t c = 0; c < 4; ++c)
    {
        uint8_t a[4];
        std::memcpy(a, &s[4 * c], 4);
        for (std::size_t r = 0; r < 4; ++r)
            s[4 * c + r] = static_cast<uint8_t>(gf_mul(a[r], 2) ^ gf_mul(a[(r + 1) % 4], 3) ^
                                                a[(r + 2) % 4] ^ a[(r + 3) % 4]);
    }
}

inline uint8_t invnorm_compressed(uint8_t x)
{
    const uint8_t y = gf_pow(x, 238);
    uint8_t z = 0;
    z |= y & 1;
    z |= (y >> 5) & 6;
    z |= (y << 1) & 8;
    return z;
}

inline void key_witness(uint8_t* w, const key_schedule& ks)
{
    std::memcpy(w, ks.rk[0].data(), 16);
    for (std::size_t r = 1; r <= 10; ++r)
        std::memcpy(w + 16 + 4 * (r - 1), ks.rk[r].data(), 4);
}

inline void encrypt(uint8_t* out, const key_schedule& ks, const uint8_t* in, uint8_t* w = nullptr)
{
    uint8_t s[16];
    for (std::size_t i = 0; i < 16; ++i)
        s[i] = static_cast<uint8_t>(in[i] ^ ks.rk[0][i]);
    for (std::size_t r = 1; r <= 10; ++r)
    {
        if (w && r < 10 && (r & 1) == 1)
        {
            for (std::size_t b = 0; b < 8; ++b)
                w[b] = static_cast<uint8_t>(invnorm_compressed(s[2 * b]) |
                                            (invnorm_compressed(s[2 * b + 1]) << 4));
            w += 8;
        }
        uint8_t after[16];
        sub_shift(after, s);
        if (w && r < 10 && (r & 1) == 0)
        {
            std::memcpy(w, after, 16);
            w += 16;
        }
        std::memcpy(s, after, 16);
        if (r < 10)
            mix(s);
        for (std::size_t i = 0; i < 16; ++i)
            s[i] ^= ks.rk[r][i];
    }
    std::memcpy(out, s, 16);
}

inline bool key_ok(const uint8_t* key) { return (key[0] & 3) != 3; }

} // namespace sdsign::tx::native

#endif
