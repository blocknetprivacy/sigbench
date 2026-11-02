#include <metal_stdlib>
#include <metal_atomic>
using namespace metal;

constant uint BLAKE2B_BLOCK_BYTES = 128U;
constant uint BLAKE2B_OUT_BYTES = 64U;
constant ulong BLAKE2B_PERSONAL_LO = 0x74656e6b636f6c62ULL;
constant ulong BLAKE2B_PERSONAL_HI = 0x0031762f776f702fULL;


constant ulong BLAKE2B_IV[8] = {
    0x6A09E667F3BCC908ULL,
    0xBB67AE8584CAA73BULL,
    0x3C6EF372FE94F82BULL,
    0xA54FF53A5F1D36F1ULL,
    0x510E527FADE682D1ULL,
    0x9B05688C2B3E6C1FULL,
    0x1F83D9ABFB41BD6BULL,
    0x5BE0CD19137E2179ULL,
};

constant uchar BLAKE2B_SIGMA[12][16] = {
    {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15},
    {14, 10, 4, 8, 9, 15, 13, 6, 1, 12, 0, 2, 11, 7, 5, 3},
    {11, 8, 12, 0, 5, 2, 15, 13, 10, 14, 3, 6, 7, 1, 9, 4},
    {7, 9, 3, 1, 13, 12, 11, 14, 2, 6, 5, 10, 4, 0, 15, 8},
    {9, 0, 5, 7, 2, 4, 10, 15, 14, 1, 11, 12, 6, 8, 3, 13},
    {2, 12, 6, 10, 0, 11, 8, 3, 4, 13, 7, 5, 15, 14, 1, 9},
    {12, 5, 1, 15, 14, 13, 4, 10, 0, 7, 6, 3, 9, 2, 8, 11},
    {13, 11, 7, 14, 12, 1, 3, 9, 5, 0, 15, 4, 8, 6, 2, 10},
    {6, 15, 14, 9, 11, 3, 0, 8, 12, 2, 13, 7, 1, 4, 10, 5},
    {10, 2, 8, 4, 7, 6, 1, 5, 15, 11, 9, 14, 3, 12, 13, 0},
    {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15},
    {14, 10, 4, 8, 9, 15, 13, 6, 1, 12, 0, 2, 11, 7, 5, 3},
};

inline void store_u32_le(thread uchar *dst, uint value) {
    dst[0] = uchar(value & 0xFFU);
    dst[1] = uchar((value >> 8) & 0xFFU);
    dst[2] = uchar((value >> 16) & 0xFFU);
    dst[3] = uchar((value >> 24) & 0xFFU);
}

inline void store_u64_le(thread uchar *dst, ulong value) {
    for (uint i = 0U; i < 8U; ++i) {
        dst[i] = uchar((value >> (8U * i)) & 0xFFULL);
    }
}

inline ulong load_u64_le(thread const uchar *src) {
    ulong value = 0ULL;
    for (uint i = 0U; i < 8U; ++i) {
        value |= ulong(src[i]) << (8U * i);
    }
    return value;
}

inline ulong load_u64_le_device(device const uchar *src) {
    ulong value = 0ULL;
    for (uint i = 0U; i < 8U; ++i) {
        value |= ulong(src[i]) << (8U * i);
    }
    return value;
}

inline ulong rotr64(ulong x, uint n) {
    return (x >> n) | (x << (64U - n));
}

struct Blake2bState {
    ulong h[8];
    ulong t0;
    ulong t1;
    uchar buf[128];
    uint buflen;
};

inline void blake2b_g(thread ulong v[16], uint a, uint b, uint c, uint d, ulong x, ulong y) {
    v[a] = v[a] + v[b] + x;
    v[d] = rotr64(v[d] ^ v[a], 32U);
    v[c] = v[c] + v[d];
    v[b] = rotr64(v[b] ^ v[c], 24U);
    v[a] = v[a] + v[b] + y;
    v[d] = rotr64(v[d] ^ v[a], 16U);
    v[c] = v[c] + v[d];
    v[b] = rotr64(v[b] ^ v[c], 63U);
}

inline void blake2b_compress(thread Blake2bState &state, thread const uchar *block, ulong last_block_flag) {
    ulong m[16];
    ulong v[16];
    for (uint i = 0U; i < 16U; ++i) {
        m[i] = load_u64_le(block + (i * 8U));
    }
    for (uint i = 0U; i < 8U; ++i) {
        v[i] = state.h[i];
        v[i + 8U] = BLAKE2B_IV[i];
    }
    v[12] ^= state.t0;
    v[13] ^= state.t1;
    v[14] ^= last_block_flag;

    for (uint round = 0U; round < 12U; ++round) {
        constant const uchar *s = BLAKE2B_SIGMA[round];
        blake2b_g(v, 0U, 4U, 8U, 12U, m[s[0]], m[s[1]]);
        blake2b_g(v, 1U, 5U, 9U, 13U, m[s[2]], m[s[3]]);
        blake2b_g(v, 2U, 6U, 10U, 14U, m[s[4]], m[s[5]]);
        blake2b_g(v, 3U, 7U, 11U, 15U, m[s[6]], m[s[7]]);
        blake2b_g(v, 0U, 5U, 10U, 15U, m[s[8]], m[s[9]]);
        blake2b_g(v, 1U, 6U, 11U, 12U, m[s[10]], m[s[11]]);
        blake2b_g(v, 2U, 7U, 8U, 13U, m[s[12]], m[s[13]]);
        blake2b_g(v, 3U, 4U, 9U, 14U, m[s[14]], m[s[15]]);
    }

    for (uint i = 0U; i < 8U; ++i) {
        state.h[i] ^= v[i] ^ v[i + 8U];
    }
}

inline void blake2b_init(thread Blake2bState &state, uint out_len) {
    for (uint i = 0U; i < 8U; ++i) {
        state.h[i] = BLAKE2B_IV[i];
    }
    state.h[0] ^= 0x01010000ULL ^ ulong(out_len);
    state.h[6] ^= BLAKE2B_PERSONAL_LO;
    state.h[7] ^= BLAKE2B_PERSONAL_HI;
    state.t0 = 0ULL;
    state.t1 = 0ULL;
    state.buflen = 0U;
    for (uint i = 0U; i < BLAKE2B_BLOCK_BYTES; ++i) {
        state.buf[i] = 0U;
    }
}

inline void blake2b_increment_counter(thread Blake2bState &state, uint increment) {
    ulong prev = state.t0;
    state.t0 += ulong(increment);
    if (state.t0 < prev) {
        state.t1 += 1ULL;
    }
}

inline void blake2b_update(thread Blake2bState &state, thread const uchar *input, uint input_len) {
    uint offset = 0U;
    while (offset < input_len) {
        uint space = BLAKE2B_BLOCK_BYTES - state.buflen;
        uint take = (input_len - offset < space) ? (input_len - offset) : space;
        for (uint i = 0U; i < take; ++i) {
            state.buf[state.buflen + i] = input[offset + i];
        }
        state.buflen += take;
        offset += take;

        if (state.buflen == BLAKE2B_BLOCK_BYTES) {
            blake2b_increment_counter(state, BLAKE2B_BLOCK_BYTES);
            blake2b_compress(state, state.buf, 0ULL);
            state.buflen = 0U;
        }
    }
}

inline void blake2b_update_device(thread Blake2bState &state, device const uchar *input, uint input_len) {
    uint offset = 0U;
    while (offset < input_len) {
        uint space = BLAKE2B_BLOCK_BYTES - state.buflen;
        uint take = (input_len - offset < space) ? (input_len - offset) : space;
        for (uint i = 0U; i < take; ++i) {
            state.buf[state.buflen + i] = input[offset + i];
        }
        state.buflen += take;
        offset += take;

        if (state.buflen == BLAKE2B_BLOCK_BYTES) {
            blake2b_increment_counter(state, BLAKE2B_BLOCK_BYTES);
            blake2b_compress(state, state.buf, 0ULL);
            state.buflen = 0U;
        }
    }
}

inline void blake2b_final(thread Blake2bState &state, thread uchar *out, uint out_len) {
    blake2b_increment_counter(state, state.buflen);
    for (uint i = state.buflen; i < BLAKE2B_BLOCK_BYTES; ++i) {
        state.buf[i] = 0U;
    }
    blake2b_compress(state, state.buf, 0xFFFFFFFFFFFFFFFFULL);

    uchar digest[BLAKE2B_OUT_BYTES];
    for (uint i = 0U; i < 8U; ++i) {
        store_u64_le(digest + (i * 8U), state.h[i]);
    }
    for (uint i = 0U; i < out_len; ++i) {
        out[i] = digest[i];
    }
}

inline void blake2b_hash(thread const uchar *input, uint input_len, thread uchar *out, uint out_len) {
    Blake2bState state;
    blake2b_init(state, out_len);
    blake2b_update(state, input, input_len);
    blake2b_final(state, out, out_len);
}

constant uint MAX_HEADER_BYTES = 128U;

kernel void blake2b512_mine_kernel(
    device const uchar  *header       [[buffer(0)]],
    device ulong        *sink         [[buffer(1)]],
    device uchar        *first_digest [[buffer(2)]],
    constant uint       &header_len   [[buffer(3)]],
    constant ulong      &nonce_base   [[buffer(4)]],
    constant uint       &per_thread   [[buffer(5)]],
    uint gid [[thread_position_in_grid]]
) {
    uchar h[MAX_HEADER_BYTES];
    uint hl = min(header_len, MAX_HEADER_BYTES);
    for (uint i = 0U; i < hl; ++i) {
        h[i] = header[i];
    }
    ulong acc = 0ULL;
    for (uint k = 0U; k < per_thread; ++k) {
        ulong nonce = nonce_base + ulong(gid) * ulong(per_thread) + ulong(k);
        uchar nb[8];
        store_u64_le(nb, nonce);
        uchar out[64];
        Blake2bState state;
        blake2b_init(state, 64U);
        blake2b_update(state, h, hl);
        blake2b_update(state, nb, 8U);
        blake2b_final(state, out, 64U);
        if (gid == 0U && k == 0U) {
            for (uint i = 0U; i < 64U; ++i) {
                first_digest[i] = out[i];
            }
        }
        acc ^= load_u64_le(out);
    }
    sink[gid] = acc;
}

inline ulong bswap64(ulong x) {
    x = ((x & 0x00FF00FF00FF00FFULL) << 8) | ((x >> 8) & 0x00FF00FF00FF00FFULL);
    x = ((x & 0x0000FFFF0000FFFFULL) << 16) | ((x >> 16) & 0x0000FFFF0000FFFFULL);
    return (x << 32) | (x >> 32);
}

kernel void blake2b512_pow_best(
    device const ulong *words      [[buffer(0)]],
    device ulong2      *best       [[buffer(1)]],
    constant ulong     &nonce_base [[buffer(2)]],
    constant uint      &per_thread [[buffer(3)]],
    uint gid [[thread_position_in_grid]]
) {
    ulong m[16];
    for (uint i = 0U; i < 16U; ++i) {
        m[i] = words[i];
    }
    const ulong m11 = m[11] & 0xFFFFFFFFULL;
    ulong h0[8];
    for (uint i = 0U; i < 8U; ++i) {
        h0[i] = BLAKE2B_IV[i];
    }
    h0[0] ^= 0x01010040ULL;
    h0[6] ^= BLAKE2B_PERSONAL_LO;
    h0[7] ^= BLAKE2B_PERSONAL_HI;
    ulong best_score = 0xFFFFFFFFFFFFFFFFULL;
    ulong best_nonce = 0ULL;
    for (uint k = 0U; k < per_thread; ++k) {
        const ulong nonce = nonce_base + ulong(gid) * ulong(per_thread) + ulong(k);
        m[11] = m11 | (nonce << 32);
        m[12] = nonce >> 32;
        ulong v[16];
        for (uint i = 0U; i < 8U; ++i) {
            v[i] = h0[i];
            v[i + 8U] = BLAKE2B_IV[i];
        }
        v[12] ^= 100ULL;
        v[14] = ~v[14];
        for (uint round = 0U; round < 12U; ++round) {
            constant const uchar *s = BLAKE2B_SIGMA[round];
            blake2b_g(v, 0U, 4U, 8U, 12U, m[s[0]], m[s[1]]);
            blake2b_g(v, 1U, 5U, 9U, 13U, m[s[2]], m[s[3]]);
            blake2b_g(v, 2U, 6U, 10U, 14U, m[s[4]], m[s[5]]);
            blake2b_g(v, 3U, 7U, 11U, 15U, m[s[6]], m[s[7]]);
            blake2b_g(v, 0U, 5U, 10U, 15U, m[s[8]], m[s[9]]);
            blake2b_g(v, 1U, 6U, 11U, 12U, m[s[10]], m[s[11]]);
            blake2b_g(v, 2U, 7U, 8U, 13U, m[s[12]], m[s[13]]);
            blake2b_g(v, 3U, 4U, 9U, 14U, m[s[14]], m[s[15]]);
        }
        const ulong score = bswap64(h0[0] ^ v[0] ^ v[8]);
        if (score < best_score) {
            best_score = score;
            best_nonce = nonce;
        }
    }
    best[gid] = ulong2(best_score, best_nonce);
}
