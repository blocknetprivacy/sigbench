extern "C" {

constexpr unsigned int BLAKE2B_BLOCK_BYTES = 128U;
constexpr unsigned int BLAKE2B_OUT_BYTES = 64U;


struct Blake2bState {
    unsigned long long h[8];
    unsigned long long t0;
    unsigned long long t1;
    unsigned char buf[BLAKE2B_BLOCK_BYTES];
    unsigned int buflen;
};

constexpr unsigned long long BLAKE2B_IV[8] = {
    0x6A09E667F3BCC908ULL,
    0xBB67AE8584CAA73BULL,
    0x3C6EF372FE94F82BULL,
    0xA54FF53A5F1D36F1ULL,
    0x510E527FADE682D1ULL,
    0x9B05688C2B3E6C1FULL,
    0x1F83D9ABFB41BD6BULL,
    0x5BE0CD19137E2179ULL,
};

constexpr unsigned char BLAKE2B_SIGMA[12][16] = {
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

__device__ __forceinline__ void device_memcpy(
    unsigned char *dst,
    const unsigned char *src,
    unsigned int len
) {
    for (unsigned int i = 0U; i < len; ++i) {
        dst[i] = src[i];
    }
}

__device__ __forceinline__ void store_u32_le(unsigned char *dst, unsigned int value) {
    dst[0] = static_cast<unsigned char>(value & 0xFFU);
    dst[1] = static_cast<unsigned char>((value >> 8) & 0xFFU);
    dst[2] = static_cast<unsigned char>((value >> 16) & 0xFFU);
    dst[3] = static_cast<unsigned char>((value >> 24) & 0xFFU);
}

__device__ __forceinline__ void store_u64_le(
    unsigned char *dst,
    unsigned long long value
) {
    for (unsigned int i = 0U; i < 8U; ++i) {
        dst[i] = static_cast<unsigned char>((value >> (8U * i)) & 0xFFULL);
    }
}

__device__ __forceinline__ unsigned long long load_u64_le(const unsigned char *src) {
    unsigned long long value = 0ULL;
    for (unsigned int i = 0U; i < 8U; ++i) {
        value |= static_cast<unsigned long long>(src[i]) << (8U * i);
    }
    return value;
}

__device__ __forceinline__ unsigned long long rotr64(
    unsigned long long x,
    unsigned int n
) {
    return (x >> n) | (x << (64U - n));
}

__device__ __forceinline__ void blake2b_g(
    unsigned long long v[16],
    unsigned int a,
    unsigned int b,
    unsigned int c,
    unsigned int d,
    unsigned long long x,
    unsigned long long y
) {
    v[a] = v[a] + v[b] + x;
    v[d] = rotr64(v[d] ^ v[a], 32U);
    v[c] = v[c] + v[d];
    v[b] = rotr64(v[b] ^ v[c], 24U);
    v[a] = v[a] + v[b] + y;
    v[d] = rotr64(v[d] ^ v[a], 16U);
    v[c] = v[c] + v[d];
    v[b] = rotr64(v[b] ^ v[c], 63U);
}

__device__ __forceinline__ void blake2b_compress(
    Blake2bState &state,
    const unsigned char block[BLAKE2B_BLOCK_BYTES],
    unsigned long long last_block_flag
) {
    unsigned long long m[16];
    unsigned long long v[16];
    for (unsigned int i = 0U; i < 16U; ++i) {
        m[i] = load_u64_le(block + (i * 8U));
    }
    for (unsigned int i = 0U; i < 8U; ++i) {
        v[i] = state.h[i];
        v[i + 8U] = BLAKE2B_IV[i];
    }
    v[12] ^= state.t0;
    v[13] ^= state.t1;
    v[14] ^= last_block_flag;

    for (unsigned int round = 0U; round < 12U; ++round) {
        const unsigned char *s = BLAKE2B_SIGMA[round];
        blake2b_g(v, 0U, 4U, 8U, 12U, m[s[0]], m[s[1]]);
        blake2b_g(v, 1U, 5U, 9U, 13U, m[s[2]], m[s[3]]);
        blake2b_g(v, 2U, 6U, 10U, 14U, m[s[4]], m[s[5]]);
        blake2b_g(v, 3U, 7U, 11U, 15U, m[s[6]], m[s[7]]);
        blake2b_g(v, 0U, 5U, 10U, 15U, m[s[8]], m[s[9]]);
        blake2b_g(v, 1U, 6U, 11U, 12U, m[s[10]], m[s[11]]);
        blake2b_g(v, 2U, 7U, 8U, 13U, m[s[12]], m[s[13]]);
        blake2b_g(v, 3U, 4U, 9U, 14U, m[s[14]], m[s[15]]);
    }

    for (unsigned int i = 0U; i < 8U; ++i) {
        state.h[i] ^= v[i] ^ v[i + 8U];
    }
}

__device__ __forceinline__ void blake2b_init(Blake2bState &state, unsigned int out_len) {
    for (unsigned int i = 0U; i < 8U; ++i) {
        state.h[i] = BLAKE2B_IV[i];
    }
    state.h[0] ^= 0x01010000ULL ^ static_cast<unsigned long long>(out_len);
    state.h[6] ^= 0x74656e6b636f6c62ULL;
    state.h[7] ^= 0x0031762f776f702fULL;
    state.t0 = 0ULL;
    state.t1 = 0ULL;
    state.buflen = 0U;
    for (unsigned int i = 0U; i < BLAKE2B_BLOCK_BYTES; ++i) {
        state.buf[i] = 0U;
    }
}

__device__ __forceinline__ void blake2b_increment_counter(
    Blake2bState &state,
    unsigned int increment
) {
    const unsigned long long prev = state.t0;
    state.t0 += static_cast<unsigned long long>(increment);
    if (state.t0 < prev) {
        state.t1 += 1ULL;
    }
}

__device__ __forceinline__ void blake2b_update(
    Blake2bState &state,
    const unsigned char *input,
    unsigned int input_len
) {
    unsigned int offset = 0U;
    while (offset < input_len) {
        const unsigned int space = BLAKE2B_BLOCK_BYTES - state.buflen;
        const unsigned int take = (input_len - offset < space)
            ? (input_len - offset)
            : space;
        device_memcpy(state.buf + state.buflen, input + offset, take);
        state.buflen += take;
        offset += take;

        if (state.buflen == BLAKE2B_BLOCK_BYTES) {
            blake2b_increment_counter(state, BLAKE2B_BLOCK_BYTES);
            blake2b_compress(state, state.buf, 0ULL);
            state.buflen = 0U;
        }
    }
}

__device__ __forceinline__ void blake2b_final(
    Blake2bState &state,
    unsigned char *out,
    unsigned int out_len
) {
    blake2b_increment_counter(state, state.buflen);
    for (unsigned int i = state.buflen; i < BLAKE2B_BLOCK_BYTES; ++i) {
        state.buf[i] = 0U;
    }
    blake2b_compress(state, state.buf, 0xFFFFFFFFFFFFFFFFULL);

    unsigned char digest[BLAKE2B_OUT_BYTES];
    for (unsigned int i = 0U; i < 8U; ++i) {
        store_u64_le(digest + (i * 8U), state.h[i]);
    }
    for (unsigned int i = 0U; i < out_len; ++i) {
        out[i] = digest[i];
    }
}

__device__ __forceinline__ void blake2b_hash(
    const unsigned char *input,
    unsigned int input_len,
    unsigned char *out,
    unsigned int out_len
) {
    Blake2bState state;
    blake2b_init(state, out_len);
    blake2b_update(state, input, input_len);
    blake2b_final(state, out, out_len);
}

constexpr unsigned int MAX_HEADER_BYTES = 128U;

__global__ void blake2b512_mine_kernel(
    const unsigned char *__restrict__ header,
    unsigned int header_len,
    unsigned long long nonce_base,
    unsigned int per_thread,
    unsigned long long *__restrict__ sink,
    unsigned char *__restrict__ first_digest
) {
    const unsigned long long gid = static_cast<unsigned long long>(blockIdx.x) * blockDim.x + threadIdx.x;
    unsigned char h[MAX_HEADER_BYTES];
    for (unsigned int i = 0U; i < header_len && i < MAX_HEADER_BYTES; ++i) {
        h[i] = header[i];
    }
    unsigned long long acc = 0ULL;
    for (unsigned int k = 0U; k < per_thread; ++k) {
        const unsigned long long nonce = nonce_base + gid * per_thread + k;
        unsigned char nb[8];
        store_u64_le(nb, nonce);
        unsigned char out[64];
        Blake2bState state;
        blake2b_init(state, 64U);
        blake2b_update(state, h, header_len);
        blake2b_update(state, nb, 8U);
        blake2b_final(state, out, 64U);
        if (gid == 0ULL && k == 0U) {
            for (unsigned int i = 0U; i < 64U; ++i) {
                first_digest[i] = out[i];
            }
        }
        acc ^= load_u64_le(out);
    }
    sink[gid] = acc;
}


}
