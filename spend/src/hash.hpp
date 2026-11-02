#ifndef HASH_HPP
#define HASH_HPP

#include "block.hpp"
#include <cinttypes>
#include <cstddef>
#include <cstring>

extern "C"
{
#include "sha3/KeccakHashtimes4.h"
#include <KeccakHash.h>
}

namespace sdsign
{

struct hash_state
{
    Keccak_HashInstance ctx;

    inline int init(secpar s)
    {
        if (secpar_to_bits(s) <= 128)
            return Keccak_HashInitialize_SHAKE128(&this->ctx);
        else
            return Keccak_HashInitialize_SHAKE256(&this->ctx);
    }

    inline int update(const void* input_ptr, size_t bytes)
    {
        return Keccak_HashUpdate(&this->ctx, static_cast<const uint8_t*>(input_ptr), bytes * 8);
    }

    inline int update_byte(uint8_t b) { return this->update(&b, 1); }

    inline int finalize(void* digest, size_t bytes)
    {
        int ret = Keccak_HashFinal(&this->ctx, nullptr);
        if (ret != KECCAK_SUCCESS)
            return ret;
        return Keccak_HashSqueeze(&this->ctx, static_cast<uint8_t*>(digest), bytes * 8);
    }
};

// Mostly copied from Picnic: instances that work with 4 SHAKE states in parallel.
struct hash_state_x4
{
    Keccak_HashInstancetimes4 ctx;

    inline void init(secpar s)
    {
        if (secpar_to_bits(s) <= 128)
            Keccak_HashInitializetimes4_SHAKE128(&this->ctx);
        else
            Keccak_HashInitializetimes4_SHAKE256(&this->ctx);
    }

    inline void update(const void** data, size_t size)
    {
        const uint8_t* data_casted[4] = {static_cast<const uint8_t*>(data[0]),
                                         static_cast<const uint8_t*>(data[1]),
                                         static_cast<const uint8_t*>(data[2]),
                                         static_cast<const uint8_t*>(data[3])};
        Keccak_HashUpdatetimes4(&this->ctx, data_casted, size * 8);
    }

    inline void update_4(const void* data0, const void* data1, const void* data2, const void* data3,
                         size_t size)
    {
        const void* data[4] = {data0, data1, data2, data3};
        this->update(data, size);
    }

    inline void update_1(const void* data, size_t size)
    {
        this->update_4(data, data, data, data, size);
    }

    inline void update_1_byte(uint8_t b) { this->update_1(&b, 1); }

    inline void init_prefix(secpar s, const uint8_t prefix)
    {
        this->init(s);
        this->update_1(&prefix, sizeof(prefix));
    }

    inline void finalize(void** buffer, size_t buflen)
    {
        uint8_t* buffer_casted[4] = {static_cast<uint8_t*>(buffer[0]),
                                     static_cast<uint8_t*>(buffer[1]),
                                     static_cast<uint8_t*>(buffer[2]),
                                     static_cast<uint8_t*>(buffer[3])};
        Keccak_HashFinaltimes4(&this->ctx, nullptr);
        Keccak_HashSqueezetimes4(&this->ctx, buffer_casted, buflen * 8);
    }

    inline void finalize_4(void* buffer0, void* buffer1, void* buffer2, void* buffer3,
                           size_t buflen)
    {
        void* buffer[4] = {buffer0, buffer1, buffer2, buffer3};
        this->finalize(buffer, buflen);
    }
};

using hash_state_x8 = hash_state_x4;

// Rate (block size) in bytes of the SHAKE instance selected by hash_state::init.
template <secpar S>
inline constexpr size_t shake_rate_bytes = (secpar_to_bits(S) <= 128) ? 168 : 136;

// Byte length absorbed by shake_prg_impl before the SHAKE padding.
template <secpar S>
inline constexpr size_t shake_prg_input_bytes =
    sizeof(block_secpar<S>) + sizeof(block128) + sizeof(uint32_t) + 1;

// Number of bytes of a Keccak lane, and the stride between consecutive lanes in
// the interleaved times4 state layout used by the SIMD back-ends: lane `l` of
// instance `j` lives at byte offset `l * 4 * 8 + j * 8`.
inline constexpr size_t keccak_lane_bytes = 8;
inline constexpr size_t keccak_x4_lane_stride = 4 * keccak_lane_bytes;

inline constexpr size_t keccak_state_lanes = 25;
inline constexpr size_t keccak_state_bytes = keccak_state_lanes * keccak_lane_bytes;

// Probe, once at start-up, whether the linked times4 back-end really stores its
// state in that plain interleaved layout, so that we may read and write the raw
// state directly instead of going through AddBytes/ExtractBytes.
//
// Two independent conditions have to hold, because a back-end is free to keep
// the state in any internal representation as long as AddBytes/ExtractBytes
// translate it:
//
//   1. Before the permutation: after InitializeAll + AddBytes the raw bytes must
//      already sit at `lane * 32 + instance * 8`. This rejects back-ends that
//      store the four instances contiguously (the fallback-on-1 build) or that
//      apply an input transformation such as lane interleaving.
//   2. After the permutation: the raw bytes must still agree with the logical
//      state reported by the official ExtractBytes. This rejects back-ends whose
//      permutation leaves the state in a transformed form -- lane complementing
//      or bit interleaving both keep condition 1 while breaking condition 2.
//
// Only when both hold is direct raw access equivalent to the official
// interface. Everything in this probe uses nothing but documented PlSnP calls,
// and it never changes which values are produced -- only how they are moved.
// Result of the layout probe, split so that each condition can be inspected and
// reported separately by the tests.
struct keccak_x4_layout_probe
{
    bool size_ok = false;
    bool layout_before_permutation = false;
    bool layout_after_permutation = false;

    constexpr bool raw_access_allowed() const
    {
        return size_ok && layout_before_permutation && layout_after_permutation;
    }
};

inline keccak_x4_layout_probe probe_keccak_x4_interleaved_lanes()
{
    KeccakP1600times4_StaticInitialize();

    keccak_x4_layout_probe result;

    if (KeccakP1600times4_statesSizeInBytes != keccak_state_lanes * keccak_x4_lane_stride)
        return result;
    result.size_ok = true;

    alignas(KeccakP1600times4_statesAlignment) unsigned char states[KeccakP1600times4_statesSizeInBytes];
    KeccakP1600times4_InitializeAll(states);

    unsigned char expected[4][keccak_state_bytes];
    for (unsigned int j = 0; j < 4; ++j)
    {
        for (unsigned int b = 0; b < keccak_state_bytes; ++b)
            expected[j][b] = (unsigned char)(1 + 37 * j + 11 * b + (b >> 3));
        KeccakP1600times4_AddBytes(states, j, expected[j], 0, keccak_state_bytes);
    }

    // Condition 1: raw layout before the permutation.
    bool before_ok = true;
    for (unsigned int j = 0; j < 4; ++j)
        for (unsigned int lane = 0; lane < keccak_state_lanes; ++lane)
            if (memcmp(states + lane * keccak_x4_lane_stride + j * keccak_lane_bytes,
                       expected[j] + lane * keccak_lane_bytes, keccak_lane_bytes) != 0)
                before_ok = false;
    result.layout_before_permutation = before_ok;

    KeccakP1600times4_PermuteAll_24rounds(states);

    // Condition 2: raw layout still matches the logical state after permuting.
    bool after_ok = true;
    for (unsigned int j = 0; j < 4; ++j)
    {
        unsigned char logical[keccak_state_bytes];
        KeccakP1600times4_ExtractBytes(states, j, logical, 0, keccak_state_bytes);
        for (unsigned int lane = 0; lane < keccak_state_lanes; ++lane)
            if (memcmp(states + lane * keccak_x4_lane_stride + j * keccak_lane_bytes,
                       logical + lane * keccak_lane_bytes, keccak_lane_bytes) != 0)
                after_ok = false;
    }
    result.layout_after_permutation = after_ok;

    return result;
}

inline bool detect_keccak_x4_interleaved_lanes()
{
    return probe_keccak_x4_interleaved_lanes().raw_access_allowed();
}

// Evaluated once during dynamic initialisation, never in a hot loop. It is
// statically zero-initialised first, so even a hypothetical use before dynamic
// initialisation would only select the safe AddBytes/ExtractBytes path.
inline const bool keccak_x4_interleaved_lanes = detect_keccak_x4_interleaved_lanes();

// Four-way SHAKE where the padded input and the requested output both fit
// strictly inside one sponge block, so the whole sponge collapses to a single
// Keccak-p[1600, 24] permutation. This absorbs exactly the same message bytes
// with exactly the same 0x1F/0x80 SHAKE padding as the generic hash_state_x4
// path and therefore produces byte-identical output; it only removes the sponge
// bookkeeping around the permutation.
//
// `use_raw_state` selects how the state is accessed. It is a public build
// property (the start-up layout probe), never anything derived from the keys,
// and both branches compute the same value; when the probe fails we still take
// the single-permutation shortcut and only move the bytes through the official
// AddBytes/ExtractBytes calls.
//
// Constant time: all offsets and lengths are derived from public parameters, so
// the control flow and the memory access pattern are independent of the keys.
template <secpar S>
inline void shake_prg_x4_single_block(const block_secpar<S>* __restrict__ keys, const block128& iv,
                                      const uint32_t& tweak, size_t num_bytes,
                                      uint8_t* __restrict__ output,
                                      bool use_raw_state = keccak_x4_interleaved_lanes)
{
    constexpr size_t input_bytes = shake_prg_input_bytes<S>;
    constexpr size_t rate = shake_rate_bytes<S>;
    static_assert(input_bytes + 1 <= rate);
    // Padded input and squeezed output must each stay inside the first block.
    constexpr size_t in_lanes = (input_bytes + 1 + keccak_lane_bytes - 1) / keccak_lane_bytes;
    constexpr size_t pad_lane = rate / keccak_lane_bytes - 1;
    static_assert(in_lanes <= pad_lane);

    alignas(KeccakP1600times4_statesAlignment) unsigned char states[KeccakP1600times4_statesSizeInBytes];
    KeccakP1600times4_InitializeAll(states);

    unsigned char buffer[in_lanes * keccak_lane_bytes];
    for (unsigned int j = 0; j < 4; ++j)
    {
        memset(buffer, 0, sizeof(buffer));
        memcpy(buffer, &keys[j], sizeof(block_secpar<S>));
        memcpy(buffer + sizeof(block_secpar<S>), &iv, sizeof(block128));
        memcpy(buffer + sizeof(block_secpar<S>) + sizeof(block128), &tweak, sizeof(uint32_t));
        buffer[input_bytes - 1] = 0;
        buffer[input_bytes] = 0x1f;

        if (use_raw_state)
        {
            for (size_t lane = 0; lane < in_lanes; ++lane)
                memcpy(states + lane * keccak_x4_lane_stride + j * keccak_lane_bytes,
                       buffer + lane * keccak_lane_bytes, keccak_lane_bytes);
            states[pad_lane * keccak_x4_lane_stride + j * keccak_lane_bytes +
                   (keccak_lane_bytes - 1)] = 0x80;
        }
        else
        {
            KeccakP1600times4_AddBytes(states, j, buffer, 0, input_bytes + 1);
            KeccakP1600times4_AddByte(states, j, 0x80, rate - 1);
        }
    }

    KeccakP1600times4_PermuteAll_24rounds(states);

    if (use_raw_state)
    {
        const size_t full_lanes = num_bytes / keccak_lane_bytes;
        const size_t tail = num_bytes % keccak_lane_bytes;
        for (unsigned int j = 0; j < 4; ++j)
        {
            uint8_t* const out = output + j * num_bytes;
            for (size_t lane = 0; lane < full_lanes; ++lane)
                memcpy(out + lane * keccak_lane_bytes,
                       states + lane * keccak_x4_lane_stride + j * keccak_lane_bytes,
                       keccak_lane_bytes);
            if (tail)
                memcpy(out + full_lanes * keccak_lane_bytes,
                       states + full_lanes * keccak_x4_lane_stride + j * keccak_lane_bytes, tail);
        }
        return;
    }

    for (unsigned int j = 0; j < 4; ++j)
        KeccakP1600times4_ExtractBytes(states, j, output + j * num_bytes, 0,
                                       (unsigned int)num_bytes);
}

// The original, unaccelerated sponge implementation. Kept as the reference that
// the single-block fast path is differentially tested against, and used
// verbatim whenever the fast path does not apply.
template <secpar S>
inline void shake_prg_generic(const block_secpar<S>* __restrict__ keys, const block128& iv,
                              const uint32_t& tweak, size_t num_keys, size_t num_bytes,
                              uint8_t* __restrict__ output)
{
    size_t i;
    for (i = 0; i + 4 <= num_keys; i += 4)
    {
        const void* key_arr[4];
        void* output_arr[4];
        for (size_t j = 0; j < 4; ++j)
        {
            key_arr[j] = &keys[i + j];
            output_arr[j] = output + (i + j) * num_bytes;
        }

        hash_state_x4 hasher;
        hasher.init(S);
        hasher.update(key_arr, sizeof(keys[i]));
        hasher.update_1(&iv, sizeof(iv));
        hasher.update_1(&tweak, sizeof(tweak));
        hasher.update_1_byte(0);
        hasher.finalize(output_arr, num_bytes);
    }

    for (; i < num_keys; ++i)
    {
        hash_state hasher;
        hasher.init(S);
        hasher.update(&keys[i], sizeof(keys[i]));
        hasher.update(&iv, sizeof(iv));
        hasher.update(&tweak, sizeof(tweak));
        hasher.update_byte(0);
        hasher.finalize(output + i * num_bytes, num_bytes);
    }
}

// Whether shake_prg_impl takes the single-permutation path for a given output
// length. Depends only on public parameters. Shared with the tests so that
// "the fast path is really engaged" is an assertable property rather than an
// assumption.
template <secpar S> constexpr bool shake_prg_uses_single_block(size_t num_bytes)
{
    return num_bytes < shake_rate_bytes<S>;
}

template <secpar S>
inline void shake_prg_impl(const block_secpar<S>* __restrict__ keys, const block128& iv,
                           const uint32_t& tweak, size_t num_keys, size_t num_bytes,
                           uint8_t* __restrict__ output)
{
    // num_bytes is a public parameter, so this branch leaks nothing.
    const bool single_block = shake_prg_uses_single_block<S>(num_bytes);

    size_t i;
    for (i = 0; i + 4 <= num_keys; i += 4)
    {
        if (single_block)
        {
            shake_prg_x4_single_block<S>(keys + i, iv, tweak, num_bytes, output + i * num_bytes);
            continue;
        }

        const void* key_arr[4];
        void* output_arr[4];
        for (size_t j = 0; j < 4; ++j)
        {
            key_arr[j] = &keys[i + j];
            output_arr[j] = output + (i + j) * num_bytes;
        }

        hash_state_x4 hasher;
        hasher.init(S);
        hasher.update(key_arr, sizeof(keys[i]));
        hasher.update_1(&iv, sizeof(iv));
        hasher.update_1(&tweak, sizeof(tweak));
        hasher.update_1_byte(0);
        hasher.finalize(output_arr, num_bytes);
    }

    for (; i < num_keys; ++i)
    {
        hash_state hasher;
        hasher.init(S);
        hasher.update(&keys[i], sizeof(keys[i]));
        hasher.update(&iv, sizeof(iv));
        hasher.update(&tweak, sizeof(tweak));
        hasher.update_byte(0);
        hasher.finalize(output + i * num_bytes, num_bytes);
    }
}

} // namespace sdsign

#endif
