#include "aes.hpp"

#include <cassert>

#define KEYGEN_WIDTH 4

#include "../common/aes_utils.inc"

namespace sdsign
{

template <secpar S>
ALWAYS_INLINE void aes_keygen_round(aes_keygen_state<S>* keygen_states, aes_round_keys<S>* aeses,
                                    size_t num_keys, size_t round)
{
    if (round < secpar_to_bits(S) / 128)
        return;

#ifdef __GNUC__
    _Pragma(STRINGIZE(GCC unroll (2*AES_PREFERRED_WIDTH / KEYGEN_WIDTH)))
#endif
        for (size_t i = 0; i < num_keys; i += KEYGEN_WIDTH, aeses += KEYGEN_WIDTH, ++keygen_states)
    {
        size_t chunk_size = num_keys - i < KEYGEN_WIDTH ? num_keys - i : KEYGEN_WIDTH;

        if (S != secpar::L3 || round % 3 < 2)
        {
            // Undo ShiftRows operation, then apply RotWord.
            const std::array<uint8_t, 16> inv_shift_rows = {0, 13, 10, 7,  4,  1, 14, 11,
                                                            8, 5,  2,  15, 12, 9, 6,  3};
            const std::array<uint8_t, 16> rot_word_then_inv_shift_rows = {
                1, 14, 11, 4, 5, 2, 15, 8, 9, 6, 3, 12, 13, 10, 7, 0};

            uint8x16_t perm, round_constant;
            if (S == secpar::L5 && round % 2 == 1)
            {
                perm = vld1q_u8(inv_shift_rows.data());
                round_constant = vdupq_n_u8(0);
            }
            else
            {
                perm = vld1q_u8(rot_word_then_inv_shift_rows.data());

                // Tell the compiler explicitly how to evaluate for each case of S.
                size_t idx; //= (2 * round + 1) / (secpar_to_bits(S) / 64);
                if constexpr (S == secpar::L1)
                    idx = round;
                else if constexpr (S == secpar::L3)
                    idx = (2 * round + 1) / 3;
                else if constexpr (S == secpar::L5)
                    idx = round / 2;

                round_constant = vreinterpretq_u8_u32(vdupq_n_u32(aes_round_constants[idx - 1]));
            }

            const uint8x16_t after_permutation =
                vqtbl1q_u8(vreinterpretq_u8_u32(keygen_states->next_sbox.data), perm);
            block128 sbox_out = {vreinterpretq_u32_u8(
                veorq_u8(vaeseq_u8(after_permutation, vdupq_n_u8(0)), round_constant))};

            size_t range_start = (S == secpar::L3 && round % 3 == 1) ? 2 : 0;
            size_t range_end = (S == secpar::L3) ? 6 : 4;
            PRAGMA_UNROLL(6)
            for (size_t j = range_start; j < range_end; ++j)
                keygen_states->key_slices[j] = keygen_states->key_slices[j] ^ sbox_out;
        }

        if (S != secpar::L3 || round % 3 == 2)
            keygen_states->next_sbox = keygen_states->key_slices[3];
        else if (round % 3 == 0)
            keygen_states->next_sbox = keygen_states->key_slices[5];

        // Unslice the current KEYGEN_WIDTH keys slices to get this round's keys.
        block128 round_keys[KEYGEN_WIDTH];
        transpose4x4_32(round_keys, &keygen_states->key_slices[0]);
#ifdef __GNUC__
        _Pragma(STRINGIZE(GCC unroll (KEYGEN_WIDTH)))
#endif
                              for (size_t j = 0; j < chunk_size; ++j) aeses[j]
                                  .keys[round] = round_keys[j];

        // Update round keys slices for next round.
        if constexpr (S == secpar::L3)
        {
            shift2_mod6(&keygen_states->key_slices[0]);
            size_t next_sbox_idx = (round % 3 + 1) * 2;
            cumulative_xor(&keygen_states->key_slices[1], next_sbox_idx - 1);
            // GCC 15 currently displays erroneous warning concerning an out of bounds access into
            // the `keygen_states` object.  Therefore we silence the specific warning for this
            // function call.
            // Bug report: https://gcc.gnu.org/bugzilla/show_bug.cgi?id=122298
#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Warray-bounds"
            cumulative_xor(&keygen_states->key_slices[next_sbox_idx], 6 - next_sbox_idx);
#pragma GCC diagnostic pop
        }
        else
        {
            cumulative_xor(&keygen_states->key_slices[0], 4);
            if constexpr (S == secpar::L5)
                shift4_mod8(&keygen_states->key_slices[0]);
        }
    }
}

// emulate AES-NI _mm_aeskeygenassist_si128
template <size_t m> static inline uint32x4_t aeskeygenassist(uint32x4_t a, const int round_constant)
{
    // clang-format off
    constexpr std::array<uint8_t, 16> select_w1 = {4, 5, 6, 7,
                                                   4, 5, 6, 7,
                                                   4, 5, 6, 7,
                                                   4, 5, 6, 7};
    constexpr std::array<uint8_t, 16> select_w3 = {12, 13, 14, 15,
                                                   12, 13, 14, 15,
                                                   12, 13, 14, 15,
                                                   12, 13, 14, 15};
    constexpr std::array<uint8_t, 16> select_w1_and_rotword = {5, 6, 7, 4,
                                                               5, 6, 7, 4,
                                                               5, 6, 7, 4,
                                                               5, 6, 7, 4};
    constexpr std::array<uint8_t, 16> select_w3_and_rotword = {13, 14, 15, 12,
                                                               13, 14, 15, 12,
                                                               13, 14, 15, 12,
                                                               13, 14, 15, 12};
    // clang-format on

    // - [A0, A1, A2, A3] -> [A0, RotWord(A1), A2, RotWord(A3)]
    // m = 0 -> 4x[SubWord(A1)]
    // m = 1 -> 4x[RotWord(SubWord(A1)) ^ RCON]
    // m = 2 -> 4x[SubWord(A3)]
    // m = 3 -> 4x[RotWord(SubWord(A3)) ^ RCON]

    uint8x16_t b;

    if constexpr (m == 0)
    {
        // - select A1
        b = vqtbl1q_u8(vreinterpretq_u8_u32(a), vld1q_u8(select_w1.data()));
        // - apply SubWord (ShiftRows doesn't matter as all rows consist of the same byte)
        b = vaeseq_u8(b, vdupq_n_u8(0));
        a = vreinterpretq_u32_u8(b);
    }
    else if constexpr (m == 1)
    {
        // - select A1 and apply RotWor
        b = vqtbl1q_u8(vreinterpretq_u8_u32(a), vld1q_u8(select_w1_and_rotword.data()));
        // - apply SubWord (ShiftRows doesn't matter as all rows consist of the same byte)
        b = vaeseq_u8(b, vdupq_n_u8(0));
        // - xor round constant
        a = veorq_u32(vreinterpretq_u32_u8(b), vdupq_n_u32(round_constant));
    }
    else if constexpr (m == 2)
    {
        // - select A3
        b = vqtbl1q_u8(vreinterpretq_u8_u32(a), vld1q_u8(select_w3.data()));
        // - apply SubWord (ShiftRows doesn't matter as all rows consist of the same byte)
        b = vaeseq_u8(b, vdupq_n_u8(0));
        a = vreinterpretq_u32_u8(b);
    }
    else if constexpr (m == 3)
    {
        // - select A3 and apply RotWor
        b = vqtbl1q_u8(vreinterpretq_u8_u32(a), vld1q_u8(select_w3_and_rotword.data()));
        // - apply SubWord (ShiftRows doesn't matter as all rows consist of the same byte)
        b = vaeseq_u8(b, vdupq_n_u8(0));
        // - xor round constant
        a = veorq_u32(vreinterpretq_u32_u8(b), vdupq_n_u32(round_constant));
    }
    else
    {
        static_assert(false);
    }

    return a;
}

static inline uint32x4_t load_high_128(const block256* block)
{
    return block->data[1].data;
}

static void aes256_keygen_helper(const block256* round_key_in, uint32x4_t kga,
                                      block256* round_key_out)
{
    uint32x4_t t1, t2, t3, t4;

    memcpy(&t1, round_key_in, sizeof(t1));
    t3 = load_high_128(round_key_in);
    t2 = kga; // keygenassist<3>

    t4 = vextq_u32(vdupq_n_u32(0), t1, 3);
    t1 = veorq_u32(t1, t4);
    t4 = vextq_u32(vdupq_n_u32(0), t4, 3);
    t1 = veorq_u32(t1, t4);
    t4 = vextq_u32(vdupq_n_u32(0), t4, 3);
    t1 = veorq_u32(t1, t4);
    t1 = veorq_u32(t1, t2);

    memcpy(round_key_out, &t1, sizeof(t1));

    t2 = aeskeygenassist<2>(t1, 0x00);
    t4 = vextq_u32(vdupq_n_u32(0), t3, 3);
    t3 = veorq_u32(t3, t4);
    t4 = vextq_u32(vdupq_n_u32(0), t4, 3);
    t3 = veorq_u32(t3, t4);
    t4 = vextq_u32(vdupq_n_u32(0), t4, 3);
    t3 = veorq_u32(t3, t4);
    t3 = veorq_u32(t3, t2);

    memcpy(((unsigned char*)round_key_out) + sizeof(t1), &t3, sizeof(t3));
}

void aes256_keygen(aes256_round_keys* round_keys, block256 key)
{
    round_keys->keys[0] = key;

    uint32x4_t kga;
    kga = aeskeygenassist<3>(load_high_128(&round_keys->keys[0]), 0x01);
    aes256_keygen_helper(&round_keys->keys[0], kga, &round_keys->keys[1]);
    kga = aeskeygenassist<3>(load_high_128(&round_keys->keys[1]), 0x02);
    aes256_keygen_helper(&round_keys->keys[1], kga, &round_keys->keys[2]);
    kga = aeskeygenassist<3>(load_high_128(&round_keys->keys[2]), 0x04);
    aes256_keygen_helper(&round_keys->keys[2], kga, &round_keys->keys[3]);
    kga = aeskeygenassist<3>(load_high_128(&round_keys->keys[3]), 0x08);
    aes256_keygen_helper(&round_keys->keys[3], kga, &round_keys->keys[4]);
    kga = aeskeygenassist<3>(load_high_128(&round_keys->keys[4]), 0x10);
    aes256_keygen_helper(&round_keys->keys[4], kga, &round_keys->keys[5]);
    kga = aeskeygenassist<3>(load_high_128(&round_keys->keys[5]), 0x20);
    aes256_keygen_helper(&round_keys->keys[5], kga, &round_keys->keys[6]);
    kga = aeskeygenassist<3>(load_high_128(&round_keys->keys[6]), 0x40);
    aes256_keygen_helper(&round_keys->keys[6], kga, &round_keys->keys[7]);
    kga = aeskeygenassist<3>(load_high_128(&round_keys->keys[7]), 0x80);
    aes256_keygen_helper(&round_keys->keys[7], kga, &round_keys->keys[8]);
    kga = aeskeygenassist<3>(load_high_128(&round_keys->keys[8]), 0x1B);
    aes256_keygen_helper(&round_keys->keys[8], kga, &round_keys->keys[9]);
    kga = aeskeygenassist<3>(load_high_128(&round_keys->keys[9]), 0x36);
    aes256_keygen_helper(&round_keys->keys[9], kga, &round_keys->keys[10]);
    kga = aeskeygenassist<3>(load_high_128(&round_keys->keys[10]), 0x6C);
    aes256_keygen_helper(&round_keys->keys[10], kga, &round_keys->keys[11]);
    kga = aeskeygenassist<3>(load_high_128(&round_keys->keys[11]), 0xD8);
    aes256_keygen_helper(&round_keys->keys[11], kga, &round_keys->keys[12]);
    kga = aeskeygenassist<3>(load_high_128(&round_keys->keys[12]), 0xAB);
    aes256_keygen_helper(&round_keys->keys[12], kga, &round_keys->keys[13]);
    kga = aeskeygenassist<3>(load_high_128(&round_keys->keys[13]), 0x4D);
    aes256_keygen_helper(&round_keys->keys[13], kga, &round_keys->keys[14]);
}

void aes256_round_function(const aes256_round_keys* __restrict__ round_keys,
                                block256* __restrict__ block, block256* __restrict__ after_sbox,
                                size_t round)
{
    block128 state[2], state_after_sbox[2], round_key[2];
    memcpy(&state[0], block, sizeof(*block));
    memcpy(&round_key[0], &round_keys->keys[round], sizeof(round_key));
    uint8x16_t zeros = vdupq_n_u8(0);

    // Use aes instructions to implement the round function.

    // ShiftRows, SubBytes
    aes256_rotate_rows_undo_128(&state[0]);
    state_after_sbox[0] =
        block128{vreinterpretq_u32_u8(vaeseq_u8(vreinterpretq_u8_u32(state[0].data), zeros))};
    state_after_sbox[1] =
        block128{vreinterpretq_u32_u8(vaeseq_u8(vreinterpretq_u8_u32(state[1].data), zeros))};

    if (round < AES_ROUNDS<secpar::L5>)
    {
        // MixColumns, AddRoundKey
        state[0] = block128{vreinterpretq_u32_u8(
                       vaesmcq_u8(vreinterpretq_u8_u32(state_after_sbox[0].data)))} ^
                   round_key[0];
        state[1] = block128{vreinterpretq_u32_u8(
                       vaesmcq_u8(vreinterpretq_u8_u32(state_after_sbox[1].data)))} ^
                   round_key[1];
    }
    else
    {
        // AddRoundKey
        state[0] = state_after_sbox[0] ^ round_key[0];
        state[1] = state_after_sbox[1] ^ round_key[1];
    }

    memcpy(after_sbox, &state_after_sbox[0], sizeof(*after_sbox));
    memcpy(block, &state[0], sizeof(*block));
}


template <secpar S, size_t num_keys, uint32_t num_blocks>
ALWAYS_INLINE void aes_keygen_impl(
    aes_round_keys<S>* __restrict__ aeses,
    const block_secpar<S>* __restrict__ keys,
    block128* __restrict__ output)
{
    aes_keygen_state<S> keygen_states[(num_keys + KEYGEN_WIDTH - 1) / KEYGEN_WIDTH];
    aes_keygen_init(keygen_states, aeses, keys, num_keys);

    constexpr auto round_start = []
    {
        if constexpr (S == secpar::L1 || S == secpar::L3)
        {
            return 1;
        }
        else if constexpr (S == secpar::L5)
        {
            return 2;
        }
        else
        {
            static_assert(false, "unsupported security parameter for AES");
        }
    }();
    constexpr auto round_end = AES_ROUNDS<S> - round_start;
    constexpr auto unroll_rounds = []
    {
        if constexpr (S == secpar::L1)
        {
            return 1;
        }
        else if constexpr (S == secpar::L3)
        {
            return 3;
        }
        else if constexpr (S == secpar::L5)
        {
            return 2;
        }
        else
        {
            static_assert(false, "unsupported security parameter for AES");
        }
    }();

    // Separate out the first and last rounds, as they work differently.
    aes_round(aeses, output, num_keys, num_blocks, 0);
    if (round_start > 1)
        aes_round(aeses, output, num_keys, num_blocks, 1);

    for (size_t round = round_start; round <= round_end; round += unroll_rounds)
    {
        // Unroll the loop, as the key generation follows a pattern that repeats every unroll_rounds
        // iterations.

        aes_keygen_round(keygen_states, aeses, num_keys, round);
        aes_round(aeses, output, num_keys, num_blocks, round);
        if (unroll_rounds > 1)
        {
            if (round_end < round + 1)
                break;
            aes_keygen_round(keygen_states, aeses, num_keys, round + 1);
            aes_round(aeses, output, num_keys, num_blocks, round + 1);
        }
        if (unroll_rounds > 2)
        {
            if (round_end < round + 2)
                break;
            aes_keygen_round(keygen_states, aeses, num_keys, round + 2);
            aes_round(aeses, output, num_keys, num_blocks, round + 2);
        }
    }

    aes_keygen_round(keygen_states, aeses, num_keys, round_end + 1);
    aes_round(aeses, output, num_keys, num_blocks, round_end + 1);
    if (round_end + 2 <= AES_ROUNDS<S>)
    {
        aes_keygen_round(keygen_states, aeses, num_keys, round_end + 2);
        aes_round(aeses, output, num_keys, num_blocks, round_end + 2);
    }
}

template <secpar S, size_t num_keys>
ALWAYS_INLINE void aes_keygen_only_impl(aes_round_keys<S>* __restrict__ aeses,
                                        const block_secpar<S>* __restrict__ keys)
{
    aes_keygen_state<S> keygen_states[(num_keys + KEYGEN_WIDTH - 1) / KEYGEN_WIDTH];
    aes_keygen_init(keygen_states, aeses, keys, num_keys);

    constexpr auto round_start = []
    {
        if constexpr (S == secpar::L1 || S == secpar::L3)
        {
            return 1;
        }
        else if constexpr (S == secpar::L5)
        {
            return 2;
        }
        else
        {
            static_assert(false, "unsupported security parameter for AES");
        }
    }();
    constexpr auto round_end = AES_ROUNDS<S> - round_start;
    constexpr auto unroll_rounds = []
    {
        if constexpr (S == secpar::L1)
        {
            return 1;
        }
        else if constexpr (S == secpar::L3)
        {
            return 3;
        }
        else if constexpr (S == secpar::L5)
        {
            return 2;
        }
        else
        {
            static_assert(false, "unsupported security parameter for AES");
        }
    }();

    for (size_t round = round_start; round <= round_end; round += unroll_rounds)
    {
        aes_keygen_round(keygen_states, aeses, num_keys, round);
        if (unroll_rounds > 1)
        {
            if (round_end < round + 1)
                break;
            aes_keygen_round(keygen_states, aeses, num_keys, round + 1);
        }
        if (unroll_rounds > 2)
        {
            if (round_end < round + 2)
                break;
            aes_keygen_round(keygen_states, aeses, num_keys, round + 2);
        }
    }

    aes_keygen_round(keygen_states, aeses, num_keys, round_end + 1);
    if (round_end + 2 <= AES_ROUNDS<S>)
        aes_keygen_round(keygen_states, aeses, num_keys, round_end + 2);
}

// Generate all explicit template instantiations.
#define DEF_AES_KEYGEN_IMPL_SKB(secparam, num_keys, num_blocks)                                    \
    template void aes_keygen_impl<secparam, num_keys, num_blocks>(                                 \
        aes_round_keys<secparam>* __restrict__ aeses,                                              \
        const block_secpar<secparam>* __restrict__ keys, block128* __restrict__ output);
#define DEF_AES_KEYGEN_ONLY_IMPL_SK(secparam, num_keys)                                            \
    template void aes_keygen_only_impl<secparam, num_keys>(                                        \
        aes_round_keys<secparam>* __restrict__ aeses,                                              \
        const block_secpar<secparam>* __restrict__ keys);
#define DEF_AES_KEYGEN_IMPL_SK1(secparam)                                                          \
    DEF_AES_KEYGEN_IMPL_SKB(secparam, 1, 1)                                                        \
    DEF_AES_KEYGEN_IMPL_SKB(secparam, 1, 2)                                                        \
    DEF_AES_KEYGEN_IMPL_SKB(secparam, 1, 3)                                                        \
    DEF_AES_KEYGEN_IMPL_SKB(secparam, 1, 4)                                                        \
    DEF_AES_KEYGEN_IMPL_SKB(secparam, 1, 5)                                                        \
    DEF_AES_KEYGEN_IMPL_SKB(secparam, 1, 6)                                                        \
    DEF_AES_KEYGEN_IMPL_SKB(secparam, 1, 7)                                                        \
    DEF_AES_KEYGEN_IMPL_SKB(secparam, 1, 8)                                                        \
    DEF_AES_KEYGEN_IMPL_SKB(secparam, 1, 9)                                                        \
    DEF_AES_KEYGEN_IMPL_SKB(secparam, 1, 10)                                                       \
    DEF_AES_KEYGEN_IMPL_SKB(secparam, 1, 11)                                                       \
    DEF_AES_KEYGEN_IMPL_SKB(secparam, 1, 12)                                                       \
    DEF_AES_KEYGEN_IMPL_SKB(secparam, 1, 13)                                                       \
    DEF_AES_KEYGEN_IMPL_SKB(secparam, 1, 14)                                                       \
    DEF_AES_KEYGEN_IMPL_SKB(secparam, 1, 15)                                                       \
    DEF_AES_KEYGEN_IMPL_SKB(secparam, 1, 16)
#define DEF_AES_KEYGEN_IMPL_SK(secparam, num_keys)                                                 \
    DEF_AES_KEYGEN_IMPL_SKB(secparam, num_keys, 1)                                                 \
    DEF_AES_KEYGEN_IMPL_SKB(secparam, num_keys, 2)                                                 \
    DEF_AES_KEYGEN_IMPL_SKB(secparam, num_keys, 3)                                                 \
    DEF_AES_KEYGEN_IMPL_SKB(secparam, num_keys, 4)
#define DEF_AES_KEYGEN_IMPL_S(secparam)                                                            \
    DEF_AES_KEYGEN_IMPL_SK1(secparam)                                                              \
    DEF_AES_KEYGEN_IMPL_SK(secparam, 2)                                                            \
    DEF_AES_KEYGEN_IMPL_SK(secparam, 3)                                                            \
    DEF_AES_KEYGEN_IMPL_SK(secparam, 4)                                                            \
    DEF_AES_KEYGEN_IMPL_SK(secparam, 5)                                                            \
    DEF_AES_KEYGEN_IMPL_SK(secparam, 6)                                                            \
    DEF_AES_KEYGEN_IMPL_SK(secparam, 7)                                                            \
    DEF_AES_KEYGEN_IMPL_SK(secparam, 8)

DEF_AES_KEYGEN_IMPL_S(secpar::L1)
DEF_AES_KEYGEN_IMPL_S(secpar::L3)
DEF_AES_KEYGEN_IMPL_S(secpar::L5)
DEF_AES_KEYGEN_ONLY_IMPL_SK(secpar::L1, 1)
DEF_AES_KEYGEN_ONLY_IMPL_SK(secpar::L1, 2)
DEF_AES_KEYGEN_ONLY_IMPL_SK(secpar::L1, 3)
DEF_AES_KEYGEN_ONLY_IMPL_SK(secpar::L1, 4)
DEF_AES_KEYGEN_ONLY_IMPL_SK(secpar::L1, 5)
DEF_AES_KEYGEN_ONLY_IMPL_SK(secpar::L1, 6)
DEF_AES_KEYGEN_ONLY_IMPL_SK(secpar::L1, 7)
DEF_AES_KEYGEN_ONLY_IMPL_SK(secpar::L1, 8)
DEF_AES_KEYGEN_ONLY_IMPL_SK(secpar::L3, 1)
DEF_AES_KEYGEN_ONLY_IMPL_SK(secpar::L3, 2)
DEF_AES_KEYGEN_ONLY_IMPL_SK(secpar::L3, 3)
DEF_AES_KEYGEN_ONLY_IMPL_SK(secpar::L3, 4)
DEF_AES_KEYGEN_ONLY_IMPL_SK(secpar::L3, 5)
DEF_AES_KEYGEN_ONLY_IMPL_SK(secpar::L3, 6)
DEF_AES_KEYGEN_ONLY_IMPL_SK(secpar::L3, 7)
DEF_AES_KEYGEN_ONLY_IMPL_SK(secpar::L3, 8)
DEF_AES_KEYGEN_ONLY_IMPL_SK(secpar::L5, 1)
DEF_AES_KEYGEN_ONLY_IMPL_SK(secpar::L5, 2)
DEF_AES_KEYGEN_ONLY_IMPL_SK(secpar::L5, 3)
DEF_AES_KEYGEN_ONLY_IMPL_SK(secpar::L5, 4)
DEF_AES_KEYGEN_ONLY_IMPL_SK(secpar::L5, 5)
DEF_AES_KEYGEN_ONLY_IMPL_SK(secpar::L5, 6)
DEF_AES_KEYGEN_ONLY_IMPL_SK(secpar::L5, 7)
DEF_AES_KEYGEN_ONLY_IMPL_SK(secpar::L5, 8)

template <secpar S> void aes_keygen(aes_round_keys<S>* round_keys, block_secpar<S> key)
{
    // There are more efficient ways to run the key schedule on a single key, but this function
    // isn't used much anyway.
    block128 empty_output;
    aes_keygen_impl<S, 1, 0>(round_keys, &key, &empty_output);
}
template void aes_keygen<secpar::L1>(aes_round_keys<secpar::L1>* round_keys,
                                       block_secpar<secpar::L1> key);
template void aes_keygen<secpar::L3>(aes_round_keys<secpar::L3>* round_keys,
                                       block_secpar<secpar::L3> key);
template void aes_keygen<secpar::L5>(aes_round_keys<secpar::L5>* round_keys,
                                       block_secpar<secpar::L5> key);


} // namespace sdsign
