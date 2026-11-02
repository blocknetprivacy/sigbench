#ifndef AES_HPP
#define AES_HPP

#include "aes_defs.hpp"
#include "block.hpp"
#include "constants.hpp"
#include "util.hpp"

#if defined(__AVX2__)
#include "avx2/aes_impl.hpp"
#elif defined(__aarch64__)
#include "aarch64/aes_impl.hpp"
#else
#error "unsupported architecture"
#endif

// Interface defined by aes_impl.h:

// #define AES_MAX_CTR /**/
// #define AES_PREFERRED_WIDTH_SHIFT /**/
// #define AES256_PREFERRED_WIDTH_SHIFT /**/

namespace sdsign
{

template <secpar S> void aes_keygen(aes_round_keys<S>* round_keys, block_secpar<S> key);
void aes256_keygen(aes256_round_keys* round_keys, block256 key);

// Apply 1 round of the cipher, writing the state after the SBox into after_sbox, and writing the
// new state back into state. round is the index of the round key to use, so it should start from
// one.
template <secpar S>
inline void aes_round_function(const aes_round_keys<S>* __restrict__ round_keys,
                               block128* __restrict__ block, block128* __restrict__ after_sbox,
                               size_t round);
void aes256_round_function(const aes256_round_keys* __restrict__ round_keys,
                                block256* __restrict__ block, block256* __restrict__ after_sbox,
                                size_t round);

// Run AES key schedule on num_keys keys, then use each to encrypt num_blocks block128s in ECB mode.
// Each key has it's own iv. Outputs from the same key are grouped together in output. counter must
// not exceed AES_MAX_CTR on any block.
template <secpar S, size_t num_keys, size_t blocks_per_key>
ALWAYS_INLINE void
aes_keygen_ecb(const block_secpar<S>* __restrict__ keys, aes_round_keys<S>* __restrict__ aeses,
               block128* __restrict__ data);

// Use each of num_keys AES keys to encrypt num_blocks block128s of data. Outputs from the same key
// are grouped together in output.
template <secpar S, size_t num_keys, size_t blocks_per_key>
inline void aes_ecb(const aes_round_keys<S>* __restrict__ aeses, block128* __restrict__ data);

// Given num_keys Even-Mansour keys, generate num_blocks block_secpars of output from each in CTR
// mode, starting at counter.
template <size_t num_keys, uint32_t num_blocks>
inline void aes_fixed_key_ctr(const aes_round_keys<secpar::L1>* __restrict__ fixed_key,
                              const block128* __restrict__ keys,
                              const block128& iv,
                              const uint32_t* __restrict__ tweaks,
                              const uint32_t* counters,
                              block128* __restrict__ output);
template <size_t num_keys, uint32_t num_blocks>
inline void aes256_fixed_key_ctr(const aes256_round_keys* __restrict__ fixed_key,
                                      const block256* __restrict__ keys,
                                      const block256& iv,
                                      const uint32_t* __restrict__ tweaks,
                                      const uint32_t* __restrict__ counters,
                                      block256* __restrict__ output);

// Same, but for block size = security parameter.
template <secpar S>
inline void aes_secpar_keygen(aes_secpar_round_keys<S>* round_keys, block_secpar<S> key)
{
    if constexpr (S == secpar::L1)
    {
        aes_keygen<S>(round_keys, key);
    }
    else if constexpr (S == secpar::L5)
    {
        aes256_keygen(round_keys, key);
    }
    else
    {
        static_assert(false, "unsupported security parameter for AES");
    }
}
template <secpar S, size_t num_keys, uint32_t num_blocks>
inline void aes_secpar_fixed_key_ctr(const aes_secpar_round_keys<S>* __restrict__ fixed_key,
                                   const block_secpar<S>* __restrict__ keys,
                                   const block_secpar<S>& iv,
                                   const uint32_t* __restrict__ tweaks,
                                   const uint32_t* __restrict__ counters,
                                   block_secpar<S>* __restrict__ output)
{
    if constexpr (S == secpar::L1)
    {
        aes_fixed_key_ctr<num_keys, num_blocks>(fixed_key, keys, iv, tweaks, counters, output);
    }
    else if constexpr (S == secpar::L5)
    {
        aes256_fixed_key_ctr<num_keys, num_blocks>(fixed_key, keys, iv, tweaks, counters, output);
    }
    else
    {
        static_assert(false, "unsupported security parameter for AES");
    }
}

} // namespace sdsign

#endif
