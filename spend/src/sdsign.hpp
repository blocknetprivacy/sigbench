#ifndef SDSIGN_HPP
#define SDSIGN_HPP

#include <cstddef>
#include <cstdint>

#include "keys.hpp"

namespace sdsign
{

template <typename P>
constexpr std::size_t SDSIGN_SIGNATURE_BYTES = P::CONSTS::SIGNATURE_BYTES;

template <typename P>
bool sdsign_keygen(uint8_t* pk, uint8_t* sk, const uint8_t* random_seed,
                 std::size_t random_seed_len);

template <typename P> bool sdsign_derive_public_key(uint8_t* pk, const uint8_t* sk);

template <typename P>
bool sdsign_sign(uint8_t* signature, const uint8_t* msg, size_t msg_len, const uint8_t* sk,
                 const uint8_t* random_seed, size_t random_seed_len);

template <typename P>
bool sdsign_verify(const uint8_t* signature, const uint8_t* msg, size_t msg_len, const uint8_t* pk);

} // namespace sdsign

#endif
