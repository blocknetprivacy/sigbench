#ifndef SDSIGN_KEYGEN_HPP
#define SDSIGN_KEYGEN_HPP

#include <cstddef>
#include <cstdint>

namespace sdsign
{

template <typename P>
bool sdsign_keygen(uint8_t* pk, uint8_t* sk, const uint8_t* random_seed,
                 std::size_t random_seed_len);

template <typename P> bool sdsign_derive_public_key(uint8_t* pk, const uint8_t* sk);

} // namespace sdsign

#endif
