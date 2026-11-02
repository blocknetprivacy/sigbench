#ifndef SDSIGN_RING_SIGNATURE_SIGN_HPP
#define SDSIGN_RING_SIGNATURE_SIGN_HPP

#include "ring_signature/constraints.hpp"
#include "ring_signature/transcript.hpp"

#include <cstddef>
#include <cstdint>

namespace sdsign::ring
{

template <typename RP>
inline constexpr std::size_t signature_bytes = RP::CONSTS::SIGNATURE_BYTES;

template <typename RP>
bool sign(uint8_t* signature, const uint8_t* msg, std::size_t msg_len,
          const prepared_public_ring<typename RP::base_parameter, RP::ring_size>& prepared,
          const uint8_t* packed_secret_key, std::size_t signer_index, const uint8_t* random_seed,
          std::size_t random_seed_len);

template <typename RP>
inline bool sign(uint8_t* signature, const uint8_t* msg, std::size_t msg_len,
                 const public_ring<typename RP::base_parameter, RP::ring_size>& ring,
                 const uint8_t* packed_secret_key, std::size_t signer_index,
                 const uint8_t* random_seed, std::size_t random_seed_len)
{
    const auto prepared = prepare_public_ring(ring);
    return sign<RP>(signature, msg, msg_len, prepared, packed_secret_key, signer_index, random_seed,
                    random_seed_len);
}

} // namespace sdsign::ring

#endif
