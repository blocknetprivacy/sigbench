#ifndef SDSIGN_RING_SIGNATURE_VERIFY_HPP
#define SDSIGN_RING_SIGNATURE_VERIFY_HPP

#include "ring_signature/sign.hpp"

namespace sdsign::ring
{

template <typename RP>
bool verify(const uint8_t* signature, const uint8_t* msg, std::size_t msg_len,
            const prepared_public_ring<typename RP::base_parameter, RP::ring_size>& prepared);

template <typename RP>
inline bool verify(const uint8_t* signature, const uint8_t* msg, std::size_t msg_len,
                   const public_ring<typename RP::base_parameter, RP::ring_size>& ring)
{
    const auto prepared = prepare_public_ring(ring);
    return verify<RP>(signature, msg, msg_len, prepared);
}

} // namespace sdsign::ring

#endif
