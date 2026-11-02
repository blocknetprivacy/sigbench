#ifndef SDSIGN_VERIFY_HPP
#define SDSIGN_VERIFY_HPP

#include <cstddef>
#include <cstdint>

namespace sdsign
{

template <typename P>
bool sdsign_verify(const uint8_t* signature, const uint8_t* msg, size_t msg_len, const uint8_t* pk);

} // namespace sdsign

#endif
