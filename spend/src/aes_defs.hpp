#ifndef AES_DEFS_HPP
#define AES_DEFS_HPP

#include "block.hpp"
#include "constants.hpp"
#include <type_traits>

namespace sdsign
{

template <secpar S> struct aes_round_keys
{
    block128 keys[AES_ROUNDS<S> + 1];
};

template <secpar S> struct aes_secpar_round_keys_impl
{
    block_secpar<S> keys[AES_ROUNDS<S> + 1];
};
using aes256_round_keys = aes_secpar_round_keys_impl<secpar::L5>;

template <secpar S>
using aes_secpar_round_keys = std::conditional_t<
    S == secpar::L1, aes_round_keys<S>,
    std::conditional_t<S == secpar::L5, aes256_round_keys, void>>;

constexpr unsigned char aes_round_constants[] = {0x01, 0x02, 0x04, 0x08, 0x10, 0x20, 0x40,
                                                 0x80, 0x1b, 0x36, 0x6c, 0xd8, 0xab, 0x4d};

} // namespace sdsign

#endif
