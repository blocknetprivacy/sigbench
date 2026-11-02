#ifndef SDSIGN_RING_SIGNATURE_KEYS_HPP
#define SDSIGN_RING_SIGNATURE_KEYS_HPP

#include "../keys.hpp"
#include "ring_signature/selector.hpp"

#include <array>
#include <cstddef>
#include <cstdint>
#include <cstring>

namespace sdsign::ring
{

template <typename P, std::size_t RingSize> struct public_ring
{
    static_assert(P::owf_v == owf::rsd, "ring signatures currently support SD keys only");

    typename P::prg_t::key_t seed_pk{};
    std::array<std::array<block_secpar<P::secpar_v>, P::y_vector_len>, RingSize> syndromes{};
};

template <typename P, std::size_t RingSize>
inline constexpr std::size_t packed_public_ring_bytes =
    P::secpar_bytes + RingSize * P::y_vector_len * P::secpar_bytes;

template <typename P, std::size_t RingSize>
void pack_public_ring(uint8_t* packed, const public_ring<P, RingSize>& ring)
{
    std::memcpy(packed, &ring.seed_pk, P::secpar_bytes);
    std::size_t offset = P::secpar_bytes;
    for (std::size_t member = 0; member < RingSize; ++member)
        for (std::size_t row = 0; row < P::y_vector_len; ++row)
        {
            std::memcpy(packed + offset, &ring.syndromes[member][row], P::secpar_bytes);
            offset += P::secpar_bytes;
        }
}

template <typename P, std::size_t RingSize>
void unpack_public_ring(public_ring<P, RingSize>* ring, const uint8_t* packed)
{
    std::memcpy(&ring->seed_pk, packed, P::secpar_bytes);
    std::size_t offset = P::secpar_bytes;
    for (std::size_t member = 0; member < RingSize; ++member)
        for (std::size_t row = 0; row < P::y_vector_len; ++row)
        {
            std::memcpy(&ring->syndromes[member][row], packed + offset, P::secpar_bytes);
            offset += P::secpar_bytes;
        }
}

// Convert ordinary SD public keys into the shared-H ring format.  This is a
// public setup operation; rejecting mixed matrices prevents proving a
// different, higher-degree relation by accident.
template <typename P, std::size_t RingSize>
bool build_public_ring(public_ring<P, RingSize>* ring,
                       const std::array<const uint8_t*, RingSize>& packed_public_keys)
{
    if (!ring)
        return false;
    std::array<sdsign_public_key<P>, RingSize> keys{};
    for (std::size_t member = 0; member < RingSize; ++member)
    {
        if (!packed_public_keys[member])
            return false;
        sdsign_unpack_public_key<P>(&keys[member], packed_public_keys[member]);
    }

    ring->seed_pk = keys[0].seed_pk;
    for (std::size_t member = 0; member < RingSize; ++member)
    {
        if (std::memcmp(&keys[member].seed_pk, &ring->seed_pk, P::secpar_bytes) != 0)
            return false;
        ring->syndromes[member] = keys[member].y;
    }
    return true;
}

// Validate that the supplied SD secret key belongs at signer_index without a
// secret-dependent ring lookup.  All public syndromes are visited in order.
template <typename P, std::size_t RingSize>
bool secret_key_matches_ring(const public_ring<P, RingSize>& ring, const uint8_t* packed_secret_key,
                             std::size_t signer_index)
{
    if (!packed_secret_key || signer_index >= RingSize)
        return false;

    sdsign_secret_key<P> key{};
    if (!sdsign_unpack_secret_key<P>(&key, packed_secret_key))
        return false;

    uint8_t mismatch = 0;
    const auto* key_seed = reinterpret_cast<const uint8_t*>(&key.pk.seed_pk);
    const auto* ring_seed = reinterpret_cast<const uint8_t*>(&ring.seed_pk);
    for (std::size_t byte = 0; byte < P::secpar_bytes; ++byte)
        mismatch |= static_cast<uint8_t>(key_seed[byte] ^ ring_seed[byte]);

    std::array<block_secpar<P::secpar_v>, P::y_vector_len> selected_y{};
    for (std::size_t member = 0; member < RingSize; ++member)
    {
        const uint8_t selected = ct_equal_size(member, signer_index);
        const auto mask = block_secpar<P::secpar_v>::set_all_8(
            static_cast<uint8_t>(std::uint8_t{0} - selected));
        for (std::size_t row = 0; row < P::y_vector_len; ++row)
            selected_y[row] = selected_y[row] ^ (ring.syndromes[member][row] & mask);
    }

    const auto* key_y = reinterpret_cast<const uint8_t*>(key.pk.y.data());
    const auto* selected_y_bytes = reinterpret_cast<const uint8_t*>(selected_y.data());
    constexpr std::size_t syndrome_bytes = P::y_vector_len * P::secpar_bytes;
    for (std::size_t byte = 0; byte < syndrome_bytes; ++byte)
        mismatch |= static_cast<uint8_t>(key_y[byte] ^ selected_y_bytes[byte]);
    return mismatch == 0;
}

} // namespace sdsign::ring

#endif
