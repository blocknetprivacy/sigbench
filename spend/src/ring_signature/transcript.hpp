#ifndef SDSIGN_RING_SIGNATURE_TRANSCRIPT_HPP
#define SDSIGN_RING_SIGNATURE_TRANSCRIPT_HPP

#include "hash.hpp"
#include "ring_signature/keys.hpp"

#include <array>
#include <cstddef>
#include <cstdint>
#include <memory>
#include <utility>

namespace sdsign::ring
{

inline constexpr std::array<uint8_t, 16> transcript_domain = {
    'S', 'D', 'S', 'I', 'G', 'N', '-', 'R', 'I', 'N', 'G', '-', 'V', '1', 0, 0,
};

inline constexpr std::array<uint8_t, 8> encode_u64_le(uint64_t value)
{
    std::array<uint8_t, 8> out{};
    for (std::size_t i = 0; i < out.size(); ++i)
        out[i] = static_cast<uint8_t>(value >> (8 * i));
    return out;
}

#ifndef SDSIGN_RING_TRANSCRIPT_PRECOMPUTE
#define SDSIGN_RING_TRANSCRIPT_PRECOMPUTE 1
#endif

template <typename P, std::size_t RingSize> struct prepared_public_ring
{
    // The transcript and the relation always refer to this same immutable
    // statement.  Owning the snapshot also makes its lifetime explicit.
    std::shared_ptr<const public_ring<P, RingSize>> ring;
#if SDSIGN_RING_TRANSCRIPT_PRECOMPUTE
    hash_state transcript_prefix{};
#endif
};

template <typename P, std::size_t RingSize>
void initialize_transcript_prefix(hash_state& hasher, const public_ring<P, RingSize>& ring)
{
    hasher.init(P::secpar_v);
    hasher.update(transcript_domain.data(), transcript_domain.size());
    const auto ring_size = encode_u64_le(RingSize);
    const auto eta_left = encode_u64_le(selector_parameters<RingSize>::eta_left);
    const auto eta_right = encode_u64_le(selector_parameters<RingSize>::eta_right);
    hasher.update(ring_size.data(), ring_size.size());
    hasher.update(eta_left.data(), eta_left.size());
    hasher.update(eta_right.data(), eta_right.size());
    hasher.update(&ring.seed_pk, P::secpar_bytes);
    for (const auto& syndrome : ring.syndromes)
        hasher.update(syndrome.data(), syndrome.size() * P::secpar_bytes);
}

template <typename P, std::size_t RingSize>
prepared_public_ring<P, RingSize>
prepare_public_ring(std::unique_ptr<public_ring<P, RingSize>> ring)
{
    prepared_public_ring<P, RingSize> prepared;
    if (!ring)
        return prepared;
    prepared.ring = std::shared_ptr<const public_ring<P, RingSize>>(std::move(ring));
#if SDSIGN_RING_TRANSCRIPT_PRECOMPUTE
    initialize_transcript_prefix(prepared.transcript_prefix, *prepared.ring);
#endif
    return prepared;
}

template <typename P, std::size_t RingSize>
prepared_public_ring<P, RingSize> prepare_public_ring(const public_ring<P, RingSize>& ring)
{
    return prepare_public_ring<P, RingSize>(
        std::make_unique<public_ring<P, RingSize>>(ring));
}

// The ordered ring, its size, selector geometry and the message are bound
// before the FAEST-style transcript begins.  Reordering or replacing even one
// public key therefore changes mu.
template <typename P, std::size_t RingSize>
block_2secpar<P::secpar_v> context_digest(const prepared_public_ring<P, RingSize>& prepared,
                                          const uint8_t* msg, std::size_t msg_len)
{
#if SDSIGN_RING_TRANSCRIPT_PRECOMPUTE
    hash_state hasher = prepared.transcript_prefix;
#else
    hash_state hasher;
    initialize_transcript_prefix(hasher, *prepared.ring);
#endif
    if (msg_len != 0)
        hasher.update(msg, msg_len);
    hasher.update_byte(0x52);

    block_2secpar<P::secpar_v> digest;
    hasher.finalize(&digest, sizeof(digest));
    return digest;
}

template <typename P, std::size_t RingSize>
block_2secpar<P::secpar_v> context_digest(const public_ring<P, RingSize>& ring, const uint8_t* msg,
                                          std::size_t msg_len)
{
    return context_digest(prepare_public_ring(ring), msg, msg_len);
}

} // namespace sdsign::ring

#endif
