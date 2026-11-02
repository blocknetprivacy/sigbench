#ifndef SDSIGN_KEYS_HPP
#define SDSIGN_KEYS_HPP

#include "block.hpp"
#include "polynomials.hpp"
#include "vole_parameters.hpp"
#include "prgs.hpp"

#include <array>
#include <cstddef>
#include <cstdint>

namespace sdsign
{

// pk size
template <typename P>
constexpr std::size_t SDSIGN_PACKED_PUBLIC_KEY_BYTES = P::packed_public_key_bytes;

template <typename P>
constexpr std::size_t SDSIGN_UNPACKED_PUBLIC_KEY_BYTES = P::unpacked_public_key_bytes;

template <typename P>
constexpr std::size_t SDSIGN_PUBLIC_KEY_BYTES = SDSIGN_UNPACKED_PUBLIC_KEY_BYTES<P>;

template <typename P> constexpr std::size_t SDSIGN_PUBLIC_KEY_VECTOR_ELEMENTS = P::y_vector_len;

// sk size
template <typename P>
constexpr std::size_t SDSIGN_PACKED_SECRET_KEY_BYTES = P::packed_secret_key_bytes;

template <typename P>
constexpr std::size_t SDSIGN_UNPACKED_SECRET_KEY_BYTES = P::unpacked_secret_key_bytes;

template <typename P> constexpr std::size_t SDSIGN_WITNESS_BYTES = P::witness_bytes;
template <typename P>
constexpr std::size_t SDSIGN_WITNESS_EXTENDED_SUBVECTOR_BITS =
    P::witness_extended_subvector_bits;
template <typename P>
constexpr std::size_t SDSIGN_WITNESS_EXTENDED_BITS =
    P::witness_rows * SDSIGN_WITNESS_EXTENDED_SUBVECTOR_BITS<P>;
template <typename P>
constexpr std::size_t SDSIGN_WITNESS_EXTENDED_BYTES = (SDSIGN_WITNESS_EXTENDED_BITS<P> + 7) / 8;
template <typename P> constexpr std::size_t SDSIGN_SEED_SK_BYTES = P::secret_seed_bytes;
template <typename P>
constexpr std::size_t SDSIGN_KEYGEN_RANDOM_SEED_BYTES =
    SDSIGN_SEED_SK_BYTES<P> + P::secpar_bytes +
    ((P::owf_v == owf::pkp) ? P::secpar_bytes : 0);

template <typename P>
constexpr std::size_t SDSIGN_SECRET_KEY_BYTES = SDSIGN_UNPACKED_SECRET_KEY_BYTES<P>;

template <typename P> struct sdsign_public_key
{
    typename P::prg_t::key_t seed_pk;
    std::array<block_secpar<P::secpar_v>, SDSIGN_PUBLIC_KEY_VECTOR_ELEMENTS<P>> y{};
};

template <typename P> struct sdsign_secret_key
{
    sdsign_public_key<P> pk;
    typename P::prg_t::key_t seed_sk;
    std::array<uint8_t, SDSIGN_WITNESS_BYTES<P>> witness{};
};

template <typename P>
void sdsign_pack_public_key(uint8_t* packed, const sdsign_public_key<P>* unpacked);

template <typename P>
void sdsign_unpack_public_key(sdsign_public_key<P>* unpacked, const uint8_t* packed);

template <typename P>
void sdsign_pack_secret_key(uint8_t* packed, const sdsign_secret_key<P>* unpacked);

template <typename P>
bool sdsign_unpack_secret_key(sdsign_secret_key<P>* unpacked, const uint8_t* packed);

template <typename P> bool sdsign_compute_witness(const sdsign_secret_key<P>* sk);

template <typename P>
bool sdsign_unpack_sk_and_get_pubkey(uint8_t* pk_packed, const uint8_t* sk_packed,
                                     sdsign_secret_key<P>* sk);

template <typename P> bool sdsign_seckey(const uint8_t* sk_packed);

template <typename P> bool sdsign_pubkey(uint8_t* pk_packed, const uint8_t* sk_packed);

} // namespace sdsign

#include "keys.inc"

#endif
