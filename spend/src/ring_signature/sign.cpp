#include "ring_signature/sign.hpp"

#include "../api_common.inc"
#include "ring_signature/constraints.inc"
#include "ring_signature/profile.hpp"
#include "ring_signature/transcript.hpp"
#include "rsd_parameters.hpp"

#include <array>
#include <cstdlib>
#include <cstring>

namespace sdsign::ring
{

using ring_base_l1_short = reduction_compensated_l1_short_set1_base;

template <typename RP>
bool sign(uint8_t* signature, const uint8_t* msg, std::size_t msg_len,
          const prepared_public_ring<typename RP::base_parameter, RP::ring_size>& prepared,
          const uint8_t* packed_secret_key, std::size_t signer_index, const uint8_t* random_seed,
          std::size_t random_seed_len)
{
    using Base = typename RP::base_parameter;
    using CP = typename RP::CONSTS;
    using OC = typename RP::OWF_CONSTS;
    constexpr auto S = RP::secpar_v;
    if (!prepared.ring)
        return false;
    const auto& ring = *prepared.ring;
    if (!signature || (!msg && msg_len != 0) || !packed_secret_key || signer_index >= RP::ring_size)
        return false;
    sdsign_secret_key<Base> sk{};
    if (!sdsign_unpack_secret_key<Base>(&sk, packed_secret_key))
        return false;
    {
        profile::scope timer(profile::SECRET_KEY_MATCH, false);
        uint8_t seed_mismatch = 0;
        const auto* key_seed = reinterpret_cast<const uint8_t*>(&sk.pk.seed_pk);
        const auto* ring_seed = reinterpret_cast<const uint8_t*>(&ring.seed_pk);
        for (std::size_t byte = 0; byte < Base::secpar_bytes; ++byte)
            seed_mismatch |= static_cast<uint8_t>(key_seed[byte] ^ ring_seed[byte]);
        if (seed_mismatch != 0)
            return false;
    }

    std::array<uint8_t, RP::witness_bytes> witness{};
    std::memcpy(witness.data(), sk.witness.data(), Base::witness_bytes);
    const auto selector = selector_encoding<RP::ring_size>::encode(signer_index);
    std::size_t selector_bit = RP::selector_witness_offset;
    for (uint8_t bit : selector.left)
        sdsign_detail::set_bit_lsb_first(witness.data(), selector_bit++, bit != 0);
    for (uint8_t bit : selector.right)
        sdsign_detail::set_bit_lsb_first(witness.data(), selector_bit++, bit != 0);

    hash_state hasher;
    block_2secpar<S> mu;
    {
        profile::scope timer(profile::CONTEXT_DIGEST, false);
        mu = context_digest<Base, RP::ring_size>(prepared, msg, msg_len);
    }
    block_secpar<S> seed;
    block128 iv;
    block128 iv_pre;
    std::array<uint8_t, sizeof(seed) + sizeof(iv_pre)> seed_iv_pre;
    hasher.init(S);
    hasher.update(&sk.seed_sk, sizeof(sk.seed_sk));
    hasher.update(&mu, sizeof(mu));
    if (random_seed)
        hasher.update(random_seed, random_seed_len);
    hasher.update_byte(3);
    hasher.finalize(seed_iv_pre.data(), seed_iv_pre.size());
    std::memcpy(&seed, seed_iv_pre.data(), sizeof(seed));
    std::memcpy(&iv_pre, seed_iv_pre.data() + sizeof(seed), sizeof(iv_pre));
    hasher.init(S);
    hasher.update(&iv_pre, sizeof(iv_pre));
    hasher.update_byte(4);
    hasher.finalize(&iv, sizeof(iv));

    auto* forest = reinterpret_cast<block_secpar<S>*>(
        fpq_aligned_alloc(alignof(block_secpar<S>), RP::bavc_t::COMMIT_NODES * sizeof(block_secpar<S>)));
    auto* hashed_leaves = reinterpret_cast<unsigned char*>(fpq_aligned_alloc(
        alignof(block_2secpar<S>), RP::bavc_t::COMMIT_LEAVES * RP::leaf_hash_t::hash_len));
    auto* u = reinterpret_cast<vole_block*>(
        fpq_aligned_alloc(alignof(vole_block), CP::VOLE_COL_BLOCKS * sizeof(vole_block)));
    auto* v = reinterpret_cast<vole_block*>(fpq_aligned_alloc(
        alignof(vole_block), RP::secpar_bits * CP::VOLE_COL_BLOCKS * sizeof(vole_block)));
    if (!forest || !hashed_leaves || !u || !v)
    {
        fpq_aligned_free(forest); fpq_aligned_free(hashed_leaves); fpq_aligned_free(u); fpq_aligned_free(v);
        return false;
    }
    uint8_t vole_commit_check[CP::VOLE_COMMIT_CHECK_SIZE];
    sdsign_vole_commit<RP>(seed, iv, forest, hashed_leaves, u, v, signature, vole_commit_check);

    std::array<uint8_t, CP::VOLE_CHECK::CHALLENGE_BYTES> chal1;
    hasher.init(S);
    hasher.update(&mu, sizeof(mu));
    hasher.update(vole_commit_check, sizeof(vole_commit_check));
    hasher.update(signature, CP::VOLE_COMMIT_SIZE);
    hasher.update(&iv, sizeof(iv));
    hasher.update_byte(9);
    hasher.finalize(chal1.data(), chal1.size());

    uint8_t* vole_check_proof = signature + CP::VOLE_COMMIT_SIZE;
    uint8_t* correction = vole_check_proof + CP::VOLE_CHECK::PROOF_BYTES;
    std::array<uint8_t, CP::QS::CHALLENGE_BYTES> chal2;
    hasher.init(S);
    hasher.update(chal1.data(), chal1.size());
    sdsign_vole_check_sender<RP>(u, v, chal1.data(), vole_check_proof, hasher);
    const uint8_t* u_bytes = reinterpret_cast<const uint8_t*>(u);
    std::memcpy(correction, u_bytes, OC::WITNESS_BYTES);
    for (std::size_t i = 0; i < OC::WITNESS_BYTES; ++i)
        correction[i] ^= witness[i];
    hasher.update(correction, OC::WITNESS_BYTES);
    hasher.update_byte(10);
    hasher.finalize(chal2.data(), chal2.size());

    constexpr std::size_t extended_bytes =
        RP::witness_extended_bytes + (OC::QS_DEGREE - 1) * RP::secpar_bytes;
    constexpr std::size_t extended_alloc =
        ((extended_bytes + sizeof(vole_block) - 1) / sizeof(vole_block)) * sizeof(vole_block);
    auto* u_extended = reinterpret_cast<uint8_t*>(fpq_aligned_alloc(alignof(vole_block), extended_alloc));
    auto* macs = reinterpret_cast<block_secpar<S>*>(fpq_aligned_alloc(
        alignof(block_secpar<S>), CP::QUICKSILVER_ROWS_PADDED * sizeof(block_secpar<S>)));
    auto* macs_extended = reinterpret_cast<block_secpar<S>*>(fpq_aligned_alloc(
        alignof(block_secpar<S>), CP::QUICKSILVER_ROWS_PADDED_EXTENDED * sizeof(block_secpar<S>)));
    if (!u_extended || !macs || !macs_extended)
    {
        fpq_aligned_free(forest); fpq_aligned_free(hashed_leaves); fpq_aligned_free(u); fpq_aligned_free(v);
        fpq_aligned_free(u_extended); fpq_aligned_free(macs); fpq_aligned_free(macs_extended);
        return false;
    }
    std::memset(u_extended, 0, extended_alloc);
    for (std::size_t bit = 0; bit < RP::selector_extended_offset; ++bit)
        sdsign_detail::set_bit_lsb_first(
            u_extended, bit, sdsign_detail::get_bit_lsb_first(witness.data(), bit) != 0);
    for (std::size_t bit = 0; bit < RP::selector_bits; ++bit)
        sdsign_detail::set_bit_lsb_first(
            u_extended, RP::selector_extended_offset + bit,
            sdsign_detail::get_bit_lsb_first(witness.data(), RP::selector_witness_offset + bit) !=
                0);
    std::memcpy(u_extended + RP::witness_extended_bytes,
                reinterpret_cast<const uint8_t*>(u) + OC::WITNESS_BYTES,
                (OC::QS_DEGREE - 1) * RP::secpar_bytes);
    fpq_aligned_free(u);
    sdsign_detail::compute_macs_extended<RP>(macs_extended, v, macs);
    fpq_aligned_free(macs);
    fpq_aligned_free(v);

    uint8_t* qs_proof = correction + OC::WITNESS_BYTES;
    std::array<uint8_t, CP::QS::CHECK_BYTES> qs_check;
    quicksilver_state<S, false, OC::QS_DEGREE, RP::quicksilver_term_v> qs(
        u_extended, macs_extended, OC::OWF_NUM_CONSTRAINTS, chal2.data());
    std::array<uint8_t, OC::QS_DEGREE * RP::secpar_bytes> folded{};
    bool signer_matches = false;
    constraints<RP, false>(&qs, &ring, folded.data(), &sk.pk.y, signer_index, &signer_matches);
    if (!signer_matches)
    {
        fpq_aligned_free(macs_extended); fpq_aligned_free(u_extended); fpq_aligned_free(forest); fpq_aligned_free(hashed_leaves);
        return false;
    }
    qs.prove(RP::witness_extended_bytes * 8, qs_proof, qs_check.data());
    for (std::size_t degree = 0; degree < OC::QS_DEGREE; ++degree)
    {
        uint8_t* dst = degree == 0 ? qs_check.data()
                                   : qs_proof + (degree - 1) * RP::secpar_bytes;
        for (std::size_t j = 0; j < RP::secpar_bytes; ++j)
            dst[j] ^= folded[degree * RP::secpar_bytes + j];
    }
    fpq_aligned_free(macs_extended);
    fpq_aligned_free(u_extended);

    uint8_t* opening = qs_proof + CP::QS::PROOF_BYTES;
    uint8_t* delta = opening + RP::bavc_t::OPEN_SIZE;
    uint8_t* iv_pre_dst = delta + sizeof(block_secpar<S>);
    std::memcpy(iv_pre_dst, &iv_pre, sizeof(iv_pre));
    uint8_t* counter_dst = iv_pre_dst + sizeof(iv_pre);
    if constexpr (!RP::use_grinding)
    {
        hasher.init(S);
        hasher.update(chal2.data(), chal2.size());
        hasher.update(qs_check.data(), qs_check.size());
        hasher.update(qs_proof, CP::QS::PROOF_BYTES);
        hasher.update_byte(11);
        hasher.finalize(delta, sizeof(block_secpar<S>));
        std::array<uint8_t, RP::delta_bits_v> delta_bytes;
        expand_bits_to_bytes(delta_bytes.data(), RP::delta_bits_v, delta);
        RP::bavc_t::open(forest, hashed_leaves, delta_bytes.data(), opening);
    }
    else
    {
        hash_state_x8 grinding_hasher;
        grinding_hasher.init(S);
        grinding_hasher.update_1(chal2.data(), chal2.size());
        grinding_hasher.update_1(qs_check.data(), qs_check.size());
        grinding_hasher.update_1(qs_proof, CP::QS::PROOF_BYTES);
        uint32_t counter = 0;
        if (!grind_and_open<typename RP::bavc_t>(forest, hashed_leaves, delta, opening,
                                                 &grinding_hasher, &counter))
        {
            fpq_aligned_free(forest); fpq_aligned_free(hashed_leaves);
            return false;
        }
        for (std::size_t i = 0; i < 4; ++i)
            counter_dst[i] = static_cast<uint8_t>(counter >> (8 * i));
    }
    fpq_aligned_free(forest);
    fpq_aligned_free(hashed_leaves);
    return true;
}

#define SDSIGN_RING_INSTANTIATE_SIGN(N)                                                            \
    template bool sign<parameter_set<ring_base_l1_short, N>>(                                     \
        uint8_t*, const uint8_t*, std::size_t,                                                     \
        const prepared_public_ring<ring_base_l1_short, N>&,                                        \
        const uint8_t*, std::size_t, const uint8_t*, std::size_t)

SDSIGN_RING_INSTANTIATE_SIGN(64);
SDSIGN_RING_INSTANTIATE_SIGN(1024);
SDSIGN_RING_INSTANTIATE_SIGN(4096);
SDSIGN_RING_INSTANTIATE_SIGN(16384);
SDSIGN_RING_INSTANTIATE_SIGN(65536);
SDSIGN_RING_INSTANTIATE_SIGN(262144);
SDSIGN_RING_INSTANTIATE_SIGN(1048576);

#undef SDSIGN_RING_INSTANTIATE_SIGN

} // namespace sdsign::ring
