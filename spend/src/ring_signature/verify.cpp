#include "ring_signature/verify.hpp"

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
bool verify(const uint8_t* signature, const uint8_t* msg, std::size_t msg_len,
            const prepared_public_ring<typename RP::base_parameter, RP::ring_size>& prepared)
{
    using Base = typename RP::base_parameter;
    using CP = typename RP::CONSTS;
    using OC = typename RP::OWF_CONSTS;
    constexpr auto S = RP::secpar_v;
    if (!prepared.ring)
        return false;
    const auto& ring = *prepared.ring;
    if (!signature || (!msg && msg_len != 0))
        return false;

    hash_state hasher;
    block_2secpar<S> mu;
    {
        profile::scope timer(profile::CONTEXT_DIGEST, true);
        mu = context_digest<Base, RP::ring_size>(prepared, msg, msg_len);
    }
    const uint8_t* vole_check_proof = signature + CP::VOLE_COMMIT_SIZE;
    const uint8_t* correction = vole_check_proof + CP::VOLE_CHECK::PROOF_BYTES;
    const uint8_t* qs_proof = correction + OC::WITNESS_BYTES;
    const uint8_t* opening = qs_proof + CP::QS::PROOF_BYTES;
    const uint8_t* delta = opening + RP::bavc_t::OPEN_SIZE;
    const uint8_t* iv_pre_ptr = delta + sizeof(block_secpar<S>);
    const uint8_t* counter = iv_pre_ptr + sizeof(block128);

    for (std::size_t i = RP::delta_bits_v; i < RP::secpar_bits; ++i)
        if (((delta[i / 8] >> (i % 8)) & 1u) != 0)
            return false;

    block128 iv;
    hasher.init(S);
    hasher.update(iv_pre_ptr, sizeof(iv));
    hasher.update_byte(4);
    hasher.finalize(&iv, sizeof(iv));
    std::array<uint8_t, RP::delta_bits_v> delta_bytes;
    expand_bits_to_bytes(delta_bytes.data(), RP::delta_bits_v, delta);

    auto* q = reinterpret_cast<vole_block*>(fpq_aligned_alloc(
        alignof(vole_block), RP::secpar_bits * CP::VOLE_COL_BLOCKS * sizeof(vole_block)));
    if (!q)
        return false;
    uint8_t vole_commit_check[CP::VOLE_COMMIT_CHECK_SIZE];
    if (!vole_reconstruct<RP>(iv, q, delta_bytes.data(), signature, opening, vole_commit_check))
    {
        fpq_aligned_free(q);
        return false;
    }

    std::array<uint8_t, CP::VOLE_CHECK::CHALLENGE_BYTES> chal1;
    hasher.init(S);
    hasher.update(&mu, sizeof(mu));
    hasher.update(vole_commit_check, sizeof(vole_commit_check));
    hasher.update(signature, CP::VOLE_COMMIT_SIZE);
    hasher.update(&iv, sizeof(iv));
    hasher.update_byte(9);
    hasher.finalize(chal1.data(), chal1.size());

    std::array<uint8_t, CP::QS::CHALLENGE_BYTES> chal2;
    hasher.init(S);
    hasher.update(chal1.data(), chal1.size());
    hasher.update(vole_check_proof, CP::VOLE_CHECK::PROOF_BYTES);
    vole_check_receiver<RP>(q, delta_bytes.data(), chal1.data(), vole_check_proof, hasher);
    hasher.update(correction, OC::WITNESS_BYTES);
    hasher.update_byte(10);
    hasher.finalize(chal2.data(), chal2.size());

    auto* macs = reinterpret_cast<block_secpar<S>*>(fpq_aligned_alloc(
        alignof(block_secpar<S>), CP::QUICKSILVER_ROWS_PADDED * sizeof(block_secpar<S>)));
    auto* macs_extended = reinterpret_cast<block_secpar<S>*>(fpq_aligned_alloc(
        alignof(block_secpar<S>), CP::QUICKSILVER_ROWS_PADDED_EXTENDED * sizeof(block_secpar<S>)));
    if (!macs || !macs_extended)
    {
        fpq_aligned_free(q); fpq_aligned_free(macs); fpq_aligned_free(macs_extended);
        return false;
    }
    std::array<vole_block, CP::WITNESS_BLOCKS> correction_blocks{};
    std::memcpy(correction_blocks.data(), correction, OC::WITNESS_BYTES);
    vole_receiver_apply_correction<RP>(CP::WITNESS_BLOCKS, RP::delta_bits_v,
                                       correction_blocks.data(), q, delta_bytes.data());
    block_secpar<S> delta_block;
    std::memcpy(&delta_block, delta, sizeof(delta_block));
    sdsign_detail::compute_macs_extended_verifier<RP>(macs_extended, q, macs, delta_block);
    fpq_aligned_free(q);
    fpq_aligned_free(macs);

    quicksilver_state<S, true, OC::QS_DEGREE, RP::quicksilver_term_v> qs(
        macs_extended, OC::OWF_NUM_CONSTRAINTS, delta_block, chal2.data());
    std::array<uint8_t, OC::QS_DEGREE * RP::secpar_bytes> folded{};
    constraints<RP, true>(&qs, &ring, folded.data());
    std::array<uint8_t, CP::QS::CHECK_BYTES> qs_check;
    qs.verify(RP::witness_extended_bytes * 8, qs_proof, qs_check.data());
    for (std::size_t j = 0; j < RP::secpar_bytes; ++j)
        qs_check[j] ^= folded[j];
    fpq_aligned_free(macs_extended);

    block_secpar<S> delta_check;
    hasher.init(S);
    hasher.update(chal2.data(), chal2.size());
    hasher.update(qs_check.data(), qs_check.size());
    hasher.update(qs_proof, CP::QS::PROOF_BYTES);
    if constexpr (RP::use_grinding)
        hasher.update(counter, RP::grinding_counter_size);
    hasher.update_byte(11);
    hasher.finalize(&delta_check, sizeof(delta_check));
    return std::memcmp(delta, &delta_check, sizeof(delta_check)) == 0;
}

#define SDSIGN_RING_INSTANTIATE_VERIFY(N)                                                          \
    template bool verify<parameter_set<ring_base_l1_short, N>>(                                   \
        const uint8_t*, const uint8_t*, std::size_t,                                                \
        const prepared_public_ring<ring_base_l1_short, N>&)

SDSIGN_RING_INSTANTIATE_VERIFY(64);
SDSIGN_RING_INSTANTIATE_VERIFY(1024);
SDSIGN_RING_INSTANTIATE_VERIFY(4096);
SDSIGN_RING_INSTANTIATE_VERIFY(16384);
SDSIGN_RING_INSTANTIATE_VERIFY(65536);
SDSIGN_RING_INSTANTIATE_VERIFY(262144);
SDSIGN_RING_INSTANTIATE_VERIFY(1048576);

#undef SDSIGN_RING_INSTANTIATE_VERIFY

} // namespace sdsign::ring
