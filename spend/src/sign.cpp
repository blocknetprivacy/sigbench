#include "api_common.inc"
#include "profile.hpp"
#include "rsd_parameters.hpp"
#include <cstdlib>

namespace sdsign
{

template <typename P>
bool sdsign_sign(uint8_t* signature, const uint8_t* msg, size_t msg_len, const uint8_t* sk_packed,
               const uint8_t* random_seed, size_t random_seed_len)
{
    using CP = P::CONSTS;
    using OC = P::OWF_CONSTS;
    constexpr auto S = P::secpar_v;

    sdsign_secret_key<P> sk;
    uint8_t pk_packed[SDSIGN_PACKED_PUBLIC_KEY_BYTES<P>];
    if (!sdsign_unpack_sk_and_get_pubkey<P>(pk_packed, sk_packed, &sk))
        return false;

    hash_state hasher;

    block_2secpar<S> mu;
    {
        profile::top_scope timer(profile::SIGN_MU);
        hasher.init(S);
        hasher.update(pk_packed, SDSIGN_PACKED_PUBLIC_KEY_BYTES<P>);
        hasher.update(msg, msg_len);
        hasher.update_byte(8 + 0);
        hasher.finalize(&mu, sizeof(mu));
    }

    block_secpar<S> seed;
    block128 iv;
    block128 iv_pre;
    std::array<uint8_t, sizeof(seed) + sizeof(iv_pre)> seed_iv_pre;
    {
        profile::top_scope timer(profile::SIGN_SEED_IV);
        hasher.init(S);
        hasher.update(&sk.seed_sk, sizeof(sk.seed_sk));
        hasher.update(&mu, sizeof(mu));
        if (random_seed)
            hasher.update(random_seed, random_seed_len);
        hasher.update_byte(3);
        hasher.finalize(seed_iv_pre.data(), sizeof(seed_iv_pre));
        memcpy(&seed, seed_iv_pre.data(), sizeof(seed));
        memcpy(&iv_pre, &seed_iv_pre[sizeof(seed)], sizeof(iv_pre));

        hasher.init(S);
        hasher.update(&iv_pre, sizeof(iv_pre));
        hasher.update_byte(4);
        hasher.finalize(reinterpret_cast<uint8_t*>(&iv), sizeof(iv));
    }

    block_secpar<S>* forest = reinterpret_cast<block_secpar<S>*>(
        fpq_aligned_alloc(alignof(block_secpar<S>), P::bavc_t::COMMIT_NODES * sizeof(block_secpar<S>)));
    unsigned char* hashed_leaves = reinterpret_cast<unsigned char*>(fpq_aligned_alloc(
        alignof(block_2secpar<S>), P::bavc_t::COMMIT_LEAVES * P::leaf_hash_t::hash_len));
    vole_block* u = reinterpret_cast<vole_block*>(
        fpq_aligned_alloc(alignof(vole_block), CP::VOLE_COL_BLOCKS * sizeof(vole_block)));
    vole_block* v = reinterpret_cast<vole_block*>(fpq_aligned_alloc(
        alignof(vole_block), P::secpar_bits * CP::VOLE_COL_BLOCKS * sizeof(vole_block)));
    uint8_t vole_commit_check[CP::VOLE_COMMIT_CHECK_SIZE];

    sdsign_vole_commit<P>(seed, iv, forest, hashed_leaves, u, v, signature, vole_commit_check);

    std::array<uint8_t, CP::VOLE_CHECK::CHALLENGE_BYTES> chal1;
    {
        profile::top_scope timer(profile::SIGN_CHAL1);
        hasher.init(S);
        hasher.update(&mu, sizeof(mu));
        hasher.update(vole_commit_check, CP::VOLE_COMMIT_CHECK_SIZE);
        hasher.update(signature, CP::VOLE_COMMIT_SIZE);
        hasher.update(&iv, sizeof(iv));
        hasher.update_byte(8 + 1);
        hasher.finalize(chal1.data(), sizeof(chal1));
    }

    std::array<uint8_t, CP::QS::CHALLENGE_BYTES> chal2;
    {
        profile::top_scope timer(profile::SIGN_VOLE_CHECK_CHAL2);
        hasher.init(S);
        hasher.update(chal1.data(), sizeof(chal1));

        uint8_t* vole_check_proof = signature + CP::VOLE_COMMIT_SIZE;
        sdsign_vole_check_sender<P>(u, v, chal1.data(), vole_check_proof, hasher);

        uint8_t* correction = vole_check_proof + CP::VOLE_CHECK::PROOF_BYTES;
        size_t remainder = (OC::WITNESS_BITS / 8) % (16 * CP::VOLE_BLOCK);
        constexpr size_t correction_block_bytes = sizeof(vole_block);
        const uint8_t* u_bytes = reinterpret_cast<const uint8_t*>(u);
        for (size_t i = 0; i < CP::WITNESS_BLOCKS - (remainder != 0); ++i)
        {
            const size_t off = i * correction_block_bytes;
            memcpy(correction + off, u_bytes + off, correction_block_bytes);
            for (size_t j = 0; j < correction_block_bytes; ++j)
                correction[off + j] ^= sk.witness[off + j];
        }
        if (remainder)
        {
            const size_t off = (CP::WITNESS_BLOCKS - 1) * correction_block_bytes;
            memcpy(correction + off, u_bytes + off, remainder);
            for (size_t j = 0; j < remainder; ++j)
                correction[off + j] ^= sk.witness[off + j];
        }

        hasher.update(correction, OC::WITNESS_BITS / 8);
        hasher.update_byte(8 + 2);
        hasher.finalize(chal2.data(), sizeof(chal2));
    }

    uint8_t* vole_check_proof = signature + CP::VOLE_COMMIT_SIZE;
    uint8_t* correction = vole_check_proof + CP::VOLE_CHECK::PROOF_BYTES;

    constexpr size_t u_extended_bytes =
        P::witness_extended_bytes + (OC::QS_DEGREE - 1) * P::secpar_bytes;
    constexpr size_t u_extended_alloc_bytes =
        ((u_extended_bytes + sizeof(vole_block) - 1) / sizeof(vole_block)) * sizeof(vole_block);
    uint8_t* u_extended =
        reinterpret_cast<uint8_t*>(fpq_aligned_alloc(alignof(vole_block), u_extended_alloc_bytes));
    uint8_t* qs_proof = correction + OC::WITNESS_BITS / 8;
    std::array<uint8_t, CP::QS::CHECK_BYTES> qs_check;
    {
        profile::top_scope timer(profile::SIGN_QS_OWF_PROVE);
        block_secpar<S>* macs = nullptr;
        block_secpar<S>* macs_extended = nullptr;
        {
            profile::scope alloc_timer(profile::SIGN_QS_ALLOC);
            macs = reinterpret_cast<block_secpar<S>*>(fpq_aligned_alloc(
                alignof(block_secpar<S>), CP::QUICKSILVER_ROWS_PADDED * sizeof(block_secpar<S>)));
            macs_extended = reinterpret_cast<block_secpar<S>*>(fpq_aligned_alloc(
                alignof(block_secpar<S>),
                CP::QUICKSILVER_ROWS_PADDED_EXTENDED * sizeof(block_secpar<S>)));
        }
        {
            profile::scope prep_timer(profile::SIGN_QS_PREP);
            memset(u_extended, 0, u_extended_alloc_bytes);
            sdsign_detail::compute_witness<P>(u_extended, sk.witness.data());
            memcpy(u_extended + P::witness_extended_bytes,
                   reinterpret_cast<const uint8_t*>(u) + OC::WITNESS_BITS / 8,
                   (OC::QS_DEGREE - 1) * P::secpar_bytes);
            fpq_aligned_free(u);
            sdsign_detail::compute_macs_extended<P>(macs_extended, v, macs);
            fpq_aligned_free(macs);
            fpq_aligned_free(v);
        }

#if !defined(SDSIGN_PROFILE_TOP_ONLY) && !defined(SDSIGN_COARSE_PROFILE)
        const uint64_t qs_init_start = profile::now_ns();
#endif
        quicksilver_state<S, false, OC::QS_DEGREE, P::quicksilver_term_v> qs(
            u_extended, macs_extended, OC::OWF_NUM_CONSTRAINTS, chal2.data());
#if !defined(SDSIGN_PROFILE_TOP_ONLY) && !defined(SDSIGN_COARSE_PROFILE)
        profile::add_time(profile::SIGN_QS_STATE_INIT, profile::now_ns() - qs_init_start);
#endif
        uint8_t folded_poly_coeffs[OC::QS_DEGREE * sdsign_secpar_to_bytes(S)] = {0};
        {
            profile::scope owf_timer(profile::SIGN_OWF_CONSTRAINTS_TOTAL);
            sdsign_owf_constraints(&qs, &sk.pk, folded_poly_coeffs);
        }

        {
            profile::scope prove_timer(profile::SIGN_QS_PROVE);
            qs.prove(P::witness_extended_bytes * 8, qs_proof, qs_check.data());
            for (size_t deg = 0; deg < OC::QS_DEGREE; ++deg)
            {
                uint8_t* dst_coeff = nullptr;
                if (deg == 0)
                    dst_coeff = qs_check.data();
                else
                    dst_coeff = qs_proof + (deg - 1) * P::secpar_bytes;

                const uint8_t* src_coeff = folded_poly_coeffs + deg * P::secpar_bytes;
                for (size_t j = 0; j < P::secpar_bytes; ++j)
                    dst_coeff[j] ^= src_coeff[j];
            }
        }
        {
            profile::scope free_timer(profile::SIGN_QS_FREE);
            fpq_aligned_free(macs_extended);
            fpq_aligned_free(u_extended);
        }
    }
    uint8_t* veccom_open_start = qs_proof + CP::QS::PROOF_BYTES;
    uint8_t* delta = veccom_open_start + P::bavc_t::OPEN_SIZE;

    uint8_t* iv_pre_dst = delta + sizeof(block_secpar<S>);
    memcpy(iv_pre_dst, &iv_pre, sizeof(iv_pre));
    uint8_t* grinding_counter_dst = iv_pre_dst + sizeof(iv_pre);

    if constexpr (!P::use_grinding)
    {
        profile::top_scope timer(profile::SIGN_GRIND_OPEN);
        hasher.init(S);
        hasher.update(chal2.data(), sizeof(chal2));
        hasher.update(qs_check.data(), CP::QS::CHECK_BYTES);
        hasher.update(qs_proof, CP::QS::PROOF_BYTES);
        hasher.update_byte(8 + 3);
        hasher.finalize(delta, sizeof(block_secpar<S>));

        std::array<uint8_t, P::delta_bits_v> delta_bytes;
        expand_bits_to_bytes(delta_bytes.data(), P::delta_bits_v, delta);

        P::bavc_t::open(forest, hashed_leaves, delta_bytes.data(), veccom_open_start);
    }
    else
    {
        profile::top_scope timer(profile::SIGN_GRIND_OPEN);
        hash_state_x8 grinding_hasher;
        grinding_hasher.init(S);
        grinding_hasher.update_1(chal2.data(), sizeof(chal2));
        grinding_hasher.update_1(qs_check.data(), CP::QS::CHECK_BYTES);
        grinding_hasher.update_1(qs_proof, CP::QS::PROOF_BYTES);
        uint32_t counter;
        bool open_success = grind_and_open<typename P::bavc_t>(
            forest, hashed_leaves, delta, veccom_open_start, &grinding_hasher, &counter);
        SDSIGN_ASSERT(open_success);
        if (!open_success)
        {
            fpq_aligned_free(forest);
            fpq_aligned_free(hashed_leaves);
            return false;
        }
        grinding_counter_dst[0] = counter;
        grinding_counter_dst[1] = counter >> 8;
        grinding_counter_dst[2] = counter >> 16;
        grinding_counter_dst[3] = counter >> 24;
    }

    fpq_aligned_free(forest);
    fpq_aligned_free(hashed_leaves);

    SDSIGN_ASSERT(grinding_counter_dst + P::grinding_counter_size ==
                 signature + SDSIGN_SIGNATURE_BYTES<P>);

    return true;
}

#define SDSIGN_INSTANTIATE_SIGN(...)                                                               \
    template bool sdsign_sign<__VA_ARGS__>(uint8_t*, const uint8_t*, size_t, const uint8_t*,       \
                                           const uint8_t*, size_t)

#if defined(SDSIGN_API_PARAM_TYPE)
SDSIGN_INSTANTIATE_SIGN(SDSIGN_API_PARAM_TYPE);
#else
template <std::size_t PARAM_SET, proof_system_set SET = proof_system_set::set0>
using sdsign_128_s_param =
    sdsign_rsd_parameter_set<secpar::L1, proof_system_variant::s, SET, PARAM_SET>;
template <std::size_t PARAM_SET, proof_system_set SET = proof_system_set::set0>
using sdsign_128_f_param =
    sdsign_rsd_parameter_set<secpar::L1, proof_system_variant::f, SET, PARAM_SET>;
template <std::size_t PARAM_SET, proof_system_set SET = proof_system_set::set0>
using sdsign_192_s_param =
    sdsign_rsd_parameter_set<secpar::L3, proof_system_variant::s, SET, PARAM_SET>;
template <std::size_t PARAM_SET, proof_system_set SET = proof_system_set::set0>
using sdsign_192_f_param =
    sdsign_rsd_parameter_set<secpar::L3, proof_system_variant::f, SET, PARAM_SET>;
template <std::size_t PARAM_SET, proof_system_set SET = proof_system_set::set0>
using sdsign_256_s_param =
    sdsign_rsd_parameter_set<secpar::L5, proof_system_variant::s, SET, PARAM_SET>;
template <std::size_t PARAM_SET, proof_system_set SET = proof_system_set::set0>
using sdsign_256_f_param =
    sdsign_rsd_parameter_set<secpar::L5, proof_system_variant::f, SET, PARAM_SET>;
#if defined(SDSIGN_ENABLE_CST_PROFILE)
using sdsign_128_s_cst =
    sdsign_parameter_set<secpar::L1, 11, owf::rsd, prg::aes_ctr, prg::aes_ctr,
                         leaf_hash::aes_ctr_stat_bind, 7,
                         std::pair<bavc, std::size_t>{bavc::one_tree, 102}, 0,
                         quicksilver_term::constant>;
using sdsign_128_f_cst =
    sdsign_parameter_set<secpar::L1, 16, owf::rsd, prg::aes_ctr, prg::aes_ctr,
                         leaf_hash::aes_ctr_stat_bind, 8,
                         std::pair<bavc, std::size_t>{bavc::one_tree, 110}, 0,
                         quicksilver_term::constant>;
#endif

SDSIGN_INSTANTIATE_SIGN(sdsign_128_s);
SDSIGN_INSTANTIATE_SIGN(sdsign_128_f);
#if defined(SDSIGN_ENABLE_CST_PROFILE)
SDSIGN_INSTANTIATE_SIGN(sdsign_128_s_cst);
SDSIGN_INSTANTIATE_SIGN(sdsign_128_f_cst);
#endif
SDSIGN_INSTANTIATE_SIGN(sdsign_128_s_param<1>);
SDSIGN_INSTANTIATE_SIGN(sdsign_128_f_param<1>);
SDSIGN_INSTANTIATE_SIGN(sdsign_128_s_param<0, proof_system_set::set1>);
SDSIGN_INSTANTIATE_SIGN(sdsign_128_f_param<0, proof_system_set::set1>);
SDSIGN_INSTANTIATE_SIGN(sdsign_128_s_param<1, proof_system_set::set1>);
SDSIGN_INSTANTIATE_SIGN(sdsign_128_f_param<1, proof_system_set::set1>);
SDSIGN_INSTANTIATE_SIGN(sdsign_192_s);
SDSIGN_INSTANTIATE_SIGN(sdsign_192_f);
SDSIGN_INSTANTIATE_SIGN(sdsign_192_s_param<1>);
SDSIGN_INSTANTIATE_SIGN(sdsign_192_f_param<1>);
SDSIGN_INSTANTIATE_SIGN(sdsign_192_s_param<0, proof_system_set::set1>);
SDSIGN_INSTANTIATE_SIGN(sdsign_192_f_param<0, proof_system_set::set1>);
SDSIGN_INSTANTIATE_SIGN(sdsign_192_s_param<1, proof_system_set::set1>);
SDSIGN_INSTANTIATE_SIGN(sdsign_192_f_param<1, proof_system_set::set1>);
SDSIGN_INSTANTIATE_SIGN(sdsign_256_s);
SDSIGN_INSTANTIATE_SIGN(sdsign_256_f);
SDSIGN_INSTANTIATE_SIGN(sdsign_256_s_param<1>);
SDSIGN_INSTANTIATE_SIGN(sdsign_256_f_param<1>);
SDSIGN_INSTANTIATE_SIGN(sdsign_256_s_param<0, proof_system_set::set1>);
SDSIGN_INSTANTIATE_SIGN(sdsign_256_f_param<0, proof_system_set::set1>);
SDSIGN_INSTANTIATE_SIGN(sdsign_256_s_param<1, proof_system_set::set1>);
SDSIGN_INSTANTIATE_SIGN(sdsign_256_f_param<1, proof_system_set::set1>);
SDSIGN_INSTANTIATE_SIGN(pkp_128_s);
SDSIGN_INSTANTIATE_SIGN(pkp_128_f);
SDSIGN_INSTANTIATE_SIGN(pkp_192_s);
SDSIGN_INSTANTIATE_SIGN(pkp_192_f);
SDSIGN_INSTANTIATE_SIGN(pkp_256_s);
SDSIGN_INSTANTIATE_SIGN(pkp_256_f);
#endif

#undef SDSIGN_INSTANTIATE_SIGN

} // namespace sdsign
