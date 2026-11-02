#include "api_common.inc"
#include "rsd_parameters.hpp"

namespace sdsign
{

template <typename P> bool sdsign_derive_public_key(uint8_t* pk, const uint8_t* sk)
{
    return sdsign_pubkey<P>(pk, sk);
}

template <typename P>
bool sdsign_keygen(uint8_t* pk, uint8_t* sk, const uint8_t* random_seed,
                 std::size_t random_seed_len)
{
    if (!pk || !sk || !random_seed)
        return false;
    if (random_seed_len != SDSIGN_KEYGEN_RANDOM_SEED_BYTES<P>)
        return false;

    sdsign_secret_key<P> unpacked_sk{};
    const uint8_t* seed_sk = random_seed;
    const uint8_t* seed_pk = random_seed + SDSIGN_SEED_SK_BYTES<P>;
    const uint8_t* seed_kernel = seed_pk + P::secpar_bytes;

    unpacked_sk.seed_sk = P::prg_t::key_t::set_zero();
    unpacked_sk.pk.seed_pk = P::prg_t::key_t::set_zero();
    memcpy(&unpacked_sk.seed_sk, seed_sk, SDSIGN_SEED_SK_BYTES<P>);
    memcpy(&unpacked_sk.pk.seed_pk, seed_pk, P::secpar_bytes);

    if constexpr (P::owf_v == owf::pkp)
    {
        std::array<uint16_t, P::pkp_n> permutation{};
        std::array<uint16_t, P::pkp_n> kernel_y{};
        std::array<uint16_t, P::pkp_n> public_x{};
        std::vector<uint16_t> h(P::pkp_n * P::pkp_m);

        sdsign_detail::pkp_expand_h_matrix<P>(h.data(), unpacked_sk.pk.seed_pk);
        sdsign_detail::pkp_sample_kernel_vector<P>(kernel_y.data(), h.data(), seed_kernel,
                                                    P::secpar_bytes);
        sdsign_detail::pkp_sample_permutation<P>(
            permutation.data(), reinterpret_cast<const uint8_t*>(&unpacked_sk.seed_sk),
            SDSIGN_SEED_SK_BYTES<P>);
        for (std::size_t i = 0; i < P::pkp_n; ++i)
            public_x[i] = kernel_y[permutation[i]];

        if (!sdsign_detail::compute_witness_from_column_indices<P>(&unpacked_sk.witness,
                                                                   permutation.data()))
            return false;
        sdsign_detail::pkp_store_public_x<P>(&unpacked_sk.pk, public_x.data());
    }
    else
    {
        std::array<uint8_t, sdsign_detail::rsd_pos_stream_bytes<P>> x_positions{};
        sdsign_detail::sdsign_sample_x_positions_from_seed<P>(
            x_positions.data(), reinterpret_cast<const uint8_t*>(&unpacked_sk.seed_sk),
            SDSIGN_SEED_SK_BYTES<P>);

        if (!sdsign_detail::compute_witness_from_x_positions<P>(&unpacked_sk.witness,
                                                                x_positions.data()))
            return false;

        sdsign_detail::sdsign_compute_y_from_x_positions_on_demand<P>(
            &unpacked_sk.pk, x_positions.data(), unpacked_sk.pk.seed_pk);
    }

    sdsign_pack_secret_key<P>(sk, &unpacked_sk);
    sdsign_pack_public_key<P>(pk, &unpacked_sk.pk);
    return true;
}

#define SDSIGN_INSTANTIATE_KEYGEN(...)                                                             \
    template bool sdsign_derive_public_key<__VA_ARGS__>(uint8_t*, const uint8_t*);                 \
    template bool sdsign_keygen<__VA_ARGS__>(uint8_t*, uint8_t*, const uint8_t*, std::size_t)

#if defined(SDSIGN_API_PARAM_TYPE)
SDSIGN_INSTANTIATE_KEYGEN(SDSIGN_API_PARAM_TYPE);
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

SDSIGN_INSTANTIATE_KEYGEN(sdsign_128_s);
SDSIGN_INSTANTIATE_KEYGEN(sdsign_128_f);
#if defined(SDSIGN_ENABLE_CST_PROFILE)
SDSIGN_INSTANTIATE_KEYGEN(sdsign_128_s_cst);
SDSIGN_INSTANTIATE_KEYGEN(sdsign_128_f_cst);
#endif
SDSIGN_INSTANTIATE_KEYGEN(sdsign_128_s_param<1>);
SDSIGN_INSTANTIATE_KEYGEN(sdsign_128_f_param<1>);
SDSIGN_INSTANTIATE_KEYGEN(sdsign_128_s_param<0, proof_system_set::set1>);
SDSIGN_INSTANTIATE_KEYGEN(sdsign_128_f_param<0, proof_system_set::set1>);
SDSIGN_INSTANTIATE_KEYGEN(sdsign_128_s_param<1, proof_system_set::set1>);
SDSIGN_INSTANTIATE_KEYGEN(sdsign_128_f_param<1, proof_system_set::set1>);
SDSIGN_INSTANTIATE_KEYGEN(sdsign_192_s);
SDSIGN_INSTANTIATE_KEYGEN(sdsign_192_f);
SDSIGN_INSTANTIATE_KEYGEN(sdsign_192_s_param<1>);
SDSIGN_INSTANTIATE_KEYGEN(sdsign_192_f_param<1>);
SDSIGN_INSTANTIATE_KEYGEN(sdsign_192_s_param<0, proof_system_set::set1>);
SDSIGN_INSTANTIATE_KEYGEN(sdsign_192_f_param<0, proof_system_set::set1>);
SDSIGN_INSTANTIATE_KEYGEN(sdsign_192_s_param<1, proof_system_set::set1>);
SDSIGN_INSTANTIATE_KEYGEN(sdsign_192_f_param<1, proof_system_set::set1>);
SDSIGN_INSTANTIATE_KEYGEN(sdsign_256_s);
SDSIGN_INSTANTIATE_KEYGEN(sdsign_256_f);
SDSIGN_INSTANTIATE_KEYGEN(sdsign_256_s_param<1>);
SDSIGN_INSTANTIATE_KEYGEN(sdsign_256_f_param<1>);
SDSIGN_INSTANTIATE_KEYGEN(sdsign_256_s_param<0, proof_system_set::set1>);
SDSIGN_INSTANTIATE_KEYGEN(sdsign_256_f_param<0, proof_system_set::set1>);
SDSIGN_INSTANTIATE_KEYGEN(sdsign_256_s_param<1, proof_system_set::set1>);
SDSIGN_INSTANTIATE_KEYGEN(sdsign_256_f_param<1, proof_system_set::set1>);
SDSIGN_INSTANTIATE_KEYGEN(pkp_128_s);
SDSIGN_INSTANTIATE_KEYGEN(pkp_128_f);
SDSIGN_INSTANTIATE_KEYGEN(pkp_192_s);
SDSIGN_INSTANTIATE_KEYGEN(pkp_192_f);
SDSIGN_INSTANTIATE_KEYGEN(pkp_256_s);
SDSIGN_INSTANTIATE_KEYGEN(pkp_256_f);
#endif

#undef SDSIGN_INSTANTIATE_KEYGEN

} // namespace sdsign
