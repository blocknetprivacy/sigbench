#include "sdsign.hpp"
#include "pkp_owf.hpp"
#include "rsd_parameters.hpp"
#include "small_vole.inc"
#include "vole_commit.inc"

namespace sdsign
{

// clang-format off

#define SDSIGN_INSTANTIATE_VOLE_RECEIVER(...)                                                      \
    template void vole_receiver<__VA_ARGS__>(                                                      \
        unsigned int, const block_secpar<__VA_ARGS__::secpar_v>* __restrict__, block128, uint32_t, \
        const vole_block* __restrict__, vole_block* __restrict__, const uint8_t* __restrict__);    \
    template void vole_receiver_apply_correction<__VA_ARGS__>(                                    \
        size_t, size_t, const vole_block* __restrict__, vole_block* __restrict__,                 \
        const uint8_t* __restrict__);                                                            \
    template bool vole_reconstruct<__VA_ARGS__>(block128, vole_block* __restrict__, const uint8_t*, \
                                                const uint8_t* __restrict__,                       \
                                                const uint8_t* __restrict__, uint8_t* __restrict__)

#if defined(SDSIGN_API_PARAM_TYPE)
SDSIGN_INSTANTIATE_VOLE_RECEIVER(SDSIGN_API_PARAM_TYPE);
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
    sdsign_rsd_parameter_set<secpar::L1, proof_system_variant::s, proof_system_set::set0, 0,
                             quicksilver_term::constant>;
using sdsign_128_f_cst =
    sdsign_rsd_parameter_set<secpar::L1, proof_system_variant::f, proof_system_set::set0, 0,
                             quicksilver_term::constant>;
#endif

SDSIGN_INSTANTIATE_VOLE_RECEIVER(sdsign_128_s);
SDSIGN_INSTANTIATE_VOLE_RECEIVER(sdsign_128_f);
#if defined(SDSIGN_ENABLE_CST_PROFILE)
SDSIGN_INSTANTIATE_VOLE_RECEIVER(sdsign_128_s_cst);
SDSIGN_INSTANTIATE_VOLE_RECEIVER(sdsign_128_f_cst);
#endif
SDSIGN_INSTANTIATE_VOLE_RECEIVER(sdsign_128_s_param<1>);
SDSIGN_INSTANTIATE_VOLE_RECEIVER(sdsign_128_f_param<1>);
SDSIGN_INSTANTIATE_VOLE_RECEIVER(sdsign_192_s);
SDSIGN_INSTANTIATE_VOLE_RECEIVER(sdsign_192_f);
SDSIGN_INSTANTIATE_VOLE_RECEIVER(sdsign_192_s_param<1>);
SDSIGN_INSTANTIATE_VOLE_RECEIVER(sdsign_192_f_param<1>);
SDSIGN_INSTANTIATE_VOLE_RECEIVER(sdsign_256_s);
SDSIGN_INSTANTIATE_VOLE_RECEIVER(sdsign_256_f);
SDSIGN_INSTANTIATE_VOLE_RECEIVER(sdsign_256_s_param<1>);
SDSIGN_INSTANTIATE_VOLE_RECEIVER(sdsign_256_f_param<1>);

#define SDSIGN_INSTANTIATE_VOLE_RECEIVER_SET1(sec, variant, param_set)                            \
    SDSIGN_INSTANTIATE_VOLE_RECEIVER(                                                              \
        sdsign_rsd_parameter_set<secpar::sec, proof_system_variant::variant,                       \
                                 proof_system_set::set1, param_set>)
SDSIGN_INSTANTIATE_VOLE_RECEIVER_SET1(L1, s, 0);
SDSIGN_INSTANTIATE_VOLE_RECEIVER_SET1(L1, f, 0);
SDSIGN_INSTANTIATE_VOLE_RECEIVER_SET1(L1, s, 1);
SDSIGN_INSTANTIATE_VOLE_RECEIVER_SET1(L1, f, 1);
SDSIGN_INSTANTIATE_VOLE_RECEIVER_SET1(L3, s, 0);
SDSIGN_INSTANTIATE_VOLE_RECEIVER_SET1(L3, f, 0);
SDSIGN_INSTANTIATE_VOLE_RECEIVER_SET1(L3, s, 1);
SDSIGN_INSTANTIATE_VOLE_RECEIVER_SET1(L3, f, 1);
SDSIGN_INSTANTIATE_VOLE_RECEIVER_SET1(L5, s, 0);
SDSIGN_INSTANTIATE_VOLE_RECEIVER_SET1(L5, f, 0);
SDSIGN_INSTANTIATE_VOLE_RECEIVER_SET1(L5, s, 1);
SDSIGN_INSTANTIATE_VOLE_RECEIVER_SET1(L5, f, 1);
#undef SDSIGN_INSTANTIATE_VOLE_RECEIVER_SET1
SDSIGN_INSTANTIATE_VOLE_RECEIVER(pkp_128_s);
SDSIGN_INSTANTIATE_VOLE_RECEIVER(pkp_128_f);
SDSIGN_INSTANTIATE_VOLE_RECEIVER(pkp_192_s);
SDSIGN_INSTANTIATE_VOLE_RECEIVER(pkp_192_f);
SDSIGN_INSTANTIATE_VOLE_RECEIVER(pkp_256_s);
SDSIGN_INSTANTIATE_VOLE_RECEIVER(pkp_256_f);
#endif

#undef SDSIGN_INSTANTIATE_VOLE_RECEIVER

// clang-format on

} // namespace sdsign
