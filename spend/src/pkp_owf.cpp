#include "pkp_owf.hpp"

namespace sdsign
{

#define SDSIGN_INSTANTIATE_PKP_OWF(type)                                                           \
    static_assert(pkp_domain_size<type>() >= type::pkp_n);                                         \
    template void pkp_compute_hpx<type>(uint16_t*, const uint16_t*, const uint16_t*,               \
                                        const uint16_t*);                                          \
    template void pkp_precompute_scaled_h_columns<type>(uint16_t*, const uint16_t*,                \
                                                        const uint16_t*);                          \
    template void pkp_compute_hpx_from_scaled<type>(uint16_t*, const uint16_t*,                    \
                                                   const uint16_t*);                               \
    template bool pkp_hpx_is_zero<type>(const uint16_t*, const uint16_t*, const uint16_t*)

SDSIGN_INSTANTIATE_PKP_OWF(pkp_128_s);
SDSIGN_INSTANTIATE_PKP_OWF(pkp_128_f);
SDSIGN_INSTANTIATE_PKP_OWF(pkp_192_s);
SDSIGN_INSTANTIATE_PKP_OWF(pkp_192_f);
SDSIGN_INSTANTIATE_PKP_OWF(pkp_256_s);
SDSIGN_INSTANTIATE_PKP_OWF(pkp_256_f);

#undef SDSIGN_INSTANTIATE_PKP_OWF

} // namespace sdsign
