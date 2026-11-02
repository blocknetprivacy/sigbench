#include "../small_vole.inc"
#include "../vole_commit.inc"
#include "ring_signature/parameters.hpp"
#include "rsd_parameters.hpp"

namespace sdsign
{

using ring_base_l1_short = ring::reduction_compensated_l1_short_set1_base;
#define SDSIGN_RING_INSTANTIATE_PRIMITIVES(N)                                                      \
    using ring_l1_short_##N = ring::parameter_set<ring_base_l1_short, N>;                          \
    template void vole_commit<ring_l1_short_##N>(                                                 \
        block_secpar<secpar::L1>, block128, block_secpar<secpar::L1>* __restrict__,                \
        unsigned char* __restrict__, vole_block* __restrict__, vole_block* __restrict__,           \
        uint8_t* __restrict__, uint8_t* __restrict__);                                             \
    template void vole_receiver_apply_correction<ring_l1_short_##N>(                              \
        size_t, size_t, const vole_block* __restrict__, vole_block* __restrict__,                  \
        const uint8_t* __restrict__);                                                              \
    template bool vole_reconstruct<ring_l1_short_##N>(                                            \
        block128, vole_block* __restrict__, const uint8_t*, const uint8_t* __restrict__,           \
        const uint8_t* __restrict__, uint8_t* __restrict__)

SDSIGN_RING_INSTANTIATE_PRIMITIVES(64);
SDSIGN_RING_INSTANTIATE_PRIMITIVES(1024);
SDSIGN_RING_INSTANTIATE_PRIMITIVES(4096);
SDSIGN_RING_INSTANTIATE_PRIMITIVES(16384);
SDSIGN_RING_INSTANTIATE_PRIMITIVES(65536);
SDSIGN_RING_INSTANTIATE_PRIMITIVES(262144);
SDSIGN_RING_INSTANTIATE_PRIMITIVES(1048576);

#undef SDSIGN_RING_INSTANTIATE_PRIMITIVES

} // namespace sdsign
