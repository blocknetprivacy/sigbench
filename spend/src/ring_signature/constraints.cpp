#include "ring_signature/constraints.inc"
#include "rsd_parameters.hpp"

namespace sdsign::ring
{

using ring_base_l1_short = reduction_compensated_l1_short_set1_base;

template <typename RP> void instantiate()
{
    using prover = quicksilver_state<RP::secpar_v, false, RP::OWF_CONSTS::QS_DEGREE,
                                     RP::quicksilver_term_v>;
    using verifier = quicksilver_state<RP::secpar_v, true, RP::OWF_CONSTS::QS_DEGREE,
                                       RP::quicksilver_term_v>;
    static_assert(sizeof(prover) != 0 && sizeof(verifier) != 0);
}

#define SDSIGN_RING_INSTANTIATE_CONSTRAINTS(N)                                                     \
    template void constraints<parameter_set<ring_base_l1_short, N>, false>(                       \
        quicksilver_state<secpar::L1, false, 4, ring_base_l1_short::quicksilver_term_v>*,          \
        const public_ring<ring_base_l1_short, N>*, uint8_t*,                                      \
        const std::array<block_secpar<secpar::L1>, ring_base_l1_short::y_vector_len>*,             \
        std::size_t, bool*);                                                                       \
    template void constraints<parameter_set<ring_base_l1_short, N>, true>(                        \
        quicksilver_state<secpar::L1, true, 4, ring_base_l1_short::quicksilver_term_v>*,           \
        const public_ring<ring_base_l1_short, N>*, uint8_t*,                                      \
        const std::array<block_secpar<secpar::L1>, ring_base_l1_short::y_vector_len>*,             \
        std::size_t, bool*)

SDSIGN_RING_INSTANTIATE_CONSTRAINTS(64);
SDSIGN_RING_INSTANTIATE_CONSTRAINTS(1024);
SDSIGN_RING_INSTANTIATE_CONSTRAINTS(4096);
SDSIGN_RING_INSTANTIATE_CONSTRAINTS(16384);
SDSIGN_RING_INSTANTIATE_CONSTRAINTS(65536);
SDSIGN_RING_INSTANTIATE_CONSTRAINTS(262144);
SDSIGN_RING_INSTANTIATE_CONSTRAINTS(1048576);

#undef SDSIGN_RING_INSTANTIATE_CONSTRAINTS

} // namespace sdsign::ring
