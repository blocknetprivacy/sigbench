#include "ring_signature/profile.hpp"

namespace sdsign::ring::profile
{

namespace
{
thread_local std::array<std::array<uint64_t, STAGE_COUNT>, 2> counters{};
}

void reset() { counters = {}; }

std::array<uint64_t, STAGE_COUNT> snapshot(bool verifier)
{
    return counters[verifier ? 1 : 0];
}

void add(stage which, bool verifier, uint64_t nanoseconds)
{
#if defined(SDSIGN_RING_PROFILE)
    counters[verifier ? 1 : 0][which] += nanoseconds;
#else
    (void)which;
    (void)verifier;
    (void)nanoseconds;
#endif
}

} // namespace sdsign::ring::profile
