#ifndef SDSIGN_RING_SIGNATURE_PROFILE_HPP
#define SDSIGN_RING_SIGNATURE_PROFILE_HPP

#include <array>
#include <chrono>
#include <cstddef>
#include <cstdint>

namespace sdsign::ring::profile
{

enum stage : std::size_t
{
    FOLD_H,
    BASE_CONSTRAINTS,
    SELECTOR_CONSTRAINTS,
    RING_SYNDROME_CONTRACTION,
    CONTEXT_DIGEST,
    SECRET_KEY_MATCH,
    STAGE_COUNT,
};

void reset();
std::array<uint64_t, STAGE_COUNT> snapshot(bool verifier);
void add(stage which, bool verifier, uint64_t nanoseconds);

struct scope
{
    stage which;
    bool verifier;
    std::chrono::steady_clock::time_point start;

    scope(stage which_in, bool verifier_in) :
        which(which_in), verifier(verifier_in), start(std::chrono::steady_clock::now())
    {}
    ~scope()
    {
#if defined(SDSIGN_RING_PROFILE)
        const auto elapsed = std::chrono::steady_clock::now() - start;
        add(which, verifier,
            static_cast<uint64_t>(
                std::chrono::duration_cast<std::chrono::nanoseconds>(elapsed).count()));
#endif
    }
};

} // namespace sdsign::ring::profile

#endif
