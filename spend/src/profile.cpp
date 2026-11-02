#include "profile.hpp"

#if defined(SDSIGN_ENABLE_PROFILE) || defined(SDSIGN_COARSE_PROFILE)

#include <atomic>
#include <ctime>

namespace sdsign::profile
{

namespace
{
std::atomic<bool> enabled{false};
std::array<std::atomic<bool>, STAGE_COUNT> stage_enabled{};
std::array<std::atomic<uint64_t>, STAGE_COUNT> stage_ns{};
constexpr size_t MAX_RECORDED_CALLS = 1024;
std::array<std::array<uint64_t, SIGN_GRIND_OPEN + 1>, MAX_RECORDED_CALLS> call_stage_ns{};
size_t skip_calls = 0;
size_t seen_sign_calls = 0;
bool current_sign_call_enabled = false;

struct init_stage_enabled
{
    init_stage_enabled()
    {
        for (auto& value : stage_enabled)
            value.store(true, std::memory_order_relaxed);
    }
} init_stage_enabled_instance;
}

void set_enabled(bool value)
{
    enabled.store(value, std::memory_order_relaxed);
}

void set_all_stages_enabled(bool value)
{
    for (auto& stage : stage_enabled)
        stage.store(value, std::memory_order_relaxed);
}

void set_stage_enabled(size_t stage, bool value)
{
    if (stage < STAGE_COUNT)
        stage_enabled[stage].store(value, std::memory_order_relaxed);
}

void set_skip_calls(size_t calls)
{
    skip_calls = calls;
    seen_sign_calls = 0;
    current_sign_call_enabled = false;
}

bool is_enabled()
{
    return enabled.load(std::memory_order_relaxed);
}

void reset()
{
    for (auto& value : stage_ns)
        value.store(0, std::memory_order_relaxed);
    seen_sign_calls = 0;
    current_sign_call_enabled = false;
    for (auto& call : call_stage_ns)
        call.fill(0);
}

uint64_t now_ns()
{
    timespec ts{};
    clock_gettime(CLOCK_MONOTONIC_RAW, &ts);
    return (uint64_t)ts.tv_sec * 1000000000ull + (uint64_t)ts.tv_nsec;
}

void add_time(size_t stage, uint64_t ns)
{
    if (stage < STAGE_COUNT)
        stage_ns[stage].fetch_add(ns, std::memory_order_relaxed);
}

std::array<uint64_t, STAGE_COUNT> snapshot()
{
    std::array<uint64_t, STAGE_COUNT> result{};
    for (size_t i = 0; i < STAGE_COUNT; ++i)
        result[i] = stage_ns[i].load(std::memory_order_relaxed);
    return result;
}

std::array<uint64_t, STAGE_COUNT> snapshot_last_calls(size_t calls)
{
    std::array<uint64_t, STAGE_COUNT> result{};
    const size_t end = seen_sign_calls < MAX_RECORDED_CALLS ? seen_sign_calls : MAX_RECORDED_CALLS;
    const size_t begin = end > calls ? end - calls : 0;
    for (size_t call = begin; call < end; ++call)
        for (size_t stage = 0; stage <= SIGN_GRIND_OPEN; ++stage)
            result[stage] += call_stage_ns[call][stage];
    return result;
}

#if !defined(SDSIGN_COARSE_PROFILE) && !defined(SDSIGN_PROFILE_TOP_ONLY)
scope::scope(size_t stage)
    : stage_(stage), start_(0), active_(false)
{
    active_ = is_enabled() && stage < STAGE_COUNT &&
              stage_enabled[stage].load(std::memory_order_relaxed);
    if (active_)
        start_ = now_ns();
}

scope::~scope()
{
    if (active_)
        add_time(stage_, now_ns() - start_);
}
#endif

top_scope::top_scope(size_t stage)
    : stage_(stage), start_(0), active_(false)
{
    if (stage == SIGN_MU)
        current_sign_call_enabled = (++seen_sign_calls > skip_calls);
    active_ = current_sign_call_enabled && is_enabled() && stage < STAGE_COUNT &&
              stage_enabled[stage].load(std::memory_order_relaxed);
    if (active_)
        start_ = now_ns();
}

top_scope::~top_scope()
{
    if (active_)
    {
        const uint64_t elapsed = now_ns() - start_;
        add_time(stage_, elapsed);
        if (seen_sign_calls > 0 && seen_sign_calls <= MAX_RECORDED_CALLS &&
            stage_ <= SIGN_GRIND_OPEN)
            call_stage_ns[seen_sign_calls - 1][stage_] += elapsed;
    }
}

} // namespace sdsign::profile

#endif
