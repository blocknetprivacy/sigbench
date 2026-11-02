#include "tx/capi.h"
#include "tx/tx.hpp"

#include <chrono>
#include <cstring>
#include <memory>
#include <vector>

using namespace sdsign;
using namespace sdsign::tx;

namespace
{

constexpr std::size_t RING = 1048576;

struct prepared
{
    anon_set set;
    std::vector<spend_key> keys;
    std::vector<coin> coins;
    std::vector<std::size_t> index;
    double digest_ms = 0;
    double build_ms = 0;
};

struct send_args
{
    int64_t first_coin = -1;
    const uint8_t* out_pk = nullptr;
    const uint8_t* out_seed = nullptr;
};

uint64_t splitmix(uint64_t& x)
{
    uint64_t z = (x += 0x9e3779b97f4a7c15ull);
    z = (z ^ (z >> 30)) * 0xbf58476d1ce4e5b9ull;
    z = (z ^ (z >> 27)) * 0x94d049bb133111ebull;
    return z ^ (z >> 31);
}

void seed_of(uint8_t* s, uint64_t a, uint64_t b)
{
    std::memcpy(s, &a, 8);
    std::memcpy(s + 8, &b, 8);
}

void filler(commitment* c, uint64_t i)
{
    uint64_t x = i * 0x9e3779b97f4a7c15ull + 1;
    auto* p = reinterpret_cast<uint8_t*>(c);
    for (std::size_t b = 0; b < sizeof(commitment); ++b)
    {
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        p[b] = static_cast<uint8_t>(x);
    }
}

constexpr std::size_t MAX_IN = 16;
constexpr uint64_t COIN = 5000000;

template <std::size_t N>
int run(const prepared& p, uint64_t seed, fpq_measure* m, double (*cpu_ms)(), uint8_t* proof_out = nullptr,
        uint8_t* witness_out = nullptr, uint8_t* public_out = nullptr, const send_args& a = {})
{
    uint8_t s[16];
    std::vector<input> ins(N);
    if (a.first_coin >= 0 && static_cast<std::size_t>(a.first_coin) + N > p.coins.size())
        return 0;
    for (std::size_t j = 0; j < N; ++j)
    {
        const std::size_t pick = a.first_coin >= 0 ? static_cast<std::size_t>(a.first_coin) + j : (seed * 7 + j) % MAX_IN;
        ins[j].c = p.coins[pick];
        ins[j].key = p.keys[pick];
        ins[j].index = p.index[pick];
    }
    for (std::size_t j = 0; j < N; ++j)
        for (std::size_t i = 0; i < j; ++i)
            if (ins[i].index == ins[j].index)
                return 0;
    const uint64_t fee = 1000 + seed % 1000;
    std::vector<coin> outs(N);
    std::vector<commitment> outc(N);
    std::vector<uint64_t> amounts(N);
    uint64_t left = N * COIN - fee;
    for (std::size_t k = 0; k < N; ++k)
    {
        owner_key to;
        if (a.out_pk)
            std::memcpy(to.data(), a.out_pk + PK_BYTES * k, PK_BYTES);
        else
        {
            spend_key rk;
            seed_of(s, seed, 1000 + k);
            if (!make_spend_key(&rk, s, 16))
                return 0;
            to = rk.pk;
        }
        const uint64_t amount = (k + 1 == N) ? left : (left / N) - k;
        left -= amount;
        amounts[k] = amount;
        seed_of(s, seed, 2000 + k);
        const uint8_t* cs = a.out_seed ? a.out_seed + 16 * k : s;
        if (!make_coin(&outs[k], &outc[k], to, amount, cs, 16))
            return 0;
    }
    std::vector<block128> nfs(N);
    for (std::size_t j = 0; j < N; ++j)
        nfs[j] = nullifier(ins[j].key, ins[j].c);
    statement st{&p.set, nfs.data(), outc.data(), fee, nullptr, 0};

    std::vector<uint8_t> proof(proof_bytes<N, N, RING>);
    seed_of(s, seed, 3000);
    using clk = std::chrono::steady_clock;
    const double c0 = cpu_ms();
    const auto t0 = clk::now();
    const bool ok_p = witness_out
                          ? prove_capture<N, N, RING>(proof.data(), st, ins.data(), outs.data(), s, 16, witness_out)
                          : prove<N, N, RING>(proof.data(), st, ins.data(), outs.data(), s, 16);
    const auto t1 = clk::now();
    const double c1 = cpu_ms();
    const bool ok_v = ok_p && verify<N, N, RING>(proof.data(), st);
    const auto t2 = clk::now();
    const double c2 = cpu_ms();
    m->proof_bytes = proof.size();
    if (proof_out)
        std::memcpy(proof_out, proof.data(), proof.size());
    if (public_out)
    {
        uint8_t* o = public_out;
        for (std::size_t j = 0; j < N; ++j, o += sizeof(block128))
            std::memcpy(o, &nfs[j], sizeof(block128));
        for (std::size_t k = 0; k < N; ++k, o += sizeof(commitment))
            std::memcpy(o, outc[k].data(), sizeof(commitment));
        for (std::size_t k = 0; k < N; ++k, o += 8)
            std::memcpy(o, &amounts[k], 8);
        std::memcpy(o, &fee, 8);
        o += 8;
        std::memcpy(o, &p.set.digest, sizeof(p.set.digest));
    }
    m->prove_ms = std::chrono::duration<double, std::milli>(t1 - t0).count();
    m->verify_ms = std::chrono::duration<double, std::milli>(t2 - t1).count();
    m->prove_cpu_ms = c1 - c0;
    m->verify_cpu_ms = c2 - c1;
    return ok_p && ok_v;
}

template <std::size_t N> int reject(const prepared& p)
{
    fpq_measure m{};
    uint8_t s[16];
    std::vector<input> ins(N);
    for (std::size_t j = 0; j < N; ++j)
    {
        ins[j].c = p.coins[j];
        ins[j].key = p.keys[j];
        ins[j].index = p.index[j];
    }
    std::vector<coin> outs(N);
    std::vector<commitment> outc(N);
    uint64_t left = N * COIN;
    for (std::size_t k = 0; k < N; ++k)
    {
        spend_key rk;
        seed_of(s, 9, k);
        make_spend_key(&rk, s, 16);
        const uint64_t amount = (k + 1 == N) ? left : left / N;
        left -= amount;
        seed_of(s, 10, k);
        make_coin(&outs[k], &outc[k], rk.pk, amount, s, 16);
    }
    std::vector<block128> nfs(N);
    for (std::size_t j = 0; j < N; ++j)
        nfs[j] = nullifier(ins[j].key, ins[j].c);
    statement st{&p.set, nfs.data(), outc.data(), 0, nullptr, 0};
    std::vector<uint8_t> proof(proof_bytes<N, N, RING>);
    if (!prove<N, N, RING>(proof.data(), st, ins.data(), outs.data(), s, 16))
        return 0;
    if (!verify<N, N, RING>(proof.data(), st))
        return 0;
    statement bad = st;
    bad.fee = 1;
    if (verify<N, N, RING>(proof.data(), bad))
        return 0;
    proof[proof.size() / 3] ^= 1;
    if (verify<N, N, RING>(proof.data(), st))
        return 0;
    (void)m;
    return 1;
}

} // namespace

extern "C" {

void* fpq_prepare(void)
{
    auto p = std::make_unique<prepared>();
    p->set.members.resize(RING);
    for (std::size_t m = 0; m < RING; ++m)
        filler(&p->set.members[m], m);
    uint8_t s[16];
    for (std::size_t j = 0; j < MAX_IN; ++j)
    {
        spend_key k;
        seed_of(s, 77, j);
        if (!make_spend_key(&k, s, 16))
            return nullptr;
        coin c;
        commitment cm;
        seed_of(s, 78, j);
        if (!make_coin(&c, &cm, k.pk, COIN, s, 16))
            return nullptr;
        const std::size_t at = (RING / (MAX_IN + 1)) * (j + 1) + 11;
        p->set.members[at] = cm;
        p->keys.push_back(k);
        p->coins.push_back(c);
        p->index.push_back(at);
    }
    const auto t0 = std::chrono::steady_clock::now();
    set_digest(&p->set);
    p->digest_ms =
        std::chrono::duration<double, std::milli>(std::chrono::steady_clock::now() - t0).count();
    return p.release();
}

void* fpq_prepare_seeded(const uint8_t* seed, size_t seed_len, size_t pool, size_t* progress)
{
    if (seed_len > 32 || pool == 0 || pool > RING)
        return nullptr;
    const auto t0 = std::chrono::steady_clock::now();
    auto p = std::make_unique<prepared>();
    p->set.members.resize(RING);
    uint8_t ms[40] = {0};
    std::memcpy(ms, seed, seed_len);
    uint64_t rng = 0;
    for (std::size_t i = 0; i < seed_len; ++i)
        rng = rng * 131 + seed[i];
    std::vector<uint8_t> taken(RING, 0);
    std::vector<std::size_t> at(pool);
    for (std::size_t j = 0; j < pool; ++j)
    {
        std::size_t x = splitmix(rng) % RING;
        while (taken[x])
            x = (x + 1) % RING;
        taken[x] = 1;
        at[j] = x;
    }
    for (uint64_t m = 0; m < RING; ++m)
    {
        std::memcpy(ms + 32, &m, 8);
        spend_key k;
        coin c;
        if (!make_spend_key(&k, ms, sizeof(ms)))
            return nullptr;
        const uint64_t amount = taken[m] ? COIN : 1 + splitmix(rng) % 100000000000ull;
        if (!make_coin(&c, &p->set.members[m], k.pk, amount, ms, sizeof(ms)))
            return nullptr;
        if (progress && (m & 1023) == 1023)
            __atomic_store_n(progress, static_cast<size_t>(m + 1), __ATOMIC_RELAXED);
    }
    for (std::size_t j = 0; j < pool; ++j)
    {
        const uint64_t m = at[j];
        std::memcpy(ms + 32, &m, 8);
        spend_key k;
        coin c;
        commitment cm;
        make_spend_key(&k, ms, sizeof(ms));
        make_coin(&c, &cm, k.pk, COIN, ms, sizeof(ms));
        p->keys.push_back(k);
        p->coins.push_back(c);
        p->index.push_back(m);
    }
    const auto t1 = std::chrono::steady_clock::now();
    set_digest(&p->set);
    const auto t2 = std::chrono::steady_clock::now();
    p->build_ms = std::chrono::duration<double, std::milli>(t2 - t0).count();
    p->digest_ms = std::chrono::duration<double, std::milli>(t2 - t1).count();
    return p.release();
}

double fpq_set_build_ms(const void* p) { return static_cast<const prepared*>(p)->build_ms; }

size_t fpq_pool_size(const void* p) { return static_cast<const prepared*>(p)->coins.size(); }

void fpq_free(void* p) { delete static_cast<prepared*>(p); }

double fpq_set_digest_ms(const void* p) { return static_cast<const prepared*>(p)->digest_ms; }

size_t fpq_set_size(void) { return RING; }

size_t fpq_set_bytes(void) { return RING * sizeof(commitment); }

size_t fpq_commitment_bytes(void) { return sizeof(commitment); }

size_t fpq_nullifier_bytes(void) { return sizeof(block128); }

size_t fpq_proof_bytes(size_t n)
{
    switch (n)
    {
    case 2: return proof_bytes<2, 2, RING>;
    case 4: return proof_bytes<4, 4, RING>;
    case 8: return proof_bytes<8, 8, RING>;
    case 16: return proof_bytes<16, 16, RING>;
    default: return 0;
    }
}

int fpq_run(const void* pv, size_t n, uint64_t seed, fpq_measure* m, double (*cpu_ms)(void))
{
    const auto& p = *static_cast<const prepared*>(pv);
    switch (n)
    {
    case 2: return run<2>(p, seed, m, cpu_ms);
    case 4: return run<4>(p, seed, m, cpu_ms);
    case 8: return run<8>(p, seed, m, cpu_ms);
    case 16: return run<16>(p, seed, m, cpu_ms);
    default: return 0;
    }
}

int fpq_self_check(const void* pv)
{
    const auto& p = *static_cast<const prepared*>(pv);
    return reject<2>(p);
}

}

extern "C" int fpq_commit_check(const uint8_t* r, const uint8_t* pk, uint64_t amount, const uint8_t* c)
{
    coin k;
    std::memcpy(&k.r, r, 16);
    std::memcpy(k.pk.data(), pk, PK_BYTES);
    k.amount = amount;
    commitment out;
    commit(&out, k);
    return std::memcmp(&out, c, sizeof(out)) == 0;
}

extern "C" int fpq_owner_key(const uint8_t* seed, size_t seed_len, uint8_t* pk_out)
{
    spend_key k;
    if (!make_spend_key(&k, seed, seed_len))
        return 0;
    std::memcpy(pk_out, k.pk.data(), PK_BYTES);
    return 1;
}

extern "C" const uint8_t* fpq_set_data(const void* pv)
{
    const auto& p = *static_cast<const prepared*>(pv);
    return reinterpret_cast<const uint8_t*>(p.set.members.data());
}

extern "C" size_t fpq_real_index(const void* pv, size_t j)
{
    const auto& p = *static_cast<const prepared*>(pv);
    return p.index[j % p.index.size()];
}

extern "C" int fpq_run_full(const void* pv, size_t n, uint64_t seed, fpq_measure* m, double (*cpu_ms)(void),
                            uint8_t* proof_out, uint8_t* witness_out, uint8_t* public_out)
{
    const auto& p = *static_cast<const prepared*>(pv);
    switch (n)
    {
    case 2: return run<2>(p, seed, m, cpu_ms, proof_out, witness_out, public_out);
    case 4: return run<4>(p, seed, m, cpu_ms, proof_out, witness_out, public_out);
    case 8: return run<8>(p, seed, m, cpu_ms, proof_out, witness_out, public_out);
    case 16: return run<16>(p, seed, m, cpu_ms, proof_out, witness_out, public_out);
    default: return 0;
    }
}

extern "C" int fpq_send(const void* pv, size_t n, uint64_t seed, size_t first_coin, const uint8_t* out_pk,
                        const uint8_t* out_seed, fpq_measure* m, double (*cpu_ms)(void), uint8_t* proof_out,
                        uint8_t* public_out)
{
    const auto& p = *static_cast<const prepared*>(pv);
    const send_args a{static_cast<int64_t>(first_coin), out_pk, out_seed};
    switch (n)
    {
    case 2: return run<2>(p, seed, m, cpu_ms, proof_out, nullptr, public_out, a);
    case 4: return run<4>(p, seed, m, cpu_ms, proof_out, nullptr, public_out, a);
    case 8: return run<8>(p, seed, m, cpu_ms, proof_out, nullptr, public_out, a);
    case 16: return run<16>(p, seed, m, cpu_ms, proof_out, nullptr, public_out, a);
    default: return 0;
    }
}

template <std::size_t N>
int verify_tx(const prepared& p, const uint8_t* proof, const uint8_t* nfs, const uint8_t* outc, uint64_t fee,
              const uint8_t* digest)
{
    if (std::memcmp(digest, &p.set.digest, sizeof(p.set.digest)) != 0)
        return 0;
    std::vector<block128> nf(N);
    std::vector<commitment> oc(N);
    std::memcpy(nf.data(), nfs, N * sizeof(block128));
    std::memcpy(oc.data(), outc, N * sizeof(commitment));
    const statement st{&p.set, nf.data(), oc.data(), fee, nullptr, 0};
    return verify<N, N, RING>(proof, st);
}

extern "C" int fpq_verify_tx(const void* pv, size_t n, const uint8_t* proof, const uint8_t* nullifiers,
                             const uint8_t* commitments, uint64_t fee, const uint8_t* set_digest)
{
    const auto& p = *static_cast<const prepared*>(pv);
    switch (n)
    {
    case 2: return verify_tx<2>(p, proof, nullifiers, commitments, fee, set_digest);
    case 4: return verify_tx<4>(p, proof, nullifiers, commitments, fee, set_digest);
    case 8: return verify_tx<8>(p, proof, nullifiers, commitments, fee, set_digest);
    case 16: return verify_tx<16>(p, proof, nullifiers, commitments, fee, set_digest);
    default: return 0;
    }
}

extern "C" int fpq_coin_matches(const uint8_t* seed, size_t seed_len, const uint8_t* pk, uint64_t amount,
                                const uint8_t* c)
{
    owner_key to;
    std::memcpy(to.data(), pk, PK_BYTES);
    coin k;
    commitment cm;
    if (!make_coin(&k, &cm, to, amount, seed, seed_len))
        return 0;
    return std::memcmp(&cm, c, sizeof(cm)) == 0;
}

extern "C" size_t fpq_public_bytes(size_t n)
{
    return n * (sizeof(block128) + sizeof(commitment) + 8) + 8 + sizeof(anon_set{}.digest);
}

extern "C" int fpq_layout(size_t n, size_t* out)
{
    switch (n)
    {
    case 2: proof_layout<2, 2, RING>(out); return 1;
    case 4: proof_layout<4, 4, RING>(out); return 1;
    case 8: proof_layout<8, 8, RING>(out); return 1;
    case 16: proof_layout<16, 16, RING>(out); return 1;
    default: return 0;
    }
}
