#ifndef SDSIGN_TX_TX_HPP
#define SDSIGN_TX_TX_HPP

#include "params.hpp"

#include <array>
#include <cstddef>
#include <cstdint>
#include <vector>

namespace sdsign::tx
{

using commitment = std::array<block128, COMMIT_BLOCKS>;
using owner_key = std::array<uint8_t, PK_BYTES>;

struct spend_key
{
    block128 sk;
    owner_key pk;
};

struct coin
{
    block128 r;
    owner_key pk;
    uint64_t amount;
};

struct anon_set
{
    std::vector<commitment> members;
    block_2secpar<secpar::L1> digest;
};

struct input
{
    coin c;
    spend_key key;
    std::size_t index;
};

struct statement
{
    const anon_set* set;
    const block128* nullifiers;
    const commitment* outputs;
    uint64_t fee;
    const uint8_t* msg;
    std::size_t msg_len;
};

bool make_spend_key(spend_key* out, const uint8_t* seed, std::size_t seed_len);
bool make_coin(coin* out, commitment* c, const owner_key& pk, uint64_t amount,
               const uint8_t* seed, std::size_t seed_len);
void commit(commitment* out, const coin& c);
block128 nullifier(const spend_key& key, const coin& c);
void set_digest(anon_set* s);

template <std::size_t NIN, std::size_t NOUT, std::size_t RING>
bool prove(uint8_t* proof, const statement& st, const input* inputs, const coin* outputs,
           const uint8_t* random_seed, std::size_t random_seed_len);

template <std::size_t NIN, std::size_t NOUT, std::size_t RING>
bool verify(const uint8_t* proof, const statement& st);

namespace testing
{
struct tamper
{
    bool skip_checks = false;
    long flip_bit = -1;
    uint8_t* witness_out = nullptr;
};
template <std::size_t NIN, std::size_t NOUT, std::size_t RING>
bool prove_tampered(uint8_t* proof, const statement& st, const input* inputs, const coin* outputs,
                    const tamper& t);
} // namespace testing

template <std::size_t NIN, std::size_t NOUT, std::size_t RING>
bool prove_capture(uint8_t* proof, const statement& st, const input* inputs, const coin* outputs,
                   const uint8_t* random_seed, std::size_t random_seed_len, uint8_t* witness_out);

template <std::size_t NIN, std::size_t NOUT, std::size_t RING>
void proof_layout(std::size_t* out);

template <std::size_t NIN, std::size_t NOUT, std::size_t RING>
inline constexpr std::size_t proof_bytes = params<NIN, NOUT, RING>::proof_bytes;

} // namespace sdsign::tx

#endif
