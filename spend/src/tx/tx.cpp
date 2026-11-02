#include "tx/tx.hpp"

#include "../api_common.inc"
#include "../vole_commit.inc"
#include "../small_vole.inc"
#include "../ring_signature/constraints.inc"
#include "tx/aes_zk.inc"
#include "tx/witness.hpp"

#include <array>
#include <cstdlib>
#include <cstring>
#include <memory>
#include <vector>

namespace sdsign::tx
{

namespace
{

constexpr std::array<uint8_t, 16> domain = {'F', 'A', 'S', 'T', 'P', 'Q', '-', 'T',
                                            'X', '-', 'V', '1', 0, 0, 0, 0};
constexpr uint8_t COMMIT_TAG = 0xC0;
constexpr uint8_t PK_TAG = 0x50;

void commit_input_block(uint8_t* block, const uint8_t* msg, std::size_t i)
{
    std::memset(block, 0, 16);
    std::memcpy(block, msg + 8 * i, 8);
    block[8] = static_cast<uint8_t>(i);
    block[9] = COMMIT_TAG;
}

void pk_input_block(uint8_t* block, std::size_t t)
{
    std::memset(block, 0, 16);
    block[15] = static_cast<uint8_t>(PK_TAG + t);
}

void coin_message(uint8_t* msg, const owner_key& pk, uint64_t amount)
{
    std::memcpy(msg, pk.data(), PK_BYTES);
    for (std::size_t i = 0; i < 8; ++i)
        msg[PK_BYTES + i] = static_cast<uint8_t>(amount >> (8 * i));
}

void derive(uint8_t* out, std::size_t out_len, uint8_t tag, const uint8_t* seed,
            std::size_t seed_len, uint32_t counter)
{
    hash_state h;
    h.init(secpar::L1);
    h.update(domain.data(), domain.size());
    h.update(seed, seed_len);
    uint8_t c[4] = {static_cast<uint8_t>(counter), static_cast<uint8_t>(counter >> 8),
                    static_cast<uint8_t>(counter >> 16), static_cast<uint8_t>(counter >> 24)};
    h.update(c, 4);
    h.update_byte(tag);
    h.finalize(out, out_len);
}

void put_bits(uint8_t* w, std::size_t bit_off, const uint8_t* src, std::size_t nbytes)
{
    std::memcpy(w + bit_off / 8, src, nbytes);
}

void set_bit(uint8_t* w, std::size_t bit, bool v)
{
    if (v)
        w[bit / 8] |= static_cast<uint8_t>(1u << (bit % 8));
    else
        w[bit / 8] &= static_cast<uint8_t>(~(1u << (bit % 8)));
}

void coin_witness(uint8_t* w, std::size_t base, const coin& c, commitment* out)
{
    uint8_t key[16];
    std::memcpy(key, &c.r, 16);
    const auto ks = native::expand(key);
    native::key_witness(w + (base + coin_layout::r) / 8, ks);
    uint8_t msg[MSG_BITS / 8];
    coin_message(msg, c.pk, c.amount);
    for (std::size_t i = 0; i < COMMIT_BLOCKS; ++i)
    {
        uint8_t in[16];
        commit_input_block(in, msg, i);
        native::encrypt(reinterpret_cast<uint8_t*>(&(*out)[i]), ks, in,
                        w + (base + coin_layout::cenc + i * ENC) / 8);
    }
    put_bits(w, base + coin_layout::msg, msg, sizeof(msg));
}

uint64_t add_witness(uint8_t* w, std::size_t carry_off, uint64_t x, uint64_t y, bool* overflow)
{
    unsigned c = 0;
    for (std::size_t i = 0; i < 64; ++i)
    {
        const unsigned xi = (x >> i) & 1;
        const unsigned yi = (y >> i) & 1;
        const unsigned cn = (xi & yi) | (c & (xi ^ yi));
        if (i < 63)
            set_bit(w, carry_off + i, cn != 0);
        else if (cn)
            *overflow = true;
        c = cn;
    }
    return x + y;
}

template <typename QS> using amount_bits = std::array<quicksilver_gf2<QS>, 64>;

template <typename QS> amount_bits<QS> load_amount(const QS* qs, std::size_t coin_base)
{
    amount_bits<QS> a;
    for (std::size_t i = 0; i < 64; ++i)
        a[i] = qs->get_witness_bit(coin_base + coin_layout::msg + AMOUNT_BIT + i);
    return a;
}

template <typename QS>
amount_bits<QS> adder(QS* qs, const amount_bits<QS>& x, const amount_bits<QS>& y,
                      std::size_t carry_off)
{
    amount_bits<QS> s;
    auto c = quicksilver_gf2<QS>(poly1::set_zero(), qs);
    for (std::size_t i = 0; i < 64; ++i)
    {
        s[i] = x[i] + y[i] + c;
        const auto next = x[i] * y[i] + c * (x[i] + y[i]);
        if (i < 63)
        {
            const auto cw = qs->get_witness_bit(carry_off + i);
            qs->add_constraint(quicksilver_gfsecpar<QS, 2>(next) +
                               quicksilver_gfsecpar<QS, 2>(cw));
            c = cw;
        }
        else
            qs->add_constraint(quicksilver_gfsecpar<QS, 2>(next));
    }
    return s;
}

template <typename QS>
void coin_constraints(QS* qs, std::size_t base, zk::round_key<QS>& key,
                      const std::array<zk::bits128<QS>, COMMIT_BLOCKS>& out)
{
    zk::key_constraints(qs, base + coin_layout::r, key);
    for (std::size_t i = 0; i < COMMIT_BLOCKS; ++i)
    {
        uint8_t tag[16];
        uint8_t zero[8] = {};
        commit_input_block(tag, zero, i);
        auto in = zk::const_bits128(qs, tag);
        for (std::size_t b = 0; b < 64; ++b)
            in[b] = qs->get_witness_bit(base + coin_layout::msg + 64 * i + b);
        zk::enc_constraints(qs, base + coin_layout::cenc + i * ENC, key, in, out[i]);
    }
}

template <typename P> using field_t = poly_secpar<P::secpar_v>;

template <typename P>
std::array<field_t<P>, COMMIT_BLOCKS> load_alpha(const uint8_t* challenge)
{
    constexpr std::size_t base = (3 * secpar_to_bits(P::secpar_v) + 64) / 8;
    std::array<field_t<P>, COMMIT_BLOCKS> alpha{};
    for (std::size_t row = 0; row < COMMIT_BLOCKS; ++row)
        alpha[row] = field_t<P>::load_dup(challenge + base + row * P::secpar_bytes);
    return alpha;
}

template <typename P>
std::vector<field_t<P>> fold_set(const anon_set& set, const std::array<field_t<P>, COMMIT_BLOCKS>& alpha)
{
    std::vector<field_t<P>> out(P::ring_size);
    for (std::size_t m = 0; m < P::ring_size; ++m)
    {
        polysecpar_dot_accumulator<P::secpar_v> acc;
        for (std::size_t row = 0; row < COMMIT_BLOCKS; ++row)
            acc.add(alpha[row], field_t<P>::load_dup(&set.members[m][row]));
        out[m] = acc.reduced();
    }
    return out;
}

template <typename P, typename QS, typename LeftCache, typename RightCache>
quicksilver_gfsecpar<QS, 4> contract(QS* qs, const std::vector<field_t<P>>& folded,
                                     const LeftCache& left, const RightCache& right)
{
    using selector = ring::selector_encoding<P::ring_size>;
    constexpr auto S = P::secpar_v;
    auto selected = quicksilver_gfsecpar<QS, 4>(poly1::set_zero(), qs);
    for (std::size_t lr = 0; lr < selector::left_size; ++lr)
    {
        const std::size_t row_start = lr * selector::right_size;
        if (row_start >= P::ring_size)
            break;
        const std::size_t limit = std::min(selector::right_size, P::ring_size - row_start);
        auto rc = quicksilver_gfsecpar<QS, 2>(poly1::set_zero(), qs);
        polysecpar_dot_accumulator<S> acc0;
        polysecpar_dot_accumulator<S> acc1;
        field_t<P> value = field_t<P>::set_zero();
        for (std::size_t rr = 0; rr < limit; ++rr)
        {
            const auto& coef = folded[row_start + rr];
            const auto& ind = right.indicators[rr];
            if constexpr (QS::is_verifier)
                acc0.add(coef, ind.mac);
            else
            {
                acc0.add(coef, ind.mac.coeffs[0]);
                acc1.add(coef, ind.mac.coeffs[1]);
                add_mul_poly1_mask_polysecpar<S>(
                    value, ::sdsign::detail::poly1_to_bit_mask(ind.value()), coef);
            }
        }
        if constexpr (QS::is_verifier)
        {
            rc.mac = acc0.reduced();
            rc.delta_powers = &qs->delta_powers;
        }
        else
        {
            rc.mac.coeffs[0] = acc0.reduced();
            rc.mac.coeffs[1] = acc1.reduced();
            rc.value() = value;
        }
        selected += left.indicators[lr] * rc;
    }
    return selected;
}

template <typename P, typename QS>
quicksilver_gfsecpar<QS> cstar_fold(QS* qs, std::size_t off,
                                    const std::array<field_t<P>, COMMIT_BLOCKS>& alpha)
{
    auto acc = quicksilver_gfsecpar<QS>(poly1::set_zero(), qs);
    for (std::size_t row = 0; row < COMMIT_BLOCKS; ++row)
    {
        for (std::size_t k = 0; k < 128; ++k)
        {
            uint8_t e[16] = {};
            e[k / 8] = static_cast<uint8_t>(1u << (k % 8));
            const auto ek = field_t<P>::load_dup(e);
            const auto ak = mul_polysecpar_reduce<P::secpar_v>(alpha[row], ek);
            acc += ak * quicksilver_gfsecpar<QS>(qs->get_witness_bit(off + 128 * row + k));
        }
    }
    return acc;
}

template <typename P, bool Verifier>
void constraints(quicksilver_state<P::secpar_v, Verifier, 4, P::quicksilver_term_v>* qs,
                 const statement& st, const std::vector<field_t<P>>& folded)
{
    using QS = quicksilver_state<P::secpar_v, Verifier, 4, P::quicksilver_term_v>;
    using SP = typename P::selector;
    const auto alpha = load_alpha<P>(qs->challenge_bytes);

    for (std::size_t j = 0; j < P::n_in; ++j)
    {
        const std::size_t base = P::input_offset(j);
        zk::round_key<QS> rkey;
        std::array<zk::bits128<QS>, COMMIT_BLOCKS> cstar;
        for (std::size_t i = 0; i < COMMIT_BLOCKS; ++i)
            cstar[i] = zk::witness_bits128(qs, base + input_layout::cstar + 128 * i);
        coin_constraints(qs, base + input_layout::coin, rkey, cstar);

        zk::round_key<QS> skey;
        zk::key_constraints(qs, base + input_layout::sk, skey);
        for (std::size_t t = 0; t < 2; ++t)
        {
            uint8_t x[16];
            pk_input_block(x, t);
            const auto in = zk::const_bits128(qs, x);
            const auto out =
                zk::witness_bits128(qs, base + input_layout::coin + coin_layout::msg + 128 * t);
            zk::enc_constraints(qs, base + input_layout::pkenc + t * ENC, skey, in, out);
        }
        {
            const auto in = zk::witness_bits128(qs, base + input_layout::coin + coin_layout::r);
            const auto out =
                zk::const_bits128(qs, reinterpret_cast<const uint8_t*>(&st.nullifiers[j]));
            zk::enc_constraints(qs, base + input_layout::nfenc, skey, in, out);
        }

        ring::detail::qs_bit_array<QS, SP::eta_left> lb{};
        ring::detail::qs_bit_array<QS, SP::eta_right> rb{};
        for (std::size_t b = 0; b < SP::eta_left; ++b)
            lb[b] = qs->get_witness_bit(base + input_layout::sel + b);
        for (std::size_t b = 0; b < SP::eta_right; ++b)
            rb[b] = qs->get_witness_bit(base + input_layout::sel + SP::eta_left + b);
        auto lc = ring::detail::make_ball_cache(qs, lb);
        auto rc = ring::detail::make_ball_cache(qs, rb);
        ring::detail::add_selector_constraints<P>(qs, lc, rc);
        auto sel = contract<P>(qs, folded, lc, rc);
        sel += quicksilver_gfsecpar<QS, 4>(cstar_fold<P>(qs, base + input_layout::cstar, alpha));
        qs->add_constraint(sel);
    }

    for (std::size_t k = 0; k < P::n_out; ++k)
    {
        const std::size_t base = P::output_offset(k);
        zk::round_key<QS> rkey;
        std::array<zk::bits128<QS>, COMMIT_BLOCKS> out;
        for (std::size_t i = 0; i < COMMIT_BLOCKS; ++i)
            out[i] = zk::const_bits128(qs, reinterpret_cast<const uint8_t*>(&st.outputs[k][i]));
        coin_constraints(qs, base, rkey, out);
    }

    std::size_t a = 0;
    auto sin = load_amount(qs, P::input_offset(0) + input_layout::coin);
    for (std::size_t j = 1; j < P::n_in; ++j)
        sin = adder(qs, sin, load_amount(qs, P::input_offset(j) + input_layout::coin),
                    P::carry_offset(a++));
    auto sout = load_amount(qs, P::output_offset(0));
    for (std::size_t k = 1; k < P::n_out; ++k)
        sout = adder(qs, sout, load_amount(qs, P::output_offset(k)), P::carry_offset(a++));
    amount_bits<QS> fee;
    for (std::size_t i = 0; i < 64; ++i)
        fee[i] = quicksilver_gf2<QS>(((st.fee >> i) & 1) ? poly1::set_one() : poly1::set_zero(),
                                     qs);
    sout = adder(qs, sout, fee, P::carry_offset(a++));
    for (std::size_t i = 0; i < 64; ++i)
        qs->add_constraint(quicksilver_gfsecpar<QS>(sin[i] + sout[i]));
}

template <typename P> block_2secpar<P::secpar_v> statement_digest(const statement& st)
{
    hash_state h;
    h.init(P::secpar_v);
    h.update(domain.data(), domain.size());
    const uint64_t shape[3] = {P::n_in, P::n_out, P::ring_size};
    h.update(shape, sizeof(shape));
    h.update(&st.set->digest, sizeof(st.set->digest));
    h.update(st.nullifiers, P::n_in * sizeof(block128));
    h.update(st.outputs, P::n_out * sizeof(commitment));
    uint8_t fee[8];
    for (std::size_t i = 0; i < 8; ++i)
        fee[i] = static_cast<uint8_t>(st.fee >> (8 * i));
    h.update(fee, 8);
    if (st.msg_len)
        h.update(st.msg, st.msg_len);
    h.update_byte(0x54);
    block_2secpar<P::secpar_v> mu;
    h.finalize(&mu, sizeof(mu));
    return mu;
}

template <typename P>
bool build_witness(uint8_t* w, const statement& st, const input* inputs, const coin* outputs,
                   const testing::tamper* t)
{
    using SP = typename P::selector;
    const bool lax = t && t->skip_checks;
    std::memset(w, 0, P::witness_bytes);
    for (std::size_t j = 0; j < P::n_in; ++j)
    {
        const std::size_t base = P::input_offset(j);
        const auto& in = inputs[j];
        if (in.index >= P::ring_size || in.index >= st.set->members.size())
            return false;
        commitment c;
        coin_witness(w, base + input_layout::coin, in.c, &c);
        if (std::memcmp(&c, &st.set->members[in.index], sizeof(c)) != 0 && !lax)
            return false;
        put_bits(w, base + input_layout::cstar, reinterpret_cast<const uint8_t*>(&c), sizeof(c));

        uint8_t sk[16];
        std::memcpy(sk, &in.key.sk, 16);
        if (!native::key_ok(sk))
            return false;
        const auto ks = native::expand(sk);
        native::key_witness(w + (base + input_layout::sk) / 8, ks);
        for (std::size_t b = 0; b < 2; ++b)
        {
            uint8_t x[16];
            uint8_t y[16];
            pk_input_block(x, b);
            native::encrypt(y, ks, x, w + (base + input_layout::pkenc + b * ENC) / 8);
            if (std::memcmp(y, in.c.pk.data() + 16 * b, 16) != 0 && !lax)
                return false;
        }
        uint8_t nf[16];
        native::encrypt(nf, ks, reinterpret_cast<const uint8_t*>(&in.c.r),
                        w + (base + input_layout::nfenc) / 8);
        if (std::memcmp(nf, &st.nullifiers[j], 16) != 0 && !lax)
            return false;

        const auto rep = ring::selector_encoding<P::ring_size>::encode(in.index);
        for (std::size_t b = 0; b < SP::eta_left; ++b)
            set_bit(w, base + input_layout::sel + b, rep.left[b] != 0);
        for (std::size_t b = 0; b < SP::eta_right; ++b)
            set_bit(w, base + input_layout::sel + SP::eta_left + b, rep.right[b] != 0);
    }
    for (std::size_t k = 0; k < P::n_out; ++k)
    {
        commitment c;
        coin_witness(w, P::output_offset(k), outputs[k], &c);
        if (std::memcmp(&c, &st.outputs[k], sizeof(c)) != 0 && !lax)
            return false;
    }
    bool overflow = false;
    std::size_t a = 0;
    uint64_t sin = inputs[0].c.amount;
    for (std::size_t j = 1; j < P::n_in; ++j)
        sin = add_witness(w, P::carry_offset(a++), sin, inputs[j].c.amount, &overflow);
    uint64_t sout = outputs[0].amount;
    for (std::size_t k = 1; k < P::n_out; ++k)
        sout = add_witness(w, P::carry_offset(a++), sout, outputs[k].amount, &overflow);
    sout = add_witness(w, P::carry_offset(a++), sout, st.fee, &overflow);
    if (t && t->flip_bit >= 0)
        w[t->flip_bit / 8] ^= static_cast<uint8_t>(1u << (t->flip_bit % 8));
    return lax || (!overflow && sin == sout);
}

} // namespace

bool make_spend_key(spend_key* out, const uint8_t* seed, std::size_t seed_len)
{
    for (uint32_t ctr = 0; ctr < 64; ++ctr)
    {
        uint8_t sk[16];
        derive(sk, 16, 1, seed, seed_len, ctr);
        if (!native::key_ok(sk))
            continue;
        std::memcpy(&out->sk, sk, 16);
        const auto ks = native::expand(sk);
        for (std::size_t t = 0; t < 2; ++t)
        {
            uint8_t x[16];
            pk_input_block(x, t);
            native::encrypt(out->pk.data() + 16 * t, ks, x);
        }
        return true;
    }
    return false;
}

void commit(commitment* out, const coin& c)
{
    uint8_t key[16];
    std::memcpy(key, &c.r, 16);
    const auto ks = native::expand(key);
    uint8_t msg[MSG_BITS / 8];
    coin_message(msg, c.pk, c.amount);
    for (std::size_t i = 0; i < COMMIT_BLOCKS; ++i)
    {
        uint8_t in[16];
        commit_input_block(in, msg, i);
        native::encrypt(reinterpret_cast<uint8_t*>(&(*out)[i]), ks, in);
    }
}

bool make_coin(coin* out, commitment* c, const owner_key& pk, uint64_t amount,
               const uint8_t* seed, std::size_t seed_len)
{
    for (uint32_t ctr = 0; ctr < 64; ++ctr)
    {
        uint8_t r[16];
        derive(r, 16, 2, seed, seed_len, ctr);
        if (!native::key_ok(r))
            continue;
        std::memcpy(&out->r, r, 16);
        out->pk = pk;
        out->amount = amount;
        commit(c, *out);
        return true;
    }
    return false;
}

block128 nullifier(const spend_key& key, const coin& c)
{
    uint8_t sk[16];
    std::memcpy(sk, &key.sk, 16);
    const auto ks = native::expand(sk);
    block128 out;
    native::encrypt(reinterpret_cast<uint8_t*>(&out), ks, reinterpret_cast<const uint8_t*>(&c.r));
    return out;
}

void set_digest(anon_set* s)
{
    hash_state h;
    h.init(secpar::L1);
    h.update(domain.data(), domain.size());
    const uint64_t n = s->members.size();
    h.update(&n, sizeof(n));
    if (n)
        h.update(s->members.data(), n * sizeof(commitment));
    h.update_byte(0x53);
    h.finalize(&s->digest, sizeof(s->digest));
}

namespace
{

template <std::size_t NIN, std::size_t NOUT, std::size_t RING>
bool prove_impl(uint8_t* proof, const statement& st, const input* inputs, const coin* outputs,
                const uint8_t* random_seed, std::size_t random_seed_len,
                const testing::tamper* t)
{
    using P = params<NIN, NOUT, RING>;
    using CP = typename P::CONSTS;
    using OC = typename P::OWF_CONSTS;
    constexpr auto S = P::secpar_v;
    if (!proof || !st.set || st.set->members.size() != RING)
        return false;

    auto witness = std::make_unique<std::array<uint8_t, P::witness_bytes>>();
    if (!build_witness<P>(witness->data(), st, inputs, outputs, t))
        return false;
    if (t && t->witness_out)
        std::memcpy(t->witness_out, witness->data(), P::witness_bytes);

    const auto mu = statement_digest<P>(st);
    hash_state hasher;
    block_secpar<S> seed;
    block128 iv;
    block128 iv_pre;
    std::array<uint8_t, sizeof(seed) + sizeof(iv_pre)> seed_iv_pre;
    hasher.init(S);
    hasher.update(witness->data(), P::witness_bytes);
    hasher.update(&mu, sizeof(mu));
    if (random_seed)
        hasher.update(random_seed, random_seed_len);
    hasher.update_byte(3);
    hasher.finalize(seed_iv_pre.data(), seed_iv_pre.size());
    std::memcpy(&seed, seed_iv_pre.data(), sizeof(seed));
    std::memcpy(&iv_pre, seed_iv_pre.data() + sizeof(seed), sizeof(iv_pre));
    hasher.init(S);
    hasher.update(&iv_pre, sizeof(iv_pre));
    hasher.update_byte(4);
    hasher.finalize(&iv, sizeof(iv));

    auto* forest = reinterpret_cast<block_secpar<S>*>(
        fpq_aligned_alloc(alignof(block_secpar<S>), P::bavc_t::COMMIT_NODES * sizeof(block_secpar<S>)));
    auto* hashed_leaves = reinterpret_cast<unsigned char*>(fpq_aligned_alloc(
        alignof(block_2secpar<S>), P::bavc_t::COMMIT_LEAVES * P::leaf_hash_t::hash_len));
    auto* u = reinterpret_cast<vole_block*>(
        fpq_aligned_alloc(alignof(vole_block), CP::VOLE_COL_BLOCKS * sizeof(vole_block)));
    auto* v = reinterpret_cast<vole_block*>(fpq_aligned_alloc(
        alignof(vole_block), P::secpar_bits * CP::VOLE_COL_BLOCKS * sizeof(vole_block)));
    if (!forest || !hashed_leaves || !u || !v)
    {
        fpq_aligned_free(forest); fpq_aligned_free(hashed_leaves); fpq_aligned_free(u); fpq_aligned_free(v);
        return false;
    }
    uint8_t vole_commit_check[CP::VOLE_COMMIT_CHECK_SIZE];
    sdsign_vole_commit<P>(seed, iv, forest, hashed_leaves, u, v, proof, vole_commit_check);

    std::array<uint8_t, CP::VOLE_CHECK::CHALLENGE_BYTES> chal1;
    hasher.init(S);
    hasher.update(&mu, sizeof(mu));
    hasher.update(vole_commit_check, sizeof(vole_commit_check));
    hasher.update(proof, CP::VOLE_COMMIT_SIZE);
    hasher.update(&iv, sizeof(iv));
    hasher.update_byte(9);
    hasher.finalize(chal1.data(), chal1.size());

    uint8_t* vole_check_proof = proof + CP::VOLE_COMMIT_SIZE;
    uint8_t* correction = vole_check_proof + CP::VOLE_CHECK::PROOF_BYTES;
    std::array<uint8_t, CP::QS::CHALLENGE_BYTES> chal2;
    hasher.init(S);
    hasher.update(chal1.data(), chal1.size());
    sdsign_vole_check_sender<P>(u, v, chal1.data(), vole_check_proof, hasher);
    const uint8_t* u_bytes = reinterpret_cast<const uint8_t*>(u);
    std::memcpy(correction, u_bytes, OC::WITNESS_BYTES);
    for (std::size_t i = 0; i < OC::WITNESS_BYTES; ++i)
        correction[i] ^= (*witness)[i];
    hasher.update(correction, OC::WITNESS_BYTES);
    hasher.update_byte(10);
    hasher.finalize(chal2.data(), chal2.size());

    constexpr std::size_t extended_bytes = P::witness_bytes + (OC::QS_DEGREE - 1) * P::secpar_bytes;
    constexpr std::size_t extended_alloc =
        ((extended_bytes + sizeof(vole_block) - 1) / sizeof(vole_block)) * sizeof(vole_block) +
        sizeof(vole_block);
    auto* u_extended = reinterpret_cast<uint8_t*>(fpq_aligned_alloc(alignof(vole_block), extended_alloc));
    auto* macs = reinterpret_cast<block_secpar<S>*>(fpq_aligned_alloc(
        alignof(block_secpar<S>), CP::QUICKSILVER_ROWS_PADDED * sizeof(block_secpar<S>)));
    auto* macs_extended = reinterpret_cast<block_secpar<S>*>(fpq_aligned_alloc(
        alignof(block_secpar<S>), CP::QUICKSILVER_ROWS_PADDED_EXTENDED * sizeof(block_secpar<S>)));
    if (!u_extended || !macs || !macs_extended)
    {
        fpq_aligned_free(forest); fpq_aligned_free(hashed_leaves); fpq_aligned_free(u); fpq_aligned_free(v);
        fpq_aligned_free(u_extended); fpq_aligned_free(macs); fpq_aligned_free(macs_extended);
        return false;
    }
    std::memset(u_extended, 0, extended_alloc);
    std::memcpy(u_extended, witness->data(), P::witness_bytes);
    std::memcpy(u_extended + P::witness_bytes, u_bytes + OC::WITNESS_BYTES,
                (OC::QS_DEGREE - 1) * P::secpar_bytes);
    fpq_aligned_free(u);
    sdsign_detail::compute_macs_extended<P>(macs_extended, v, macs);
    fpq_aligned_free(macs);
    fpq_aligned_free(v);

    uint8_t* qs_proof = correction + OC::WITNESS_BYTES;
    std::array<uint8_t, CP::QS::CHECK_BYTES> qs_check;
    {
        quicksilver_state<S, false, OC::QS_DEGREE, P::quicksilver_term_v> qs(
            u_extended, macs_extended, OC::OWF_NUM_CONSTRAINTS, chal2.data());
        const auto folded = fold_set<P>(*st.set, load_alpha<P>(chal2.data()));
        constraints<P, false>(&qs, st, folded);
        qs.prove(P::witness_bytes * 8, qs_proof, qs_check.data());
    }
    fpq_aligned_free(macs_extended);
    fpq_aligned_free(u_extended);

    uint8_t* opening = qs_proof + CP::QS::PROOF_BYTES;
    uint8_t* delta = opening + P::bavc_t::OPEN_SIZE;
    uint8_t* iv_pre_dst = delta + sizeof(block_secpar<S>);
    std::memcpy(iv_pre_dst, &iv_pre, sizeof(iv_pre));
    uint8_t* counter_dst = iv_pre_dst + sizeof(iv_pre);
    if constexpr (!P::use_grinding)
    {
        hasher.init(S);
        hasher.update(chal2.data(), chal2.size());
        hasher.update(qs_check.data(), qs_check.size());
        hasher.update(qs_proof, CP::QS::PROOF_BYTES);
        hasher.update_byte(11);
        hasher.finalize(delta, sizeof(block_secpar<S>));
        std::array<uint8_t, P::delta_bits_v> delta_bytes;
        expand_bits_to_bytes(delta_bytes.data(), P::delta_bits_v, delta);
        P::bavc_t::open(forest, hashed_leaves, delta_bytes.data(), opening);
    }
    else
    {
        hash_state_x8 grinding_hasher;
        grinding_hasher.init(S);
        grinding_hasher.update_1(chal2.data(), chal2.size());
        grinding_hasher.update_1(qs_check.data(), qs_check.size());
        grinding_hasher.update_1(qs_proof, CP::QS::PROOF_BYTES);
        uint32_t counter = 0;
        if (!grind_and_open<typename P::bavc_t>(forest, hashed_leaves, delta, opening,
                                                &grinding_hasher, &counter))
        {
            fpq_aligned_free(forest); fpq_aligned_free(hashed_leaves);
            return false;
        }
        for (std::size_t i = 0; i < 4; ++i)
            counter_dst[i] = static_cast<uint8_t>(counter >> (8 * i));
    }
    fpq_aligned_free(forest);
    fpq_aligned_free(hashed_leaves);
    return true;
}

} // namespace

template <std::size_t NIN, std::size_t NOUT, std::size_t RING>
bool prove(uint8_t* proof, const statement& st, const input* inputs, const coin* outputs,
           const uint8_t* random_seed, std::size_t random_seed_len)
{
    return prove_impl<NIN, NOUT, RING>(proof, st, inputs, outputs, random_seed, random_seed_len,
                                       nullptr);
}

template <std::size_t NIN, std::size_t NOUT, std::size_t RING>
bool prove_capture(uint8_t* proof, const statement& st, const input* inputs, const coin* outputs,
                   const uint8_t* random_seed, std::size_t random_seed_len, uint8_t* witness_out)
{
    testing::tamper t;
    t.witness_out = witness_out;
    return prove_impl<NIN, NOUT, RING>(proof, st, inputs, outputs, random_seed, random_seed_len, &t);
}

template <std::size_t NIN, std::size_t NOUT, std::size_t RING> void proof_layout(std::size_t* out)
{
    using P = params<NIN, NOUT, RING>;
    using CP = typename P::CONSTS;
    out[0] = CP::VOLE_COMMIT_SIZE;
    out[1] = CP::VOLE_CHECK::PROOF_BYTES;
    out[2] = P::OWF_CONSTS::WITNESS_BYTES;
    out[3] = CP::QS::PROOF_BYTES;
    out[4] = P::proof_bytes - out[0] - out[1] - out[2] - out[3];
    out[5] = P::witness_bytes;
}

#if defined(FASTPQ_TX_TESTING)
namespace testing
{
template <std::size_t NIN, std::size_t NOUT, std::size_t RING>
bool prove_tampered(uint8_t* proof, const statement& st, const input* inputs, const coin* outputs,
                    const tamper& t)
{
    const uint8_t seed[1] = {7};
    return prove_impl<NIN, NOUT, RING>(proof, st, inputs, outputs, seed, 1, &t);
}
template bool prove_tampered<1, 2, 64>(uint8_t*, const statement&, const input*, const coin*,
                                       const tamper&);
template bool prove_tampered<2, 2, 64>(uint8_t*, const statement&, const input*, const coin*,
                                       const tamper&);
} // namespace testing
#endif

template <std::size_t NIN, std::size_t NOUT, std::size_t RING>
bool verify(const uint8_t* proof, const statement& st)
{
    using P = params<NIN, NOUT, RING>;
    using CP = typename P::CONSTS;
    using OC = typename P::OWF_CONSTS;
    constexpr auto S = P::secpar_v;
    if (!proof || !st.set || st.set->members.size() != RING)
        return false;

    const auto mu = statement_digest<P>(st);
    hash_state hasher;
    const uint8_t* vole_check_proof = proof + CP::VOLE_COMMIT_SIZE;
    const uint8_t* correction = vole_check_proof + CP::VOLE_CHECK::PROOF_BYTES;
    const uint8_t* qs_proof = correction + OC::WITNESS_BYTES;
    const uint8_t* opening = qs_proof + CP::QS::PROOF_BYTES;
    const uint8_t* delta = opening + P::bavc_t::OPEN_SIZE;
    const uint8_t* iv_pre_ptr = delta + sizeof(block_secpar<S>);
    const uint8_t* counter = iv_pre_ptr + sizeof(block128);

    for (std::size_t i = P::delta_bits_v; i < P::secpar_bits; ++i)
        if (((delta[i / 8] >> (i % 8)) & 1u) != 0)
            return false;

    block128 iv;
    hasher.init(S);
    hasher.update(iv_pre_ptr, sizeof(iv));
    hasher.update_byte(4);
    hasher.finalize(&iv, sizeof(iv));
    std::array<uint8_t, P::delta_bits_v> delta_bytes;
    expand_bits_to_bytes(delta_bytes.data(), P::delta_bits_v, delta);

    auto* q = reinterpret_cast<vole_block*>(fpq_aligned_alloc(
        alignof(vole_block), P::secpar_bits * CP::VOLE_COL_BLOCKS * sizeof(vole_block)));
    if (!q)
        return false;
    uint8_t vole_commit_check[CP::VOLE_COMMIT_CHECK_SIZE];
    if (!vole_reconstruct<P>(iv, q, delta_bytes.data(), proof, opening, vole_commit_check))
    {
        fpq_aligned_free(q);
        return false;
    }

    std::array<uint8_t, CP::VOLE_CHECK::CHALLENGE_BYTES> chal1;
    hasher.init(S);
    hasher.update(&mu, sizeof(mu));
    hasher.update(vole_commit_check, sizeof(vole_commit_check));
    hasher.update(proof, CP::VOLE_COMMIT_SIZE);
    hasher.update(&iv, sizeof(iv));
    hasher.update_byte(9);
    hasher.finalize(chal1.data(), chal1.size());

    std::array<uint8_t, CP::QS::CHALLENGE_BYTES> chal2;
    hasher.init(S);
    hasher.update(chal1.data(), chal1.size());
    hasher.update(vole_check_proof, CP::VOLE_CHECK::PROOF_BYTES);
    vole_check_receiver<P>(q, delta_bytes.data(), chal1.data(), vole_check_proof, hasher);
    hasher.update(correction, OC::WITNESS_BYTES);
    hasher.update_byte(10);
    hasher.finalize(chal2.data(), chal2.size());

    auto* macs = reinterpret_cast<block_secpar<S>*>(fpq_aligned_alloc(
        alignof(block_secpar<S>), CP::QUICKSILVER_ROWS_PADDED * sizeof(block_secpar<S>)));
    auto* macs_extended = reinterpret_cast<block_secpar<S>*>(fpq_aligned_alloc(
        alignof(block_secpar<S>), CP::QUICKSILVER_ROWS_PADDED_EXTENDED * sizeof(block_secpar<S>)));
    if (!macs || !macs_extended)
    {
        fpq_aligned_free(q); fpq_aligned_free(macs); fpq_aligned_free(macs_extended);
        return false;
    }
    std::vector<vole_block> correction_blocks(CP::WITNESS_BLOCKS);
    std::memset(correction_blocks.data(), 0, CP::WITNESS_BLOCKS * sizeof(vole_block));
    std::memcpy(correction_blocks.data(), correction, OC::WITNESS_BYTES);
    vole_receiver_apply_correction<P>(CP::WITNESS_BLOCKS, P::delta_bits_v,
                                      correction_blocks.data(), q, delta_bytes.data());
    block_secpar<S> delta_block;
    std::memcpy(&delta_block, delta, sizeof(delta_block));
    sdsign_detail::compute_macs_extended_verifier<P>(macs_extended, q, macs, delta_block);
    fpq_aligned_free(q);
    fpq_aligned_free(macs);

    std::array<uint8_t, CP::QS::CHECK_BYTES> qs_check;
    {
        quicksilver_state<S, true, OC::QS_DEGREE, P::quicksilver_term_v> qs(
            macs_extended, OC::OWF_NUM_CONSTRAINTS, delta_block, chal2.data());
        const auto folded = fold_set<P>(*st.set, load_alpha<P>(chal2.data()));
        constraints<P, true>(&qs, st, folded);
        qs.verify(P::witness_bytes * 8, qs_proof, qs_check.data());
    }
    fpq_aligned_free(macs_extended);

    block_secpar<S> delta_check;
    hasher.init(S);
    hasher.update(chal2.data(), chal2.size());
    hasher.update(qs_check.data(), qs_check.size());
    hasher.update(qs_proof, CP::QS::PROOF_BYTES);
    if constexpr (P::use_grinding)
        hasher.update(counter, P::grinding_counter_size);
    hasher.update_byte(11);
    hasher.finalize(&delta_check, sizeof(delta_check));
    return std::memcmp(delta, &delta_check, sizeof(delta_check)) == 0;
}

#define FASTPQ_TX_INSTANTIATE(NIN, NOUT, RING)                                                     \
    template bool prove<NIN, NOUT, RING>(uint8_t*, const statement&, const input*, const coin*,   \
                                         const uint8_t*, std::size_t);                            \
    template bool verify<NIN, NOUT, RING>(const uint8_t*, const statement&);                    \
    template bool prove_capture<NIN, NOUT, RING>(uint8_t*, const statement&, const input*,        \
                                                 const coin*, const uint8_t*, std::size_t,         \
                                                 uint8_t*);                                        \
    template void proof_layout<NIN, NOUT, RING>(std::size_t*)

FASTPQ_TX_INSTANTIATE(1, 2, 64);
FASTPQ_TX_INSTANTIATE(2, 2, 64);
FASTPQ_TX_INSTANTIATE(1, 2, 1048576);
FASTPQ_TX_INSTANTIATE(2, 2, 1048576);
FASTPQ_TX_INSTANTIATE(8, 16, 1048576);
FASTPQ_TX_INSTANTIATE(4, 4, 1048576);
FASTPQ_TX_INSTANTIATE(8, 8, 1048576);
FASTPQ_TX_INSTANTIATE(16, 16, 1048576);

#undef FASTPQ_TX_INSTANTIATE

} // namespace sdsign::tx
