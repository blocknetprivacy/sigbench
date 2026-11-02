#ifndef SDSIGN_TX_PARAMS_HPP
#define SDSIGN_TX_PARAMS_HPP

#include "../ring_signature/parameters.hpp"
#include "../ring_signature/selector.hpp"
#include "aes_zk.inc"

#include <cstddef>

namespace sdsign::tx
{

inline constexpr std::size_t COMMIT_BLOCKS = 5;
inline constexpr std::size_t PK_BYTES = 32;
inline constexpr std::size_t MSG_BITS = 8 * PK_BYTES + 64;
inline constexpr std::size_t AMOUNT_BIT = 8 * PK_BYTES;
inline constexpr std::size_t CARRY_BITS = 64;

inline constexpr std::size_t KEY = zk::KEY_WITNESS_BITS;
inline constexpr std::size_t ENC = zk::ENC_WITNESS_BITS;

struct coin_layout
{
    static constexpr std::size_t r = 0;
    static constexpr std::size_t cenc = r + KEY;
    static constexpr std::size_t msg = cenc + COMMIT_BLOCKS * ENC;
    static constexpr std::size_t end = msg + MSG_BITS;
};

struct input_layout
{
    static constexpr std::size_t coin = 0;
    static constexpr std::size_t cstar = coin_layout::end;
    static constexpr std::size_t sk = cstar + 128 * COMMIT_BLOCKS;
    static constexpr std::size_t pkenc = sk + KEY;
    static constexpr std::size_t nfenc = pkenc + 2 * ENC;
    static constexpr std::size_t sel = nfenc + ENC;
};

template <std::size_t NIN, std::size_t NOUT, std::size_t RING>
struct params : ring::reduction_compensated_l1_short_set1_base
{
    static_assert(NIN >= 1 && NOUT >= 1);
    using base_parameter = ring::reduction_compensated_l1_short_set1_base;
    using selector = ring::selector_parameters<RING>;
    static constexpr std::size_t n_in = NIN;
    static constexpr std::size_t n_out = NOUT;
    static constexpr std::size_t ring_size = RING;
    static constexpr std::size_t selector_bits_raw = selector::selector_bits;
    static constexpr std::size_t selector_bits_padded = ((selector_bits_raw + 7) / 8) * 8;

    static constexpr std::size_t input_bits = input_layout::sel + selector_bits_padded;
    static constexpr std::size_t output_bits = coin_layout::end;
    static constexpr std::size_t adders = (NIN - 1) + NOUT;

    static constexpr std::size_t input_offset(std::size_t j) { return j * input_bits; }
    static constexpr std::size_t output_offset(std::size_t k)
    {
        return NIN * input_bits + k * output_bits;
    }
    static constexpr std::size_t carry_offset(std::size_t a)
    {
        return NIN * input_bits + NOUT * output_bits + a * CARRY_BITS;
    }

    static constexpr std::size_t witness_raw_bits = carry_offset(adders);
    static constexpr std::size_t witness_bits = ((witness_raw_bits + 7) / 8) * 8;
    static constexpr std::size_t witness_bytes = witness_bits / 8;
    static constexpr std::size_t witness_extended_bits = witness_bits;
    static constexpr std::size_t witness_extended_bytes = witness_bytes;

    static constexpr std::size_t selector_constraints =
        ring::choose3(selector::eta_left) + ring::choose3(selector::eta_right) + 1;
    static constexpr std::size_t input_constraints =
        2 * zk::KEY_CONSTRAINTS + (COMMIT_BLOCKS + 3) * zk::ENC_CONSTRAINTS +
        selector_constraints + 1;
    static constexpr std::size_t output_constraints =
        zk::KEY_CONSTRAINTS + COMMIT_BLOCKS * zk::ENC_CONSTRAINTS;
    static constexpr std::size_t owf_num_constraints =
        NIN * input_constraints + NOUT * output_constraints + 64 * adders + 64;

    static constexpr std::size_t qs_extra_challenges = COMMIT_BLOCKS;

    using OWF_CONSTS = SDSIGN_OWF_CONSTANTS<secpar_v, witness_bits, 4, owf_num_constraints, 0, 0, 0>;
    using CONSTS = SDSIGN_CONSTANTS<params<NIN, NOUT, RING>>;

    static constexpr std::size_t proof_bytes = CONSTS::SIGNATURE_BYTES;
};

} // namespace sdsign::tx

#endif
