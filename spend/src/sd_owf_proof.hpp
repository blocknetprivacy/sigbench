#ifndef SDSIGN_SD_OWF_PROOF_HPP
#define SDSIGN_SD_OWF_PROOF_HPP

#include "keys.hpp"
#include "hash.hpp"
#include "quicksilver.hpp"
#include "transpose_secpar.hpp"
#include "vole_check.hpp"
#include "vole_commit.hpp"
#include <cstdint>

namespace sdsign
{

constexpr std::size_t sdsign_secpar_to_bits(secpar s) { return secpar_to_bits(s); }
constexpr std::size_t sdsign_secpar_to_bytes(secpar s) { return secpar_to_bytes(s); }

constexpr std::size_t sdsign_transpose_bits_rows = TRANSPOSE_BITS_ROWS;

template <secpar S>
inline void sdsign_transpose_secpar(const void* input, void* output, std::size_t stride,
                                  std::size_t rows)
{
    transpose_secpar<S>(input, output, stride, rows);
}

template <typename P>
inline void sdsign_vole_commit(block_secpar<P::secpar_v> seed, block128 iv,
                             block_secpar<P::secpar_v>* forest, unsigned char* hashed_leaves,
                             vole_block* u, vole_block* v, uint8_t* com, uint8_t* check)
{
    vole_commit<P>(seed, iv, forest, hashed_leaves, u, v, com, check);
}

template <typename P>
inline void sdsign_vole_check_sender(const vole_block* u, const vole_block* v,
                                   const uint8_t* challenge, uint8_t* proof, hash_state& hasher)
{
    vole_check_sender<P>(u, v, challenge, proof, hasher);
}

namespace sdsign_detail
{

template <typename P, bool verifier>
void sdsign_fold_expanded_h_rows(
    block_secpar<P::secpar_v>* folded_row_out, std::size_t folded_row_len,
    const typename P::prg_t::key_t& seed_pk,
    const quicksilver_state<P::secpar_v, verifier, P::OWF_CONSTS::QS_DEGREE,
                            P::quicksilver_term_v>* state);

} // namespace sdsign_detail

template <typename P, bool verifier>
void sdsign_owf_constraints(
    quicksilver_state<P::secpar_v, verifier, P::OWF_CONSTS::QS_DEGREE, P::quicksilver_term_v>*
        state,
    const sdsign_public_key<P>* pk, uint8_t* folded_poly_coeffs_out = nullptr);

} // namespace sdsign

#endif
