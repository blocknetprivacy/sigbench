#ifndef SDSIGN_RING_SIGNATURE_CONSTRAINTS_HPP
#define SDSIGN_RING_SIGNATURE_CONSTRAINTS_HPP

#include "../quicksilver.hpp"
#include "ring_signature/keys.hpp"

namespace sdsign::ring
{

template <typename RP, bool Verifier>
void constraints(quicksilver_state<RP::secpar_v, Verifier, RP::OWF_CONSTS::QS_DEGREE,
                                   RP::quicksilver_term_v>* state,
                 const public_ring<typename RP::base_parameter, RP::ring_size>* ring,
                 uint8_t* folded_poly_coeffs_out = nullptr,
                 const std::array<block_secpar<RP::secpar_v>,
                                  RP::y_vector_len>* signer_syndrome = nullptr,
                 std::size_t signer_index = 0, bool* signer_matches = nullptr);

} // namespace sdsign::ring

#endif
