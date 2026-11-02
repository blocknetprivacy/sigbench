#ifndef BLOCK_HPP
#define BLOCK_HPP

#include "vole_parameters.hpp"

#if defined(__AVX2__)
#include "avx2/block_impl.hpp"
#elif defined(__aarch64__)
#include "aarch64/block_impl.hpp"
#else
#error "unsupported architecture"
#endif

namespace sdsign
{

static_assert(sizeof(block128) == 16, "Padding in block128.");
static_assert(sizeof(block192) == 24, "Padding in block192.");
static_assert(sizeof(block256) == 32, "Padding in block256.");
static_assert(sizeof(block384) == 48, "Padding in block384.");
static_assert(sizeof(block512) == 64, "Padding in block512.");

template <secpar S> using block_secpar = block<secpar_to_bits(S)>;

template <secpar S> using block_2secpar = block<2 * secpar_to_bits(S)>;

} // namespace sdsign

#endif
