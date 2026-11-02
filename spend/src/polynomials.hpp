#ifndef POLYNOMIALS_HPP
#define POLYNOMIALS_HPP

#if defined(__AVX2__)
#include "avx2/polynomials_impl.hpp"
#elif defined(__aarch64__)
#include "aarch64/polynomials_impl.hpp"
#else
#error "unsupported architecture"
#endif
#include "vole_parameters.hpp"

namespace sdsign
{

// Multiplication in GF(2). The architecture backends specialize only the
// poly1-times-wide-polynomial cases; authenticated-bit multiplication also
// needs the scalar case.
inline poly1 operator*(poly1 x, poly1 y) { return poly1::set_all(x.data & y.data); }

template <secpar S> using poly_secpar = poly<secpar_to_bits(S)>;

template <secpar S> using poly_secpar_plus_64 = poly<secpar_to_bits(S) + 64>;

template <secpar S> using poly_2secpar = poly<2 * secpar_to_bits(S)>;

} // namespace sdsign

#endif
