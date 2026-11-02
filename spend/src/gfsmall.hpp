#ifndef GFSMALL_HPP
#define GFSMALL_HPP

#if defined(__AVX2__)
#include "avx2/gfsmall_impl.hpp"
#elif defined(__aarch64__)
#include "aarch64/gfsmall_impl.hpp"
#else
#error "unsupported architecture"
#endif

#endif
