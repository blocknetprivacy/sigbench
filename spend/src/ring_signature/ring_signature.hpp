#ifndef SDSIGN_RING_SIGNATURE_HPP
#define SDSIGN_RING_SIGNATURE_HPP

#include "ring_signature/keys.hpp"
#include "ring_signature/parameters.hpp"
#include "ring_signature/sign.hpp"
#include "ring_signature/verify.hpp"
#include "rsd_parameters.hpp"

namespace sdsign::ring
{

using l1_short_set1_base = reduction_compensated_l1_short_set1_base;
using l1_short_set1_n64 = parameter_set<l1_short_set1_base, 64>;
using l1_short_set1_n1024 = parameter_set<l1_short_set1_base, 1024>;
using l1_short_set1_n4096 = parameter_set<l1_short_set1_base, 4096>;
using l1_short_set1_n16384 = parameter_set<l1_short_set1_base, 16384>;
using l1_short_set1_n65536 = parameter_set<l1_short_set1_base, 65536>;
using l1_short_set1_n262144 = parameter_set<l1_short_set1_base, 262144>;
using l1_short_set1_n1048576 = parameter_set<l1_short_set1_base, 1048576>;

} // namespace sdsign::ring

#endif
