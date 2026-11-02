#include "ring_signature/parameters.hpp"

// Instantiate the ordinary SD key-generation algorithm only for the
// ring-signature-local RSD parameter type.  Keeping this instantiation in the
// ring library prevents the parameter from entering the ordinary SD API.
#define SDSIGN_API_PARAM_TYPE sdsign::ring::reduction_compensated_l1_short_set1_base
#include "../keygen.cpp"
#undef SDSIGN_API_PARAM_TYPE
