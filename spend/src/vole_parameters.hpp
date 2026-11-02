#ifndef SDSIGN_VOLE_PARAMETERS_HPP
#define SDSIGN_VOLE_PARAMETERS_HPP

#if defined(__AVX2__)
#include "avx2/constants_impl.hpp"
#elif defined(__aarch64__)
#include "aarch64/constants_impl.hpp"
#else
#error "unsupported architecture"
#endif

#include <cstddef>
#include <cstdint>
#include <type_traits>
#include <utility>

namespace sdsign
{

enum class secpar : std::size_t
{
    L1 = 128,
    L3 = 192,
    L5 = 256,
};

constexpr std::size_t secpar_to_bits(secpar s) { return std::to_underlying(s); }
constexpr std::size_t secpar_to_bytes(secpar s) { return secpar_to_bits(s) / 8; }

enum class owf : unsigned int
{
    rsd = 0,
    pkp = 1,
};

enum class elementary_encoding : unsigned int
{
    hamming_ball = 0,
    optimal = 1,
};

enum class quicksilver_term : unsigned int
{
    leading = 0,
    constant = 1,
};

enum class prg
{
    aes_ctr,
    aes_secpar_fixed_key_ctr,
};

enum class leaf_hash
{
    aes_ctr,
    aes_ctr_stat_bind,
    aes_secpar_fixed_key_ctr,
    aes_secpar_fixed_key_ctr_stat_bind,
    crh,
};

enum class proof_system_set
{
    set0,
    set1,
};

enum class proof_system_variant
{
    s,
    f,
};

template <std::size_t bits> struct block;
template <std::size_t bits> struct poly;

template <secpar S> using block_secpar = block<secpar_to_bits(S)>;
template <secpar S> using block_2secpar = block<2 * secpar_to_bits(S)>;
template <secpar S> using poly_secpar = poly<secpar_to_bits(S)>;
template <secpar S> using poly_2secpar = poly<2 * secpar_to_bits(S)>;

template <secpar S> struct aes_ctr_prg;
template <secpar S> struct aes_secpar_fixed_key_ctr_prg;
template <typename PRG> struct prg_leaf_hash;
template <typename PRG, uint32_t MAX_TWEAKS> struct stat_binding_leaf_hash;
template <secpar S> struct crh_leaf_hash;

template <secpar S, prg PRG> struct prg_type;
template <secpar S, prg PRG> using prg_type_t = typename prg_type<S, PRG>::type;
template <secpar S> struct prg_type<S, prg::aes_ctr>
{
    using type = aes_ctr_prg<S>;
};
template <secpar S> struct prg_type<S, prg::aes_secpar_fixed_key_ctr>
{
    using type = aes_secpar_fixed_key_ctr_prg<S>;
};

template <secpar S, uint32_t MAX_TWEAKS, leaf_hash LH> struct leaf_hash_type;
template <secpar S, uint32_t MAX_TWEAKS, leaf_hash LH>
using leaf_hash_type_t = typename leaf_hash_type<S, MAX_TWEAKS, LH>::type;
template <secpar S, uint32_t MAX_TWEAKS> struct leaf_hash_type<S, MAX_TWEAKS, leaf_hash::aes_ctr>
{
    using type = prg_leaf_hash<aes_ctr_prg<S>>;
};
template <secpar S, uint32_t MAX_TWEAKS>
struct leaf_hash_type<S, MAX_TWEAKS, leaf_hash::aes_ctr_stat_bind>
{
    using type = stat_binding_leaf_hash<aes_ctr_prg<S>, MAX_TWEAKS>;
};
template <secpar S, uint32_t MAX_TWEAKS>
struct leaf_hash_type<S, MAX_TWEAKS, leaf_hash::aes_secpar_fixed_key_ctr>
{
    using type = prg_leaf_hash<aes_secpar_fixed_key_ctr_prg<S>>;
};
template <secpar S, uint32_t MAX_TWEAKS>
struct leaf_hash_type<S, MAX_TWEAKS, leaf_hash::aes_secpar_fixed_key_ctr_stat_bind>
{
    using type = stat_binding_leaf_hash<aes_secpar_fixed_key_ctr_prg<S>, MAX_TWEAKS>;
};
template <secpar S, uint32_t MAX_TWEAKS> struct leaf_hash_type<S, MAX_TWEAKS, leaf_hash::crh>
{
    using type = crh_leaf_hash<S>;
};

enum class bavc
{
    ggm_forest,
    one_tree,
};

template <secpar S, std::size_t TAU, std::size_t DELTA_BITS, prg TREE_PRG, leaf_hash LEAF_HASH,
          std::size_t VOLE_WIDTH_SHIFT>
struct ggm_forest_bavc;

template <secpar S, std::size_t TAU, std::size_t DELTA_BITS, prg TREE_PRG, leaf_hash LEAF_HASH,
          std::size_t VOLE_WIDTH_SHIFT, std::size_t OPENING_SEEDS_THRESHOLD>
struct one_tree_bavc;

template <secpar S, std::size_t TAU, std::size_t DELTA_BITS, prg TREE_PRG, leaf_hash LEAF_HASH,
          std::size_t VOLE_WIDTH_SHIFT, bavc BAVC, std::size_t BAVC_PARAM>
struct bavc_type;
template <secpar S, std::size_t TAU, std::size_t DELTA_BITS, prg TREE_PRG, leaf_hash LEAF_HASH,
          std::size_t VOLE_WIDTH_SHIFT, bavc BAVC, std::size_t BAVC_PARAM>
using bavc_type_t = typename bavc_type<S, TAU, DELTA_BITS, TREE_PRG, LEAF_HASH, VOLE_WIDTH_SHIFT,
                                       BAVC, BAVC_PARAM>::type;
template <secpar S, std::size_t TAU, std::size_t DELTA_BITS, prg TREE_PRG, leaf_hash LEAF_HASH,
          std::size_t VOLE_WIDTH_SHIFT>
struct bavc_type<S, TAU, DELTA_BITS, TREE_PRG, LEAF_HASH, VOLE_WIDTH_SHIFT, bavc::ggm_forest, 0>
{
    using type = ggm_forest_bavc<S, TAU, DELTA_BITS, TREE_PRG, LEAF_HASH, VOLE_WIDTH_SHIFT>;
};
template <secpar S, std::size_t TAU, std::size_t DELTA_BITS, prg TREE_PRG, leaf_hash LEAF_HASH,
          std::size_t VOLE_WIDTH_SHIFT, std::size_t BAVC_PARAM>
struct bavc_type<S, TAU, DELTA_BITS, TREE_PRG, LEAF_HASH, VOLE_WIDTH_SHIFT, bavc::one_tree,
                 BAVC_PARAM>
{
    using type =
        one_tree_bavc<S, TAU, DELTA_BITS, TREE_PRG, LEAF_HASH, VOLE_WIDTH_SHIFT, BAVC_PARAM>;
};

template <secpar S, std::size_t WITNESS_BITS_IN, std::size_t QS_DEGREE_IN,
          std::size_t OWF_NUM_CONSTRAINTS_IN, std::size_t OWF_MUL_C_PRE_IN,
          std::size_t OWF_MUL_C_IP_IN, std::size_t OWF_MUL_C_TOTAL_IN>
struct SDSIGN_OWF_CONSTANTS;
template <typename P> struct SDSIGN_CONSTANTS;

template <secpar S, proof_system_variant V, proof_system_set SET> struct proof_system_parameters;

#define SDSIGN_PROOF_SYSTEM_PARAMETERS(sec, variant, set, tau_value, leaf_hash_value,              \
                                       vole_width_value, bavc_value)                               \
    template <>                                                                                    \
    struct proof_system_parameters<secpar::sec, proof_system_variant::variant,                     \
                                   proof_system_set::set>                                          \
    {                                                                                              \
        constexpr static std::size_t tau = tau_value;                                              \
        constexpr static leaf_hash leaf_hash_v = leaf_hash_value;                                  \
        constexpr static std::size_t vole_width_shift = vole_width_value;                          \
        constexpr static std::pair<bavc, std::size_t> bavc_param = {bavc::one_tree, bavc_value};   \
    }

SDSIGN_PROOF_SYSTEM_PARAMETERS(L1, s, set0, 11, leaf_hash::aes_ctr_stat_bind, 7, 102);
SDSIGN_PROOF_SYSTEM_PARAMETERS(L1, f, set0, 16, leaf_hash::aes_ctr_stat_bind, 8, 110);
SDSIGN_PROOF_SYSTEM_PARAMETERS(L3, s, set0, 16, leaf_hash::aes_ctr_stat_bind, 12, 162);
SDSIGN_PROOF_SYSTEM_PARAMETERS(L3, f, set0, 24, leaf_hash::aes_ctr_stat_bind, 8, 163);
SDSIGN_PROOF_SYSTEM_PARAMETERS(L5, s, set0, 22, leaf_hash::aes_ctr_stat_bind, 6, 245);
SDSIGN_PROOF_SYSTEM_PARAMETERS(L5, f, set0, 32, leaf_hash::aes_ctr_stat_bind, 8, 246);

SDSIGN_PROOF_SYSTEM_PARAMETERS(L1, s, set1, 11, leaf_hash::crh, 7, 107);
SDSIGN_PROOF_SYSTEM_PARAMETERS(L1, f, set1, 16, leaf_hash::crh, 0, 101);
SDSIGN_PROOF_SYSTEM_PARAMETERS(L3, s, set1, 16, leaf_hash::crh, 0, 157);
SDSIGN_PROOF_SYSTEM_PARAMETERS(L3, f, set1, 24, leaf_hash::crh, 0, 153);
SDSIGN_PROOF_SYSTEM_PARAMETERS(L5, s, set1, 21, leaf_hash::crh, 4, 216);
SDSIGN_PROOF_SYSTEM_PARAMETERS(L5, f, set1, 32, leaf_hash::crh, 0, 207);

#undef SDSIGN_PROOF_SYSTEM_PARAMETERS

} // namespace sdsign

#endif
