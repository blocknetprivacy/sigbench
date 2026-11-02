#ifndef FASTPQ_TX_CAPI_H
#define FASTPQ_TX_CAPI_H

#include <stddef.h>
#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

typedef struct
{
    size_t proof_bytes;
    double prove_ms;
    double verify_ms;
    double prove_cpu_ms;
    double verify_cpu_ms;
} fpq_measure;

void* fpq_prepare(void);
void fpq_free(void* p);
double fpq_set_digest_ms(const void* p);
size_t fpq_set_size(void);
size_t fpq_set_bytes(void);
size_t fpq_commitment_bytes(void);
size_t fpq_nullifier_bytes(void);
size_t fpq_proof_bytes(size_t n);
int fpq_run(const void* p, size_t n, uint64_t seed, fpq_measure* m, double (*cpu_ms)(void));
int fpq_self_check(const void* p);
int fpq_commit_check(const uint8_t* r, const uint8_t* pk, uint64_t amount, const uint8_t* c);
int fpq_owner_key(const uint8_t* seed, size_t seed_len, uint8_t* pk_out);
const uint8_t* fpq_set_data(const void* p);
size_t fpq_real_index(const void* p, size_t j);
int fpq_run_full(const void* p, size_t n, uint64_t seed, fpq_measure* m, double (*cpu_ms)(void), uint8_t* proof_out,
                 uint8_t* witness_out, uint8_t* public_out);
size_t fpq_public_bytes(size_t n);
void* fpq_prepare_seeded(const uint8_t* seed, size_t seed_len, size_t pool, size_t* progress);
double fpq_set_build_ms(const void* p);
size_t fpq_pool_size(const void* p);
int fpq_send(const void* p, size_t n, uint64_t seed, size_t first_coin, const uint8_t* out_pk, const uint8_t* out_seed,
             fpq_measure* m, double (*cpu_ms)(void), uint8_t* proof_out, uint8_t* public_out);
int fpq_verify_tx(const void* p, size_t n, const uint8_t* proof, const uint8_t* nullifiers, const uint8_t* commitments,
                  uint64_t fee, const uint8_t* set_digest);
int fpq_coin_matches(const uint8_t* seed, size_t seed_len, const uint8_t* pk, uint64_t amount, const uint8_t* c);
int fpq_layout(size_t n, size_t* out);

#ifdef __cplusplus
}
#endif

#endif
