/* Board variant of sphincs/bench_io.c. Same externs (pq_mark, pq_mode, pq_load, pq_report, pq_report_bytes) with the
 * same semantics; differences: pq_mark records a 64-bit DWT cycle stamp into PQX (pqx.h) instead of a QEMU timer,
 * reports go straight to PQX.rep (no semihosting flush).
 * 64-bit cycles: DWT_CYCCNT is 32-bit. pq_cyc64() extends it in software and is sampled at every pq_mark and at the
 * entry of every cross-module call of the fork's Keccak-256 (linker --wrap of Keccak.Fast.keccak256IG, which the
 * @[csimp] makes every caller of keccak256 call). Sound as long as no gap between two samples
 * exceeds 2^32 cycles; the longest keccak-free stretch was decodeSignature, about 1.27e9 cycles before the readBytes
 * csimp and about 5e6 after it, below 2^32 = 4.29e9. */
#include <stdint.h>
#include <lean/lean.h>
#include "bench.h"
#include "pqx.h"
extern volatile const uint8_t pq_vec[];
#ifndef PQ_MODE
#define PQ_MODE 0
#endif
static volatile uint32_t pq_mode_v = PQ_MODE;
static uint32_t cyc_last, cyc_hi, nkeccak;
uint64_t pq_cyc64(void) { uint32_t c = bench_cyc(); if (c < cyc_last) cyc_hi++; cyc_last = c; return ((uint64_t)cyc_hi << 32) | c; }
void pq_store_nkeccak(void) { PQX.nkeccak = nkeccak; }
lean_object *__real_lp_EthLib_EthLib_Cryptography_Hash_Keccak_Fast_keccak256IG(lean_object *);
lean_object *__wrap_lp_EthLib_EthLib_Cryptography_Hash_Keccak_Fast_keccak256IG(lean_object *m) {
  (void)pq_cyc64(); nkeccak++;
  return __real_lp_EthLib_EthLib_Cryptography_Hash_Keccak_Fast_keccak256IG(m);
}
__attribute__((noinline, used)) lean_object *pq_mark(uint32_t k) {
  __asm__ volatile("" ::: "memory");
  uint64_t t = pq_cyc64();
  uint32_t n = PQX.nmarks;
  if (n < PQX_NMARK) { PQX.marks[n][0] = k; PQX.marks[n][1] = (uint32_t)t; PQX.marks[n][2] = (uint32_t)(t >> 32); PQX.nmarks = n + 1; }
  return lean_box(0);
}
uint32_t pq_mode(lean_object *u) { (void)u; return pq_mode_v; }
lean_object *pq_load(uint32_t off, uint32_t len) {
  lean_object *r = lean_alloc_sarray(1, len, len);
  for (uint32_t i = 0; i < len; i++) lean_sarray_cptr(r)[i] = pq_vec[off + i];
  return r;
}
static void rep_put(uint8_t b) { uint32_t n = PQX.rep_len; if (n < sizeof PQX.rep) { PQX.rep[n] = b; PQX.rep_len = n + 1; } }
lean_object *pq_report(uint32_t tag, uint32_t v) {
  rep_put(0); rep_put((uint8_t)tag); rep_put(4);
  for (int i = 0; i < 4; i++) rep_put((uint8_t)(v >> (24 - 8 * i)));
  return lean_box(0);
}
lean_object *pq_report_bytes(uint32_t tag, lean_object *b) {
  size_t n = lean_sarray_size(b); rep_put(1); rep_put((uint8_t)tag); rep_put((uint8_t)n);
  for (size_t i = 0; i < n; i++) rep_put(lean_sarray_cptr(b)[i]);
  return lean_box(0);
}
