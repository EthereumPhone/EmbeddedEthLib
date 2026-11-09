/* Lean 4.35 BaseIO externs return their value directly (no IO result, no world token).
 * Benchmark I/O for SphincsBench.lean: volatile input loads, segment markers, result reports. */
#include <stdint.h>
#include <lean/lean.h>
extern volatile const uint8_t pq_vec[];
void pq_sh_puts(const char *s);
void pq_sh_putu(uint32_t v);
void pq_sh_puthex(uint8_t b);
#ifndef PQ_MODE
#define PQ_MODE 0
#endif
static volatile uint32_t pq_mode_v = PQ_MODE;
/* The trace counter splits the instruction stream at every executed entry of pq_mark. */
/* Optional instruction clock for untraced runs (-DPQ_TIMER): QEMU's CMSDK TIMER0 (secure alias 0x50000000),
 * which under `-icount shift=0` advances one tick per sysclk period of virtual time, i.e. a fixed number of
 * executed instructions per tick. The ratio is calibrated against a traced run (see README). */
#ifdef PQ_TIMER
#define T0 ((volatile uint32_t *)0x50000000u)
static uint32_t mark_t[64], mark_k[64], nmarks;
static void timer_start(void) { T0[2] = 0xFFFFFFFFu; T0[1] = 0xFFFFFFFFu; T0[0] = 1; }
#endif
/* Keccak-256 call counter (the @[csimp] makes every caller of keccak256 call Keccak.Fast.keccak256IG): link with -Wl,--wrap=lp_EthLib_EthLib_Cryptography_Hash_Keccak_Fast_keccak256IG -DPQ_KCOUNT. */
#ifdef PQ_KCOUNT
lean_object *__real_lp_EthLib_EthLib_Cryptography_Hash_Keccak_Fast_keccak256IG(lean_object *);
static volatile uint32_t pq_kcount;
lean_object *__wrap_lp_EthLib_EthLib_Cryptography_Hash_Keccak_Fast_keccak256IG(lean_object *x) {
  pq_kcount++; return __real_lp_EthLib_EthLib_Cryptography_Hash_Keccak_Fast_keccak256IG(x);
}
static uint32_t kmark_c[64], kmark_k[64], knmarks;
#endif
#ifdef PQ_SEGPEAK
/* Per-segment arena peak: at each mark, record the peak since the previous mark and the live bytes. */
extern uint32_t pq_live, pq_peak;
static uint32_t smark_k[64], smark_peak[64], smark_live[64], snmarks, sgmax;
#endif
__attribute__((noinline, used)) lean_object *pq_mark(uint32_t k) {
#ifdef PQ_SEGPEAK
  if (snmarks < 64) { smark_k[snmarks] = k; smark_peak[snmarks] = pq_peak; smark_live[snmarks++] = pq_live; }
  if (pq_peak > sgmax) sgmax = pq_peak;
  pq_peak = pq_live;
#endif
#ifdef PQ_KCOUNT
  if (knmarks < 64) { kmark_c[knmarks] = pq_kcount; kmark_k[knmarks++] = k; }
#endif
  __asm__ volatile("" ::: "memory");
#ifdef PQ_TIMER
  if (nmarks == 0) timer_start();
  if (nmarks < 64) { mark_t[nmarks] = T0[1]; mark_k[nmarks++] = k; }
#endif
  (void)k; return lean_box(0);
}
uint32_t pq_mode(lean_object *u) { (void)u; return pq_mode_v; }
lean_object *pq_load(uint32_t off, uint32_t len) {
  lean_object *r = lean_alloc_sarray(1, len, len);
  for (uint32_t i = 0; i < len; i++) lean_sarray_cptr(r)[i] = pq_vec[off + i];
  return r;
}
/* Reports are buffered in RAM and printed after lean_fw_main returns (pq_flush), so no semihosting
 * I/O falls inside a measured segment. */
static uint8_t rep_buf[4096]; static uint32_t rep_len;
static void rep_put(uint8_t b) { if (rep_len < sizeof rep_buf) rep_buf[rep_len++] = b; }
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
void pq_flush(void) {
#ifdef PQ_SEGPEAK
  for (uint32_t i = 0; i < snmarks; i++) { pq_sh_puts("P mark "); pq_sh_putu(smark_k[i]); pq_sh_puts(" live "); pq_sh_putu(smark_live[i]); pq_sh_puts(" peak_since_prev "); pq_sh_putu(smark_peak[i]); pq_sh_puts("\n"); }
  if (sgmax > pq_peak) pq_peak = sgmax;
#endif
#ifdef PQ_KCOUNT
  for (uint32_t i = 1; i < knmarks; i++) { pq_sh_puts("K "); pq_sh_putu(kmark_k[i - 1]); pq_sh_puts("->"); pq_sh_putu(kmark_k[i]); pq_sh_puts(" keccak_calls "); pq_sh_putu(kmark_c[i] - kmark_c[i - 1]); pq_sh_puts("\n"); }
#endif
#ifdef PQ_TIMER
  for (uint32_t i = 1; i < nmarks; i++) { pq_sh_puts("T "); pq_sh_putu(mark_k[i - 1]); pq_sh_puts("->"); pq_sh_putu(mark_k[i]); pq_sh_puts(" ticks "); pq_sh_putu(mark_t[i - 1] - mark_t[i]); pq_sh_puts("\n"); }
#endif
  for (uint32_t i = 0; i < rep_len; ) {
    uint8_t kind = rep_buf[i], tag = rep_buf[i + 1], n = rep_buf[i + 2]; i += 3;
    pq_sh_puts("R "); pq_sh_putu(tag); pq_sh_puts(" ");
    if (kind == 0) { uint32_t v = 0; for (int k = 0; k < 4; k++) v = (v << 8) | rep_buf[i + k]; pq_sh_putu(v); }
    else for (int k = 0; k < n; k++) pq_sh_puthex(rep_buf[i + k]);
    i += n; pq_sh_puts("\n");
  }
}
