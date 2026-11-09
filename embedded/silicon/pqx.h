/* Extended results block for the SPHINCS silicon run: BENCH_RESULTS_ADDR + 0x100 (0x30000100..0x300003FF on the
 * board, i.e. the unused gap between bench.h's 256-B block and the image at 0x30000400). 192 words. NOT in the
 * linker script (fixed address, never loaded); run_on_board.sh poisons it when called with NW=256. */
#ifndef PQX_H
#define PQX_H
#include <stdint.h>
#include "bench.h"
#define PQX_MAGIC 0x5051534Cu   /* 'PQSL' */
#define PQX_NMARK 24
typedef struct {
  volatile uint32_t magic;            /* x0 */
  volatile uint32_t mode;             /* x1 */
  volatile uint32_t clk_cfgr1;        /* x2 RCC_CFGR1 after clock-up (SWS bits 3:2 = 11 -> PLL1) */
  volatile uint32_t clk_pll1divr;     /* x3 RCC_PLL1DIVR after clock-up */
  volatile uint32_t clk_vosr;         /* x4 PWR_VOSR after clock-up */
  volatile uint32_t clk_saved_cfgr1;  /* x5 RCC_CFGR1 at entry */
  volatile uint32_t clk_rest_cfgr1;   /* x6 RCC_CFGR1 after restore */
  volatile uint32_t clk_rest_vosr;    /* x7 PWR_VOSR after restore */
  volatile uint32_t arena[10];        /* x8..x17 constants op_allocs op_frees live_after_op peak freed_bytes nonzero_in_freed bump ARENA_BYTES stack_depth */
  volatile uint32_t init_lo, init_hi; /* x18,x19 module initialiser cycles (64-bit) */
  volatile uint32_t main_lo, main_hi; /* x20,x21 lean_fw_main cycles (64-bit) */
  volatile uint32_t nkeccak;          /* x22 wrapped keccak256 calls (cross-module calls only) */
  volatile uint32_t nmarks;           /* x23 */
  volatile uint32_t marks[PQX_NMARK][3]; /* x24..x95: k, cyc64 lo, cyc64 hi */
  volatile uint32_t rep_len;          /* x96 */
  volatile uint8_t rep[380];          /* x97..x191: same record format as sphincs/bench_io.c rep_buf */
} pqx_t;
_Static_assert(sizeof(pqx_t) == 192 * 4, "pqx size");
#define PQX (*(pqx_t *)(BENCH_RESULTS_ADDR + 0x100u))
uint64_t pq_cyc64(void);
#endif
