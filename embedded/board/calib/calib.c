/* Calibration: known instruction sequences timed with DWT CYCCNT (ldr of CYCCNT on both sides, in one asm). */
#include "bench.h"
#ifndef NBLK
#define NBLK 1000
#endif
#define STR_(x) #x
#define STR(x) STR_(x)
#define TIMED(body) ({ uint32_t a_, b_; __asm volatile("movw r2, #0x1004\n movt r2, #0xE000\n movw r12, #0x0040\n movt r12, #0x3000\n ldr %0, [r2]\n" body "ldr %1, [r2]\n" : "=&r"(a_), "=&r"(b_) : : "r1", "r2", "r3", "r12", "cc", "memory"); b_ - a_; })
void bench_run(void) {
  BENCH.user[0] = TIMED("");                                                     /* empty: CYCCNT-read overhead */
  BENCH.user[1] = TIMED(".rept " STR(NBLK) "\n adds r1, r1, #1\n .endr\n");      /* NBLK 16-bit ALU */
  BENCH.user[2] = TIMED(".rept " STR(NBLK) "\n add.w r1, r1, #1\n .endr\n");     /* NBLK 32-bit ALU */
  BENCH.user[3] = TIMED(".rept " STR(NBLK) "\n ldr r1, [r12]\n .endr\n");         /* NBLK loads from SRAM */
  BENCH.user[4] = TIMED("movw r3, #" STR(NBLK) "\n 1: subs r3, r3, #1\n bne 1b\n"); /* NBLK-iteration loop: 2*NBLK+1 instr */
  BENCH.user[5] = TIMED(".rept " STR(NBLK) "\n adds r1, r1, #1\n .endr\n");      /* repeat of [1] (determinism) */
  BENCH.user[6] = NBLK;
}
