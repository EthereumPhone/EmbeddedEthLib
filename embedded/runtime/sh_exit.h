/* Semihosting exit with a host exit status, for the QEMU builds (runtime/rt.c and the QEMU twin of board/startup.c;
 * sha256/ref.c, which cannot fail, makes the plain SYS_EXIT below inline). The board never uses semihosting.
 *
 * On AArch32, SYS_EXIT (0x18) takes the reason code itself in R1, not a pointer to a {reason, subcode} block as on
 * AArch64. QEMU exits with status 0 for ADP_Stopped_ApplicationExit (0x20026) and with 1 for any other value, a
 * pointer included. SYS_EXIT_EXTENDED (0x20) takes a pointer to {reason, subcode} on AArch32 too, and QEMU exits with
 * the subcode. The host keeps 8 bits of it, so a failure code whose low byte is zero is reported as 1.
 * Measured with qemu-system-arm 8.2.2, mps2-an505. */
#ifndef PQ_SH_EXIT_H
#define PQ_SH_EXIT_H
#include <stdint.h>
static inline uint32_t pq_sh_call(uint32_t op, uint32_t arg) {
  register uint32_t r0 __asm__("r0") = op; register uint32_t r1 __asm__("r1") = arg;
  __asm__ volatile("bkpt 0xab" : "+r"(r0) : "r"(r1) : "memory");
  return r0;
}
/* code 0: success, host status 0. Any other code: host status (code & 0xFF), or 1 if that is 0. */
__attribute__((noreturn)) static inline void pq_sh_exit(uint32_t code) {
  if (code == 0) pq_sh_call(0x18, 0x20026u);           /* SYS_EXIT, ADP_Stopped_ApplicationExit: status 0 */
  uint32_t st = code & 0xFFu; if (st == 0) st = 1;
  volatile uint32_t blk[2] = {0x20026u, st};          /* on the stack: a static would grow .bss, and with it the
                                                          instructions of the start-up .bss loop before the first mark */
  pq_sh_call(0x20, (uint32_t)blk);                     /* SYS_EXIT_EXTENDED: status st */
  pq_sh_call(0x18, 0x20023u);                          /* if 0x20 is unsupported: ADP_Stopped_RunTimeErrorUnknown, status 1 */
  for (;;) {}
}
#endif
