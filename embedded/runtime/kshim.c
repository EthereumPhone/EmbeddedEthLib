/* Runtime shim for the fast Keccak sponge: a byte offset that is a big Nat (>= 2^31) cannot index a
 * ByteArray on a 32-bit target, so this is unreachable; halt loudly if it is ever reached. */
#include <stddef.h>
#include <stdint.h>
#include <lean/lean.h>
void pq_fatal(uint32_t code);
size_t lean_usize_of_big_nat(b_lean_obj_arg a) { (void)a; pq_fatal(0xF1); return 0; }
