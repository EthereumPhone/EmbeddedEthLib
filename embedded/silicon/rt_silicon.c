/* SILICON VARIANT of runtime/rt.c: the next 222 lines are runtime/rt.c lines 1-222 VERBATIM (allocator, zero-on-free,
 * runtime). Only the I/O tail (after them) differs: no semihosting; text -> bench.h text buffer; halts ->
 * bench_halt; bench_run() replaces Reset_Handler; reports -> extended results block PQX (pqx.h). */
/* Minimal Lean runtime for a Cortex-M33 secure image: a fixed arena instead of a general heap.
 * - Every object comes from one static arena (no malloc, no OS).
 * - Every freed object is wiped immediately (zero-on-free).
 * - After the operation, the harness checks that nothing is still alive and the arena is all zero.
 * This file is the trusted, unproved part of the experiment. */
#include <stdint.h>
#include <stddef.h>
#include <lean/lean.h>

#ifndef STACK_PAINT
#define STACK_PAINT (128 * 1024)
#endif
#ifndef ARENA_BYTES
#define ARENA_BYTES (512 * 1024)
#endif
#define NCLASS 8192   /* exact-size classes up to 64 KiB, so large blocks (7.7 KB signature arrays) are reused */
static uint8_t arena[ARENA_BYTES] __attribute__((aligned(8)));
static uint32_t bump;
static uint8_t *freelist[NCLASS];
uint32_t pq_live, pq_peak, pq_allocs, pq_frees;

static void pq_halt(uint32_t code);
static void pq_oom_report(uint32_t rs, uint32_t bump);
/* (d) word-wide wipe: every block size is a multiple of 8 and every object is 8-aligned. */
static void wipe(void *p, uint32_t n) { volatile uint32_t *q = p, *e = (volatile uint32_t *)((uint8_t *)p + n); while (q < e) { q[0] = 0; q[1] = 0; q += 2; } }

/* block = [size:4][next:4][object ...] */
static void *pq_alloc(size_t sz) {
  uint32_t rs = (uint32_t)((sz + 7) & ~(size_t)7), cls = rs / 8;
  uint8_t *b;
  if (cls < NCLASS && freelist[cls]) { b = freelist[cls]; freelist[cls] = *(uint8_t **)(b + 4); *(uint8_t **)(b + 4) = 0; }
  else { if (bump + rs + 8 > ARENA_BYTES) { pq_oom_report(rs, bump); pq_halt(0xA0); } b = arena + bump; bump += rs + 8; }
  *(uint32_t *)b = rs;            /* bit 0 clear = in use */
  pq_live += rs; pq_allocs++; if (pq_live > pq_peak) pq_peak = pq_live;
  return b + 8;
}
static void pq_free(void *o) {
  uint8_t *b = (uint8_t *)o - 8; uint32_t rs = *(uint32_t *)b, cls = rs / 8;
  wipe(o, rs);
  *(uint32_t *)b = rs | 1;          /* mark free */                                  /* zero-on-free: no secret outlives its object */
  pq_live -= rs; pq_frees++;
  if (cls < NCLASS) { *(uint8_t **)(b + 4) = freelist[cls]; freelist[cls] = b; }
}

/* Hooks that lean.h's inline code calls (config.h selects the mimalloc names). */
void *mi_malloc_small(size_t sz) { return pq_alloc(sz); }
void mi_free(void *p) { pq_free(p); }
lean_object *lean_alloc_object(size_t sz) { return (lean_object *)pq_alloc(sz); }
void lean_free_object(lean_object *o) { pq_free(o); }
void lean_inc_heartbeat(void) {}
void lean_mark_persistent(lean_object *o) {
  if (lean_is_scalar(o) || o->m_rc == 0) return;
  o->m_rc = 0;
  if (lean_ptr_tag(o) <= LeanMaxCtorTag) { for (unsigned i = 0; i < lean_ctor_num_objs(o); i++) lean_mark_persistent(lean_ctor_obj_cptr(o)[i]); }
  else if (lean_ptr_tag(o) == LeanArray) { for (size_t i = 0; i < lean_array_size(o); i++) lean_mark_persistent(lean_array_cptr(o)[i]); }
}
/* Lean's core-library initialiser: our code uses none of its globals (checked by the wrong-answer test). */
/* l_instInhabitedUInt32 is a uint32_t global in Lean 4.35 (core/Init_Prelude.c); its value 0 is the zeroed .bss. */
extern lean_object *l_ByteArray_empty;           /* Init.Prelude global, normally set by initialize_Init_Prelude */
lean_object *initialize_Init(uint8_t builtin) {
  (void)builtin;
  if (!l_ByteArray_empty) { l_ByteArray_empty = lean_alloc_sarray(1, 0, 0); lean_mark_persistent(l_ByteArray_empty); }
  return lean_io_result_mk_ok(lean_box(0));
}

/* Reference counting reached zero: release children, then the object. */
void lean_dec_ref_cold(lean_object *o) {
  if (o->m_rc != 1) pq_halt(0xB0);              /* multi-threaded objects are not supported */
  uint8_t tag = lean_ptr_tag(o);
  if (tag <= LeanMaxCtorTag) {
    lean_object **objs = lean_ctor_obj_cptr(o); unsigned n = lean_ctor_num_objs(o);
    for (unsigned i = 0; i < n; i++) if (!lean_is_scalar(objs[i])) lean_dec_ref(objs[i]);
  } else if (tag == LeanArray) {
    for (size_t i = 0; i < lean_array_size(o); i++) { lean_object *e = lean_array_cptr(o)[i]; if (!lean_is_scalar(e)) lean_dec_ref(e); }
  } else if (tag == LeanClosure) {
    for (unsigned i = 0; i < lean_closure_num_fixed(o); i++) { lean_object *e = lean_closure_arg_cptr(o)[i]; if (!lean_is_scalar(e)) lean_dec_ref(e); }
  } else if (tag != LeanScalarArray && tag != LeanString && tag != LeanMPZ) pq_halt(0xB1);
  pq_free(o);
}

/* Array and ByteArray growth (normally in the C++ runtime). */
lean_object *lean_copy_expand_array(lean_object *a, bool expand) {
  size_t sz = lean_array_size(a), cap = lean_array_capacity(a); if (expand) cap = cap * 2 + 1;
  lean_object *r = lean_alloc_array(sz, cap);
  for (size_t i = 0; i < sz; i++) { lean_object *e = lean_array_cptr(a)[i]; if (!lean_is_scalar(e)) lean_inc(e); lean_array_cptr(r)[i] = e; }
  lean_dec(a); return r;
}
lean_object *lean_array_push(lean_object *a, lean_object *v) {
  lean_object *r = (lean_is_exclusive(a) && lean_array_capacity(a) > lean_array_size(a)) ? a : lean_copy_expand_array(a, lean_array_capacity(a) <= lean_array_size(a));
  lean_array_cptr(r)[lean_array_size(r)] = v; lean_to_array(r)->m_size++; return r;
}
static lean_object *copy_sarray(lean_object *a, size_t cap) {
  size_t sz = lean_sarray_size(a); lean_object *r = lean_alloc_sarray(1, sz, cap);
  for (size_t i = 0; i < sz; i++) lean_sarray_cptr(r)[i] = lean_sarray_cptr(a)[i];
  lean_dec(a); return r;
}
lean_object *lean_copy_byte_array(lean_object *a) { return copy_sarray(a, lean_sarray_capacity(a)); }
lean_object *lean_byte_array_push(lean_object *a, uint8_t b) {
  lean_object *r = a;
  if (!lean_is_exclusive(a) || lean_sarray_capacity(a) <= lean_sarray_size(a)) r = copy_sarray(a, lean_sarray_size(a) * 2 + 1);
  lean_sarray_cptr(r)[lean_sarray_size(r)] = b; lean_to_sarray(r)->m_size++; return r;
}

/* Panics (out-of-bounds `!`, overflow): stop the device. Strings are only needed for panic messages. */
lean_object *lean_mk_string_unchecked(const char *s, size_t sz, size_t len) { (void)s; (void)sz; (void)len; return lean_box(0); }
lean_object *lean_panic_fn(lean_object *d, lean_object *m) { (void)d; (void)m; pq_halt(0xC0); return d; }
void lean_internal_panic_out_of_memory(void) { pq_halt(0xC1); }
void lean_internal_panic_overflow(void) { pq_halt(0xC2); }
void lean_internal_panic_rc_overflow(void) { pq_halt(0xC3); }
static void puts_(const char *s); static void putu(uint32_t v);
void lean_notify_assert(const char *a, int b, const char *c) { puts_("assert "); puts_(a); puts_(":"); putu((uint32_t)b); puts_(" "); puts_(c); puts_("\n"); pq_halt(0xC4); }
/* moved to rt_ext.c: lean_object *lean_nat_big_succ */
/* moved to rt_ext.c: lean_object *lean_nat_big_add */
/* moved to rt_ext.c: lean_object *lean_nat_big_sub */
/* moved to rt_ext.c: lean_object *lean_nat_big_mul */
/* moved to rt_ext.c: lean_object *lean_nat_big_mod */
/* moved to rt_ext.c: lean_object *lean_nat_big_div */
/* moved to rt_ext.c: lean_object *lean_nat_overflow_mul */
/* moved to rt_ext.c: bool lean_nat_big_lt */
/* moved to rt_ext.c: bool lean_nat_big_le */
/* moved to rt_ext.c: bool lean_nat_big_eq */
/* moved to rt_ext.c: uint64_t lean_uint64_of_big_nat */
/* moved to rt_ext.c: uint32_t lean_uint32_of_big_nat */
/* moved to rt_ext.c: uint8_t lean_uint8_of_big_nat */
/* moved to rt_ext.c: lean_object *lean_big_usize_to_nat */
/* moved to rt_ext.c: lean_object *lean_big_uint64_to_nat */


lean_object *lean_array_get_panic(lean_object *d) { pq_halt(0xC6); return d; }
lean_object *lean_array_set_panic(lean_object *a, lean_object *v) { (void)v; pq_halt(0xC7); return a; }
/* ByteArray <-> Array UInt8 conversions (ByteArray.mk / .data) */
lean_object *lean_byte_array_mk(lean_object *a) {
  size_t n = lean_array_size(a); lean_object *r = lean_alloc_sarray(1, n, n);
  for (size_t i = 0; i < n; i++) lean_sarray_cptr(r)[i] = (uint8_t)lean_unbox(lean_array_cptr(a)[i]);
  lean_dec(a); return r;
}
lean_object *lean_byte_array_data(lean_object *a) {
  size_t n = lean_sarray_size(a); lean_object *r = lean_alloc_array(n, n);
  for (size_t i = 0; i < n; i++) lean_array_cptr(r)[i] = lean_box(lean_sarray_cptr(a)[i]);
  lean_dec(a); return r;
}

lean_object *lean_mk_array(lean_object *n, lean_object *v) {
  size_t sz = lean_unbox(n); lean_object *r = lean_alloc_array(sz, sz);
  for (size_t i = 0; i < sz; i++) { if (!lean_is_scalar(v)) lean_inc(v); lean_array_cptr(r)[i] = v; }
  lean_dec(v); return r;
}
/* moved to rt_ext.c: lean_object *lean_nat_big_shiftr */
/* Lazy one-time constants (single core, no threads): compute, mark persistent, remember. */
lean_object *lean_obj_once_cold(lean_object **loc, lean_once_cell_t *tok, lean_object *(*init)(void)) {
  lean_object *v = init(); lean_mark_persistent(v); *loc = v; tok->state = 1; return v;
}
#define ONCE(T, N) T N(T *loc, lean_once_cell_t *tok, T (*init)(void)) { T v = init(); *loc = v; tok->state = 1; return v; }
ONCE(uint8_t, lean_uint8_once_cold) ONCE(uint16_t, lean_uint16_once_cold) ONCE(uint32_t, lean_uint32_once_cold)
ONCE(uint64_t, lean_uint64_once_cold) ONCE(size_t, lean_usize_once_cold)

/* ---- Closures (normally apply.cpp): call the boxed function once all arguments are present. ---- */
typedef lean_object *(*F1)(lean_object*); typedef lean_object *(*F2)(lean_object*,lean_object*);
typedef lean_object *(*F3)(lean_object*,lean_object*,lean_object*); typedef lean_object *(*F4)(lean_object*,lean_object*,lean_object*,lean_object*);
typedef lean_object *(*F5)(lean_object*,lean_object*,lean_object*,lean_object*,lean_object*);
typedef lean_object *(*F6)(lean_object*,lean_object*,lean_object*,lean_object*,lean_object*,lean_object*);
typedef lean_object *(*F7)(lean_object*,lean_object*,lean_object*,lean_object*,lean_object*,lean_object*,lean_object*);
typedef lean_object *(*F8)(lean_object*,lean_object*,lean_object*,lean_object*,lean_object*,lean_object*,lean_object*,lean_object*);
static lean_object *call_full(void *fn, unsigned k, lean_object **a) {
  switch (k) {
    case 1: return ((F1)fn)(a[0]); case 2: return ((F2)fn)(a[0],a[1]); case 3: return ((F3)fn)(a[0],a[1],a[2]);
    case 4: return ((F4)fn)(a[0],a[1],a[2],a[3]); case 5: return ((F5)fn)(a[0],a[1],a[2],a[3],a[4]);
    case 6: return ((F6)fn)(a[0],a[1],a[2],a[3],a[4],a[5]); case 7: return ((F7)fn)(a[0],a[1],a[2],a[3],a[4],a[5],a[6]);
    case 8: return ((F8)fn)(a[0],a[1],a[2],a[3],a[4],a[5],a[6],a[7]);
    default: pq_halt(0xE0); return 0;
  }
}
lean_object *lean_apply_n(lean_object *f, unsigned n, lean_object **args) {
  unsigned arity = lean_closure_arity(f), fixed = lean_closure_num_fixed(f);
  if (fixed + n < arity) {                       /* under-application: a bigger closure */
    lean_object *r = lean_alloc_closure(lean_closure_fun(f), arity, fixed + n);
    for (unsigned i = 0; i < fixed; i++) { lean_object *x = lean_closure_arg_cptr(f)[i]; lean_inc(x); lean_closure_arg_cptr(r)[i] = x; }
    for (unsigned i = 0; i < n; i++) lean_closure_arg_cptr(r)[fixed + i] = args[i];
    lean_dec(f); return r;
  }
  unsigned take = arity - fixed; lean_object *all[16];
  if (arity > 16) pq_halt(0xE1);
  for (unsigned i = 0; i < fixed; i++) { lean_object *x = lean_closure_arg_cptr(f)[i]; lean_inc(x); all[i] = x; }
  for (unsigned i = 0; i < take; i++) all[fixed + i] = args[i];
  void *fn = lean_closure_fun(f); lean_dec(f);
  lean_object *r = call_full(fn, arity, all);
  return take == n ? r : lean_apply_n(r, n - take, args + take);   /* over-application */
}
lean_object *lean_apply_1(lean_object *f, lean_object *a) { lean_object *v[1] = {a}; return lean_apply_n(f, 1, v); }
lean_object *lean_apply_2(lean_object *f, lean_object *a, lean_object *b) { lean_object *v[2] = {a, b}; return lean_apply_n(f, 2, v); }
lean_object *lean_apply_3(lean_object *f, lean_object *a, lean_object *b, lean_object *c) { lean_object *v[3] = {a, b, c}; return lean_apply_n(f, 3, v); }
lean_object *lean_apply_4(lean_object *f, lean_object *a, lean_object *b, lean_object *c, lean_object *d) { lean_object *v[4] = {a, b, c, d}; return lean_apply_n(f, 4, v); }

/* Array -> List (List.cons = ctor 1 with 2 fields, List.nil = box 0). */
lean_object *lean_array_to_list(lean_object *a) {
  lean_object *r = lean_box(0);
  for (size_t i = lean_array_size(a); i-- > 0; ) {
    lean_object *x = lean_array_cptr(a)[i]; lean_inc(x);
    lean_object *c = lean_alloc_ctor(1, 2, 0); lean_ctor_set(c, 0, x); lean_ctor_set(c, 1, r); r = c;
  }
  lean_dec(a); return r;
}
/* ByteArray.copySlice (src borrowed, dest owned), as the C++ runtime defines it. */
lean_object *lean_byte_array_copy_slice(lean_object *src, lean_object *o_so, lean_object *dest, lean_object *o_do, lean_object *o_len, uint8_t exact) {
  size_t ssz = lean_sarray_size(src), dsz = lean_sarray_size(dest);
  size_t so = (lean_is_scalar(o_so) && lean_unbox(o_so) < ssz) ? lean_unbox(o_so) : ssz;
  size_t len = (lean_is_scalar(o_len) && lean_unbox(o_len) < ssz - so) ? lean_unbox(o_len) : ssz - so;
  size_t dof = (lean_is_scalar(o_do) && lean_unbox(o_do) < dsz) ? lean_unbox(o_do) : dsz;
  size_t nsz = dof + len > dsz ? dof + len : dsz;
  lean_object *r = dest;
  if (!lean_is_exclusive(dest) || nsz > lean_sarray_capacity(dest)) {
    r = lean_alloc_sarray(1, dsz, exact ? nsz : 2 * nsz);
    for (size_t i = 0; i < dsz; i++) lean_sarray_cptr(r)[i] = lean_sarray_cptr(dest)[i];
    lean_dec(dest);
  }
  lean_to_sarray(r)->m_size = nsz;
  uint8_t *d = lean_sarray_cptr(r) + dof, *s = lean_sarray_cptr(src) + so;
  if (d < s) for (size_t i = 0; i < len; i++) d[i] = s[i]; else for (size_t i = len; i-- > 0; ) d[i] = s[i];
  return r;
}
/* Array.ofFn: generated from Init/Data/Array/Basic.lean (core/), no longer hand-written here. */


/* ======================= SILICON I/O TAIL (replaces runtime/rt.c lines 223-267) ======================= */
#include "pqx.h"
uint32_t pq_mode(lean_object *u);
static void puts_(const char *s) { while (*s) bench_putc(*s++); }
static void putu(uint32_t v) { char b[11]; int i = 10; b[i] = 0; do { b[--i] = '0' + v % 10; v /= 10; } while (v); puts_(&b[i]); }
static void pq_halt(uint32_t code) { bench_halt(code); }
lean_object *pq_putc(uint32_t c) { bench_putc((char)c); return lean_box(0); }
void pq_sh_puts(const char *s) { puts_(s); }
void pq_sh_putu(uint32_t v) { putu(v); }
void pq_fatal(uint32_t code) { pq_halt(code); }
static void pq_oom_report(uint32_t rs, uint32_t b) { puts_("OOM req="); putu(rs); puts_(" bump="); putu(b); puts_(" live="); putu(pq_live); }
void pq_fault_handler(void) { pq_halt(0xFA); }

/* ---- Optional clock raise (-DCLK160): MSIS 4 MHz -> PLL1 160 MHz, VOLATILE RCC/PWR writes only, secure aliases.
 * Same register values as OpenOCD's stm32u5x_clock_config EXCEPT that FLASH_ACR is NOT written (code, data and
 * vector table are all in SRAM; nothing fetches from flash while the PLL runs). Everything is restored to the saved
 * entry values before bench_run returns; any system reset also undoes it. */
#define REG(a) (*(volatile uint32_t *)(a))
#define RCC_S 0x56020C00u
#define PWR_S 0x56020800u
#if defined(CLK160) && !defined(QEMU)
static uint32_t sv_ahb3, sv_pllcfgr, sv_plldivr, sv_vosr, sv_cr, sv_cfgr1;
static void spin_until(uint32_t addr, uint32_t mask, uint32_t want, uint32_t code) {
  for (uint32_t i = 0; i < 20000000u; i++) if ((REG(addr) & mask) == want) return;
  pq_halt(code);
}
#ifndef CLK_ENABLE
#define CLK_ENABLE 1
#endif
static volatile uint32_t pq_clk_enable = CLK_ENABLE;   /* runtime switch: same code layout at 4 MHz and 160 MHz */
static uint32_t clk_on;
static void clock_up(void) {
  if (!pq_clk_enable) return;
  clk_on = 1;
  sv_ahb3 = REG(RCC_S + 0x94); sv_pllcfgr = REG(RCC_S + 0x28); sv_plldivr = REG(RCC_S + 0x34);
  sv_vosr = REG(PWR_S + 0x0C); sv_cr = REG(RCC_S + 0x00); sv_cfgr1 = REG(RCC_S + 0x1C);
  PQX.clk_saved_cfgr1 = sv_cfgr1;
  if ((sv_cfgr1 & 0xFu) != 0 || (sv_cr & 0x01000000u)) pq_halt(0xE0);   /* not MSIS / PLL1 already on: do nothing */
  REG(RCC_S + 0x94) = sv_ahb3 | 0x4u; (void)REG(RCC_S + 0x94);          /* AHB3ENR.PWREN */
  REG(PWR_S + 0x0C) |= 0x00030000u; spin_until(PWR_S + 0x0C, 0x8000u, 0x8000u, 0xE1);   /* VOS range 1, VOSRDY */
  REG(RCC_S + 0x28) = 0x00040009u;                                       /* PLL1: src MSIS, M=/1, REN, MBOOST=/1 */
  REG(PWR_S + 0x0C) |= 0x00040000u; spin_until(PWR_S + 0x0C, 0x4000u, 0x4000u, 0xE2);   /* BOOSTEN, BOOSTRDY */
  REG(RCC_S + 0x34) = 0x0101024Fu;                                       /* N=80, P=Q=R=/2 -> 160 MHz */
  REG(RCC_S + 0x00) |= 0x01000000u; spin_until(RCC_S + 0x00, 0x02000000u, 0x02000000u, 0xE3);   /* PLL1ON, PLL1RDY */
  REG(RCC_S + 0x1C) = (REG(RCC_S + 0x1C) & ~3u) | 3u; spin_until(RCC_S + 0x1C, 0xCu, 0xCu, 0xE4);  /* SW = PLL1 */
  PQX.clk_cfgr1 = REG(RCC_S + 0x1C); PQX.clk_pll1divr = REG(RCC_S + 0x34); PQX.clk_vosr = REG(PWR_S + 0x0C);
}
static void clock_down(void) {
  if (!clk_on) return;
  REG(RCC_S + 0x1C) &= ~3u; spin_until(RCC_S + 0x1C, 0xCu, 0x0u, 0xE5);          /* SW = MSIS */
  REG(RCC_S + 0x00) &= ~0x01000000u; spin_until(RCC_S + 0x00, 0x02000000u, 0, 0xE6);  /* PLL1 off */
  REG(RCC_S + 0x34) = sv_plldivr; REG(RCC_S + 0x28) = sv_pllcfgr;
  REG(PWR_S + 0x0C) &= ~0x00040000u;                                                /* BOOSTEN off */
  REG(PWR_S + 0x0C) = sv_vosr;                                                      /* VOS back */
  PQX.clk_rest_cfgr1 = REG(RCC_S + 0x1C); PQX.clk_rest_vosr = REG(PWR_S + 0x0C);
  REG(RCC_S + 0x94) = sv_ahb3;
}
#else
static void clock_up(void) {}
static void clock_down(void) {}
#endif

#ifndef STACK_PAINT
#define STACK_PAINT (60 * 1024)
#endif
extern lean_object *lean_fw_main(lean_object *unit);
lean_object *pq_mark(uint32_t k);
void pq_store_nkeccak(void);
extern lean_object *PQ_INIT(uint8_t builtin);
void bench_run(void) {
  for (uint32_t i = 0; i < sizeof(pqx_t) / 4; i++) ((volatile uint32_t *)&PQX)[i] = 0;
  PQX.magic = PQX_MAGIC; PQX.mode = pq_mode(lean_box(0));
  clock_up();
  /* Stack high-water: paint STACK_PAINT bytes below the current SP (inside the 64 KiB MSPLIM-guarded stack). */
  uint32_t sp0; __asm__ volatile("mov %0, sp" : "=r"(sp0));
  for (volatile uint32_t *w = (uint32_t *)(sp0 - 256); w > (uint32_t *)(sp0 - STACK_PAINT); w--) *w = 0xDEADBEEFu;
  uint64_t t0 = pq_cyc64();
  lean_object *r = PQ_INIT(1); if (lean_io_result_is_error(r)) pq_halt(0xD0); lean_dec_ref(r);
  uint64_t t1 = pq_cyc64();
  uint32_t base = pq_live;
  uint32_t a0 = pq_allocs, f0 = pq_frees; pq_peak = pq_live;
  uint64_t t2 = pq_cyc64();
  lean_fw_main(lean_box(0));
  pq_mark(0xFFFF);
  uint64_t t3 = pq_cyc64();
  PQX.init_lo = (uint32_t)(t1 - t0); PQX.init_hi = (uint32_t)((t1 - t0) >> 32);
  PQX.main_lo = (uint32_t)(t3 - t2); PQX.main_hi = (uint32_t)((t3 - t2) >> 32);
  pq_store_nkeccak();
  uint32_t nonzero = 0, freeb = 0;
  for (uint32_t off = 0; off < bump; ) { uint32_t w = *(uint32_t *)(arena + off), rs = w & ~1u;
    if (w & 1) { freeb += rs; for (uint32_t i = 0; i < rs; i++) nonzero += arena[off + 8 + i] != 0; }
    off += rs + 8; }
  uint32_t *w = (uint32_t *)(sp0 - STACK_PAINT + 4); while (w < (uint32_t *)(sp0 - 256) && *w == 0xDEADBEEFu) w++;
  PQX.arena[0] = base; PQX.arena[1] = pq_allocs - a0; PQX.arena[2] = pq_frees - f0; PQX.arena[3] = pq_live - base;
  PQX.arena[4] = pq_peak; PQX.arena[5] = freeb; PQX.arena[6] = nonzero; PQX.arena[7] = bump; PQX.arena[8] = ARENA_BYTES;
  PQX.arena[9] = sp0 - (uint32_t)w;
  clock_down();
}
