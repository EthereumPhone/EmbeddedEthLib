/* Runtime functions that Lean 4.35 generated C needs beyond rt.c (normally in the C++ runtime).
 * Big Nat: on 32-bit, a Nat >= 2^31 is a heap object. Here it is a LeanMPZ-tagged object holding one
 * uint64_t, so every Nat below 2^64 works; any result >= 2^64 halts loudly (code 0xF0..). leanSPHINCS
 * only needs this for MAX_COUNTER_TRIALS = 2^32 (the signer's counter fuel) and UInt32/UInt64 -> Nat. */
#include <stdint.h>
#include <stddef.h>
#include <lean/lean.h>
void pq_fatal(uint32_t code);
void pq_sh_puts(const char *s);

typedef struct { lean_object hdr; uint32_t pad; uint64_t v; } pq_bignat;
static lean_object *mk_nat64(uint64_t v) {
  if (v <= LEAN_MAX_SMALL_NAT) return lean_box((size_t)v);
  pq_bignat *o = (pq_bignat *)lean_alloc_small_object(sizeof(pq_bignat));
  lean_set_st_header((lean_object *)o, LeanMPZ, 0); o->pad = 0; o->v = v; return (lean_object *)o;
}
static uint64_t nat64(b_lean_obj_arg a) {
  if (lean_is_scalar(a)) return lean_unbox(a);
  if (lean_ptr_tag(a) != LeanMPZ) pq_fatal(0xF1);
  return ((pq_bignat *)a)->v;
}
lean_object *lean_nat_big_succ(lean_object *a) { uint64_t x = nat64(a); if (x == UINT64_MAX) pq_fatal(0xF0); lean_object *r = mk_nat64(x + 1); lean_dec(a); return r; }
lean_object *lean_nat_big_add(lean_object *a, lean_object *b) { uint64_t x = nat64(a), y = nat64(b); if (x + y < x) pq_fatal(0xF0); return mk_nat64(x + y); }
lean_object *lean_nat_big_sub(lean_object *a, lean_object *b) { uint64_t x = nat64(a), y = nat64(b); return mk_nat64(x < y ? 0 : x - y); }
lean_object *lean_nat_big_mul(lean_object *a, lean_object *b) { uint64_t x = nat64(a), y = nat64(b); if (y && x > UINT64_MAX / y) pq_fatal(0xF0); return mk_nat64(x * y); }
lean_object *lean_nat_big_div(lean_object *a, lean_object *b) { uint64_t x = nat64(a), y = nat64(b); return mk_nat64(y ? x / y : 0); }
lean_object *lean_nat_big_mod(lean_object *a, lean_object *b) { uint64_t x = nat64(a), y = nat64(b); return mk_nat64(y ? x % y : x); }
lean_object *lean_nat_big_xor(lean_object *a, lean_object *b) { return mk_nat64(nat64(a) ^ nat64(b)); }
lean_object *lean_nat_big_shiftr(lean_object *a, lean_object *b) { uint64_t x = nat64(a), y = nat64(b); return mk_nat64(y >= 64 ? 0 : x >> y); }
lean_object *lean_nat_overflow_mul(size_t a, size_t b) { return mk_nat64((uint64_t)a * (uint64_t)b); }
bool lean_nat_big_eq(lean_object *a, lean_object *b) { return nat64(a) == nat64(b); }
bool lean_nat_big_lt(lean_object *a, lean_object *b) { return nat64(a) < nat64(b); }
bool lean_nat_big_le(lean_object *a, lean_object *b) { return nat64(a) <= nat64(b); }
uint64_t lean_uint64_of_big_nat(lean_object *a) { return nat64(a); }
uint32_t lean_uint32_of_big_nat(lean_object *a) { return (uint32_t)nat64(a); }
uint8_t lean_uint8_of_big_nat(lean_object *a) { return (uint8_t)nat64(a); }
lean_object *lean_big_usize_to_nat(size_t n) { return mk_nat64(n); }
lean_object *lean_big_uint64_to_nat(uint64_t n) { return mk_nat64(n); }
lean_object *lean_cstr_to_nat(const char *s) {
  uint64_t v = 0;
  for (; *s; s++) { uint64_t d = (uint64_t)(*s - '0'); if (d > 9 || v > (UINT64_MAX - d) / 10) pq_fatal(0xF2); v = v * 10 + d; }
  return mk_nat64(v);
}
lean_object *lean_nat_pow(lean_object *a, lean_object *b) {
  uint64_t x = nat64(a), e = nat64(b), r = 1;
  while (e--) { if (x && r > UINT64_MAX / x) pq_fatal(0xF0); r *= x; }
  return mk_nat64(r);
}

/* Arrays and scalar arrays. */
lean_object *lean_copy_expand_array(lean_object *a, bool expand);
lean_object *lean_copy_expand_array_nonlinear(lean_object *a, bool expand) { return lean_copy_expand_array(a, expand); }
lean_object *lean_copy_sarray_nonlinear(lean_object *a, size_t cap) {
  size_t sz = lean_sarray_size(a), es = lean_sarray_elem_size(a);
  lean_object *r = lean_alloc_sarray(es, sz, cap);
  uint8_t *d = lean_sarray_cptr(r), *s = lean_sarray_cptr(a);
  for (size_t i = 0; i < sz * es; i++) d[i] = s[i];
  lean_dec(a); return r;
}
bool lean_sarray_eq_cold(lean_object *a, lean_object *b) {
  size_t n = lean_sarray_size(a) * lean_sarray_elem_size(a); uint8_t *x = lean_sarray_cptr(a), *y = lean_sarray_cptr(b);
  for (size_t i = 0; i < n; i++) if (x[i] != y[i]) return false;
  return true;
}
/* List α -> Array α (List.cons = ctor 1, fields head, tail). */
lean_object *lean_array_mk(lean_object *l) {
  size_t n = 0; for (lean_object *p = l; !lean_is_scalar(p); p = lean_ctor_get(p, 1)) n++;
  lean_object *r = lean_alloc_array(n, n); size_t i = 0;
  for (lean_object *p = l; !lean_is_scalar(p); p = lean_ctor_get(p, 1)) { lean_object *x = lean_ctor_get(p, 0); lean_inc(x); lean_array_cptr(r)[i++] = x; }
  lean_dec(l); return r;
}
/* String.data: UTF-8 -> List Char (Char boxed as uint32, as lean.h does on 32-bit). */
lean_object *lean_string_data(lean_object *s) {
  const uint8_t *p = (const uint8_t *)lean_string_cstr(s); size_t n = lean_string_size(s) - 1;
  uint32_t cps[256]; size_t k = 0;
  for (size_t i = 0; i < n; ) {
    uint8_t c = p[i]; uint32_t cp; size_t len;
    if (c < 0x80) { cp = c; len = 1; } else if ((c & 0xE0) == 0xC0) { cp = c & 0x1F; len = 2; }
    else if ((c & 0xF0) == 0xE0) { cp = c & 0x0F; len = 3; } else { cp = c & 0x07; len = 4; }
    for (size_t j = 1; j < len; j++) cp = (cp << 6) | (p[i + j] & 0x3F);
    if (k == 256) pq_fatal(0xF3);
    cps[k++] = cp; i += len;
  }
  lean_object *r = lean_box(0);
  while (k--) { lean_object *c = lean_alloc_ctor(1, 2, 0); lean_ctor_set(c, 0, lean_box_uint32(cps[k])); lean_ctor_set(c, 1, r); r = c; }
  lean_dec(s); return r;
}

/* Lean 4.35 module initialisers call this; Init's runtime part has nothing our code uses. */
lean_object *runtime_initialize_Init(uint8_t builtin) { (void)builtin; return lean_io_result_mk_ok(lean_box(0)); }
