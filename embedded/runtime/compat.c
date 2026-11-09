/* Lean >= 4.35 runtime-ABI shim for the arena runtime in rt.c (rt.c is unchanged).
   4.35 moved the small-object fast path out of lean.h into lean_alloc_small_object_core
   (mimalloc.cpp: heartbeat + mimalloc + set m_cs_sz) and added lean_initialize_runtime_module.
   This mirrors 4.32's inline path exactly: heartbeat call, same arena allocator, set m_cs_sz. */
#include <lean/lean.h>
void *mi_malloc_small(size_t sz);
lean_object *lean_alloc_small_object_core(unsigned sz) {
  lean_inc_heartbeat();
  lean_object *o = (lean_object *)mi_malloc_small(sz);
  o->m_cs_sz = sz;
  return o;
}
void lean_initialize_runtime_module(void) {}
/* With -DNDEBUG, 4.35's inline lean_alloc_small_object also references mi_malloc for objects above
   MI_SMALL_SIZE_MAX; route it to the same arena allocator (pq_alloc handles any size). */
void *mi_malloc(size_t sz) { return mi_malloc_small(sz); }
