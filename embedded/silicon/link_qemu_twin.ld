/* QEMU mps2-an505 twin of ../board/link_sram.ld (instruction counting only; -DQEMU -DBENCH_RESULTS_ADDR=0x38000000).
 * Same as ../board/qemu/link_qemu.ld but with 0x400 of results (bench.h block + PQX) and a 4 MiB RAM window. */
MEMORY { VEC : ORIGIN = 0x10000000, LENGTH = 0x400
         RESULTS : ORIGIN = 0x38000000, LENGTH = 0x400
         RAM : ORIGIN = 0x38000400, LENGTH = 0x400000 - 0x400 }
STACK_SIZE = 0x10000;
ENTRY(_start)
SECTIONS {
  .qvec : { LONG(__stack_top) LONG(_start | 1) } > VEC
  .results (NOLOAD) : { . = . + 0x400; } > RESULTS
  .vtable  : { KEEP(*(.vtable)) } > RAM
  .text    : { KEEP(*(.entry)) *(.text*) *(.rodata*) . = ALIGN(8); } > RAM
  .data    : { *(.data*) . = ALIGN(8); } > RAM
  .bss (NOLOAD) : { . = ALIGN(8); __bss_start__ = .; *(.bss*) *(COMMON) . = ALIGN(8); __bss_end__ = .; } > RAM
  __stack_top = ORIGIN(RAM) + LENGTH(RAM);
  __stack_limit = __stack_top - STACK_SIZE;
  /DISCARD/ : { *(.ARM.exidx*) *(.ARM.extab*) }
}
