/* QEMU mps2-an505: code in secure SSRAM1 alias (4 MB), data+arena+stack in secure SSRAM2/3 alias (4 MB). */
MEMORY { FLASH : ORIGIN = 0x10000000, LENGTH = 4M
         RAM   : ORIGIN = 0x38000000, LENGTH = 4M }
ENTRY(Reset_Handler)
SECTIONS {
  .vectors : { LONG(ORIGIN(RAM) + LENGTH(RAM)) LONG(Reset_Handler | 1) LONG(pq_fault_handler | 1) LONG(pq_fault_handler | 1)
               LONG(pq_fault_handler | 1) LONG(pq_fault_handler | 1) LONG(pq_fault_handler | 1) } > FLASH  /* NMI, HardFault, MemManage, BusFault, UsageFault */
  .text    : { *(.text*) *(.rodata*) } > FLASH
  .data    : { __data_start__ = .; *(.data*) __data_end__ = .; } > RAM AT > FLASH
  __data_load__ = LOADADDR(.data);
  .bss     : { __bss_start__ = .; *(.bss*) *(COMMON) __bss_end__ = .; } > RAM
}
