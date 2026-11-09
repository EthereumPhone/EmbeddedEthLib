/* Linker script for the plain C SHA-256 reference (sha256/ref.c) on QEMU mps2-an505. */
MEMORY { FLASH : ORIGIN = 0x10000000, LENGTH = 512K
         RAM   : ORIGIN = 0x38000000, LENGTH = 128K }
ENTRY(Reset_Handler)
SECTIONS {
  .vectors : { LONG(ORIGIN(RAM) + LENGTH(RAM)) LONG(Reset_Handler | 1) } > FLASH
  .text    : { *(.text*) *(.rodata*) } > FLASH
  .data    : { __data_start__ = .; *(.data*) __data_end__ = .; } > RAM AT > FLASH
  __data_load__ = LOADADDR(.data);
  .bss     : { __bss_start__ = .; *(.bss*) *(COMMON) __bss_end__ = .; } > RAM
}

