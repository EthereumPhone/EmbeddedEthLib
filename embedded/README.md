# Cortex-M33 tooling

This directory reproduces the Cortex-M33 measurements in [`../EMBEDDED.md`](../EMBEDDED.md).
It cross-compiles the C that `lake build` writes for this repository (`.lake/build/ir`), links it with a small freestanding Lean runtime, and runs it on QEMU's `mps2-an505` (a Cortex-M33) or from the secure SRAM of an STM32U585.
Nothing here is part of the Lean library, and nothing here is proved.

| path | what |
|---|---|
| `runtime/rt.c` | the Lean runtime for a bare Cortex-M33: one static arena with exact-size free lists, every freed object wiped, a stack painter, and an arena and leak report after the run |
| `runtime/rt_ext.c` | runtime functions the generated C needs beyond `rt.c`: big `Nat` as one `uint64_t` (any result of 2^64 or more halts), `Array`/`ByteArray` helpers, a no-op `Init` initialiser |
| `runtime/compat.c` | the Lean 4.35 allocator entry points (`lean_alloc_small_object_core`, `mi_malloc`) routed to the arena |
| `runtime/kshim.c` | `lean_usize_of_big_nat`, unreachable on a 32-bit target (a byte offset of 2^31 or more cannot index a `ByteArray`), halts if reached |
| `runtime/link_qemu.ld` | QEMU `mps2-an505` memory map |
| `gen_core.sh` | writes `runtime/core/*.c`, the C of the seven Lean core (`Init`) modules the EthLib C calls, from the toolchain's own sources with `lean -c` |
| `sphincs/` | the leanSPHINCS benchmark: `SphincsBench.lean` (entry), `bench_io.c` (inputs, marks, reports, optional Keccak call counter and per-segment arena peaks), `genvec.py` (embeds the known answers of `tests/cryptography/sphincs`), `build.sh` |
| `sha256/` | the SHA-256 benchmark: `ShaBench.lean.in`, `build.sh fast|spec`, and `ref.c`, a plain C SHA-256 for comparison |
| `tools/` | `count_run.sh` and `count_seg.py` (exact instruction counts per segment from a QEMU trace), `count.py` (one total), `prof.py` (instructions per function), `closure.py` (the EthLib modules a Lean file imports), `hashcount.py` (hash-call model of the specification's leanSPHINCS) |
| `board/` | the STM32U585 SRAM runner: `run_on_board.sh`, `startup.c`, `bench.h`, `link_sram.ld`, the calibration program `calib/calib.c`, and `sha/ref_board.c`, the C SHA-256 on the board |
| `silicon/` | the board build of the benchmarks: `build.sh`, `rt_silicon.c`, `bench_io_silicon.c`, `pqx.h`, `decode.py`, `link_qemu_twin.ld`, `clkctl/clkwrap.c` |
| `hosttest/` | a host executable that checks the fork's compiled code against the SHA-256, Keccak and leanSPHINCS vectors in `tests/cryptography` |
| `gen/keccak/` | the generators of `EthLib/Cryptography/Hash/Keccak/Fast.lean` and of the `FastProofI` proofs |

## Requirements

- The Lean toolchain of `lean-toolchain` (elan installs it), and the library modules built at the repository root, for example `lake build EthLib.Cryptography.Sphincs EthLib.Cryptography.Hash.Sha256`. The scripts find the toolchain with `lean --print-prefix`; set `TC` to override it, and `ETH` to use another EthLib checkout.
- `arm-none-eabi-gcc` (13.2 was used) and `qemu-system-arm` with the `mps2-an505` machine.
- `python3`.
- For the board: an STM32U585 board with an ST-LINK (a B-U585I-IOT02A was used), and OpenOCD with `stm32u5x.cfg`.

`build.sh` writes its generated C next to the output ELF (`gen/` there), and `runtime/core/` on its first run.
Both are ignored by git.

## leanSPHINCS on QEMU

```bash
lake build EthLib.Cryptography.Sphincs
mkdir -p out
embedded/sphincs/build.sh embedded/runtime/link_qemu.ld out/v.elf
qemu-system-arm -M mps2-an505 -nographic -semihosting -kernel out/v.elf
```

The verify-mode output must read:

```text
R 1 1
R 2 0
R 3 590e9206cebee6ae6b9a1a525b441e6ab7ef4e0a387048525388e9b997552c60
R 4 944ec2ca5ab502b8f7f6ccb3beddce80
R 5 b29add900c2965efa4d53f790d3016b8
R 6 271601342e875ad39473283d6bfb78b6
R 7 fe25d7dc2a09b5b93472638154b3ebbb
R 8 586644c735115483b821557411b5dae8
R 9 0
```

`R 1 1` is the known-answer signature verifying, `R 2 0` the same signature with its last bit flipped failing, and `R 3` to `R 8` are digests of the isolated pieces.
After them, `rt.c` prints the stack depth and the arena report (`nonzero_in_freed=0` means every freed byte was wiped).

Exact instruction counts per segment (the segments are the `mark` calls in `SphincsBench.lean`):

```bash
embedded/tools/count_run.sh out/v.elf
```

Signing and key generation execute billions of instructions, too many to trace.
Build them with the instruction timer and run QEMU in instruction-counting mode, where one tick is 50 instructions:

```bash
embedded/sphincs/build.sh embedded/runtime/link_qemu.ld out/sign.elf -DPQ_TIMER -DPQ_MODE=1
qemu-system-arm -M mps2-an505 -nographic -semihosting -icount shift=0 -kernel out/sign.elf
```

`PQ_MODE=1` signs and compares with the known-answer signature (`R 10 1`), and `PQ_MODE=2` generates the key and compares with the known-answer public key (`R 11 1`).
Two more switches:

- `-DPQ_KCOUNT -Wl,--wrap=lp_EthLib_EthLib_Cryptography_Hash_Keccak_Fast_keccak256IG` counts Keccak-256 calls per segment. Every caller of `keccak256` calls `Keccak.Fast.keccak256IG` through the `@[csimp]`, so this is the symbol to wrap. A signature of the known answer makes 485,244 calls.
- `-DPQ_SEGPEAK` prints the arena peak of each segment. In sign mode, segment 1 to 3 is signing and 3 to 2 is `encodeSignature`.

## SHA-256 on QEMU

```bash
lake build EthLib.Cryptography.Hash.Sha256
embedded/sha256/build.sh fast embedded/runtime/link_qemu.ld out/sha_fast.elf
embedded/sha256/build.sh spec embedded/runtime/link_qemu.ld out/sha_spec.elf
embedded/tools/count_run.sh out/sha_fast.elf
embedded/tools/count_run.sh out/sha_spec.elf
```

`fast` imports `EthLib.Cryptography.Hash.Sha256`, so the `@[csimp]` compiles `Sha256.hash` to the zero-allocation form.
`spec` imports only `EthLib.Cryptography.Hash.Sha256.Spec`, so the same source calls the compiled specification.
Segment 1 hashes 3 bytes, segment 2 64 bytes, segment 3 1,072 bytes, and segment 4 ten 64-byte messages.
Both builds must print the same four `R` lines; Python's `hashlib` gives the same digests for the same bytes of the known-answer blob.

The C reference, `ref.c`, hashes `NHASH` 3-byte messages; the instructions per hash are the difference of two counts divided by 10:

```bash
for N in 1 11; do
  arm-none-eabi-gcc -mcpu=cortex-m33 -mthumb -O2 -ffreestanding -nostdlib -DNHASH=$N \
    -T embedded/sha256/link_ref.ld -Wl,--no-warn-rwx-segments embedded/sha256/ref.c -lgcc -o out/ref$N.elf
  qemu-system-arm -M mps2-an505 -nographic -semihosting -kernel out/ref$N.elf -d in_asm,exec,nochain -D out/ref$N.log
  python3 embedded/tools/count.py out/ref$N.log
done
```

## Compiler flags, and the debug-build trap

The builds use `-mcpu=cortex-m33 -mthumb -O2 -DNDEBUG -DLEAN_EMSCRIPTEN -ffunction-sections -fdata-sections -ffreestanding -nostdlib` and link with `--gc-sections`.

- `-DNDEBUG` is essential. Without it `lean.h` keeps its assertions, and every reference-count and object access is checked. Measured with `sha256/build.sh` and `-UNDEBUG`: the specification's SHA-256 executes 2.0 to 3.1 times as many instructions (3 bytes: 20,162 to 40,408; 1,072 bytes: 152,468 to 474,966), and the zero-allocation form 1.06 to 1.33 times as many. A measurement without the flag says little about the code.
- `-DLEAN_EMSCRIPTEN` selects `lean.h`'s 32-bit paths that need no C++ runtime.
- The generated C of a module calls Lean core functions (`Array.ofFn`, `List` helpers, `Init.Prelude`), which the toolchain ships compiled only for the host. `gen_core.sh` regenerates their C from the toolchain's sources. The output depends only on the toolchain.

## The STM32U585 SRAM runner

`board/run_on_board.sh <elf> <result_addr> <result_words> [timeout_s]` loads an image into the secure SRAM alias (0x30000000 to 0x300BFFFF), runs it, and reads a results block back over SWD.
It never writes flash, option bytes or OTP, and it ends every run, also on errors, with `reset run`, so the board boots its own firmware again.
It refuses an ELF with a loadable segment outside the SRAM range.

Writing a program for it: define `void bench_run(void)`; `startup.c` calls it with interrupts masked, a fresh stack and zeroed `.bss`.
Time with `bench_cyc()` (DWT_CYCCNT), and store results in `BENCH.user[]` (`bench.h`).
The results block starts with a status word: `DONE` when `bench_run` returned, a fault code with the exception number on a fault, and the poison value `0xDEADBEEF` when the program never wrote it.

```bash
arm-none-eabi-gcc -mcpu=cortex-m33 -mthumb -O2 -ffunction-sections -fdata-sections -ffreestanding -nostdlib \
  -Iembedded/board -T embedded/board/link_sram.ld -Wl,--gc-sections embedded/board/startup.c my.c -lgcc -o my.elf
embedded/board/run_on_board.sh my.elf 0x30000000 64 60
```

The Lean benchmarks build for the board with `silicon/build.sh`, which uses the same compiler, flags and generated C as the QEMU build.
It swaps `rt.c` for `rt_silicon.c` (the same allocator, with the board's I/O and an optional switch to 160 MHz) and `bench_io.c` for `bench_io_silicon.c` (each mark records a 64-bit DWT cycle stamp):

```bash
embedded/silicon/build.sh embedded/board/link_sram.ld out/m0.elf -DPQ_MODE=0 -DARENA_BYTES=393216 -DCLK160
embedded/board/run_on_board.sh out/m0.elf 0x30000000 256 600
python3 embedded/silicon/decode.py out/m0.elf.openocd.log
```

`BUILDER=embedded/silicon/build.sh embedded/sha256/build.sh fast embedded/board/link_sram.ld out/sha.elf` builds the SHA-256 benchmark for the board the same way.
The QEMU twin of a board image (`silicon/link_qemu_twin.ld` with `-DQEMU -DBENCH_RESULTS_ADDR=0x38000000u`) runs the same sources under QEMU, for instruction counts.

What was learned building the runner:

- OpenOCD's default work area for this target lies in the non-secure alias of the same SRAM, and `verify_image` ran its CRC routine there, over the results block. The runner sets the work-area size to 0. Do not re-enable it.
- OpenOCD steps over a `bkpt` at the resume address, so a program cannot start with one.
- `reset init` runs OpenOCD's clock configuration. The runner uses `reset halt` only.
- DWT_CYCCNT is 32 bits wide. `bench_io_silicon.c` extends it in software at every mark and at every Keccak-256 call (the linker `--wrap` in `silicon/build.sh`), which is sound while no stretch between two samples exceeds 2^32 cycles.
- At the reset clock (4 MHz) a signature takes hours. `-DCLK160` raises the clock to 160 MHz with volatile RCC and PWR writes only, and restores it before `bench_run` returns; a reset undoes it anyway. SRAM has no wait states, so the cycle counts do not depend on the clock: the two clocks agreed to within 0.03 % on the same image.
- These are SRAM-resident numbers: no flash wait states and no instruction cache. Code run from flash will have a different cycles-per-instruction ratio.
- Debug state (DHCSR.C_DEBUGEN, DEMCR.TRCENA, DWT_CTRL.CYCCNTENA) survives `reset run` until a power-on reset. It is harmless to flash.

`calib/calib.c` times known instruction sequences: an ALU instruction takes 1 cycle, a load from SRAM 2, and a taken branch 2.

## Host test

```bash
cd embedded/hosttest
lake build hosttest
.lake/build/bin/hosttest            # add --no-sign to skip the five signatures
```

It shares the repository's resolved dependencies (`packagesDir`), so it downloads nothing.
It checks every SHA-256 vector through six paths (`Hash.sha256`, `Sha256.hash`, `Sha256.hash32`, and `Sha256.Zsf.hashInto` with a fresh, an empty and a reused buffer), every Keccak-256, Keccak-512 and Keccak-f[1600] vector, and every leanSPHINCS key generation, signing and verification vector.
It calls the library functions, which the C exports wrap, because loading the Exports shared library as a plugin while elaborating the test failed with an undefined symbol (`lp_EthLib_EthLib_Base_ChainConfig_mainnet`), which was not investigated.
