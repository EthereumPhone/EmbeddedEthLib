#!/usr/bin/env bash
# build.sh <linker.ld> <out.elf> [gcc args]: the board variant of ../sphincs/build.sh.
#
# Same compiler, flags and Lean-generated C as the QEMU build. Replaced for the board: runtime/rt.c ->
# rt_silicon.c (runtime/rt.c lines 1-222 verbatim, then the board I/O tail and the optional -DCLK160 clock
# raise), sphincs/bench_io.c -> bench_io_silicon.c (64-bit DWT marks into the PQX block, pqx.h). Added:
# ../board/startup.c (entry, VTOR_S, .bss zeroing, DWT enable) and a linker --wrap of the Keccak-256 that
# every caller of keccak256 reaches through the @[csimp], so the 32-bit cycle counter is sampled often enough.
#
# Board image:  ./build.sh ../board/link_sram.ld out/m0.elf -DPQ_MODE=0 -DARENA_BYTES=393216 -DCLK160
# QEMU twin:    ./build.sh link_qemu_twin.ld out/q0.elf -DQEMU -DBENCH_RESULTS_ADDR=0x38000000u -DPQ_MODE=0
# Other bench entries (BENCH=...) work too, for example the SHA-256 one that ../sha256/build.sh writes.
set -euo pipefail
[ $# -ge 2 ] || { echo "usage: $0 <linker.ld> <out.elf> [gcc args...]" >&2; exit 2; }
LD="$1"; OUT="$2"; shift 2
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"; EMB="$(cd "$HERE/.." && pwd)"; BD="$EMB/board"
KSYM=lp_EthLib_EthLib_Cryptography_Hash_Keccak_Fast_keccak256IG
RT="$HERE/rt_silicon.c" BENCH_IO="$HERE/bench_io_silicon.c" \
  exec "$EMB/sphincs/build.sh" "$LD" "$OUT" -I"$HERE" -I"$BD" "$BD/startup.c" -Wl,--wrap=$KSYM "$@"
