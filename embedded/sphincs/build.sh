#!/usr/bin/env bash
# build.sh <linker-script.ld> <out.elf> [extra gcc args, e.g. -DPQ_MODE=1 -DARENA_BYTES=393216 -DPQ_TIMER]
#
# Cross-compiles this repository's leanSPHINCS (the Lean 4.35.0 C that `lake build` writes to
# .lake/build/ir) together with a benchmark entry (BENCH, default sphincs/SphincsBench.lean), the freestanding arena runtime and the known-answer
# vectors for a Cortex-M33, and links them with the given linker script. The script must place
# FLASH/RAM and define __data_start__/__data_end__/__data_load__/__bss_start__/__bss_end__ and the
# vector table (initial SP, Reset_Handler), as runtime/link_qemu.ld does.
#
# Needs: `lake build EthLib.Cryptography.Sphincs` at the repository root (or at $ETH), arm-none-eabi-gcc.
# Env: ETH (EthLib checkout, default this repository), TC (Lean toolchain prefix, default
#      `lean --print-prefix`), MODULES (file listing the EthLib modules to link; default: the import
#      closure of SphincsBench.lean), RT (runtime C file, default runtime/rt.c), BENCH_IO (default
#      sphincs/bench_io.c), WORK (directory for generated C, default next to out.elf).
set -euo pipefail
[ $# -ge 2 ] || { echo "usage: $0 <linker.ld> <out.elf> [gcc args...]" >&2; exit 2; }
LD="$(realpath "$1")"; OUT="$(realpath -m "$2")"; shift 2
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
EMB="$(cd "$HERE/.." && pwd)"
ETH="$(realpath "${ETH:-$EMB/..}")"
TC="${TC:-$(cd "$ETH" && lean --print-prefix)}"
IR="$ETH/.lake/build/ir"
WORK="$(realpath -m "${WORK:-$(dirname "$OUT")/gen}")"; mkdir -p "$WORK"
# The benchmark entry's C, against this checkout's .olean files.
BENCH="$(realpath "${BENCH:-$HERE/SphincsBench.lean}")"; NAME="$(basename "$BENCH" .lean)"
LEAN_PATH="$ETH/.lake/build/lib/lean:$TC/lib/lean" "$TC/bin/lean" --root="$(dirname "$BENCH")" -c "$WORK/$NAME.c" "$BENCH"
# The known answers of tests/cryptography/sphincs, as one volatile blob.
python3 "$HERE/genvec.py" "$ETH/tests/cryptography/sphincs" "$WORK/vec.c" > "$WORK/vec.txt"
# The Lean core C (generated once from the toolchain's sources).
[ -d "$EMB/runtime/core" ] || "$EMB/gen_core.sh" "$EMB/runtime/core" > /dev/null
if [ -z "${MODULES:-}" ]; then
  python3 "$EMB/tools/closure.py" "$ETH" "$BENCH" > "$WORK/modules.txt" 2> /dev/null
  MODULES="$WORK/modules.txt"
fi
SRCS=("$WORK/$NAME.c" "${RT:-$EMB/runtime/rt.c}" "$EMB/runtime/rt_ext.c" "$EMB/runtime/compat.c" "$EMB/runtime/kshim.c"
      "${BENCH_IO:-$HERE/bench_io.c}" "$WORK/vec.c")
while read -r m; do [ -n "$m" ] && SRCS+=("$IR/$(echo "$m" | tr . /).c"); done < "$MODULES"
for f in "$EMB"/runtime/core/*.c; do SRCS+=("$f"); done
# -DNDEBUG is essential: without it lean.h's assertions stay in and every object operation is checked.
CF=(-mcpu=cortex-m33 -mthumb -O2 -DNDEBUG -DLEAN_EMSCRIPTEN -ffunction-sections -fdata-sections -ffreestanding
    -nostdlib -I"$TC/include" -w -DPQ_INIT=initialize_$NAME)
arm-none-eabi-gcc "${CF[@]}" "$@" -T "$LD" -Wl,--gc-sections -Wl,--no-warn-rwx-segments -Wl,-Map="${OUT%.elf}.map" \
  "${SRCS[@]}" -lgcc -o "$OUT"
arm-none-eabi-size "$OUT"
