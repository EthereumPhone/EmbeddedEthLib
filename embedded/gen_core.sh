#!/usr/bin/env bash
# gen_core.sh [outdir]: regenerate the C of the Lean core (Init) modules that the EthLib C calls.
# The Lean toolchain ships these modules compiled into libInit.a for the host only, so a freestanding
# Cortex-M33 image compiles them from the toolchain's own sources with `lean -c`. The output depends
# only on the toolchain (checked: byte-identical across runs). Default outdir: runtime/core.
set -euo pipefail
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO="$(cd "$HERE/.." && pwd)"
TC="${TC:-$(cd "$REPO" && lean --print-prefix)}"
OUTDIR="$(realpath -m "${1:-$HERE/runtime/core}")"; mkdir -p "$OUTDIR"
MODS=(Init/Prelude Init/Data/Array/Basic Init/Data/Array/DecidableEq Init/Data/Fin/Basic
      Init/Data/List/Basic Init/Data/List/Impl Init/Data/UInt/BasicAux)
cd "$TC/src/lean"
for m in "${MODS[@]}"; do
  n="$(echo "$m" | tr / _)"
  [ -f "$OUTDIR/$n.c" ] && continue
  LEAN_PATH="$TC/lib/lean" "$TC/bin/lean" --root=. -c "$OUTDIR/$n.c" "$m.lean"
done
echo "core C in $OUTDIR"
