#!/usr/bin/env bash
# build.sh <fast|spec|into> <linker-script.ld> <out.elf> [extra gcc args]
#
# Builds a SHA-256 benchmark entry against this repository's generated C: `fast` imports
# EthLib.Cryptography.Hash.Sha256 (the @[csimp] compiles Sha256.hash to the zero-allocation form),
# `spec` imports only EthLib.Cryptography.Hash.Sha256.Spec (the compiled specification), both from
# ShaBench.lean.in; `into` is ShaInto.lean, Sha256.Zsf.hashInto into one reused 32-byte buffer.
# Needs `lake build EthLib.Cryptography.Hash.Sha256` at the repository root. Env as for sphincs/build.sh,
# plus BUILDER (default ../sphincs/build.sh; ../silicon/build.sh builds the board image or its QEMU twin).
set -euo pipefail
[ $# -ge 3 ] || { echo "usage: $0 <fast|spec|into> <linker.ld> <out.elf> [gcc args...]" >&2; exit 2; }
V="$1"; shift
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
OUTDIR="$(dirname "$(realpath -m "$2")")"; GEN="$OUTDIR/gen-sha-$V"; mkdir -p "$GEN"
case "$V" in
  fast) IMP="import EthLib.Cryptography.Hash.Sha256"; NAME=ShaBench ;;
  spec) IMP="import EthLib.Cryptography.Hash.Sha256.Spec"; NAME=ShaBenchSpec ;;
  into) NAME=ShaInto ;;
  *) echo "variant must be fast, spec or into" >&2; exit 2 ;;
esac
if [ "$V" = into ]; then cp "$HERE/ShaInto.lean" "$GEN/$NAME.lean"
else sed "s|^@IMPORT@\$|$IMP|" "$HERE/ShaBench.lean.in" > "$GEN/$NAME.lean"; fi
BENCH="$GEN/$NAME.lean" WORK="$GEN" exec "${BUILDER:-$HERE/../sphincs/build.sh}" "$@"
