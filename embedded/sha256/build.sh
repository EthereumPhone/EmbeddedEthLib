#!/usr/bin/env bash
# build.sh <fast|spec> <linker-script.ld> <out.elf> [extra gcc args]
#
# Builds the SHA-256 benchmark entry against this repository's generated C: `fast` imports
# EthLib.Cryptography.Hash.Sha256 (the @[csimp] compiles Sha256.hash to the zero-allocation form),
# `spec` imports only EthLib.Cryptography.Hash.Sha256.Spec (the compiled specification).
# Needs `lake build EthLib.Cryptography.Hash.Sha256` at the repository root. Env as for sphincs/build.sh,
# plus BUILDER (default ../sphincs/build.sh; ../silicon/build.sh builds the board image or its QEMU twin).
set -euo pipefail
[ $# -ge 3 ] || { echo "usage: $0 <fast|spec> <linker.ld> <out.elf> [gcc args...]" >&2; exit 2; }
V="$1"; shift
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
OUTDIR="$(dirname "$(realpath -m "$2")")"; GEN="$OUTDIR/gen-sha-$V"; mkdir -p "$GEN"
case "$V" in
  fast) IMP="import EthLib.Cryptography.Hash.Sha256"; NAME=ShaBench ;;
  spec) IMP="import EthLib.Cryptography.Hash.Sha256.Spec"; NAME=ShaBenchSpec ;;
  *) echo "variant must be fast or spec" >&2; exit 2 ;;
esac
sed "s|^@IMPORT@\$|$IMP|" "$HERE/ShaBench.lean.in" > "$GEN/$NAME.lean"
BENCH="$GEN/$NAME.lean" WORK="$GEN" exec "${BUILDER:-$HERE/../sphincs/build.sh}" "$@"
