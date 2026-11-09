#!/usr/bin/env bash
# count_run.sh <elf> : run under QEMU mps2-an505 with exec tracing streamed through a FIFO into count_seg.py.
set -eu
HERE="$(cd "$(dirname "$0")" && pwd)"; ELF="$(realpath "$1")"
D=$(mktemp -d "${TMPDIR:-/tmp}/pqcount.XXXXXX"); mkfifo "$D/log"
python3 "$HERE/count_seg.py" "$D/log" "$ELF" > "$D/segs" &
CP=$!
timeout "${QEMU_TIMEOUT:-3000}" qemu-system-arm -M mps2-an505 -nographic -semihosting -kernel "$ELF" -d in_asm,exec,nochain -D "$D/log" || true   # exits 1: rt.c passes SYS_EXIT a pointer, QEMU reads it as the reason
wait $CP; cat "$D/segs"; rm -rf "$D"
