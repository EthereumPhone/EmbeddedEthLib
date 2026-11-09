#!/usr/bin/env bash
# count_run.sh <elf> : run under QEMU mps2-an505 with exec tracing streamed through a FIFO into count_seg.py.
# Prints the program's output and the segment counts, and exits with QEMU's status: 0 after a complete run,
# nonzero after a HALT or a FAULT (runtime/sh_exit.h), 124 on a timeout (QEMU_TIMEOUT seconds, default 3000).
set -eu
HERE="$(cd "$(dirname "$0")" && pwd)"; ELF="$(realpath "$1")"
D=$(mktemp -d "${TMPDIR:-/tmp}/pqcount.XXXXXX"); mkfifo "$D/log"
python3 "$HERE/count_seg.py" "$D/log" "$ELF" > "$D/segs" &
CP=$!
RC=0
timeout "${QEMU_TIMEOUT:-3000}" qemu-system-arm -M mps2-an505 -nographic -semihosting -kernel "$ELF" -d in_asm,exec,nochain -D "$D/log" || RC=$?
wait $CP; cat "$D/segs"; rm -rf "$D"
[ "$RC" -eq 0 ] || echo "count_run.sh: qemu exit status $RC" >&2
exit "$RC"
