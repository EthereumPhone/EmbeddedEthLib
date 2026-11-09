#!/usr/bin/env python3
"""decode.py <elf.openocd.log> [qemu_segs.txt] : decode the bench.h block (w0..w63) and the PQX block (w64..w255)."""

import sys

log = sys.argv[1]
w = [int(x, 16) for x in next(l for l in open(log) if l.startswith("RESULT_WORDS")).split()[1:]]
assert len(w) >= 256, len(w)
st = w[0]
print(
    "STATUS 0x%08x %s"
    % (st, {0x444F4E45: "DONE", 0x53545254: "STARTED", 0xDEADBEEF: "POISON"}.get(st, "FAULT/HALT"))
)
print("cyc_run(32-bit, wraps) %d dwt_ctrl 0x%08x overhead %d" % (w[1], w[2], w[3]))
if st >> 16 == 0xFA17:
    print("FAULT", " ".join("0x%08x" % x for x in w[16:24]))
n = w[24]
if 0 < n <= 156:
    print("TEXT", repr(b"".join(x.to_bytes(4, "little") for x in w[25:64])[:n].decode("latin-1")))
x = w[64:256]
print("PQX magic 0x%08x (%s) mode %d" % (x[0], "ok" if x[0] == 0x5051534C else "BAD", x[1]))
print(
    "clock: saved_cfgr1 0x%08x  cfgr1 0x%08x (SWS=%d)  pll1divr 0x%08x  vosr 0x%08x  rest_cfgr1 0x%08x (SWS=%d)  rest_vosr 0x%08x"
    % (x[5], x[2], (x[2] >> 2) & 3, x[3], x[4], x[6], (x[6] >> 2) & 3, x[7])
)
names = "constants op_allocs op_frees live_after_op peak freed_bytes nonzero_in_freed bump ARENA_BYTES stack_depth".split()
print("arena: " + " ".join("%s=%d" % (k, v) for k, v in zip(names, x[8:18], strict=True)))
init = x[18] | x[19] << 32
main = x[20] | x[21] << 32
print("init_cycles %d  lean_fw_main_cycles %d  nkeccak %d" % (init, main, x[22]))
nm = x[23]
marks = [(x[24 + 3 * i], x[25 + 3 * i] | x[26 + 3 * i] << 32) for i in range(min(nm, 24))]
q = {}
if len(sys.argv) > 2:
    for l in open(sys.argv[2]):
        f = l.split()
        if f and f[0] == "seg":
            q[int(f[1])] = int(f[2])
print("marks %d" % nm)
for i in range(1, len(marks)):
    c = marks[i][1] - marks[i - 1][1]
    qi = q.get(i)
    print(
        "seg %2d (mark %d->%d): %15d cycles  %10.3f ms@160MHz"
        % (i, marks[i - 1][0], marks[i][0], c, c / 160e3)
        + ("  qemu_instr %13d  CPI %.3f" % (qi, c / qi) if qi else "")
    )
rl = x[96]
rb = b"".join(v.to_bytes(4, "little") for v in x[97:192])[:rl]
i = 0
while i < len(rb):
    kind, tag, n = rb[i], rb[i + 1], rb[i + 2]
    i += 3
    body = rb[i : i + n]
    i += n
    print("R %d %s" % (tag, int.from_bytes(body, "big") if kind == 0 else body.hex()))
