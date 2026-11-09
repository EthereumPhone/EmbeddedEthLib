# Segmented instruction counter for QEMU `-d in_asm,exec,nochain` logs (file or FIFO).
# Usage: count_seg.py <log> <elf>. Splits the executed-instruction total at every execution of the
# TB that starts at pq_mark's entry; prints one line per segment: "<from_mark_ordinal> <instructions>".
# Thumb-2 instruction length from the first halfword (no capstone needed), as in count.py.
import re, sys, subprocess
log, elf = sys.argv[1], sys.argv[2]
nm = subprocess.run(['arm-none-eabi-nm', elf], capture_output=True, text=True).stdout
mark = next(int(l.split()[0], 16) & ~1 for l in nm.splitlines() if l.endswith(' pq_mark'))
def ninsn(hexs):
    b = bytes.fromhex(hexs); i = n = 0
    while i + 1 < len(b):
        hw = b[i] | (b[i+1] << 8)
        i += 4 if (hw >> 11) in (0b11101, 0b11110, 0b11111) else 2
        n += 1
    return n
tb, cur, buf = {}, None, ''
segs, acc, total = [], 0, 0
def flush():
    global cur, buf
    if cur is not None: tb[cur] = ninsn(buf)
    cur, buf = None, ''
trace = re.compile(r'Trace \d+: 0x[0-9a-f]+ \[[0-9a-f]+/([0-9a-f]+)/')
for line in open(log, errors='replace'):
    if line.startswith('Trace'):
        m = trace.match(line)
        if m:
            flush(); pc = int(m.group(1), 16)
            if pc == mark: segs.append(acc); acc = 0
            n = tb.get(pc, 0); acc += n; total += n
        continue
    if line.startswith('IN:'): flush(); continue
    m = re.match(r'0x([0-9a-f]{8}):', line)
    if m and cur is None and not buf: cur = int(m.group(1), 16); continue
    if line.startswith('OBJD-T:'): buf += line.split(':', 1)[1].strip(); continue
flush(); segs.append(acc)
print('pre-first-mark', segs[0])
for i, s in enumerate(segs[1:], 1): print('seg', i, s)
print('total', total)
