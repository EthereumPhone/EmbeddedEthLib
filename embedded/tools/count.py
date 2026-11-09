# Count executed Thumb-2 instructions from QEMU `-d in_asm,exec,nochain` (no capstone: raw OBJD-T bytes).
import re, sys
def ninsn(hexs):
    b = bytes.fromhex(hexs); i = n = 0
    while i + 1 < len(b):
        hw = b[i] | (b[i+1] << 8)
        i += 4 if (hw >> 11) in (0b11101, 0b11110, 0b11111) else 2
        n += 1
    return n
tb, cur, buf, total, execs = {}, None, '', 0, 0
def flush():
    global cur, buf
    if cur is not None: tb[cur] = ninsn(buf)
    cur, buf = None, ''
for line in open(sys.argv[1], errors='replace'):
    if line.startswith('IN:'): flush(); continue
    m = re.match(r'0x([0-9a-f]{8}):', line)
    if m and cur is None and not buf: cur = int(m.group(1), 16); continue
    if line.startswith('OBJD-T:'): buf += line.split(':', 1)[1].strip(); continue
    m = re.search(r'Trace \d+: 0x[0-9a-f]+ \[[0-9a-f]+/([0-9a-f]+)/', line)
    if m:
        flush(); execs += 1; total += tb.get(int(m.group(1), 16), 0)
flush(); print(total)
