# Attribute executed Thumb-2 instructions to functions (QEMU -d in_asm,exec,nochain + nm symbol map).
import re, sys, subprocess, bisect, collections
syms = []
for l in subprocess.run(['arm-none-eabi-nm', '-n', '--defined-only', sys.argv[2]], capture_output=True, text=True).stdout.splitlines():
    p = l.split()
    if len(p) == 3 and p[1] in 'tT': syms.append((int(p[0], 16) & ~1, p[2]))
addrs = [a for a, _ in syms]
def fn(pc): i = bisect.bisect_right(addrs, pc) - 1; return syms[i][1] if i >= 0 else '?'
def ninsn(h):
    b = bytes.fromhex(h); i = n = 0
    while i + 1 < len(b):
        hw = b[i] | (b[i+1] << 8); i += 4 if (hw >> 11) in (29, 30, 31) else 2; n += 1
    return n
tb, cur, buf, cnt = {}, None, '', collections.Counter()
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
        flush(); pc = int(m.group(1), 16); cnt[fn(pc)] += tb.get(pc, 0)
tot = sum(cnt.values())
for f, c in cnt.most_common(int(sys.argv[3]) if len(sys.argv) > 3 else 15): print(f"{100*c/tot:5.1f}%  {c:>9,}  {f}")
print(f"total {tot:,}")
