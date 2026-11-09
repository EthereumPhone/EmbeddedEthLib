# Transitive import closure of a Lean file: prints EthLib module names, and (stderr) non-EthLib imports.
import os
import re
import sys

root = sys.argv[1]
start = sys.argv[2]
seen, other, todo = set(), set(), [start]


def imports(path):
    out = []
    for line in open(path):
        m = re.match(r"^\s*(?:public\s+|meta\s+|private\s+)*import\s+(?:all\s+)?([\w.]+)", line)
        if m:
            out.append(m.group(1))
    return out


first = True
while todo:
    x = todo.pop()
    path = x if first else os.path.join(root, x.replace(".", "/") + ".lean")
    first = False
    for m in imports(path):
        if m.startswith("EthLib"):
            if m not in seen:
                seen.add(m)
                todo.append(m)
        else:
            other.add(m)
for m in sorted(seen):
    print(m)
print("non-EthLib imports:", sorted(other), file=sys.stderr)
