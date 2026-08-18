#!/usr/bin/env python3
"""Split the canonical program.wat into per-function bodies -> data/wat.json.

Run from the ledger/ directory after `just verifier-build mergesort`.
"""
import json, re, os

HERE = os.path.dirname(os.path.abspath(__file__))
LEDGER = os.path.dirname(HERE)
REPO = os.path.abspath(os.path.join(LEDGER, '..', '..', '..', '..', '..'))
WAT = os.path.join(REPO, 'programs', 'rust', 'build', 'mergesort', 'program.wat')

lines = open(WAT).read().splitlines()
out = {}
cur = None
buf = []

def flush():
    global buf, cur
    if cur is not None:
        # trim the trailing lone ')' indentation artifacts are fine as-is
        out[cur] = '\n'.join(buf)
    buf = []

for line in lines:
    m = re.match(r'  \(func \(;(\d+);\)', line)
    if m:
        flush()
        cur = int(m.group(1))
        buf = [line[2:]]  # dedent two spaces
        continue
    if cur is not None:
        if re.match(r'  \((table|memory|global|export|elem|data)\b', line) or line == ')':
            flush()
            cur = None
            continue
        buf.append(line[2:] if line.startswith('  ') else line)
flush()

# imports have no body; record their declaration for completeness
for line in lines:
    m = re.match(r'  \(import "stdio" "\w+" \(func \(;(\d+);\).*', line)
    if m:
        out[int(m.group(1))] = line.strip()

json.dump({str(k): v for k, v in sorted(out.items())},
          open(os.path.join(LEDGER, 'data', 'wat.json'), 'w'))
print('wrote', len(out), 'function bodies,',
      sum(len(v) for v in out.values()), 'chars')
