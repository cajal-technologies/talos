#!/usr/bin/env python3
"""Rebuild data/graph.json (call graph, signatures, transitive closures) and
data/names.tsv (wasm index -> demangled Rust symbol) for the mergesort module.

Inputs:
  programs/rust/build/mergesort/program.wat            (just verifier-build mergesort)
  programs/rust/target/wasm32-unknown-unknown/release/mergesort.wasm
      -- the raw cargo output; identical to the canonical wasm except that its
         custom sections (incl. the `name` section) are not stripped.

Needs `wasm-tools` and `rustfilt` on PATH for name extraction.
"""
import re, json, os, subprocess

HERE = os.path.dirname(os.path.abspath(__file__))
LEDGER = os.path.dirname(HERE)
REPO = os.path.abspath(os.path.join(LEDGER, '..', '..', '..', '..', '..'))
WAT = os.path.join(REPO, 'programs', 'rust', 'build', 'mergesort', 'program.wat')
RAW_WASM = os.path.join(REPO, 'programs', 'rust', 'target',
                        'wasm32-unknown-unknown', 'release', 'mergesort.wasm')
NAMES = os.path.join(LEDGER, 'data', 'names.tsv')

# ---- names (only if the raw wasm is present; otherwise reuse checked-in tsv)
if os.path.exists(RAW_WASM):
    printed = subprocess.run(['wasm-tools', 'print', RAW_WASM],
                             capture_output=True, text=True, check=True).stdout
    pairs = re.findall(r'^  \(func \$([^ ]+) \(;(\d+);\)', printed, re.M)
    mangled = '\n'.join(p[0] for p in pairs)
    demangled = subprocess.run(['rustfilt'], input=mangled,
                               capture_output=True, text=True, check=True).stdout.splitlines()
    with open(NAMES, 'w') as fh:
        for (_, idx), name in zip(pairs, demangled):
            fh.write(f'{idx}\t{name}\n')
    print('names.tsv rebuilt from raw wasm')
else:
    print('raw wasm not found; keeping existing names.tsv')

wat = open(WAT).read().splitlines()

types = {}
func_type = {}
calls = {}
indirect = {}
elem = []
cur = None

for line in wat:
    m = re.match(r'\s*\(type \(;(\d+);\) \(func(.*)\)\)\s*$', line)
    if m:
        idx = int(m.group(1)); rest = m.group(2)
        params = re.findall(r'\(param ([^)]*)\)', rest)
        results = re.findall(r'\(result ([^)]*)\)', rest)
        types[idx] = {'params': params[0].split() if params else [],
                      'results': results[0].split() if results else []}
        continue
    m = re.match(r'\s*\(import "stdio" "(\w+)" \(func \(;(\d+);\) \(type (\d+)\)\)\)', line)
    if m:
        func_type[int(m.group(2))] = int(m.group(3))
        continue
    m = re.match(r'\s*\(func \(;(\d+);\) \(type (\d+)\)', line)
    if m:
        cur = int(m.group(1)); func_type[cur] = int(m.group(2))
        calls[cur] = set(); indirect[cur] = set()
        continue
    m = re.match(r'\s*\(elem \(;0;\) \(i32\.const 1\) func (.*)\)', line)
    if m:
        elem = [int(x) for x in m.group(1).split()]
        continue
    if cur is not None:
        m = re.match(r'\s*call (\d+)$', line.rstrip())
        if m:
            calls[cur].add(int(m.group(1)))
        m = re.match(r'\s*call_indirect \(type (\d+)\)$', line.rstrip())
        if m:
            indirect[cur].add(int(m.group(1)))

def indirect_targets(t):
    return sorted(i for i in elem if func_type[i] == t)

edges = {}
for f in calls:
    tgt = set(calls[f])
    for t in indirect[f]:
        tgt |= set(indirect_targets(t))
    edges[f] = sorted(tgt)

closure = {}
def close(f):
    if f in closure: return closure[f]
    seen = set(); stack = list(edges.get(f, []))
    while stack:
        x = stack.pop()
        if x in seen: continue
        seen.add(x)
        stack.extend(edges.get(x, []))
    closure[f] = sorted(seen)
    return closure[f]
for f in calls: close(f)

names = {}
for line in open(NAMES):
    i, n = line.rstrip('\n').split('\t')
    names[int(i)] = n
names[0] = 'stdio::read (import)'
names[1] = 'stdio::write (import)'

callers = {i: [] for i in func_type}
for f, ts in calls.items():
    for t in ts:
        callers[t].append(f)
for f, ts in indirect.items():
    for t in ts:
        for tgt in indirect_targets(t):
            callers[tgt].append(f'{f}*')

out = {}
for i in sorted(func_type):
    t = func_type[i]
    out[i] = {
        'wasm': i,
        'lean': None if i < 2 else f'func{i-2}',
        'name': names.get(i, '?'),
        'params': types[t]['params'],
        'results': types[t]['results'],
        'direct_calls': sorted(calls.get(i, [])),
        'indirect_types': sorted(indirect.get(i, [])),
        'indirect_possible': sorted(set().union(*[set(indirect_targets(t)) for t in indirect.get(i, set())]) if indirect.get(i) else set()),
        'transitive': closure.get(i, []),
        'callers': sorted(set(str(c) for c in callers.get(i, []))),
        'in_table': i in elem,
    }
json.dump({'functions': out, 'elem': elem},
          open(os.path.join(LEDGER, 'data', 'graph.json'), 'w'), indent=1)
print('graph.json:', len(out), 'functions,', len(elem), 'table entries')
