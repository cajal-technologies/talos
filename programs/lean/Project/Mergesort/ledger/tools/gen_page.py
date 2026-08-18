#!/usr/bin/env python3
"""Generate ../index.html (the mergesort proof ledger) from data/graph.json,
data/wat.json and tools/meta.py.

Proof states live in ../status.json (Complete / In Progress / Pending) and are
read by the page at load time — edit status.json and refresh the page. This
script never overwrites an existing status.json; it only creates a fresh
all-pending template when the file is missing, and it embeds the current
contents as a fallback snapshot for contexts where fetch() is unavailable.

Run from the ledger/ directory:  python3 tools/gen_page.py
"""
import json, html, re, os, sys

HERE = os.path.dirname(os.path.abspath(__file__))
LEDGER = os.path.dirname(HERE)
sys.path.insert(0, HERE)
from meta import M, CAT, CATEGORIES, CATEGORY_ORDER, HAPPY, PANIC_DESC, PANIC_PROP, COLDFMT_DESC, COLDFMT_PROP

g = json.load(open(os.path.join(LEDGER, 'data', 'graph.json')))
wat = json.load(open(os.path.join(LEDGER, 'data', 'wat.json')))
funcs = {int(k): v for k, v in g['functions'].items()}

def leanname(i):
    return funcs[i]['lean'] or ('import0' if i == 0 else 'import1')

def shortname(i):
    if i in M and 'short' in M[i]:
        return M[i]['short']
    n = funcs[i]['name']
    n = re.sub(r'\b(core|alloc|std)::', '', n)
    n = n.replace('fmt::builders::', '').replace('panicking::panic_handler::', 'panic_handler::')
    n = n.replace('io::buffered::bufwriter::', '').replace('dlmalloc::dlmalloc::', '')
    return n if len(n) <= 58 else n[:55] + '…'

data = []
for i in sorted(funcs):
    f = funcs[i]
    cat = CAT[i]
    m = M.get(i, {})
    if 'desc' in m:
        desc, props = m['desc'], m.get('props', [])
    elif cat == 'panic':
        desc, props = PANIC_DESC, PANIC_PROP
    else:
        desc, props = COLDFMT_DESC, COLDFMT_PROP
    data.append({
        'i': i, 'lean': leanname(i), 'short': shortname(i), 'full': f['name'],
        'params': f['params'], 'results': f['results'],
        'cat': cat, 'happy': i in HAPPY, 'table': f['in_table'],
        'calls': f['direct_calls'], 'ind': f['indirect_possible'],
        'trans': f['transitive'],
        'callers': sorted({int(str(c).rstrip('*')) for c in f['callers']}),
        'desc': desc,
        'props': [{'n': n, 's': s} for n, s in props],
        'wat': wat.get(str(i), ''),
    })

# ---- status.json ----------------------------------------------------------
STATUS_PATH = os.path.join(LEDGER, 'status.json')
all_keys = [f"{d['lean']}.{p['n']}" for d in data for p in d['props']]
if not os.path.exists(STATUS_PATH):
    json.dump({k: 'pending' for k in all_keys}, open(STATUS_PATH, 'w'), indent=1)
    print('created fresh all-pending', STATUS_PATH)
status_snapshot = json.load(open(STATUS_PATH))
# keep template keys in sync: add new obligations as pending, keep user values
changed = False
for k in all_keys:
    if k not in status_snapshot:
        status_snapshot[k] = 'pending'
        changed = True
if changed:
    json.dump(status_snapshot, open(STATUS_PATH, 'w'), indent=1)
    print('added new pending keys to status.json')

n_happy = sum(1 for d in data if d['happy'])
n_dead = len(data) - n_happy
cat_counts = {c: sum(1 for d in data if d['cat'] == c) for c in CATEGORY_ORDER}

payload = json.dumps({'funcs': data, 'order': CATEGORY_ORDER,
                      'cats': {k: v[0] for k, v in CATEGORIES.items()}},
                     separators=(',', ':'))
status_js = json.dumps(status_snapshot, separators=(',', ':'))

cat_legend = ''.join(
    f'<span class="lg"><i style="background:var(--c-{c})"></i>{CATEGORIES[c][0]} <em>{cat_counts[c]}</em></span>'
    for c in CATEGORY_ORDER)

sections = []
for c in CATEGORY_ORDER:
    title, blurb = CATEGORIES[c]
    sections.append(
        f'<section class="cat" id="cat-{c}">'
        f'<h2><i class="dot" style="background:var(--c-{c})"></i>{html.escape(title)}'
        f'<span class="count">{cat_counts[c]} fn</span></h2>'
        f'<p class="blurb">{blurb}</p>'
        f'<div class="cards" data-cat="{c}"></div></section>')
sections_html = ''.join(sections)

page = r'''<meta charset="utf-8">
<title>Mergesort Proof Ledger</title>
<style>
:root{
  --bg:#f7f6f2; --panel:#fdfcf9; --panel2:#f0eee7; --line:#ddd9cd; --ink:#26302e;
  --muted:#6d746f; --accent:#177e6e; --accent-ink:#0d5a4e; --amber:#a16207;
  --code-bg:#eceae2; --chip:#e7e4da; --sel:#177e6e;
  --ok:#177e6e; --wip:#b3731d; --pend:#8b8677;
  --c-entry:#177e6e; --c-core:#1e6fa8; --c-parse:#7c5cb0; --c-io:#2e8540;
  --c-fmtout:#b3599a; --c-alloc:#c07a2d; --c-dlmalloc:#a8552e; --c-intrinsic:#5b7d8a;
  --c-panic:#b3403c; --c-coldfmt:#8b8677;
}
@media (prefers-color-scheme: dark){
  :root:not([data-theme="light"]){
    --bg:#171a1c; --panel:#1e2225; --panel2:#23282b; --line:#33393c; --ink:#dfe3de;
    --muted:#95a09a; --accent:#3fb9a5; --accent-ink:#63d0bd; --amber:#d6a04a;
    --code-bg:#14181a; --chip:#2a3033; --sel:#3fb9a5;
    --ok:#3fb9a5; --wip:#d6a04a; --pend:#8f9a94;
    --c-entry:#3fb9a5; --c-core:#5da9dd; --c-parse:#a98fd8; --c-io:#63b873;
    --c-fmtout:#d488bf; --c-alloc:#d99e56; --c-dlmalloc:#cf8261; --c-intrinsic:#8fb0bd;
    --c-panic:#d97671; --c-coldfmt:#9a958a;
  }
}
:root[data-theme="dark"]{
  --bg:#171a1c; --panel:#1e2225; --panel2:#23282b; --line:#33393c; --ink:#dfe3de;
  --muted:#95a09a; --accent:#3fb9a5; --accent-ink:#63d0bd; --amber:#d6a04a;
  --code-bg:#14181a; --chip:#2a3033; --sel:#3fb9a5;
  --ok:#3fb9a5; --wip:#d6a04a; --pend:#8f9a94;
  --c-entry:#3fb9a5; --c-core:#5da9dd; --c-parse:#a98fd8; --c-io:#63b873;
  --c-fmtout:#d488bf; --c-alloc:#d99e56; --c-dlmalloc:#cf8261; --c-intrinsic:#8fb0bd;
  --c-panic:#d97671; --c-coldfmt:#9a958a;
}
*{box-sizing:border-box}
body{background:var(--bg);color:var(--ink);margin:0;
  font:15px/1.55 -apple-system,BlinkMacSystemFont,"Segoe UI",Roboto,sans-serif;}
.wrap{max-width:1060px;margin:0 auto;padding:0 20px 80px}
header.hero{padding:52px 0 8px}
h1{font-family:"Iowan Old Style",Palatino,"Palatino Linotype",Georgia,serif;
  font-size:2.5rem;font-weight:600;margin:0 0 6px;letter-spacing:.2px;text-wrap:balance}
h1 .tick{color:var(--accent)}
.sub{color:var(--muted);max-width:62ch;margin:0}
.statrow{display:flex;flex-wrap:wrap;gap:12px;margin:26px 0 8px}
.stat{background:var(--panel);border:1px solid var(--line);border-radius:8px;
  padding:10px 16px;min-width:118px}
.stat b{display:block;font-size:1.45rem;font-variant-numeric:tabular-nums;
  font-family:ui-monospace,SFMono-Regular,Menlo,monospace;color:var(--accent-ink)}
.stat.warn b{color:var(--amber)}
.stat.s-ok b{color:var(--ok)} .stat.s-wip b{color:var(--wip)} .stat.s-pend b{color:var(--pend)}
.stat span{font-size:.78rem;color:var(--muted);text-transform:uppercase;letter-spacing:.06em}
#statusnote{font-size:.8rem;color:var(--muted);margin:4px 0 0}
#statusnote code{font:.9em ui-monospace,Menlo,monospace;background:var(--code-bg);padding:.06em .3em;border-radius:4px}
#statusnote .err{color:var(--amber)}
h2{font-family:"Iowan Old Style",Palatino,Georgia,serif;font-size:1.5rem;font-weight:600;
  margin:44px 0 6px;display:flex;align-items:center;gap:10px}
h2 .count{font:12px ui-monospace,Menlo,monospace;color:var(--muted);margin-left:auto}
.dot{width:11px;height:11px;border-radius:3px;display:inline-block;flex:none}
p.blurb{color:var(--muted);margin:0 0 16px;max-width:72ch}
.prose{max-width:74ch}
.prose code, td code, .card code{font:.86em ui-monospace,SFMono-Regular,Menlo,monospace;
  background:var(--code-bg);padding:.08em .3em;border-radius:4px}
.layers{margin:14px 0 0;padding:0;list-style:none;counter-reset:ly}
.layers li{counter-increment:ly;display:flex;gap:14px;padding:10px 0;border-top:1px solid var(--line)}
.layers li::before{content:counter(ly);font:600 13px/26px ui-monospace,Menlo,monospace;
  color:var(--accent);border:1px solid var(--line);border-radius:6px;width:26px;height:26px;
  text-align:center;flex:none;background:var(--panel)}
.layers b{display:block}
.layers span{color:var(--muted);font-size:.92rem}
/* graph */
#graphbox{background:var(--panel);border:1px solid var(--line);border-radius:10px;padding:14px;margin-top:14px}
#graphscroll{overflow-x:auto}
#legend{display:flex;flex-wrap:wrap;gap:6px 16px;margin-bottom:8px;font-size:.8rem;color:var(--muted)}
.lg i{width:9px;height:9px;border-radius:2px;display:inline-block;margin-right:5px}
.lg em{font-style:normal;font-family:ui-monospace,Menlo,monospace;font-size:.75rem}
#gdetail{border-top:1px solid var(--line);margin-top:10px;padding-top:10px;font-size:.88rem;min-height:2.2em;color:var(--muted)}
#gdetail b{color:var(--ink);font-family:ui-monospace,Menlo,monospace}
svg text{font:10px ui-monospace,SFMono-Regular,Menlo,monospace;fill:var(--ink)}
svg .colhead{font-size:11px;fill:var(--muted);letter-spacing:.05em}
svg rect.node{cursor:pointer;stroke-width:1}
svg rect.node:focus{outline:2px solid var(--sel)}
svg .dim{opacity:.18}
svg .edge{fill:none;stroke-width:1.1;opacity:.85}
svg .edge.trans{stroke-dasharray:3 3;opacity:.4;stroke-width:1}
svg .edge.caller{stroke-dasharray:1.5 2.5}
.gbtns{display:flex;gap:8px;margin-bottom:8px;flex-wrap:wrap}
.gbtns button{background:var(--chip);color:var(--ink);border:1px solid var(--line);
  border-radius:6px;padding:4px 10px;font:12px ui-monospace,Menlo,monospace;cursor:pointer}
.gbtns button[aria-pressed="true"]{background:var(--accent);color:var(--bg);border-color:var(--accent)}
/* state pills */
.pill{font:10.5px ui-monospace,Menlo,monospace;padding:1px 8px;border-radius:99px;white-space:nowrap}
.pill.ok{color:var(--ok);border:1px solid var(--ok)}
.pill.wip{color:var(--wip);border:1px solid var(--wip)}
.pill.pend{color:var(--pend);border:1px solid var(--pend)}
.agg{font:10.5px ui-monospace,Menlo,monospace;color:var(--muted);white-space:nowrap}
.agg b{font-weight:600}
.agg .a-ok{color:var(--ok)} .agg .a-wip{color:var(--wip)} .agg .a-pend{color:var(--pend)}
/* cards */
.card{background:var(--panel);border:1px solid var(--line);border-radius:8px;margin:10px 0;overflow:hidden}
.card>summary{list-style:none;display:flex;flex-wrap:wrap;align-items:baseline;gap:8px 12px;
  padding:10px 14px;cursor:pointer}
.card>summary::-webkit-details-marker{display:none}
.card>summary:hover{background:var(--panel2)}
.fid{font:600 13px ui-monospace,SFMono-Regular,Menlo,monospace;color:var(--accent-ink);min-width:64px}
.fname{font-weight:600;font-size:.95rem}
.fsig{font:11.5px ui-monospace,Menlo,monospace;color:var(--muted);margin-left:auto}
.badge{font:10.5px ui-monospace,Menlo,monospace;padding:1px 7px;border-radius:99px;
  border:1px solid var(--line);color:var(--muted)}
.badge.happy{color:var(--accent-ink);border-color:var(--accent-ink)}
.badge.dead{color:var(--amber);border-color:var(--amber)}
.cbody{padding:2px 14px 14px;border-top:1px solid var(--line)}
.cbody p{margin:10px 0;max-width:78ch;font-size:.92rem}
.mangled{font:10.5px ui-monospace,Menlo,monospace;color:var(--muted);word-break:break-all;margin:6px 0 0}
.props{margin:12px 0 0}
.props h4, .watd h4{margin:0 0 6px;font-size:.78rem;text-transform:uppercase;letter-spacing:.07em;color:var(--muted)}
.prophead{display:flex;align-items:center;gap:10px;margin-top:10px}
.prophead b{font:600 12px ui-monospace,Menlo,monospace;color:var(--accent-ink)}
.prophead .who{font-size:.75rem;color:var(--muted)}
pre{background:var(--code-bg);border:1px solid var(--line);border-radius:6px;padding:10px 12px;
  overflow-x:auto;font:12px/1.5 ui-monospace,SFMono-Regular,Menlo,monospace;margin:6px 0}
details.watd{margin-top:14px}
details.watd summary{cursor:pointer;font:11px ui-monospace,Menlo,monospace;color:var(--muted)}
details.watd pre{max-height:420px;overflow:auto}
.rels{display:flex;flex-direction:column;gap:6px;margin-top:12px;font-size:.8rem}
.rels .lbl{color:var(--muted);font:11px ui-monospace,Menlo,monospace;min-width:120px}
.rrow{display:flex;gap:8px;align-items:baseline;flex-wrap:wrap}
.chip{font:11px ui-monospace,Menlo,monospace;background:var(--chip);border:1px solid var(--line);
  border-radius:5px;padding:1px 6px;cursor:pointer;color:var(--ink);text-decoration:none}
.chip:hover{border-color:var(--accent)}
details.transd summary{cursor:pointer;font:11px ui-monospace,Menlo,monospace;color:var(--muted)}
nav#minitoc{position:sticky;top:0;z-index:5;background:var(--bg);border-bottom:1px solid var(--line);
  display:flex;gap:4px;overflow-x:auto;padding:8px 0;margin:24px -20px 0;padding-left:20px}
nav#minitoc a{font:11.5px ui-monospace,Menlo,monospace;color:var(--muted);text-decoration:none;
  padding:3px 9px;border-radius:99px;border:1px solid transparent;white-space:nowrap}
nav#minitoc a:hover{color:var(--ink);border-color:var(--line)}
@media (prefers-reduced-motion: no-preference){ .card{scroll-margin-top:60px} }
</style>
<div class="wrap">
<header class="hero">
  <h1>Mergesort Proof Ledger<span class="tick"> ⊢</span></h1>
  <p class="sub">Every function in the compiled <code>mergesort</code> wasm module
  (<code>programs/lean/Project/Mergesort/Program.lean</code>), what it does, the memory contract it
  lives under, and the <code>twp</code> properties the total-correctness proof of
  <code>MergesortSpec</code> needs from it — plus the full call graph, direct and transitive.</p>
  <div class="statrow">
    <div class="stat"><b>__NFUNCS__</b><span>functions (2 imports)</span></div>
    <div class="stat"><b>__NHAPPY__</b><span>on the happy path</span></div>
    <div class="stat warn"><b>__NDEAD__</b><span>must be unreachable</span></div>
    <div class="stat s-ok"><b id="n-ok">–</b><span>complete</span></div>
    <div class="stat s-wip"><b id="n-wip">–</b><span>in progress</span></div>
    <div class="stat s-pend"><b id="n-pend">–</b><span>pending</span></div>
  </div>
  <p id="statusnote">Proof states load from <code>status.json</code> — set an obligation to
  <code>"complete"</code>, <code>"in_progress"</code> (optionally
  <code>{"state":"in_progress","by":"name"}</code>) or <code>"pending"</code>, then refresh.
  <span id="statuserr"></span></p>
</header>

<nav id="minitoc"><a href="#strategy">strategy</a><a href="#graph">call graph</a>__TOC__</nav>

<section class="prose" id="strategy">
  <h2>Endpoint & strategy</h2>
  <p>The target is <code>Project.Mergesort.Spec.MergesortSpec</code>: for every input list of
  <code>u64</code>, the exported <code>mergesort</code> entry runs to completion through the StdIO seam and
  emits the sorted permutation, space-separated. The proof stack:</p>
  <ol class="layers">
    <li><b>Host seam</b><span><code>twp</code> rules for the two imports, fixed by
      <code>StdIO.spec</code> (already proven compatible: <code>stdio_env_satisfies</code>).</span></li>
    <li><b>Leaf specs</b><span>pure helpers first — <code>memchr</code>, <code>memcmp</code>,
      <code>__multi3</code>, <code>from_utf8</code> — each a small frame-local <code>twp</code> lemma.</span></li>
    <li><b>dlmalloc model</b><span>the critical unlock: an abstract heap predicate
      <code>dlmallocInv</code> + <code>blockAt</code> with malloc/free/realloc specs and a budget argument
      making allocation failure unreachable. Everything Vec-shaped sits on top.</span></li>
    <li><b>I/O and fmt pipelines</b><span>BufWriter/Adapter invariants tie
      <code>write!("{}")</code> to <code>toString n</code> byte-for-byte; the reader side ties
      <code>read_line</code> to the host input stream.</span></li>
    <li><b>Algorithm core</b><span><code>twp_mergesort_rec</code> by strong induction on length,
      reusing the merge-loop invariants already proven for the hand-built module in
      <code>CodeLib.Examples.MergeSort.TotalProof</code>.</span></li>
    <li><b>Entry composition & adequacy</b><span>compose the black-box specs through the entry
      body, discharge every panic guard, then <code>SmallStepAdequacy</code> turns the <code>twp</code>
      into <code>TerminatesWith</code> / <code>StdIO.Runs</code> — fuel never appears in a statement.</span></li>
  </ol>
  <p>Reachability discipline: <b>__NHAPPY__ functions</b> execute on well-formed input and get full
  <code>twp</code> specs; the other <b>__NDEAD__</b> (panic runtime + diagnostic formatting) must be
  proven <em>never entered</em> — each call site's guard is discharged, so no spec of their bodies is
  ever needed. Indirect calls go through a 38-entry <code>funcref</code> table; on the happy path only
  four slots are ever dispatched (<code>Adapter::write_str</code>, <code>u64 Display::fmt</code>, the
  BufWriter flush vtable, drop glue).</p>
</section>

<section id="graph">
  <h2>Call graph</h2>
  <p class="blurb">Click a node: <b style="color:var(--accent)">solid</b> edges = direct calls
  (arrows point callee-ward), <span style="opacity:.75">dotted</span> = via the funcref table
  (possible targets by type), faded = the rest of the transitive closure. Dashed edges lead back to
  callers. Columns are the categories below; dimmed nodes are the ones that must be unreachable.</p>
  <div id="graphbox">
    <div id="legend">__LEGEND__</div>
    <div class="gbtns">
      <button id="b-happy" aria-pressed="true">happy path</button>
      <button id="b-all" aria-pressed="false">everything</button>
      <span class="lbl" style="align-self:center;font-size:.75rem;color:var(--muted)">selection: click nodes · Esc clears</span>
    </div>
    <div id="graphscroll"></div>
    <div id="gdetail">Select a node to trace its calls.</div>
  </div>
</section>

__SECTIONS__
</div>
<script>
const DATA = __PAYLOAD__;
const EMBEDDED_STATUS = __STATUS__;
const byId = {}; DATA.funcs.forEach(f => byId[f.i] = f);
const esc = s => s.replace(/&/g,'&amp;').replace(/</g,'&lt;');

/* ---------- proof states ---------- */
const STATES = {complete:{cls:'ok',label:'complete'},
                in_progress:{cls:'wip',label:'in progress'},
                pending:{cls:'pend',label:'pending'}};
function normStatus(raw){
  const out = {};
  for (const [k,v] of Object.entries(raw || {})){
    if (typeof v === 'string') out[k] = {state: v};
    else if (v && typeof v === 'object') out[k] = v;
  }
  return out;
}
let STATUS = normStatus(EMBEDDED_STATUS);
function stateOf(key){
  const s = (STATUS[key] && STATUS[key].state) || 'pending';
  return STATES[s] ? s : 'pending';
}
function pillHtml(key){
  const s = stateOf(key), who = STATUS[key] && STATUS[key].by;
  return `<span class="pill ${STATES[s].cls}" data-key="${esc(key)}">${STATES[s].label}</span>` +
         (who ? `<span class="who">· ${esc(who)}</span>` : '');
}
function aggHtml(f){
  let ok=0, wip=0, pend=0;
  for (const p of f.props){
    const s = stateOf(`${f.lean}.${p.n}`);
    if (s === 'complete') ok++; else if (s === 'in_progress') wip++; else pend++;
  }
  return `<span class="agg" title="complete / in progress / pending">` +
    `<b class="a-ok">${ok}✓</b> <b class="a-wip">${wip}◐</b> <b class="a-pend">${pend}○</b></span>`;
}
function renderCounts(){
  let ok=0, wip=0, pend=0;
  for (const f of DATA.funcs) for (const p of f.props){
    const s = stateOf(`${f.lean}.${p.n}`);
    if (s === 'complete') ok++; else if (s === 'in_progress') wip++; else pend++;
  }
  document.getElementById('n-ok').textContent = ok;
  document.getElementById('n-wip').textContent = wip;
  document.getElementById('n-pend').textContent = pend;
}

/* ---------- cards ---------- */
function renderCards(){
  document.querySelectorAll('.cards').forEach(b => b.innerHTML = '');
  for (const f of DATA.funcs) {
    const box = document.querySelector(`.cards[data-cat="${f.cat}"]`);
    const sig = `(${f.params.join(' ')}) → (${f.results.join(' ')})`;
    const badges =
      (f.happy ? '<span class="badge happy">happy path</span>'
               : '<span class="badge dead">must be unreachable</span>') +
      (f.table ? '<span class="badge">in table</span>' : '');
    const chips = ids => ids.length
      ? ids.map(j => `<a class="chip" href="#fn-${j}" title="${esc(byId[j].full)}">${byId[j].lean}</a>`).join('')
      : '<span class="chip" style="cursor:default;opacity:.6">—</span>';
    const props = f.props.map(p =>
      `<div class="prophead"><b>${esc(p.n)}</b>${pillHtml(`${f.lean}.${p.n}`)}</div>` +
      `<pre>${esc(p.s)}</pre>`).join('');
    const trans = f.trans.length
      ? `<details class="transd"><summary>transitive closure · ${f.trans.length} functions</summary>
         <div class="rrow" style="margin-top:6px">${chips(f.trans)}</div></details>`
      : '';
    const watBlock = f.wat
      ? `<details class="watd"><summary>WAT · ${f.wat.split('\n').length} lines</summary>
         <pre>${esc(f.wat)}</pre></details>`
      : '';
    const el = document.createElement('details');
    el.className = 'card'; el.id = 'fn-' + f.i;
    el.innerHTML = `<summary>
        <span class="fid">${f.lean}</span><span class="fname">${esc(f.short)}</span>
        ${badges}${aggHtml(f)}<span class="fsig">wasm ${f.i} · ${sig}</span></summary>
      <div class="cbody">
        <p class="mangled">${esc(f.full)}</p>
        <p>${f.desc}</p>
        <div class="props"><h4>Properties to prove</h4>${props}</div>
        ${watBlock}
        <div class="rels">
          <div class="rrow"><span class="lbl">calls (direct)</span>${chips(f.calls)}</div>
          ${f.ind.length ? `<div class="rrow"><span class="lbl">indirect (possible)</span>${chips(f.ind)}</div>` : ''}
          <div class="rrow"><span class="lbl">called by</span>${chips(f.callers)}</div>
          ${trans}
        </div></div>`;
    box.appendChild(el);
  }
}
document.addEventListener('click', e => {
  const a = e.target.closest('a.chip');
  if (!a) return;
  const t = document.querySelector(a.getAttribute('href'));
  if (t) { t.open = true; }
});

/* ---------- status loading ---------- */
function loadStatus(){
  fetch('status.json', {cache: 'no-store'})
    .then(r => { if (!r.ok) throw new Error(r.status); return r.json(); })
    .then(j => { STATUS = normStatus(j); refresh(); })
    .catch(() => {
      const el = document.getElementById('statuserr');
      el.className = 'err';
      el.textContent = location.protocol === 'file:'
        ? '(live status.json needs http — run e.g. `python3 -m http.server` in ledger/; showing the snapshot embedded at generation time)'
        : '(status.json could not be loaded; showing the embedded snapshot)';
      refresh();
    });
}
function refresh(){ renderCounts(); renderCards(); }

/* ---------- graph ---------- */
const NW = 74, NH = 16, GX = 150, GY = 21, PAD = 26, HEADH = 34;
let mode = 'happy';
const scroll = document.getElementById('graphscroll');
const detail = document.getElementById('gdetail');
let selected = null;

function visible(f){ return mode === 'all' || f.happy; }

function layout(){
  const cols = DATA.order.map(c => DATA.funcs.filter(f => f.cat === c && visible(f)))
                         .filter(col => col.length);
  const H = Math.max(...cols.map(c => c.length)) * GY + HEADH + PAD;
  const W = cols.length * GX + PAD;
  const pos = {};
  let svg = `<svg width="${W}" height="${H}" viewBox="0 0 ${W} ${H}" role="img" aria-label="call graph">`;
  svg += `<defs><marker id="arr" viewBox="0 0 6 6" refX="5.5" refY="3" markerWidth="5" markerHeight="5" orient="auto"><path d="M0 0L6 3L0 6z" fill="context-stroke"/></marker></defs>`;
  cols.forEach((col, ci) => {
    const x = PAD/2 + ci*GX;
    svg += `<text class="colhead" x="${x}" y="${HEADH-16}">${DATA.cats[col[0].cat].toUpperCase()}</text>`;
    col.forEach((f, ri) => {
      const y = HEADH + ri*GY;
      pos[f.i] = {x, y};
      svg += `<g class="gn" data-i="${f.i}">
        <rect class="node" tabindex="0" data-i="${f.i}" x="${x}" y="${y}" width="${NW}" height="${NH}" rx="4"
          fill="var(--panel2)" stroke="var(--c-${f.cat})" ${f.happy?'':'opacity=".45"'}>
        </rect>
        <text x="${x+6}" y="${y+11.5}" pointer-events="none">${f.lean}</text></g>`;
    });
  });
  svg += `<g id="edges"></g></svg>`;
  scroll.innerHTML = svg;
  scroll._pos = pos;
}

function edge(a, b, cls, color){
  const pos = scroll._pos; if (!pos[a] || !pos[b]) return '';
  const p = pos[a], q = pos[b];
  let x1, x2;
  if (q.x > p.x) { x1 = p.x + NW; x2 = q.x - 1; }
  else if (q.x < p.x) { x1 = p.x; x2 = q.x + NW + 1; }
  else {
    const y1 = p.y + NH/2, y2 = q.y + NH/2, bow = 16 + Math.abs(y1-y2)/8;
    return `<path class="edge ${cls}" marker-end="url(#arr)" stroke="${color}"
      d="M${p.x} ${y1} C ${p.x-bow} ${y1}, ${q.x-bow} ${y2}, ${q.x+1} ${y2}"/>`;
  }
  const y1 = p.y + NH/2, y2 = q.y + NH/2, mx = (x1+x2)/2;
  return `<path class="edge ${cls}" marker-end="url(#arr)" stroke="${color}"
    d="M${x1} ${y1} C ${mx} ${y1}, ${mx} ${y2}, ${x2} ${y2}"/>`;
}

function select(i){
  selected = i;
  const g = document.getElementById('edges');
  const f = byId[i];
  document.querySelectorAll('#graphscroll .gn').forEach(n => n.classList.remove('dim'));
  if (i == null){ g.innerHTML=''; detail.textContent='Select a node to trace its calls.'; return; }
  const direct = new Set(f.calls), ind = new Set(f.ind.filter(x=>!direct.has(x)));
  const trans = new Set(f.trans.filter(x => !direct.has(x) && !ind.has(x) && x !== i));
  const callers = new Set(f.callers);
  const keep = new Set([i, ...direct, ...ind, ...trans, ...callers]);
  document.querySelectorAll('#graphscroll .gn').forEach(n => {
    if (!keep.has(+n.dataset.i)) n.classList.add('dim');
  });
  let e = '';
  for (const t of trans) e += edge(i, t, 'trans', 'var(--muted)');
  for (const c of callers) e += edge(c, i, 'caller', `var(--c-${byId[c].cat})`);
  for (const t of ind) e += edge(i, t, 'trans', `var(--c-${f.cat})`);
  for (const t of direct) e += edge(i, t, '', `var(--c-${f.cat})`);
  g.innerHTML = e;
  detail.innerHTML = `<b>${f.lean}</b> · ${esc(f.short)} — direct calls
    <b>${f.calls.length}</b>${f.ind.length?` (+${f.ind.length} possible via table)`:''},
    transitive closure <b>${f.trans.length}</b>, callers <b>${f.callers.length}</b>.
    <a class="chip" href="#fn-${i}">open card ↓</a>`;
}

scroll.addEventListener('click', e => {
  const r = e.target.closest('rect.node');
  select(r ? +r.dataset.i : null);
});
scroll.addEventListener('keydown', e => {
  const r = e.target.closest('rect.node');
  if (r && (e.key === 'Enter' || e.key === ' ')) { e.preventDefault(); select(+r.dataset.i); }
});
document.addEventListener('keydown', e => { if (e.key === 'Escape') select(null); });

function setMode(m){
  mode = m;
  document.getElementById('b-happy').setAttribute('aria-pressed', m==='happy');
  document.getElementById('b-all').setAttribute('aria-pressed', m==='all');
  layout(); select(selected != null && (mode==='all' || byId[selected].happy) ? selected : null);
}
document.getElementById('b-happy').onclick = () => setMode('happy');
document.getElementById('b-all').onclick = () => setMode('all');
refresh(); layout(); select(15); loadStatus();
</script>
'''

toc = ''.join(f'<a href="#cat-{c}">{CATEGORIES[c][0].lower()}</a>' for c in CATEGORY_ORDER)
page = (page
        .replace('__NFUNCS__', str(len(data)))
        .replace('__NHAPPY__', str(n_happy))
        .replace('__NDEAD__', str(n_dead))
        .replace('__LEGEND__', cat_legend)
        .replace('__TOC__', toc)
        .replace('__SECTIONS__', sections_html)
        .replace('__PAYLOAD__', payload)
        .replace('__STATUS__', status_js))

out = os.path.join(LEDGER, 'index.html')
open(out, 'w').write(page)
print('wrote', out, len(page), 'bytes;', len(all_keys), 'obligations')
