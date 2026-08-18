# Mergesort proof ledger

A static page tracking the total-correctness proof of the StdIO `mergesort`
module (`Project/Mergesort/Program.lean`): every wasm function, its memory
contract, its inline WAT, the `twp` properties the proof needs from it, and the
full call graph (direct + transitive).

## Viewing

```
cd programs/lean/Project/Mergesort/ledger
python3 -m http.server 8000     # then open http://localhost:8000/
```

Serving over http is needed so the page can fetch `status.json` live; opened as
a plain `file://` it falls back to the status snapshot embedded at generation
time (and says so in the header).

## Tracking proof progress

`status.json` maps each obligation (`<leanFunc>.<propertyName>`) to one of

- `"pending"` — nobody has started it (the default),
- `"in_progress"` — someone is working on it; use
  `{"state": "in_progress", "by": "who"}` to say who,
- `"complete"` — proven and merged.

Edit the file and refresh the page; the header counters, per-card aggregates
(`✓ / ◐ / ○`) and per-property pills all re-render from it.

## Regenerating

The page is generated; edit `tools/meta.py` (descriptions, categories,
property sketches) rather than `index.html`. Then:

```
just verifier-build mergesort         # refresh programs/rust/build/mergesort/program.wat
python3 tools/extract_graph.py        # data/graph.json + data/names.tsv (needs wasm-tools, rustfilt)
python3 tools/extract_wat.py          # data/wat.json
python3 tools/gen_page.py             # index.html (+ adds any new obligations to status.json as pending)
```

`gen_page.py` never overwrites states you have set in `status.json`; it only
appends newly-appearing obligations as `pending`.

Name recovery works off the *raw* cargo artifact
(`programs/rust/target/wasm32-unknown-unknown/release/mergesort.wasm`), which is
byte-identical to the canonical `build/mergesort/program.wasm` except that its
custom sections (including the `name` section) are not stripped. Lean `funcN`
corresponds to wasm function index `N + 2` (the two stdio imports come first).
