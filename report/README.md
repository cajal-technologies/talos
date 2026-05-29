# talos-report

Static-site generator (Astro) that turns `verifier extract` JSON artifacts
into a browsable progress report.

## Usage

```bash
cd report
npm install
npm run build-report -- ../programs/extracted
open out/index.html
```

A second argument overrides the output directory (default `./out`):

```bash
npm run build-report -- ../programs/extracted ./public
```

Serve the report locally:

```bash
python3 -m http.server --directory out
```

## What it shows

- **Index** — coverage bar (`% exports with a proven spec`), aggregate
  stats, and a sortable/filterable project table.
- **All specs** (`specs.html`) — every spec across every project,
  filterable by name / project / informal text, with proven/unproven
  filter.
- **Project page** (`projects/<slug>.html`) — spec-first layout:
  - Sticky sidebar listing specs, exports, and other sections.
  - Each spec rendered as a 3-column card:
    1. **Informal spec** — Markdown + KaTeX (math).
    2. **Formal statement** — Lean, syntax-highlighted, with deep-link
       buttons to each matching proof.
    3. **Rust binding** — exports the spec mentions via
       `@[spec_of "rust-exported" …]`, plus the raw reference list.
  - Exports, Program, orphan verifications, diagnostics.
  - Source-files appendix grouped by language; deep-links open the
    relevant `<details>` block and scroll to the line.

## Layout

```
report/
  astro.config.mjs
  package.json
  scripts/build.mjs      ← CLI wrapper; same args as v0.1
  src/
    layouts/Base.astro
    components/          ← Badge, CoverageBar, Sidebar, SpecCard, SourceViewer
    pages/
      index.astro
      specs.astro
      projects/[slug].astro
    lib/
      load.ts            ← reads TALOS_EXTRACTED_DIR, normalizes artifacts
      markdown.ts        ← marked + KaTeX
      highlight.ts       ← shiki (rust / lean4 / wasm / toml)
      slug.ts
    styles/global.css
    types.ts
```

The schema this consumes is defined in
[`../tasks/extract-schema.md`](../tasks/extract-schema.md). Notable v0.2
additions consumed by the report:

- `verification.body_span` — used for proof deep-links.
