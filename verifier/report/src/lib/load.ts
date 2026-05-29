import { readdirSync, readFileSync, existsSync, statSync } from "node:fs";
import { join, resolve, basename } from "node:path";
import type {
  Artifact,
  LoadedArtifact,
  ProjectView,
  SpecView,
  Verification,
  ExportedFunction,
} from "../types.js";

function inputDir(): string {
  const env = process.env.TALOS_EXTRACTED_DIR;
  if (!env) {
    throw new Error(
      "TALOS_EXTRACTED_DIR is not set. Run via `scripts/build.mjs <extracted-dir>`.",
    );
  }
  const abs = resolve(env);
  if (!existsSync(abs) || !statSync(abs).isDirectory()) {
    throw new Error(`TALOS_EXTRACTED_DIR=${abs} is not a directory`);
  }
  return abs;
}

let cache: LoadedArtifact[] | null = null;

export function loadArtifacts(): LoadedArtifact[] {
  if (cache) return cache;
  const dir = inputDir();
  const files = readdirSync(dir).filter((f) => f.endsWith(".json")).sort();
  const out: LoadedArtifact[] = [];
  for (const name of files) {
    const path = join(dir, name);
    try {
      const data: Artifact = JSON.parse(readFileSync(path, "utf8"));
      out.push({ slug: basename(name, ".json"), fileName: name, data });
    } catch (e) {
      console.error(`error: failed to parse ${path}: ${(e as Error).message}`);
    }
  }
  out.sort((a, b) =>
    displayName(a).localeCompare(displayName(b)),
  );
  cache = out;
  return out;
}

export function displayName(a: LoadedArtifact): string {
  return a.data.project.name ?? a.data.project.crate ?? a.slug;
}

function exportsBoundBySpec(
  refs: { kind: string; target: string; resolved: boolean }[],
  crate: string,
  exports: ExportedFunction[],
): ExportedFunction[] {
  const targetFns = new Set<string>();
  for (const r of refs) {
    if (r.kind !== "rust-exported") continue;
    const parts = r.target.split("::");
    if (parts.length === 2 && parts[0] === crate) {
      targetFns.add(parts[1]);
    } else if (parts.length === 1) {
      targetFns.add(parts[0]);
    }
  }
  return exports.filter((e) => targetFns.has(e.name));
}

export function projectView(a: LoadedArtifact): ProjectView {
  const art = a.data;
  const crate = art.project.crate ?? art.project.name ?? a.slug;
  const specs: SpecView[] = art.specs.map((s) => {
    const proofs = art.verifications.filter((v) => v.proves === s.name);
    return {
      spec: s,
      proofs,
      exports: exportsBoundBySpec(s.refs, crate, art.exported),
      status: proofs.length > 0 ? "proven" : "unproven",
    };
  });
  const orphan: Verification[] = art.verifications.filter(
    (v) => !art.specs.some((s) => s.name === v.proves),
  );

  // Coverage = exports for which at least one spec is proven.
  const provenExportNames = new Set<string>();
  for (const sv of specs) {
    if (sv.status !== "proven") continue;
    for (const ex of sv.exports) provenExportNames.add(ex.name);
  }
  const coverage = {
    exportsProven: provenExportNames.size,
    exportsTotal: art.exported.length,
  };

  return {
    slug: a.slug,
    displayName: displayName(a),
    artifact: art,
    specs,
    orphanVerifications: orphan,
    coverage,
  };
}

export function allProjectViews(): ProjectView[] {
  return loadArtifacts().map(projectView);
}

export function loadAggregate() {
  const arts = loadArtifacts();
  const totalSpecs = arts.reduce((n, a) => n + a.data.specs.length, 0);
  const totalVerifs = arts.reduce((n, a) => n + a.data.verifications.length, 0);
  const totalExports = arts.reduce((n, a) => n + a.data.exported.length, 0);
  const totalDiags = arts.reduce((n, a) => n + a.data.diagnostics.length, 0);
  const views = arts.map(projectView);
  const provenSpecs = views.reduce(
    (n, v) => n + v.specs.filter((s) => s.status === "proven").length,
    0,
  );
  const exportsProven = views.reduce((n, v) => n + v.coverage.exportsProven, 0);
  const exportsTotal = views.reduce((n, v) => n + v.coverage.exportsTotal, 0);
  const first = arts[0]?.data;
  return {
    arts,
    views,
    totals: {
      projects: arts.length,
      exports: totalExports,
      specs: totalSpecs,
      verifications: totalVerifs,
      diagnostics: totalDiags,
      provenSpecs,
      exportsProven,
      exportsTotal,
    },
    repoCommit: first?.repo_commit ?? null,
    rustcEdition: first?.toolchains?.rustc ?? null,
    leanToolchain: first?.toolchains?.lean ?? null,
    extractedAt: first?.extracted_at ?? null,
  };
}
