#!/usr/bin/env node
// Thin CLI wrapper around `astro build` that preserves the v0.1 interface:
//   npm run build-report -- <extracted-dir> [out-dir]
//
// We just translate args to environment variables and shell out to Astro.
// Astro reads `TALOS_EXTRACTED_DIR` to find the JSON artifacts and
// `TALOS_OUT_DIR` for the output location.
import { spawn } from "node:child_process";
import { existsSync, statSync } from "node:fs";
import { resolve, dirname } from "node:path";
import { fileURLToPath } from "node:url";

const here = dirname(fileURLToPath(import.meta.url));
const root = resolve(here, "..");

function usage() {
  console.error("usage: build-report <extracted-dir> [out-dir]");
  console.error("  <extracted-dir>  directory of `verifier extract` JSON artifacts");
  console.error("  [out-dir]        output directory (default: ./out)");
  process.exit(2);
}

const args = process.argv.slice(2);
if (args.length < 1 || args[0] === "-h" || args[0] === "--help") usage();

const extractedDir = resolve(args[0]);
const outDir = resolve(args[1] ?? "out");

if (!existsSync(extractedDir) || !statSync(extractedDir).isDirectory()) {
  console.error(`error: ${extractedDir} is not a directory`);
  process.exit(1);
}

const env = {
  ...process.env,
  TALOS_EXTRACTED_DIR: extractedDir,
  TALOS_OUT_DIR: outDir,
};

const child = spawn("npx", ["astro", "build"], { cwd: root, env, stdio: "inherit" });
child.on("exit", (code) => {
  if (code === 0) {
    console.log(`\nReport built → ${outDir}/index.html`);
  }
  process.exit(code ?? 1);
});
