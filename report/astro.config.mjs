import { defineConfig } from "astro/config";

// Output dir overridable via env var (set by scripts/build.mjs).
const outDir = process.env.TALOS_OUT_DIR || "./out";

export default defineConfig({
  outDir,
  // Static site: no SSR adapter needed.
  output: "static",
  // No base path — the report is served from the root of wherever it lands.
  trailingSlash: "ignore",
  build: {
    format: "file", // emit `foo.html` not `foo/index.html`, matches the old generator.
    assets: "_assets",
  },
  devToolbar: { enabled: false },
  vite: {
    server: { fs: { strict: false } },
  },
});
