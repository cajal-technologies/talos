import assert from "node:assert/strict";
import { readFileSync } from "node:fs";
import test from "node:test";
import ts from "typescript";

// Compile the actual report loader without depending on Node's optional TS loader.
const source = readFileSync(new URL("../src/lib/load.ts", import.meta.url), "utf8");
const { outputText } = ts.transpileModule(source, {
  compilerOptions: { module: ts.ModuleKind.ESNext, target: ts.ScriptTarget.ES2022 },
});
const { projectView } = await import(
  `data:text/javascript;base64,${Buffer.from(outputText).toString("base64")}`,
);

test("partial export references bind the same Rust function as total references", () => {
  for (const kind of ["rust-exported", "rust-exported-partial"]) {
    const view = projectView({
      slug: "rust_vec",
      data: {
        project: { crate: "rust_vec" },
        exported: [{ name: "vec_pop" }, { name: "vec_len" }],
        specs: [{ name: "PopSpec", refs: [{ kind, target: "rust_vec::vec_pop", resolved: true }] }],
        verifications: [],
      },
    });
    assert.deepEqual(view.specs[0].exports.map(e => e.name), ["vec_pop"]);
    assert.equal(view.specs[0].status, "unproven");
    assert.equal(view.coverage.exportsProven, 0);
  }
});

test("internal partial references are not mistaken for export bindings", () => {
  const view = projectView({
    slug: "rust_vec",
    data: {
      project: { crate: "rust_vec" },
      exported: [{ name: "vec_pop" }],
      specs: [{ name: "PopSpec", refs: [{
        kind: "rust-internal-partial", target: "rust_vec::vec_pop", resolved: false,
      }] }],
      verifications: [],
    },
  });
  assert.deepEqual(view.specs[0].exports, []);
});
