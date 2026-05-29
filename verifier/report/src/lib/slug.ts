/** Convert a dotted Lean / Rust identifier into an HTML-safe anchor id. */
export function anchorId(name: string): string {
  return name.replace(/[^A-Za-z0-9_-]/g, "-");
}

/** Convert a file path into a stable prefix used for per-line `<span id>`
 *  attributes inside the source viewer. */
export function fileLineIdPrefix(filepath: string): string {
  return "file-" + filepath.replace(/[^A-Za-z0-9_]/g, "-");
}
