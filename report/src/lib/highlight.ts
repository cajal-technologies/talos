import { getHighlighter, type Highlighter } from "shiki";

let hl: Promise<Highlighter> | null = null;

function langKey(language: string): string {
  switch (language) {
    case "rust":
    case "toml":
      return language;
    case "lean":
      // shiki ships a `lean4` grammar; fall back to `lean` if absent.
      return "lean4";
    case "wat":
      return "wasm";
    case "toolchain":
      return "text";
    default:
      return "text";
  }
}

export async function highlighter(): Promise<Highlighter> {
  if (!hl) {
    hl = getHighlighter({
      themes: ["github-light"],
      langs: ["rust", "lean4", "wasm", "toml", "text"],
    });
  }
  return hl;
}

/** Highlight a code block to HTML; falls back to escaped text if the
 *  language isn't loaded or shiki rejects the source. Adds per-line
 *  span IDs of the form `<idPrefix>-L<n>` for deep-linking. */
export async function highlightCode(
  code: string,
  language: string,
  idPrefix?: string,
): Promise<string> {
  const h = await highlighter();
  const lang = langKey(language);
  let html: string;
  try {
    html = h.codeToHtml(code, { lang, theme: "github-light" });
  } catch {
    html = `<pre class="shiki"><code>${escapeHtml(code)}</code></pre>`;
  }
  if (idPrefix) {
    let lineNo = 0;
    html = html.replace(/<span class="line"/g, () => {
      lineNo += 1;
      return `<span class="line" id="${idPrefix}-L${lineNo}"`;
    });
  }
  return html;
}

function escapeHtml(s: string): string {
  return s
    .replace(/&/g, "&amp;")
    .replace(/</g, "&lt;")
    .replace(/>/g, "&gt;");
}
