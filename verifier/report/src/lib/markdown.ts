import { Marked } from "marked";
import markedKatex from "marked-katex-extension";

const marked = new Marked();
marked.use(
  markedKatex({
    throwOnError: false,
    nonStandard: true,
  }),
);
marked.setOptions({ gfm: true, breaks: false });

/** Render an informal-spec / docstring blob as HTML.
 *  Markdown with GFM, plus inline/display KaTeX (`$…$`, `$$…$$`). */
export function renderMarkdown(src: string | null | undefined): string {
  if (!src) return "";
  return marked.parse(src) as string;
}
