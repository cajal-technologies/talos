# Hand-authored metadata for the mergesort proof ledger.
# Keyed by wasm function index. Lean name = func{idx-2} for idx >= 2.

CATEGORIES = {
    'entry':      ('Entry point', 'The exported wasm function driving the whole program.'),
    'core':       ('Sort algorithm', 'The recursive merge sort over 64-bit words in linear memory. The generic merge was inlined into the recursion at opt-level 3.'),
    'io':         ('Host I/O seam', 'The two stdio imports and the buffered reader/writer machinery between the program and the host.'),
    'parse':      ('Input parsing', 'Splitting the input line on spaces and parsing each token as a u64.'),
    'fmtout':     ('Output formatting', 'The core::fmt pipeline that renders each u64 in base ten and pads it into the writer.'),
    'alloc':      ('Vec growth & alloc shims', 'RawVec growth logic and the __rust_alloc/__rdl_* shims that route it into dlmalloc.'),
    'dlmalloc':   ('dlmalloc', 'The bundled dlmalloc allocator: malloc, free, realloc, memalign and chunk bookkeeping.'),
    'panic':      ('Panic runtime', 'The panic/abort machinery. Every path through here ends in __rust_abort (an unreachable trap). The proof obligation is that none of these are ever entered.'),
    'coldfmt':    ('Diagnostic formatting', 'Debug/Display impls and fmt builders that are only reachable while formatting a panic or io-error message. Unreachable under the spec precondition.'),
    'intrinsic':  ('Compiler intrinsics', 'compiler-builtins routines the codegen calls directly.'),
}

CATEGORY_ORDER = ['entry', 'core', 'parse', 'io', 'fmtout', 'alloc', 'dlmalloc', 'intrinsic', 'panic', 'coldfmt']

# category assignment
CAT = {
    0: 'io', 1: 'io',
    15: 'entry',
    14: 'core',
    3: 'parse', 86: 'parse', 112: 'parse', 120: 'intrinsic', 121: 'intrinsic',
    21: 'io', 22: 'io', 23: 'io', 4: 'io', 5: 'io', 50: 'io', 68: 'io', 53: 'io',
    10: 'io', 11: 'io', 26: 'io', 27: 'io',
    7: 'fmtout', 8: 'fmtout', 9: 'fmtout', 82: 'fmtout', 84: 'fmtout',
    97: 'fmtout', 98: 'fmtout', 99: 'fmtout',
    12: 'alloc', 13: 'alloc', 25: 'alloc', 33: 'alloc',
    16: 'alloc', 17: 'alloc', 18: 'alloc', 19: 'alloc', 20: 'alloc',
    37: 'alloc', 41: 'alloc', 43: 'alloc', 47: 'alloc',
    38: 'dlmalloc', 39: 'dlmalloc', 42: 'dlmalloc', 44: 'dlmalloc',
    45: 'dlmalloc', 51: 'dlmalloc', 75: 'dlmalloc',
    # panic runtime
    24: 'panic', 28: 'panic', 29: 'panic', 30: 'panic', 31: 'panic', 32: 'panic',
    34: 'panic', 35: 'panic', 36: 'panic', 40: 'panic', 46: 'panic', 48: 'panic',
    49: 'panic', 52: 'panic', 54: 'panic', 55: 'panic', 59: 'panic', 60: 'panic',
    61: 'panic', 64: 'panic', 69: 'panic', 70: 'panic', 73: 'panic', 58: 'panic',
    76: 'panic', 77: 'panic', 78: 'panic', 79: 'panic', 80: 'panic', 81: 'panic',
    89: 'panic', 105: 'panic', 106: 'panic', 109: 'panic', 110: 'panic', 113: 'panic',
}
# everything unassigned -> coldfmt
for i in list(range(0, 122)):
    CAT.setdefault(i, 'coldfmt')

# happy-path set: functions that execute on a well-formed input
HAPPY = {0, 1, 15, 14, 3, 86, 112, 120, 121,
         21, 22, 23, 4, 5, 50, 68, 53,
         8, 82, 84, 97, 98, 99,
         13, 12, 16, 17, 18, 19, 20,
         37, 38, 39, 41, 42, 43, 44, 45, 47, 51, 75}

# ---------------------------------------------------------------------------
# Descriptions + properties for the load-bearing functions.
# desc: contract prose. props: list of (name, statement) with Lean-ish twp text.
# ---------------------------------------------------------------------------

M = {}

M[15] = dict(short='mergesort (entry)', desc=(
    "The exported entry point, wasm export <code>\"mergesort\"</code>. No parameters, no results; all "
    "observable behaviour flows through the two stdio imports. It (1) builds the buffered ExtIO pair, "
    "(2) reads one line from stdin into a heap <code>String</code>, (3) splits on <code>' '</code> and parses every token "
    "as <code>u64</code> into a <code>Vec&lt;u64&gt;</code> (panicking on malformed input), (4) allocates a zeroed scratch "
    "vector of the same length, (5) calls the recursive sort, and (6) writes the sorted values back "
    "space-separated with no trailing newline, flushing the BufWriter on drop.<br><br>"
    "<b>Before:</b> fresh store from <code>initialStore</code>: globals at their initial values (shadow-stack pointer "
    "= 1048576), data segment intact, heap above <code>__heap_base</code> (1055536) unallocated, host state offering "
    "input bytes <code>encodeValues values</code>. <b>After:</b> host output stream equals <code>encodeValues sorted</code> where "
    "<code>sorted</code> is the unique sorted permutation of <code>values</code>; final memory/allocator state is existentially "
    "quantified away."), props=[
    ("twp_entry",
     "theorem twp_entry [WasmSmallStepGS hlc StdIO.State]\n"
     "    (values : List UInt64) (hfit : Fits values) :\n"
     "  stdioAt ⟨encodeValues values, []⟩ ∗ initialMemory ⊢\n"
     "  WP call \"mergesort\" [] [{ _ ⇒ ∃ sorted,\n"
     "      ⌜sorted.Pairwise (·≤·) ∧ values.Perm sorted⌝ ∗\n"
     "      stdioAt ⟨[], encodeValues sorted⟩ ∗ True }]"),
    ("mergesort_correct (endpoint)",
     "theorem mergesort_correct : Project.Mergesort.Spec.MergesortSpec\n"
     "-- ∀ input, ∃ output, RunsValues input output ∧ SortedPermutation input output\n"
     "-- via adequacy: twp_entry + SmallStepAdequacy ⇒ TerminatesWith ⇒ StdIO.Runs"),
])

M[14] = dict(short='mergesort::mergesort', desc=(
    "The recursive sort, monomorphised for <code>u64</code> with the generic <code>merge</code> fully inlined. "
    "Signature <code>(arr_ptr, arr_len, scratch_ptr, scratch_len) → ()</code> — two Rust fat slice references. "
    "For <code>len ≤ 1</code> returns immediately. Otherwise recurses on <code>[0, len/2)</code> and <code>[len/2, len)</code> (sharing the "
    "split scratch), merges the two sorted halves into scratch, then copies scratch back over arr.<br><br>"
    "<b>Before:</b> <code>arr_ptr</code> and <code>scratch_ptr</code> address disjoint in-bounds ranges of <code>8·len</code> bytes "
    "(the panic guards <code>slice_index_fail</code>, <code>panic_bounds_check</code>, <code>len_mismatch_fail</code> are all dominated by "
    "<code>scratch_len = arr_len</code> plus in-bounds slices, so they never fire). Uses only the value stack and its two "
    "memory regions — no allocation, no globals, no shadow stack frame. <b>After:</b> arr holds the sorted "
    "permutation, scratch holds junk, everything else in memory is untouched (frame rule)."), props=[
    ("twp_mergesort_rec",
     "theorem twp_mergesort_rec [WasmSmallStepGS hlc α]\n"
     "    (a s : UInt32) (arr scratch : List UInt64)\n"
     "    (hlen : scratch.length = arr.length)\n"
     "    (hdisj : Disjoint64 a arr.length s)      -- separation, given by ∗\n"
     "    (hfits : Fits64 a arr.length ∧ Fits64 s arr.length) :\n"
     "  array64At a arr ∗ array64At s scratch ⊢\n"
     "  WP call func12 [i32 a, i32 arr.length, i32 s, i32 arr.length]\n"
     "    [{ rs ⇒ ⌜rs = []⌝ ∗ ∃ sorted junk,\n"
     "        ⌜sorted.Pairwise (·≤·) ∧ arr.Perm sorted⌝ ∗\n"
     "        array64At a sorted ∗ array64At s junk }]\n"
     "-- by strong induction on arr.length (well-founded twp_loop_wf_family)"),
    ("twp_merge_inlined",
     "-- inner lemma for the three inlined merge loops (mirrors\n"
     "-- CodeLib.Examples.MergeSort.TotalProof.twp_mergeMainLoop):\n"
     "theorem twp_merge_loops … :\n"
     "  MergeLoopInvariant arr scratch left mid right i j k emitted →\n"
     "  array64At a arr ∗ array64At s scratch ⊢ WP ⟨merge loops⟩\n"
     "    [{ _ ⇒ array64At s (mergedOf arr left mid right) ∗ array64At a arr }]"),
    ("twp_copy_back",
     "-- final copy_from_slice: scratch[0..len) overwrites arr[0..len)\n"
     "theorem twp_copy_back … :  array64At a arr ∗ array64At s merged ⊢\n"
     "  WP ⟨copy loop⟩ [{ _ ⇒ array64At a merged ∗ array64At s merged }]"),
])

M[3] = dict(short='parse iterator next', desc=(
    "<code>Map&lt;Split, parse&gt;::next</code>: pulls the next space-separated token out of the input string and parses "
    "it as <code>u64</code>. Out-params <code>(ret_ptr, iter_ptr)</code>: writes a 16-byte <code>Option&lt;Result&lt;u64, ParseIntError&gt;&gt;</code>-shaped "
    "value to <code>ret_ptr</code> and advances the iterator state in place. Calls <code>memchr</code> to find the next space, "
    "<code>memcmp</code> on candidate digits and <code>__multi3</code> for the overflow-checked <code>×10 + digit</code> accumulation.<br><br>"
    "<b>Before:</b> iterator state points at a live UTF-8 string slice; 16 free bytes at <code>ret_ptr</code> on the shadow "
    "stack. <b>After:</b> if the remaining input is <code>tok ++ ' ' ++ rest</code> with <code>tok</code> a decimal numeral fitting u64, "
    "returns <code>some (ok (parseU64 tok))</code> and the iterator advances past the space; at end of input returns "
    "<code>none</code>. The entry's precondition (well-formed input) rules out the error variant."), props=[
    ("twp_parse_next",
     "theorem twp_parse_next [WasmSmallStepGS hlc α]\n"
     "    (it : SplitIter) (toks : List (List UInt8)) (hwf : WfTokens toks) :\n"
     "  splitIterAt it toks ∗ scratch16At ret ⊢\n"
     "  WP call func1 [i32 ret, i32 it.ptr]\n"
     "    [{ _ ⇒ match toks with\n"
     "        | []      ⇒ optionU64At ret none ∗ splitIterAt it []\n"
     "        | t :: ts ⇒ optionU64At ret (some (parseU64 t)) ∗ splitIterAt it ts }]"),
])

M[86] = dict(short='from_utf8', desc=(
    "UTF-8 validation of the freshly read line before it becomes a <code>String</code>. <code>(ret_ptr, buf_ptr, buf_len)</code>; "
    "writes a <code>Result</code> discriminant (+ error position on failure) to <code>ret_ptr</code>. Pure: reads the byte "
    "range, writes only the return slot.<br><br><b>Property needed:</b> on ASCII input (which "
    "<code>encodeValues</code> always produces — digits and spaces) it returns <code>Ok</code>."), props=[
    ("twp_from_utf8_ascii",
     "theorem twp_from_utf8_ascii …\n"
     "    (hascii : ∀ b ∈ bytes, b < 128) :\n"
     "  bytesAt p bytes ∗ retAt r ⊢ WP call func84 [r, p, bytes.length]\n"
     "    [{ _ ⇒ bytesAt p bytes ∗ okAt r }]"),
])

M[112] = dict(short='memchr_aligned', desc=(
    "Word-at-a-time <code>memchr</code>: finds the first occurrence of a byte (here <code>'\\n'</code> for <code>read_line</code>, <code>' '</code> for "
    "the splitter) in a byte range. <code>(ret_ptr, needle, hay_ptr, hay_len)</code> writing <code>Option&lt;usize&gt;</code> to "
    "<code>ret_ptr</code>. Pure reader.<br><br><b>Property:</b> result is exactly <code>bytes.idxOf? needle</code> — first index "
    "or none, matching <code>List.findIdx?</code>."), props=[
    ("twp_memchr",
     "theorem twp_memchr …:  bytesAt p bytes ∗ retAt r ⊢\n"
     "  WP call func110 [r, i32 c, p, bytes.length]\n"
     "    [{ _ ⇒ bytesAt p bytes ∗ optionNatAt r (bytes.findIdx? (· = c)) }]"),
])

M[120] = dict(short='memcmp', desc=(
    "compiler-builtins byte comparison <code>(a, b, n) → i32</code>: sign of the first differing byte, 0 if the "
    "ranges are equal. Pure reader of both ranges."), props=[
    ("twp_memcmp",
     "theorem twp_memcmp …:  bytesAt a xs ∗ bytesAt b ys ∗ ⌜xs.length = n ∧ ys.length = n⌝ ⊢\n"
     "  WP call func118 [a, b, n] [{ rs ⇒ ⌜sign rs = compareLex xs ys⌝ ∗ bytesAt a xs ∗ bytesAt b ys }]"),
])

M[121] = dict(short='__multi3', desc=(
    "128-bit multiply from compiler-builtins: <code>(ret_ptr, a_lo, a_hi, b_lo, b_hi)</code> writes the 16-byte "
    "product <code>a·b mod 2¹²⁸</code> to <code>ret_ptr</code>. Used by the parser's overflow-checked <code>u64 × 10</code>. "
    "Register-level except for the 16-byte result slot; no branches, no calls."), props=[
    ("twp_multi3",
     "theorem twp_multi3 …:  scratch16At r ⊢\n"
     "  WP call func119 [r, i64 alo, i64 ahi, i64 blo, i64 bhi]\n"
     "    [{ _ ⇒ u128At r ((toU128 ahi alo) * (toU128 bhi blo)) }]\n"
     "-- pure bit-vector fact; close with bv_decide"),
])

M[0] = dict(short='stdio.read import', desc=(
    "Host import <code>stdio.read : (buf_ptr, buf_len) → n</code>. Reads at most <code>buf_len</code> bytes from the host "
    "input stream into memory at <code>buf_ptr</code>, returns the count (0 at EOF). Behaviour is fixed by "
    "<code>StdIO.env</code> / the relational <code>StdIO.spec</code> already proven compatible in <code>Spec.lean</code> "
    "(<code>stdio_env_satisfies</code>)."), props=[
    ("twp_host_read",
     "-- host rule (given by StdIO.spec, mirrors SelectionSort execute_read):\n"
     "theorem twp_host_read …:  stdioAt ⟨inp, out⟩ ∗ bytesAt p junk ⊢\n"
     "  WP callImport \"read\" [p, n] [{ rs ⇒ ⌜rs = [i32 (min n inp.length)]⌝ ∗\n"
     "      stdioAt ⟨inp.drop (min n inp.length), out⟩ ∗ bytesAt p (inp.take … ++ junk.drop …) }]"),
])

M[1] = dict(short='stdio.write import', desc=(
    "Host import <code>stdio.write : (buf_ptr, buf_len) → ()</code>. Appends the byte range to the host output "
    "stream. Total, never traps for in-bounds ranges."), props=[
    ("twp_host_write",
     "theorem twp_host_write …:  stdioAt ⟨inp, out⟩ ∗ bytesAt p bs ⊢\n"
     "  WP callImport \"write\" [p, bs.length]\n"
     "    [{ _ ⇒ stdioAt ⟨inp, out ++ bs⟩ ∗ bytesAt p bs }]"),
])

M[21] = dict(short='ExtIO::buffered', desc=(
    "Constructs the <code>(BufReader-ish, BufWriter&lt;ExtIO&gt;)</code> pair used by the entry: allocates the two "
    "buffers via <code>__rust_alloc</code> and writes the struct fields to the 8-byte out-slot. "
    "<b>After:</b> a fresh writer with empty buffer and a reader with empty lookahead; the error arm "
    "(<code>handle_error</code>) fires only on allocator exhaustion, excluded by the heap-budget invariant."), props=[
    ("twp_buffered",
     "theorem twp_buffered …:  heapBudget B ∗ scratchAt ret ⊢ WP call func19 [ret]\n"
     "  [{ _ ⇒ ∃ r w, extioAt ret r w ∗ bufWriterInv w [] ∗ heapBudget (B - bufBytes) }]"),
])

M[22] = dict(short='ExtIO Read::read', desc=(
    "Thin wrapper over the <code>stdio.read</code> import implementing <code>std::io::Read</code>: forwards the buffer, wraps "
    "the count in <code>Ok</code>. Never fails."), props=[
    ("twp_extio_read",
     "theorem twp_extio_read …:  stdioAt ⟨inp, out⟩ ∗ bytesAt p junk ⊢\n"
     "  WP call func20 [ret, self, p, n] [{ _ ⇒ okUsizeAt ret (min n inp.length) ∗ … }]"),
])

M[23] = dict(short='ExtIO Write::write', desc=(
    "Thin wrapper over the <code>stdio.write</code> import implementing <code>std::io::Write</code>: writes the whole "
    "buffer, returns <code>Ok(len)</code>. Never fails — this is what makes every downstream io::Error branch dead."), props=[
    ("twp_extio_write",
     "theorem twp_extio_write …:  stdioAt ⟨inp, out⟩ ∗ bytesAt p bs ⊢\n"
     "  WP call func21 [ret, self, p, bs.length]\n"
     "    [{ _ ⇒ okUsizeAt ret bs.length ∗ stdioAt ⟨inp, out ++ bs⟩ ∗ bytesAt p bs }]"),
])

M[5] = dict(short='BufWriter::flush_buf', desc=(
    "Drains the writer's internal buffer into <code>ExtIO::write</code> in a loop (via the vtable, dispatching to "
    "func 23), tracking partial writes with the <code>BufGuard</code> helper pair (funcs 50, 68). Since ExtIO::write "
    "always accepts everything, exactly one iteration runs.<br><b>After:</b> buffer empty, buffered bytes "
    "appended to host output."), props=[
    ("twp_flush_buf",
     "theorem twp_flush_buf …:  bufWriterInv w pending ∗ stdioAt ⟨inp, out⟩ ⊢\n"
     "  WP call func3 [ret, w] [{ _ ⇒ okAt ret ∗ bufWriterInv w [] ∗ stdioAt ⟨inp, out ++ pending⟩ }]"),
])

M[4] = dict(short='BufWriter::write_all_cold', desc=(
    "Slow path of <code>BufWriter::write</code>: taken when a write does not fit the spare buffer capacity — "
    "flushes, then either buffers the payload or forwards oversized payloads straight to the sink. "
    "<b>After:</b> the payload bytes are logically appended to the writer's pending stream."), props=[
    ("twp_write_all_cold",
     "theorem twp_write_all_cold …:  bufWriterInv w pending ∗ bytesAt p bs ∗ stdioAt σ ⊢\n"
     "  WP call func2 [ret, w, p, bs.length]\n"
     "    [{ _ ⇒ okAt ret ∗ ∃ pending' σ', ⌜stream σ' pending' = stream σ (pending ++ bs)⌝ ∗ … }]"),
])

M[8] = dict(short='Adapter::write_str', desc=(
    "The bridge from <code>core::fmt</code> into the BufWriter: <code>std::io::default_write_fmt::Adapter</code>'s "
    "<code>Write::write_str</code>, the vtable slot that <code>core::fmt::write</code> actually invokes while printing. Copies "
    "the str into the writer buffer (fast path inline, cold path via func 4), records any error in the "
    "adapter state (never happens here)."), props=[
    ("twp_adapter_write_str",
     "theorem twp_adapter_write_str …:  adapterInv a w pending ∗ strAt p s ⊢\n"
     "  WP call func6 [a, p, s.utf8Len] [{ rs ⇒ ⌜rs = [i32 0]⌝ ∗ adapterInv a w (pending ++ s.bytes) ∗ strAt p s }]"),
])

M[82] = dict(short='u64 Display::fmt', desc=(
    "Formats a <code>u64</code> in base ten: repeated division producing digits into a 39-byte stack buffer, then "
    "hands the digit str to <code>Formatter::pad_integral</code>. This is the itoa core of the output path.<br>"
    "<b>Property:</b> with a default formatter (no width/flags — which is what <code>write!(\"{}\")</code> passes) it "
    "emits exactly <code>toString n</code> to the underlying writer."), props=[
    ("twp_u64_display",
     "theorem twp_u64_display …:  u64RefAt self n ∗ formatterInv f w pending defaultOpts ⊢\n"
     "  WP call func80 [self, f] [{ rs ⇒ ⌜rs = [i32 0]⌝ ∗\n"
     "      formatterInv f w (pending ++ (toString n).toUTF8) ∗ u64RefAt self n }]\n"
     "-- digit-loop invariant mirrors the itoa recipe (divmod peeling)"),
])

M[84] = dict(short='core::fmt::write', desc=(
    "The formatting interpreter: walks the <code>Arguments</code> piece/arg tables, emitting literal pieces via the "
    "output vtable's <code>write_str</code> and each argument via its formatter function pointer "
    "(<code>call_indirect</code>, types 2 and 3). The entry only ever builds two shapes of <code>Arguments</code>: a lone "
    "<code>\"{}\"</code> u64 and the literal <code>\" \"</code> separator, so only vtable targets 8 (Adapter::write_str) and 82 "
    "(u64 Display) are exercised on the happy path.<br><b>Assumption:</b> piece/arg tables live in the data "
    "segment (read-only), vtable pointers valid table indices."), props=[
    ("twp_fmt_write_u64",
     "theorem twp_fmt_write_u64 …:  adapterInv a w pending ∗ argsU64At args n ⊢\n"
     "  WP call func82 [ret, a, vt_adapter, args]\n"
     "    [{ _ ⇒ okAt ret ∗ adapterInv a w (pending ++ (toString n).toUTF8) }]"),
    ("twp_fmt_write_lit",
     "theorem twp_fmt_write_lit …:  adapterInv a w pending ∗ argsLitAt args s ⊢\n"
     "  WP call func82 [ret, a, vt_adapter, args]\n"
     "    [{ _ ⇒ okAt ret ∗ adapterInv a w (pending ++ s.toUTF8) }]"),
])

M[97] = dict(short='Formatter::pad_integral', desc=(
    "Applies sign/prefix/width/fill around a formatted integer body. With default options (the only ones "
    "the entry creates) it reduces to: write prefix (empty) then write the digit str once via the vtable. "
    "Calls <code>do_count_chars</code> only when a width is set — dead here, but the spec keeps the general "
    "hypothesis <code>opts = default</code> to skip it."), props=[
    ("twp_pad_integral_default",
     "theorem twp_pad_integral_default …:\n"
     "  formatterInv f out pending defaultOpts ∗ strAt p digits ⊢\n"
     "  WP call func95 [f, 1, empty, p, digits.len]\n"
     "    [{ rs ⇒ ⌜rs = [i32 0]⌝ ∗ formatterInv f out (pending ++ digits.bytes) }]"),
])

M[99] = dict(short='pad_integral::write_prefix', desc=(
    "Helper of <code>pad_integral</code>: writes the sign char and radix prefix if present. With default options "
    "both are absent and it returns <code>Ok</code> without touching the writer."), props=[
    ("twp_write_prefix_empty",
     "theorem twp_write_prefix_empty …:  formatterInv f out pending opts ⊢\n"
     "  WP call func97 [f, out_vt, 0, 0, 0] [{ rs ⇒ ⌜rs = [i32 0]⌝ ∗ formatterInv f out pending opts }]"),
])

M[98] = dict(short='do_count_chars', desc=(
    "Counts UTF-8 chars word-at-a-time; used by padding logic only when a width option is set. Dead on the "
    "happy path (default options); a pure-reader spec is easy if ever needed."), props=[
    ("(unreachable on happy path)",
     "-- guarded by opts.width = none in twp_pad_integral_default;\n"
     "-- no spec required for the endpoint theorem"),
])

M[13] = dict(short='RawVec reserve (do_reserve_and_handle)', desc=(
    "Out-of-line Vec growth used while pushing parsed u64s: computes a new capacity (amortised doubling), "
    "calls <code>finish_grow</code> (func 12), on failure diverts to <code>handle_error</code>. "
    "<b>After (success):</b> the Vec's buffer pointer/capacity updated, old contents preserved — the "
    "allocator returns fresh disjoint memory and frees the old block."), props=[
    ("twp_reserve",
     "theorem twp_reserve …:  vecInv v xs cap ∗ heapBudget B ∗ ⌜xs.length = cap⌝ ⊢\n"
     "  WP call func11 [v, cap, 1, 8, addl]\n"
     "    [{ _ ⇒ ∃ cap' ≥ cap + addl, vecInv v xs cap' ∗ heapBudget (B - growth) }]\n"
     "-- heapBudget B excludes the alloc-failure branch: dlmalloc with one\n"
     "-- 17-page memory always satisfies requests below the budget"),
])

M[12] = dict(short='RawVec finish_grow', desc=(
    "Performs the actual (re)allocation for Vec growth: <code>__rust_alloc</code> for a fresh buffer or "
    "<code>__rust_realloc</code> to extend, reporting <code>(ptr, size) | err</code> through an out-struct. Also checks "
    "<code>__rust_no_alloc_shim_is_unstable_v2</code> (a no-op probe)."), props=[
    ("twp_finish_grow",
     "theorem twp_finish_grow …:  heapBudget B ∗ oldBlockAt p old ∗ ⌜new ≤ B⌝ ⊢\n"
     "  WP call func10 [ret, new, 8, old_layout…]\n"
     "    [{ _ ⇒ ∃ q, okBlockAt ret q new ∗ bytesAt q (old ++ junk) ∗ heapBudget (B - Δ) }]"),
])
M[33] = dict(short='RawVec finish_grow (2nd mono)', desc=(
    "Second monomorphisation of <code>finish_grow</code> (identical body shape to func 12) reached from the "
    "String/Vec&lt;u8&gt; growth in <code>read_line</code>. Same spec as func 12."), props=[
    ("twp_finish_grow'", "-- same statement as twp_finish_grow, at func31")])
M[25] = dict(short='RawVec reserve (String path)', desc=(
    "Second monomorphisation of <code>do_reserve_and_handle</code> used by <code>String::push_str</code>/<code>read_line</code> "
    "growth. Same spec as func 13."), props=[
    ("twp_reserve'", "-- same statement as twp_reserve, at func23")])

for i, nm, tgt in [(16, '__rust_alloc', '__rdl_alloc'), (17, '__rust_dealloc', '__rdl_dealloc'),
                   (18, '__rust_realloc', '__rdl_realloc'), (19, '__rust_alloc_zeroed', '__rdl_alloc_zeroed')]:
    M[i] = dict(short=nm, desc=(
        f"Allocator shim: tail-calls <code>{tgt}</code>. Contract is exactly the callee's; kept as a separate "
        "one-line lifting lemma so call sites never unfold allocator internals."), props=[
        (f"twp_{nm}", f"-- lifting: twp of func maps directly to twp_{tgt}")])
M[20] = dict(short='__rust_no_alloc_shim_is_unstable_v2', desc=(
    "Empty probe function (body is a single <code>end</code>); exists so the linker keeps the alloc shims. "
    "Trivial spec: no-op."), props=[
    ("twp_noop", "theorem twp_noop …:  emp ⊢ WP call func18 [] [{ rs ⇒ ⌜rs = []⌝ }]")])

M[37] = dict(short='__rdl_alloc', desc=(
    "Default-allocator entry: for align ≤ 8 calls <code>malloc</code>, else <code>memalign</code>. All layouts in this "
    "program have align ≤ 8, so only the malloc arm is live."), props=[
    ("twp_rdl_alloc",
     "theorem twp_rdl_alloc …:  dlmallocInv h ∗ ⌜size ≤ budget h⌝ ⊢\n"
     "  WP call func35 [size, align] [{ rs ⇒ ∃ p ≠ 0, ⌜rs = [i32 p]⌝ ∗\n"
     "      blockAt p size ∗ dlmallocInv (h.alloc p size) }]")])
M[39] = dict(short='dlmalloc::malloc', desc=(
    "The core allocator. Maintains the dlmalloc heap structure above <code>__heap_base</code>: small-bin exact "
    "fit, tree-bin best fit, else carve from the top chunk; first call grows via <code>sys::alloc</code> "
    "(<code>memory.grow</code>-backed, func 75). <b>This is the hard modelling target</b> — the proof needs an "
    "abstract heap predicate <code>dlmallocInv</code> relating the free-list/bin structure to a set of live "
    "disjoint blocks, plus a budget argument making failure unreachable at this program's allocation "
    "profile (≤ a few KiB live at once against a 17-page memory)."), props=[
    ("twp_malloc",
     "theorem twp_malloc …:  dlmallocInv h ∗ ⌜size ≤ budget h⌝ ⊢\n"
     "  WP call func37 [size] [{ rs ⇒ ∃ p, ⌜rs = [i32 p] ∧ p ≠ 0 ∧ aligned8 p⌝ ∗\n"
     "      blockAt p size ∗ dlmallocInv (h.alloc p size) }]"),
    ("dlmallocInv (definition)",
     "-- the load-bearing abstraction:\n"
     "def dlmallocInv (h : AbstractHeap) : IProp … :=\n"
     "  chunkChain h.chunks ∗ binMaps h ∗ topChunkAt h.top ∗\n"
     "  ⌜wellFormed h ∧ blocks h pairwise-disjoint ∧ above __heap_base⌝"),
])
M[42] = dict(short='dlmalloc::free', desc=(
    "Returns a block: coalesces with free neighbours (<code>unlink_chunk</code>/<code>insert_large_chunk</code>), "
    "updates bins or top chunk."), props=[
    ("twp_free",
     "theorem twp_free …:  dlmallocInv h ∗ blockAt p size ⊢\n"
     "  WP call func40 [self, p] [{ _ ⇒ dlmallocInv (h.free p) }]")])
M[38] = dict(short='dlmalloc::memalign', desc=(
    "Aligned allocation: over-allocates then trims. Dead in this program (all aligns ≤ 8) — needs only an "
    "unreachability note, or the general spec if we want robustness."), props=[
    ("(dead branch)", "-- align ≤ 8 at every call site ⇒ never called; no spec needed")])
M[43] = dict(short='__rdl_realloc', desc=(
    "Realloc shim: for align ≤ 8 delegates to a malloc+memcpy+free sequence or in-place growth via "
    "dlmalloc realloc logic (inlined here: calls malloc 39, free 42, dispose_chunk 45…). "
    "<b>After:</b> a block of the new size whose prefix holds the old bytes."), props=[
    ("twp_rdl_realloc",
     "theorem twp_rdl_realloc …:  dlmallocInv h ∗ blockAt p old ∗ bytesAt p bs ∗ ⌜new ≤ budget⌝ ⊢\n"
     "  WP call func41 [p, old, 8, new] [{ rs ⇒ ∃ q ≠ 0, ⌜rs = [i32 q]⌝ ∗\n"
     "      blockAt q new ∗ bytesAt q (bs.take (min old new) ++ junk) ∗ dlmallocInv h' }]")])
M[47] = dict(short='__rdl_alloc_zeroed', desc=(
    "Zeroed allocation (used for <code>vec![0; len]</code> scratch): malloc then the fresh block is zero-filled. "
    "dlmalloc's fresh-from-top memory is zero because linear memory grows zeroed — the spec still asserts "
    "zeros explicitly."), props=[
    ("twp_alloc_zeroed",
     "theorem twp_alloc_zeroed …:  dlmallocInv h ∗ ⌜size ≤ budget h⌝ ⊢\n"
     "  WP call func45 [size, align] [{ rs ⇒ ∃ p ≠ 0, ⌜rs = [i32 p]⌝ ∗\n"
     "      bytesAt p (List.replicate size 0) ∗ blockAt p size ∗ dlmallocInv h' }]")])
M[44] = dict(short='unlink_chunk', desc=(
    "Removes a chunk from its bin (small-bin doubly-linked unlink or tree-bin surgery). Internal helper — "
    "specified as a pure transformation of <code>dlmallocInv</code>'s bin maps."), props=[
    ("twp_unlink_chunk",
     "theorem twp_unlink_chunk …:  binMaps h ∗ ⌜c ∈ h.bins⌝ ⊢\n"
     "  WP call func42 [self, c] [{ _ ⇒ binMaps (h.unlink c) }]")])
M[45] = dict(short='dispose_chunk', desc=(
    "Frees a chunk during realloc trimming: coalesce + reinsert. Same abstraction level as free."), props=[
    ("twp_dispose_chunk", "-- dlmallocInv h ∗ chunkAt c ⊢ WP … [{ _ ⇒ dlmallocInv (h.free c) }]")])
M[51] = dict(short='insert_large_chunk', desc=(
    "Inserts a free chunk into the tree bins. Helper of free/dispose; pure bin-map transformation."), props=[
    ("twp_insert_large_chunk", "-- binMaps h ⊢ WP … [{ _ ⇒ binMaps (h.insert c) }]")])
M[75] = dict(short='sys::System alloc', desc=(
    "Grows linear memory: <code>memory.grow</code> by the requested page count, returns the old boundary as the "
    "new arena. The interpreter's grow rule gives back zeroed pages; failure (grow returning −1) is "
    "excluded because the program's total demand fits the initial 17 pages + slack."), props=[
    ("twp_sys_alloc",
     "theorem twp_sys_alloc …:  memPages n ∗ ⌜n + pages ≤ maxPages⌝ ⊢\n"
     "  WP call func73 [ret, size, flags] [{ _ ⇒ ∃ p, arenaAt ret p size ∗\n"
     "      bytesAt p (replicate size 0) ∗ memPages (n + pages) }]")])

M[50] = dict(short='BufGuard::remaining', desc=(
    "Helper of flush_buf: returns the not-yet-flushed slice of the buffer. Pure reader; the "
    "<code>slice_index_fail</code> guard is dominated by the flush-loop invariant <code>written ≤ len</code>."), props=[
    ("twp_bufguard_remaining",
     "-- guardInv g buf written ⊢ WP call func48 [ret, g]\n"
     "--   [{ _ ⇒ sliceAt ret (buf.drop written) ∗ guardInv g buf written }]")])
M[68] = dict(short='BufGuard::drop', desc=(
    "Drop glue of the flush guard: shifts any unflushed tail to the buffer start (memmove) and stores the "
    "new length. In the always-successful write case the tail is empty and it just zeroes the length."), props=[
    ("twp_bufguard_drop",
     "-- guardInv g buf buf.length ⊢ WP call func66 [g] [{ _ ⇒ bufWriterInv w [] }]")])
M[53] = dict(short='io::Guard::drop', desc=(
    "Drop glue of <code>read_line</code>'s UTF-8 guard: truncates the String's length back to the validated "
    "prefix. On the happy path (validation succeeded) it is a no-op store of the full length."), props=[
    ("twp_ioguard_drop",
     "-- stringInv s bytes ⊢ WP call func51 [g] [{ _ ⇒ stringInv s bytes }]")])

M[10] = dict(short='drop Adapter<BufWriter>', desc=(
    "Drop glue for the write-side adapter: frees the BufWriter's buffer via <code>__rust_dealloc</code>. Runs "
    "once at entry exit, flushing already done."), props=[
    ("twp_drop_adapter", "-- bufWriterInv w [] ∗ dlmallocInv h ⊢ WP … [{ _ ⇒ dlmallocInv (h.free w.buf) }]")])
M[11] = dict(short='drop io::Error', desc=(
    "Drop glue for <code>std::io::Error</code>; frees the boxed payload if present. Only reachable on error "
    "paths — dead under the spec precondition."), props=[("(dead)", "-- unreachable: ExtIO never returns Err")])
M[26] = dict(short='drop Option<Vec<u8>>', desc=(
    "Drop glue used when read_line's internal state unwinds. Only the <code>none</code>/already-moved case runs "
    "on the happy path (no-op) — the freeing arm is panic-path only."), props=[
    ("twp_drop_none", "-- emp ⊢ WP … [{ _ ⇒ emp }] in the happy-path (none) case")])
M[27] = dict(short='drop String', desc=(
    "Drop glue for the input String: <code>__rust_dealloc</code> of its buffer at entry exit."), props=[
    ("twp_drop_string", "-- stringInv s bs ∗ dlmallocInv h ⊢ WP … [{ _ ⇒ dlmallocInv (h.free s.buf) }]")])

M[7] = dict(short='Write::write_char (adapter)', desc=(
    "Default <code>write_char</code> for the io Adapter: encodes the char to UTF-8 on the stack and forwards to "
    "write_str. Reachable only for padded formatting — dead with default options."), props=[
    ("(dead branch)", "-- default fmt options ⇒ fmt::write never calls the write_char slot")])
M[9] = dict(short='Write::write_fmt (adapter)', desc=(
    "Default vtable <code>write_fmt</code>: re-enters <code>core::fmt::write</code> with the same output. Not exercised "
    "by the entry's two Arguments shapes."), props=[("(dead branch)", "-- not called for piece-only / single-{} Arguments")])

# --- generic templates for the rest ---
PANIC_DESC = ("Panic-path function. Under the spec precondition (well-formed input, heap budget respected, "
              "in-bounds slices) every call site is dominated by a branch we prove is not taken. All routes "
              "end in <code>__rust_abort</code> → <code>unreachable</code>, i.e. a <code>.Trap</code> — so for total correctness these "
              "must simply never execute.")
PANIC_PROP = [("unreachable_under_spec",
               "-- obligation at each call site: the guarding branch condition is false.\n"
               "-- no twp spec: the function never appears in a happy-path derivation.")]
COLDFMT_DESC = ("Diagnostic formatting: only reachable while rendering a panic or io-error message "
                "(Debug/Display of error payloads, fmt builders, unicode tables). Transitively dead once the "
                "panic runtime is proven unreachable.")
COLDFMT_PROP = [("transitively_dead",
                 "-- reachable only from the panic/error cone; covered by its unreachability.")]
