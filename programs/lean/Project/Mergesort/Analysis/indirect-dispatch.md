# Indirect table and dispatch analysis

Status: **complete for exclusion purposes**.  Dynamic hook/argument validation
is intentionally out of scope unless a reachable guard can enter this
component.

The module has one table of fixed size 18.  Slot zero is null; the element
segment initializes slots 1--17 exactly as follows.

| Slot | Absolute / local | Wasm type | Decoded role |
| ---: | --- | --- | --- |
| 1 | abs26 / `func23` | type0 `(i32,i32)->()` | default allocation-error hook |
| 2 | abs18 / `func15` | type9 `(i32)->()` | drop String |
| 3 | abs41 / `func38` | type1 `(i32,i32,i32)->i32` | String `write_str` |
| 4 | abs40 / `func37` | type2 `(i32,i32)->i32` | String `write_char` |
| 5 | abs45 / `func42` | type1 | String `write_fmt` |
| 6 | abs39 / `func36` | type2 | StaticStrPayload `fmt` |
| 7 | abs38 / `func35` | type0 | StaticStrPayload `take_box` |
| 8 | abs36 / `func33` | type0 | StaticStrPayload `get` |
| 9 | abs37 / `func34` | type0 | StaticStrPayload `as_str` |
| 10 | abs19 / `func16` | type9 | drop FormatStringPayload |
| 11 | abs35 / `func32` | type2 | FormatStringPayload `fmt` |
| 12 | abs43 / `func40` | type0 | FormatStringPayload `take_box` |
| 13 | abs42 / `func39` | type0 | FormatStringPayload `get` |
| 14 | abs44 / `func41` | type0 | FormatStringPayload `as_str` |
| 15 | abs34 / `func31` | type0 | `&str` TypeId |
| 16 | abs33 / `func30` | type0 | String TypeId |
| 17 | abs57 / `func54` | type2 | u32 Display `fmt` |

Wasm's `call_indirect` checks both table bounds/non-nullness and the exact type.
These decoded targets are used only to establish the shape of the excluded
subgraph.  No high-level vtable predicate or callee contract is introduced
while all dispatch roots remain unreachable.

## Indirect call sites

## Frozen vtable records

All words below were decoded from the single data segment beginning at memory
address `1048576` in the frozen stripped Wasm.

### String writer vtable at `1049112`

```text
+0  drop slot 2       +4 size 12       +8 alignment 4
+12 write_str slot 3  +16 write_char slot 4  +20 write_fmt slot 5
```

These words confirm that excluded formatter calls through offsets 12 and 16
target the decoded String writer functions.  Offset 20 is used when an
excluded formatting API selects the full write-fmt method.

### StaticStrPayload vtable at `1049136`

```text
+0  no drop (slot 0)  +4 size 8        +8 alignment 4
+12 fmt slot 6        +16 take_box slot 7
+20 get slot 8        +24 as_str slot 9
```

### FormatStringPayload vtable at `1049164`

```text
+0  drop slot 10      +4 size 16       +8 alignment 4
+12 fmt slot 11       +16 take_box slot 12
+20 get slot 13       +24 as_str slot 14
```

The two TypeId-only records are also visible:

```text
at 1049224: no drop, size 8, alignment 4, TypeId slot 15 (`&str`)
at 1049240: drop slot 2, size 12, alignment 4, TypeId slot 16 (String)
```

### Rust OOM selector: absolute func21 / local `func18`

One type0 call loads `(alignment,size)` from the Layout pointer and the selector
cell at `1049504`.  Selector zero is replaced by slot one; a nonzero selector is
used directly.  The exact initial state therefore resolves to `func23`.
If this component ever becomes reachable and the scope is reopened, a future
analysis would have to restrict nonzero selectors to registered type0 handlers
or account for the exact indirect-call trap.  The current valid-input proof
does neither because it proves the incoming allocation-error guard false.

### `panic_with_hook`: absolute func25 / local `func22`

Three syntactic type0 sites load:

- payload method at vtable offset 20, now resolved to static `get` slot 8 or
  formatted `get` slot 13;
- configured hook method at hook-vtable offset 20; and
- payload method at vtable offset 24, now resolved to static `as_str` slot 9 or
  formatted `as_str` slot 14.

These offsets show that all payload-method and hook dispatch remains inside the
excluded panic component.  Payload ownership and the dynamically configured
hook are therefore not modeled by predicates in the valid-input proof.

### Formatting engine: absolute func51 / local `func48`

Type1 sites call the Writer's `write_str` slot loaded from Writer vtable offset
12 for literal pieces and trailing strings.  Type2 sites load a formatter slot
from each eight-byte argument descriptor and call it on `(argument,Formatter)`.
For this binary, formatter descriptors may resolve to static payload fmt
(slot6), format payload fmt (slot11), or u32 Display (slot17).

### Integral padding: absolute func53 / local `func50`

Type2 calls use Writer vtable offset 16 for repeated fill characters.  Type1
calls use offset 12 for digit/prefix byte strings.

### Prefix helper: absolute func55 / local `func52`

The type2 call at line 3467 writes a sign character through Writer offset 16;
the type1 call at line 3484 writes a prefix through offset 12.  The special
scalar `1114112` means no sign character.  The helper returns immediately on
the first nonzero status.

### Formatter string adapter: absolute func56 / local `func53`

The sole type1 call loads the underlying writer and its vtable from Formatter,
then dispatches offset 12 with the source pointer/length.

## Scope consequence

No indirect call is reachable under the valid-input invariants.  This table and
vtable decoding are exclusion evidence only; the indirect callees receive no WP
specifications or proofs.  The reachable proof instead establishes, at each
guard in `func1`, `func2`, and `func3`, that control never enters the component
containing these dispatches.  Dynamic hook and formatter-descriptor semantics
need investigation only if that reachability result changes.
