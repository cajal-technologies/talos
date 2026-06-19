# Verifying a Rust std function and reusing it

The exact steps to add one function of a primitive type, prove it once in
CodeLib, and reuse it in another program. Run all commands from `programs/`.

---

## The crate: one per primitive type

One crate per primitive type — `rust_u64`, `rust_u32`, … accumulating all
of that type's functions over time. This is done via:

```bash
just verifier-add rust_u64
```



The files should be:



`rust/rust_u64/src/lib.rs`

```rust
mod exports;
```

`rust/rust_u64/src/exports.rs`



```rust
#[unsafe(no_mangle)]
pub extern "C" fn abs_diff(a: u64, b: u64) -> u64 {
    a.abs_diff(b)
}

#[unsafe(no_mangle)]
pub extern "C" fn entrypoint(a: u64, b: u64) {
    let _ = abs_diff(a, b);
}
```





One `#[unsafe(no_mangle)] pub extern "C"` wrapper
per method, plus a single `entrypoint` that calls all of them so nothing is
dropped. **This file grows**: each new function appends one wrapper
and one line in `entrypoint`.

---

## Example: prove `u64::abs_diff` in CodeLib

### 1. Create the crate (first time only)
```bash
just verifier-add rust_u64
```

### 2. Write the source files
`rust/rust_u64/src/lib.rs`:
```rust
mod exports;
```
`rust/rust_u64/src/exports.rs`:
```rust
#[unsafe(no_mangle)]
pub extern "C" fn abs_diff(a: u64, b: u64) -> u64 {
    a.abs_diff(b)
}

#[unsafe(no_mangle)]
pub extern "C" fn entrypoint(a: u64, b: u64) {
    let _ = abs_diff(a, b);
}
```

### 3. Compile to wasm and transpile to Lean
```bash
just verifier-build rust_u64
just verifier-emit --force-emit rust_u64
```

### 4. Find the function index
Open `lean/Project/RustU64/Program.lean`. In the `exports` list, `abs_diff`
points to a wrapper function whose body is just `localGet …; .call N; ret`, it
forwards to the real implementation, the inner `core::num::abs_diff`. **Lift `N`**
(in this run the wrapper was index 1 and `N = 0`).

### 5. Lift it
```bash
just verifier-lift rust_u64 0 U64 absDiff
```
Where:

- `rust_u64` is the crate

- `0` is the index found in Program.lean
- `U64` is the name of the lean counterpart of the rust primitive
- `absDiff` is the name to choose of the new function in codelib



This writes `codelib/CodeLib/RustStd/U64/AbsDiff.lean`: the body copied verbatim
(`absDiffBody`, `absDiffFunc` complete) and a theorem stub with two things to fill in

the `Returns` result, written `(sorry : Value)`, and the proof, written `sorry`.

### 6. Fill the result and the proof
Filling the two things is the only step that needs Lean. The reusable theorem
stays in **`wp` form about the body**.



```lean
import CodeLib.RustStd.Frame
import Interpreter.Wasm.Wp.Tactic
import Interpreter.Wasm.Wp.Block
import CodeLib.Entry

namespace Wasm.RustStd.U64

open Wasm

def absDiffBody : Program :=
  [
  .globalGet 0, .const (16 : UInt32), .sub, .localSet 2,
  .block 0 0 [
    .block 0 0 [
      .localGet 0, .localGet 1, .ltUI64, .const (1 : UInt32), .and, .br_if 0,
      .localGet 2, .localGet 0, .localGet 1, .subI64, .store64 (8 : UInt32), .br 1
    ],
    .localGet 2, .localGet 1, .localGet 0, .subI64, .store64 (8 : UInt32)
  ],
  .localGet 2, .load64 (8 : UInt32), .ret
]

def absDiffFunc : Function :=
  { params := [.i64, .i64], locals := [.i32], body := absDiffBody, results := [.i64] }

set_option maxRecDepth 4096 in
/-- `u64::abs_diff a b = if a < b then b - a else a - b`. -/
theorem absDiff_wp {α} {m : Module} {env : HostEnv α} (st : Store α)
    (sp : UInt32) (a : UInt64) (b : UInt64) (vs : List Value)
    (hsp : st.globals.globals[0]? = some (.i32 sp))
    (hlo : 16 ≤ sp.toNat) (hhi : sp.toNat ≤ st.mem.pages * 65536) :
    wp m absDiffBody
      (Returns (.i64 (if a < b then b - a else a - b) :: vs)        -- hole 1: the result
        (fun st' => st'.globals = st.globals ∧ st'.mem.pages = st.mem.pages))
      st ⟨[.i64 a, .i64 b], [.i32 0], vs⟩ env := by
  unfold absDiffBody Returns                                        -- hole 2: the proof
  wp_run
  simp only [hsp]
  apply wp_block_cons
  apply wp_block_cons
  wp_run
  have hle : (16 : UInt32) ≤ sp := UInt32.le_iff_toNat_le.mpr (by simpa using hlo)
  have hsub : (sp - 16).toNat = sp.toNat - 16 := UInt32.toNat_sub_of_le sp 16 hle
  have hnt : ¬ ((sp - 16).toNat + 8 + 8 > st.mem.pages * 65536) := by rw [hsub]; omega
  have h8 : ((8 : UInt32)).toNat = 8 := rfl
  by_cases hab : a < b <;>
    simp [hab, h8, hnt, Mem.read64_write64_same, Mem.write64_pages]

end Wasm.RustStd.U64
```

### 7. Register the file
Add to `codelib/CodeLib.lean`:
```lean
import CodeLib.RustStd.U64.AbsDiff
```

### 8. Write the per-crate spec
In `lean/Project/RustU64/Spec.lean` tagged `rust-internal` because the proved
function is the inner std function, not a direct export of the crate:

```lean
import Project.RustU64.Program

namespace Project.RustU64.Spec

open Wasm Wasm.RustStd.U64

@[spec_of "rust-internal" "core::num::abs_diff"]
def AbsDiffSpec : Prop :=
  ∀ (env : HostEnv Unit) (a b : UInt64),
    TerminatesWith env «module» 0 «module».initialStore [.i64 b, .i64 a]
      (fun _ rs => rs = [.i64 (if a < b then b - a else a - b)])

@[proves Project.RustU64.Spec.AbsDiffSpec]
theorem abs_diff_correct : AbsDiffSpec := by
  intro env a b
  exact (TerminatesWith.of_returns_wp (f := absDiffFunc)
      (rs := [.i64 (if a < b then b - a else a - b)]) rfl rfl
      (absDiff_wp «module».initialStore 1048576 a b [] rfl (by decide) (by decide))
      rfl).mono (fun _ _ h => h.1)

end Project.RustU64.Spec
```
`«module» 0` is the inner index from step **4**  the **one** hard-coded number. If
adding other functions later renumbers it, the `rfl` stops matching and the build
fails on that line; read the new index from `Program.lean` and bump it. This may or may not change.

### 9. Verify
```bash
just verifier-prove rust_u64
```

---

## Reuse it in another program

A separate crate using `abs_diff` non-trivially:
`total_variation a b c = |a-b| + |b-c|` (two calls, summed).

(No `entrypoint` keep-alive is needed here: `total_variation` is itself the
exported `#[unsafe(no_mangle)]` function — a root export, so it can't be
dead-code eliminated. The `entrypoint` wrapper is only for the per-type corpus
crates like `rust_u64`, where the individual method wrappers would otherwise be
dropped.)

### 1–3. Create, write, build same as before.
```bash
just verifier-add total_variation
```
`rust/total_variation/src/lib.rs`:
```rust
mod exports;
```
`rust/total_variation/src/exports.rs`:
```rust
#[unsafe(no_mangle)]
pub extern "C" fn total_variation(a: u64, b: u64, c: u64) -> u64 {
    a.abs_diff(b).wrapping_add(b.abs_diff(c))
}
```
```bash
just verifier-build total_variation
just verifier-emit --force-emit total_variation
```

### 4. Prove it, reusing `absDiff_wp`
In `lean/Project/TotalVariation/Spec.lean`:
```lean
import Project.TotalVariation.Program
import Interpreter.Wasm.Wp.Call

namespace Project.TotalVariation.Spec

open Wasm Wasm.RustStd.U64

-- `abs_diff` specialized to a call site (operands `b :: a :: rest` on the stack).
private theorem absDiff_call {env : HostEnv Unit} (st : Store Unit) (a b : UInt64)
    (rest : List Value)
    (hsp : st.globals.globals[0]? = some (.i32 1048576))
    (hhi : 1048576 ≤ st.mem.pages * 65536) :
    TerminatesWith env «module» 0 st (.i64 b :: .i64 a :: rest)
      (fun st' vs => vs = .i64 (if a < b then b - a else a - b) :: rest
        ∧ st'.globals = st.globals ∧ st'.mem.pages = st.mem.pages) :=
  TerminatesWith.of_returns_wp (f := absDiffFunc)
    (rs := [.i64 (if a < b then b - a else a - b)]) rfl rfl
    (absDiff_wp st 1048576 a b [] hsp (by decide) hhi) rfl   -- ★ REUSE: the proven CodeLib theorem

@[spec_of "rust-exported" "total_variation::total_variation"]
def TotalVariationSpec : Prop :=
  ∀ (env : HostEnv Unit) (a b c : UInt64),
    TerminatesWith env «module» 1 «module».initialStore [.i64 c, .i64 b, .i64 a]
      (fun _ rs => rs = [.i64 ((if a < b then b - a else a - b)
                             + (if b < c then c - b else b - c))])

set_option maxRecDepth 4096 in
@[proves Project.TotalVariation.Spec.TotalVariationSpec]
theorem total_variation_correct : TotalVariationSpec := by
  intro env a b c
  apply TerminatesWith.of_wp_entry_for (f := func1Def) rfl
  unfold func1Def func1
  wp_run
  apply wp_call_tw (absDiff_call «module».initialStore a b [] rfl (by decide))      -- ★ REUSE: first |a-b|
  intro st1 vs1 h1
  obtain ⟨hvs1, hg1, hp1⟩ := h1
  subst hvs1
  wp_run
  apply wp_call_tw (absDiff_call st1 b c [.i64 (if a < b then b - a else a - b)]    -- ★ REUSE: second |b-c|
    (by rw [hg1]; rfl) (by rw [hp1]; decide))
  intro st2 vs2 h2
  obtain ⟨hvs2, _, _⟩ := h2
  subst hvs2
  wp_run
  simp

end Project.TotalVariation.Spec
```

**Where the reuse happens:**

1. `absDiff_call` applies the proven CodeLib theorem `absDiff_wp` **as a term**,
   no tactic re-runs `abs_diff`'s instructions, and `of_returns_wp` bridges it to
   the form the call rule needs.
2. The two `apply wp_call_tw (absDiff_call …)` lines drop that fact onto each
   `.call`. Everything else just steps `total_variation`'s own instructions.

### 5. Verify
```bash
just verifier-prove total_variation
```
