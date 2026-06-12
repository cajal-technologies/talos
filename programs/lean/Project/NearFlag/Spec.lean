import Project.NearFlag.Program

set_option maxRecDepth 1048576
set_option maxHeartbeats 1000000

/-!
# Specification for `near_flag`

`programs/rust/near_flag` is the simplest possible NEAR contract: raw
host-function bindings (no `near-sdk`), one exported method `set_flag`
that

1. `log_utf8(8, ptr)` — logs the constant message `"flag set"`, then
2. `storage_write(4, key_ptr, 1, val_ptr, u64::MAX)` — stores `[1]`
   under the constant key `"flag"`, discarding any evicted value.

Because the compiled wasm is tiny (two straight-line host calls with
constant arguments), we can prove a **general, symbolic spec** over an
arbitrary incoming `NearState` — not just concrete `native_decide`
checks:

* *projection:* after the call, `storage["flag"] = [1]`;
* *frame:* every other storage key is unchanged;
* *logs:* exactly `"flag set"` is appended to the log list.

`SetFlagSpec` quantifies over every non-view `NearState` whose
configured limits admit the (tiny) log/key/value sizes.
-/

namespace Project.NearFlag

open Wasm
open Wasm.Near

/-! ## Constants mirrored from the Rust source -/

/-- `b"flag"` — the storage key written by `set_flag`. -/
def flagKey : List UInt8 := [102, 108, 97, 103]

/-- `[1]` — the value stored under `flagKey`. -/
def flagVal : List UInt8 := [1]

/-- `b"flag set"` — the log line emitted before the write. -/
def logMsg : List UInt8 := [102, 108, 97, 103, 32, 115, 101, 116]

/-! ## Host environment

The module imports exactly `log_utf8` and `storage_write` (in that
order); `env` aligns positionally with `«module».imports`. The
`native_decide` check below confirms the canonical NEAR resolver
covers the declared imports. -/

/-- Positional host environment for the two declared imports. -/
def env : HostEnv NearState := { funcs := [logUtf8Fn, storageWriteFn] }

def importsResolve : Bool :=
  match Wasm.Near.resolveEnv? «module», Wasm.Near.resolveSpec? «module» with
  | some renv, some _ => renv.funcs.length == «module».imports.length
  | _, _              => false

theorem imports_resolve : importsResolve = true := by native_decide

/-- Unified function index of the exported `set_flag` (imports occupy
indices 0–1, the single in-module function is 2). -/
def setFlagIdx : Nat := 2

/-- The module's initial store with the NEAR projection `ns` injected. -/
def initialWith (ns : NearState) : Store NearState :=
  { («module».initialStore : Store NearState) with host := ns }

/-! ## Concrete memory facts

The data segment puts `"flag setflag\x01"` at offset 1048576, and the
linear memory has 17 pages. These facts do not depend on the incoming
`NearState`, so they are discharged by computation. -/

/-- The (NearState-independent) initial linear memory. -/
def initMem : Mem := («module».initialStore : Store NearState).mem

theorem initialWith_mem (ns : NearState) : (initialWith ns).mem = initMem := rfl

theorem initMem_pages : initMem.pages = 17 := by decide

theorem initMem_log :
    initMem.readBytes (1048576 : UInt64).toNat (8 : UInt64).toNat = logMsg := by
  decide

theorem initMem_key :
    initMem.readBytes (1048584 : UInt64).toNat (4 : UInt64).toNat = flagKey := by
  decide

theorem initMem_val :
    initMem.readBytes (1048588 : UInt64).toNat (1 : UInt64).toNat = flagVal := by
  decide

/-! ## Host-invocation lemmas -/

theorem getMemOrReg_initMem (st : Store NearState) (hMem : st.mem = initMem)
    {ptr len : UInt64} {out : List UInt8} (hLen : len ≠ u64Max)
    (hBound : ptr.toNat + len.toNat ≤ 17 * 65536)
    (hRead : initMem.readBytes ptr.toNat len.toNat = out) :
    getMemOrReg st ptr len = some out := by
  have hB : ptr.toNat + len.toNat ≤ memBytes st := by
    rw [memBytes, hMem, initMem_pages]; exact hBound
  rw [getMemOrReg_mem st ptr len hLen hB, hMem, hRead]

/-- `log_utf8(8, 1048576)` on any store carrying the initial memory:
appends `logMsg` to the host log list. -/
theorem logUtf8_invoke (st : Store NearState) (hMem : st.mem = initMem)
    (hLen : withinLimit st.host.config.maxLogLen logMsg.length)
    (hCount : withinLimit st.host.config.maxNumberLogs (st.host.logs.length + 1)) :
    logUtf8Fn.invoke st [.i64 8, .i64 1048576] =
      .Return [] { st with host := { st.host with logs := st.host.logs ++ [logMsg] } } := by
  have hGet : getMemOrReg st 1048576 8 = some logMsg :=
    getMemOrReg_initMem st hMem (by decide) (by decide) initMem_log
  simp [logUtf8Fn, hGet, appendLogResult, checkDataLimit, hLen, hCount]

/-- The store after the `log_utf8` call: initial memory and globals,
`logMsg` appended to the incoming logs. -/
def afterLog (ns : NearState) : Store NearState :=
  { initialWith ns with host := { ns with logs := ns.logs ++ [logMsg] } }

/-- The store after the `storage_write` call: additionally
`flagKey ↦ flagVal` is inserted (and iterators invalidated, matching
`storage_write` semantics). -/
def afterSet (ns : NearState) : Store NearState :=
  { initialWith ns with
    host := (NearState.setStorage { ns with logs := ns.logs ++ [logMsg] }
      flagKey flagVal).invalidateIterators }

/-- `storage_write(4, 1048584, 1, 1048588, u64::MAX)` on any non-view
store carrying the initial memory: sets `flagKey ↦ flagVal`, discarding
any evicted value (output register is the `u64::MAX` sentinel). -/
theorem storageWrite_invoke (st : Store NearState) (hMem : st.mem = initMem)
    (hView : st.host.context.isView = false)
    (hKeyLim : withinLimit st.host.config.maxStorageKeyLen flagKey.length)
    (hValLim : withinLimit st.host.config.maxStorageValueLen flagVal.length) :
    storageWriteFn.invoke st
      [.i64 4, .i64 1048584, .i64 1, .i64 1048588, .i64 18446744073709551615] =
      .Return [.i64 (if (st.host.storage flagKey).isSome then 1 else 0)]
        { st with host := (st.host.setStorage flagKey flagVal).invalidateIterators } := by
  have hKeyGet : getMemOrReg st 1048584 4 = some flagKey :=
    getMemOrReg_initMem st hMem (by decide) (by decide) initMem_key
  have hValGet : getMemOrReg st 1048588 1 = some flagVal :=
    getMemOrReg_initMem st hMem (by decide) (by decide) initMem_val
  cases hOld : st.host.storage flagKey with
  | none =>
    rw [storageWriteFn_invoke_absent st flagKey flagVal 4 1048584 1 1048588
      18446744073709551615 hView hKeyGet hValGet hKeyLim hValLim hOld]
    simp
  | some old =>
    rw [storageWriteFn_invoke_present st flagKey flagVal old 4 1048584 1 1048588
      18446744073709551615 st hView hKeyGet hValGet hKeyLim hValLim hOld
      (by simp [checkedSetRegister?, u64Max])]
    simp

/-- `log_utf8` step, specialized to the module's initial store: lands
exactly in `afterLog ns`. -/
theorem logUtf8_invoke_init (ns : NearState)
    (hLen : withinLimit ns.config.maxLogLen logMsg.length)
    (hCount : withinLimit ns.config.maxNumberLogs (ns.logs.length + 1)) :
    logUtf8Fn.invoke (initialWith ns) [.i64 8, .i64 1048576] =
      .Return [] (afterLog ns) :=
  logUtf8_invoke (initialWith ns) rfl hLen hCount

/-- `storage_write` step, specialized to `afterLog ns`: lands exactly
in `afterSet ns`. -/
theorem storageWrite_invoke_afterLog (ns : NearState)
    (hView : ns.context.isView = false)
    (hKeyLim : withinLimit ns.config.maxStorageKeyLen flagKey.length)
    (hValLim : withinLimit ns.config.maxStorageValueLen flagVal.length) :
    storageWriteFn.invoke (afterLog ns)
      [.i64 4, .i64 1048584, .i64 1, .i64 1048588, .i64 18446744073709551615] =
      .Return [.i64 (if (ns.storage flagKey).isSome then 1 else 0)] (afterSet ns) :=
  storageWrite_invoke (afterLog ns) rfl hView hKeyLim hValLim

/-! ## The specification -/

/-- Post-condition of `set_flag` relative to the incoming projection
`ns`: the flag is stored, all other keys are framed, and exactly one
log line was appended. -/
def SetFlagPost (ns : NearState) (st : Store NearState) : Prop :=
  st.host.storage flagKey = some flagVal ∧
  (∀ k, k ≠ flagKey → st.host.storage k = ns.storage k) ∧
  st.host.logs = ns.logs ++ [logMsg]

/-- **Spec for `set_flag`.**

Informal spec:
`set_flag()` logs `"flag set"` and stores the byte `1` under the
storage key `"flag"`, leaving every other storage key untouched.

For any non-view incoming NEAR state whose
configured limits admit an 8-byte log line (plus one more log entry), a
4-byte storage key and a 1-byte value, the call terminates and the
final NEAR projection satisfies `SetFlagPost`: `storage["flag"] = [1]`,
every other key is unchanged, and `"flag set"` is appended to the logs.

The store is pinned to the module's `initialStore` (memory and globals
as set up by instantiation) with the NEAR projection injected as
`host := ns`, per the repo convention for memory-touching specs. -/
@[spec_of "rust-exported" "near_flag::set_flag"]
def SetFlagSpec : Prop :=
  ∀ ns : NearState,
    ns.context.isView = false →
    withinLimit ns.config.maxLogLen logMsg.length →
    withinLimit ns.config.maxNumberLogs (ns.logs.length + 1) →
    withinLimit ns.config.maxStorageKeyLen flagKey.length →
    withinLimit ns.config.maxStorageValueLen flagVal.length →
    TerminatesWith env «module» setFlagIdx (initialWith ns) []
      (fun st _ => SetFlagPost ns st)

/-! ## Proof -/

/-- `set_flag` meets its spec. Straight-line symbolic execution: two
host calls with constant arguments, discharged by the invocation
lemmas above. -/
@[proves Project.NearFlag.SetFlagSpec]
theorem set_flag_spec : SetFlagSpec := by
  intro ns hView hLogLen hLogCount hKeyLim hValLim
  apply TerminatesWith.of_wp_entry_for (f := func0Def)
  · rfl
  · unfold func0Def func0
    wp_run
    refine wp_call_host_cons
      (imp := { «module» := "env", name := "log_utf8", params := [.i64, .i64], results := [] })
      (hf := logUtf8Fn) rfl rfl ?_ ?_
    · intro vs st' hInv
      norm_num at hInv
      rw [logUtf8_invoke_init ns hLogLen hLogCount] at hInv
      injection hInv with hvs hst
      subst hvs
      subst st'
      wp_run
      refine wp_call_host_cons
        (imp := { «module» := "env", name := "storage_write",
                  params := [.i64, .i64, .i64, .i64, .i64], results := [.i64] })
        (hf := storageWriteFn) rfl rfl ?_ ?_
      · intro vs st' hInv
        norm_num at hInv
        rw [storageWrite_invoke_afterLog ns hView hKeyLim hValLim] at hInv
        injection hInv with hvs hst
        subst hvs
        subst st'
        wp_run
        refine ⟨?_, ?_, ?_⟩
        · simp [afterSet, NearState.invalidateIterators]
        · intro k hk
          simp [afterSet, NearState.invalidateIterators, setStorage_other _ hk]
        · simp [afterSet, NearState.invalidateIterators, NearState.setStorage]
      · intro st' msg hInv
        norm_num at hInv
        rw [storageWrite_invoke_afterLog ns hView hKeyLim hValLim] at hInv
        cases hInv
    · intro st' msg hInv
      norm_num at hInv
      rw [logUtf8_invoke_init ns hLogLen hLogCount] at hInv
      cases hInv

/-! ## Concrete end-to-end validation

Full pipeline checks (`native_decide`): run the decoded module through
the interpreter against the canonical resolver environment and inspect
the resulting NEAR projection. -/

def resolvedNearEnv : HostEnv NearState :=
  (Wasm.Near.resolveEnv? «module»).getD {}

def runSetFlag (ns : NearState) : Result NearState :=
  run 100 «module» setFlagIdx (initialWith ns) [] resolvedNearEnv

/-- Storage projection of `flagKey` after running `set_flag`. -/
def storedFlag (ns : NearState) : Option (List UInt8) :=
  match runSetFlag ns with
  | .Success _ st => st.host.storage flagKey
  | _             => none

/-- Logs after running `set_flag`. -/
def logsAfter (ns : NearState) : Option (List (List UInt8)) :=
  match runSetFlag ns with
  | .Success _ st => some st.host.logs
  | _             => none

/-- The run succeeds, stores the flag, and logs the message. -/
theorem demo_stored : storedFlag {} = some flagVal := by native_decide

theorem demo_logged : logsAfter {} = some [logMsg] := by native_decide

/-- Frame check against a non-empty incoming store: an unrelated
pre-existing key survives the write. -/
def demoNs : NearState :=
  { storage := fun k => if k = [42] then some [7] else none
    logs := [[9]] }

theorem demo_frame : (match runSetFlag demoNs with
    | .Success _ st => st.host.storage [42]
    | _             => none) = some [7] := by native_decide

theorem demo_logs_appended : logsAfter demoNs = some [[9], logMsg] := by native_decide

end Project.NearFlag
