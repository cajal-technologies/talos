import Interpreter.Wasm.Wp.Tactic
import Interpreter.Wasm.Wp.Call

/-! ## Example: storage-backed counter (M5 + M6)

    Pulls the full host-function stack together over a *polymorphic*
    `Store α`:

    1. The host state is an alist `List (UInt32 × UInt32)`, declared
       once as `Counter.HostState`. The Wasm interpreter knows
       nothing of its shape — it just threads `α := Counter.HostState`
       through.
    2. Two host imports — `storage_read` and `storage_write` —
       operate on `st.host` (now of type `Counter.HostState`).
    3. A small wasm function `counter` reads slot `0`, adds `1`,
       writes back.
    4. A `HostSpec` describes the storage interface *relationally*.
    5. `counter_correct` is proved **parametric over any `HostEnv`**
       that satisfies the spec — the proof reads no host code, only
       the contracts.

    Real blockchain runtimes pass byte-sequence keys/values via linear
    memory; this demo uses i32 args directly. The mechanism
    (`Satisfies` + `wp_call_host_cons`) generalises unchanged. -/

namespace Wasm
namespace Counter

/-! ### Host state shape and helpers

    `HostState` is *this host's choice* of `α`. It lives entirely in
    user code; the interpreter never inspects it. -/

abbrev HostState := List (UInt32 × UInt32)

/-- Look up `key` in the alist; `0` if absent (blockchain convention). -/
def lookup (kv : HostState) (key : UInt32) : UInt32 :=
  match kv.find? (·.1 = key) with
  | some (_, v) => v
  | none        => 0

/-- Insert or overwrite `key → value`. -/
def insert (kv : HostState) (key value : UInt32) : HostState :=
  (kv.filter (·.1 ≠ key)) ++ [(key, value)]

/-! ### Concrete hosts -/

def storageReadHost : HostFn HostState :=
  { params  := [.i32]
    results := [.i32]
    invoke  := fun st args => match args with
      | [.i32 key] => .Return [.i32 (Counter.lookup st.host key)] st
      | _          => .Trap st "storage_read: bad arity" }

def storageWriteHost : HostFn HostState :=
  { params  := [.i32, .i32]
    results := []
    invoke  := fun st args => match args with
      | [.i32 key, .i32 value] =>
        .Return [] { st with host := Counter.insert st.host key value }
      | _ => .Trap st "storage_write: bad arity" }

def env : HostEnv HostState :=
  { funcs := [storageReadHost, storageWriteHost] }

/-! ### Counter module -/

def counterBody : Program := [
  .const 0,         -- write-key (stays at the bottom until step 6)
  .const 0,         -- read-key
  .call 0,          -- storage_read → stack: [0, counter]
  .const 1,
  .add,             -- stack: [0, counter + 1]
  .call 1           -- storage_write → stack: []
]

def counterModule : Module :=
  { imports :=
      [ { «module» := "env", name := "storage_read",
          params := [.i32], results := [.i32] }
      , { «module» := "env", name := "storage_write",
          params := [.i32, .i32], results := [] } ]
    funcs := [
      -- Unified index 2: the counter function (no params, no results).
      { body := counterBody }
    ] }

/-! ### Relational contracts -/

def storageReadContract : HostContract HostState :=
  fun st args result =>
    ∀ key, args = [.i32 key] →
      result = .Return [.i32 (Counter.lookup st.host key)] st

def storageWriteContract : HostContract HostState :=
  fun st args result =>
    ∀ key value, args = [.i32 key, .i32 value] →
      result = .Return []
        { st with host := Counter.insert st.host key value }

def counterSpec : HostSpec HostState :=
  { contracts := [storageReadContract, storageWriteContract] }

/-! ### The concrete hosts satisfy the spec -/

theorem env_satisfies : Counter.env.Satisfies counterModule counterSpec := by
  intro i hi
  have : counterModule.imports.length = 2 := rfl
  rcases i with _ | _ | i
  · refine ⟨storageReadHost, storageReadContract, rfl, rfl, ?_⟩
    intro st args key hArgs
    subst hArgs
    rfl
  · refine ⟨storageWriteHost, storageWriteContract, rfl, rfl, ?_⟩
    intro st args key value hArgs
    subst hArgs
    rfl
  · omega

/-! ### Abstract correctness

    Running the counter from any initial store ends in a store whose
    `host` alist has slot 0 set to `1 + old`. The proof never touches
    the concrete host functions; it only consumes the relational
    facts from `hSat`. -/

theorem counter_correct
    {env : HostEnv HostState}
    (hSat : env.Satisfies counterModule counterSpec)
    (st : Store HostState) :
    wp counterModule counterBody
      (fun c => c = .Fallthrough
                      { st with host := Counter.insert st.host 0
                                           (1 + Counter.lookup st.host 0) }
                      ⟨[], [], []⟩)
      st ⟨[], [], []⟩ env := by
  -- Extract resolvers + contracts for both imports.
  obtain ⟨hfR, cR, hEnvR, hCR, hInvR⟩ := hSat 0 (by decide)
  obtain ⟨hfW, cW, hEnvW, hCW, hInvW⟩ := hSat 1 (by decide)
  -- Pin the contracts to the spec entries.
  have hCRid : counterSpec.contracts[0]? = some storageReadContract := rfl
  rw [hCRid] at hCR; injection hCR with hCR'; subst hCR'
  have hCWid : counterSpec.contracts[1]? = some storageWriteContract := rfl
  rw [hCWid] at hCW; injection hCW with hCW'; subst hCW'
  unfold counterBody
  simp only [wp_const_cons]
  refine wp_call_host_cons
    (imp := ⟨"env", "storage_read", [.i32], [.i32]⟩) (hf := hfR)
    rfl hEnvR ?_ ?_
  · intro vsR stR hInvR_eq
    simp at hInvR_eq
    have hCR := hInvR st [.i32 0] 0 rfl
    rw [hInvR_eq] at hCR
    injection hCR with hvs hst
    subst vsR
    subst stR
    simp only [wp_const_cons, wp_add_cons]
    refine wp_call_host_cons
      (imp := ⟨"env", "storage_write", [.i32, .i32], []⟩) (hf := hfW)
      rfl hEnvW ?_ ?_
    · intro vsW stW hInvW_eq
      simp at hInvW_eq
      have hCW := hInvW st
                    [.i32 0, .i32 (1 + Counter.lookup st.host 0)]
                    0 (1 + Counter.lookup st.host 0) rfl
      rw [hInvW_eq] at hCW
      injection hCW with hvs hst
      subst vsW
      subst stW
      simp
    · intro stW msg hInvW_eq
      simp at hInvW_eq
      have hCW := hInvW st
                    [.i32 0, .i32 (1 + Counter.lookup st.host 0)]
                    0 (1 + Counter.lookup st.host 0) rfl
      rw [hInvW_eq] at hCW
      cases hCW
  · intro stR msg hInvR_eq
    simp at hInvR_eq
    have hCR := hInvR st [.i32 0] 0 rfl
    rw [hInvR_eq] at hCR
    cases hCR

end Counter
end Wasm
