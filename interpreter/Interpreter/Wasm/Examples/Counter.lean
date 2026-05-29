import Interpreter.Wasm.Wp.Tactic
import Interpreter.Wasm.Wp.Call

/-! ## Example: storage-backed counter (M5)

    Pulls the full host-function stack together:

    1. Two host imports — `storage_read` and `storage_write` — operate
       on `Store.host`, the runtime's persistent KV slot.
    2. A small wasm function `counter` reads slot `0`, adds `1`, writes
       back.
    3. A `HostSpec` describes the storage interface *relationally*,
       without committing to any particular implementation.
    4. `counter_correct` is proved **parametric over any `HostEnv`**
       that satisfies the spec — the proof reads no host code, only
       the contracts.

    Real blockchain runtimes pass byte-sequence keys/values via linear
    memory; this demo uses i32 args directly. The mechanism
    (`Satisfies` + `wp_call_host_cons`) generalises unchanged. -/

namespace Wasm
namespace Counter

/-! ### Concrete hosts -/

def storageReadHost : HostFn :=
  { params  := [.i32]
    results := [.i32]
    invoke  := fun st args => match args with
      | [.i32 key] => .Return [.i32 (st.hostLookup key)] st
      | _          => .Trap st "storage_read: bad arity" }

def storageWriteHost : HostFn :=
  { params  := [.i32, .i32]
    results := []
    invoke  := fun st args => match args with
      | [.i32 key, .i32 value] => .Return [] (st.hostInsert key value)
      | _                      => .Trap st "storage_write: bad arity" }

def env : HostEnv := { funcs := [storageReadHost, storageWriteHost] }

/-! ### Counter module

    Body: push the write-key, read slot 0, increment, write back. The
    write-key is pushed *first* so it sits below the eventual
    `counter + 1` for the `storage_write` call. -/

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

def storageReadContract : HostContract :=
  fun st args result =>
    ∀ key, args = [.i32 key] →
      result = .Return [.i32 (st.hostLookup key)] st

def storageWriteContract : HostContract :=
  fun st args result =>
    ∀ key value, args = [.i32 key, .i32 value] →
      result = .Return [] (st.hostInsert key value)

def counterSpec : HostSpec :=
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

    Running the counter from any initial store ends in
    `st.hostInsert 0 (st.hostLookup 0 + 1)` — i.e. slot 0 has been
    incremented by 1. The proof never touches the concrete host
    functions; it only consumes the relational facts from `hSat`. -/

theorem counter_correct
    {env : HostEnv} (hSat : env.Satisfies counterModule counterSpec)
    (st : Store) :
    wp counterModule counterBody
      (fun c => c = .Fallthrough
                      (st.hostInsert 0 (1 + st.hostLookup 0))
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
  -- Symbolic execution of the straight-line prefix.
  unfold counterBody
  simp only [wp_const_cons]
  -- Goal: wp counterModule (.call 0 :: …) Q st ⟨[], [], [.i32 0, .i32 0]⟩ env
  refine wp_call_host_cons
    (imp := ⟨"env", "storage_read", [.i32], [.i32]⟩) (hf := hfR)
    rfl hEnvR ?_ ?_
  · -- storage_read returns; use its contract to nail the result.
    intro vsR stR hInvR_eq
    simp at hInvR_eq
    have hCR := hInvR st [.i32 0] 0 rfl
    -- `hCR : hfR.invoke st [.i32 0] = .Return [.i32 (st.hostLookup 0)] st`.
    -- Combine with `hInvR_eq` to force `vsR` and `stR` to their contract shapes.
    rw [hInvR_eq] at hCR
    injection hCR with hvs hst
    subst vsR
    subst stR
    -- Stack now: [.i32 (st.hostLookup 0), .i32 0]; next: .const 1 :: .add :: .call 1
    simp only [wp_const_cons, wp_add_cons]
    -- After +1, stack: [.i32 (st.hostLookup 0 + 1), .i32 0]
    refine wp_call_host_cons
      (imp := ⟨"env", "storage_write", [.i32, .i32], []⟩) (hf := hfW)
      rfl hEnvW ?_ ?_
    · -- storage_write returns; the resulting store is `hostInsert 0 (1 + counter)`.
      intro vsW stW hInvW_eq
      simp at hInvW_eq
      have hCW := hInvW st [.i32 0, .i32 (1 + st.hostLookup 0)] 0 (1 + st.hostLookup 0) rfl
      rw [hInvW_eq] at hCW
      injection hCW with hvs hst
      subst vsW
      subst stW
      simp
    · -- storage_write cannot trap on a well-shaped call (contract forces .Return).
      intro stW msg hInvW_eq
      simp at hInvW_eq
      have hCW := hInvW st [.i32 0, .i32 (1 + st.hostLookup 0)] 0 (1 + st.hostLookup 0) rfl
      rw [hInvW_eq] at hCW
      cases hCW
  · -- storage_read cannot trap (contract forces .Return).
    intro stR msg hInvR_eq
    simp only [List.take, List.reverse_cons, List.reverse_nil,
               List.nil_append] at hInvR_eq
    have hCR := hInvR st [.i32 0] 0 rfl
    rw [hInvR_eq] at hCR
    cases hCR

end Counter
end Wasm
