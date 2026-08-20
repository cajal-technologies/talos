import Interpreter.Wasm.SmallStep

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
    memory; this demo uses i32 args directly. The relational `Satisfies`
    contract and host-step constructor generalise unchanged. -/

namespace Wasm
open SmallStep
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

private theorem counter_import0 : 0 < counterModule.imports.length := by
  decide

private theorem counter_import1 : 1 < counterModule.imports.length := by
  decide

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

def counterConfig (env : HostEnv HostState)
    (st : Store HostState) : Config HostState :=
  { expr := .running
      { locals := {}
        code := counterBody
        resultArity := 0
        callerRemainder := [] }
    store := { runtime := { instances := #[{ module := counterModule, host := env }], entry := ⟨0⟩ }, wasm := st } }

theorem counter_steps
    {env : HostEnv HostState}
    (hSat : env.Satisfies counterModule counterSpec)
    (st : Store HostState) :
    Steps (counterConfig env st)
      [(.instruction (.const 0)), (.instruction (.const 0)), (.host 0),
       (.instruction (.const 1)), (.instruction .add), (.host 1),
       (.administrative .finish)]
      ⟨.done [],
        { (counterConfig env st).store with
          wasm := { st with
            host := Counter.insert st.host 0
              (1 + Counter.lookup st.host 0) } }⟩ := by
  obtain ⟨readHost, hreadHost, hreadContract⟩ :=
    hSat.lookup_contract (i := 0) (by decide)
      (c := storageReadContract) rfl
  obtain ⟨writeHost, hwriteHost, hwriteContract⟩ :=
    hSat.lookup_contract (i := 1) (by decide)
      (c := storageWriteContract) rfl
  have hread :
      readHost.invoke st [.i32 0] =
        .Return [.i32 (Counter.lookup st.host 0)] st :=
    hreadContract st [.i32 0] 0 rfl
  have hwrite :
      writeHost.invoke st
          [.i32 0, .i32 (1 + Counter.lookup st.host 0)] =
        .Return []
          { st with host :=
              (Counter.insert st.host 0
                (1 + Counter.lookup st.host 0)) } :=
    hwriteContract st
      [.i32 0, .i32 (1 + Counter.lookup st.host 0)]
      0 (1 + Counter.lookup st.host 0) rfl
  apply Steps.cons .const
  apply Steps.cons .const
  apply Steps.cons (.callHostReturn counter_import0 rfl hreadHost hread)
  apply Steps.cons .const
  apply Steps.cons .add
  apply Steps.cons (.callHostReturn counter_import1 rfl hwriteHost hwrite)
  exact Steps.cons .finish (Steps.refl _)

theorem counter_correct
    {env : HostEnv HostState}
    (hSat : env.Satisfies counterModule counterSpec)
    (st : Store HostState) :
    TerminatesWith (counterConfig env st)
      (fun values store =>
        values = [] ∧
        store.wasm.host =
          Counter.insert st.host 0
            (1 + Counter.lookup st.host 0)) := by
  refine ⟨_, _, _, counter_steps hSat st, rfl, ?_⟩
  rfl

theorem counter_partial
    {env : HostEnv HostState}
    (hSat : env.Satisfies counterModule counterSpec)
    (st : Store HostState) :
    PartiallyMeets (counterConfig env st)
      (fun values store =>
        values = [] ∧
        store.wasm.host =
          Counter.insert st.host 0
            (1 + Counter.lookup st.host 0)) := by
  intro trace values store execution
  obtain ⟨rfl, rfl⟩ :=
    steps_done_deterministic (counter_steps hSat st) execution
  exact ⟨rfl, rfl⟩

end Counter
end Wasm
