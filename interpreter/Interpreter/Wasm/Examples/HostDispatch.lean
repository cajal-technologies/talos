import Interpreter.Wasm.Wp.Tactic
import Interpreter.Wasm.Wp.Call

/-! ## Example: host-function dispatch (M2)

    Three minimal modules with a single import each, exercising the
    `.call` dispatch added in M2:

    1. `inc(x : i32) → i32` — value-returning host function.
    2. `abort() → ⊥` — host call that always traps.
    3. `memLoad(addr : i32) → i32` — host reads caller's linear memory.

    For each demo the host import lives at unified function index `0`,
    so the in-module function that calls it (and is itself exercised by
    `run`) sits at unified index `1` — that's the index passed to `run`. -/

namespace Wasm
namespace HostDispatch

/-! ### Demo 1 — `inc`: host returns a value

    `inc(x)` is a host function that returns `x + 1`. The wasm caller
    just forwards its argument and yields the result. -/

def incHost : HostFn Unit :=
  { params  := [.i32]
    results := [.i32]
    invoke  := fun st args => match args with
      | [.i32 x] => .Return [.i32 (x + 1)] st
      | _        => .Trap st "inc: bad arity" }

def incEnv : HostEnv Unit := { funcs := [incHost] }

def incModule : Module :=
  { imports := [{ «module» := "env", name := "inc",
                  params := [.i32], results := [.i32] }]
    funcs := [
      -- unified index 1: pushes its arg and calls the host import.
      { params := [.i32], body := [.localGet 0, .call 0], results := [.i32] }
    ] }

/-! ### Demo 2 — `abort`: host trap propagates

    A bare host trap inside `.call` must surface as a `Result.Trap`
    carrying the host's message, with no further wasm execution. -/

def abortHost : HostFn Unit :=
  { invoke := fun st _ => .Trap st "host abort" }

def abortEnv : HostEnv Unit := { funcs := [abortHost] }

def abortModule : Module :=
  { imports := [{ «module» := "env", name := "abort" }]
    funcs := [
      -- unified index 1: call the trapping host, then unreachable
      -- (which we never reach since the trap aborts).
      { body := [.call 0, .unreachable] }
    ] }

/-! ### Demo 3 — `memLoad`: host reads caller memory

    `memLoad(addr)` reads `st.mem.read32 addr` and returns it. The host
    only needs the `Store Unit` it's already been handed, so this exercises
    the "host inspects caller memory" use case (the read direction of
    eventual blockchain `storage_read`-style imports). -/

def memLoadHost : HostFn Unit :=
  { params  := [.i32]
    results := [.i32]
    invoke  := fun st args => match args with
      | [.i32 addr] =>
        if addr.toNat + 4 > st.mem.pages * 65536 then
          .Trap st "memLoad: out of bounds"
        else
          .Return [.i32 (st.mem.read32 addr)] st
      | _ => .Trap st "memLoad: bad arity" }

def memLoadEnv : HostEnv Unit := { funcs := [memLoadHost] }

def memLoadModule : Module :=
  { imports := [{ «module» := "env", name := "memLoad",
                  params := [.i32], results := [.i32] }]
    funcs := [
      { params := [.i32], body := [.localGet 0, .call 0], results := [.i32] }
    ]
    memory := some { pagesMin := 1
                     data := [{ offset := some 0, bytes := [42, 0, 0, 0] }] } }

/-! ### `native_decide` checks

    `runVals` / `runTrap` extract the success values or trap message so
    we don't need `DecidableEq` on `Store Unit`. -/

private def runVals (m : Module) (env : HostEnv Unit) (idx : Nat)
    (st : Store Unit) (args : List Value) : List Value :=
  match run 10 m idx st args env with
  | .Success vs _ => vs
  | _ => []

private def runTrap (m : Module) (env : HostEnv Unit) (idx : Nat)
    (st : Store Unit) (args : List Value) : Option String :=
  match run 10 m idx st args env with
  | .Trap _ msg => some msg
  | _ => none

theorem inc_returns_plus_one :
    runVals incModule incEnv 1 incModule.initialStore [.i32 41] = [.i32 42] := by
  native_decide

theorem abort_propagates_trap :
    runTrap abortModule abortEnv 1 abortModule.initialStore [] = some "host abort" := by
  native_decide

theorem memLoad_reads_caller_memory :
    runVals memLoadModule memLoadEnv 1 memLoadModule.initialStore [.i32 0]
      = [.i32 42] := by
  native_decide

/-! ### M3: WP-level proof through `wp_call_host_cons`

    Reasons about the host `inc` symbolically rather than running it.
    The state machine: operand stack starts as `[.i32 n]`; the wasm body
    is just `[.call 0]`; after the host returns, the stack is
    `[.i32 (n + 1)]` and the program is empty so `wp_nil` closes. -/

theorem inc_call_wp (st : Store Unit) (n : UInt32) :
    wp incModule [.call 0]
      (fun c => c = .Fallthrough st ⟨[], [], [.i32 (n + 1)]⟩)
      st ⟨[], [], [.i32 n]⟩ incEnv := by
  refine wp_call_host_cons (imp := ⟨"env", "inc", [.i32], [.i32]⟩) (hf := incHost)
    rfl rfl ?_ ?_
  · -- Return case: the host invocation is concrete; destructure it.
    intro vs st' hInv
    -- `hInv : incHost.invoke st [.i32 n] = .Return vs st'`.
    -- Unfolding the host fn computes the LHS to `.Return [.i32 (n+1)] st`.
    simp only [incHost, List.take, List.reverse_cons, List.reverse_nil,
               List.nil_append] at hInv
    -- Now `hInv : HostResult.Return [.i32 (n+1)] st = .Return vs st'`.
    injection hInv with hvs hst
    subst hvs
    subst hst
    -- Goal: wp incModule [] (...) st ⟨[], [], [.i32 (n+1)]⟩ incEnv  -- by wp_nil.
    simp
  · -- Trap case is unreachable: the host always returns on a one-element
    -- i32 stack, so `hInv` equates two distinct `HostResult Unit` constructors.
    intro st' msg hInv
    simp only [incHost, List.take, List.reverse_cons, List.reverse_nil,
               List.nil_append] at hInv
    cases hInv

/-! ### M4: abstract specification through `HostSpec Unit` + `Satisfies`

    The same `inc` theorem, but now **parametric over any `HostEnv Unit`** that
    satisfies a contract. The proof never mentions `incHost`; it only
    consumes the relational fact provided by `hSat`. Verified once, the
    theorem holds for every implementation of `inc` that meets the spec. -/

/-- Contract for `inc`: must `.Return` a single i32 equal to `arg + 1`,
without modifying the store, on every one-element i32 input. -/
def incContract : HostContract Unit :=
  fun st args result =>
    ∀ x, args = [.i32 x] → result = .Return [.i32 (x + 1)] st

def incSpec : HostSpec Unit := { contracts := [incContract] }

/-- The concrete `incHost` defined above satisfies `incSpec`. Used at
the executor boundary to instantiate the abstract theorem. -/
theorem incHost_satisfies : (incEnv).Satisfies incModule incSpec := by
  intro i hi
  -- The module has exactly one import, so `i = 0`.
  have hi0 : i = 0 := by
    have : incModule.imports.length = 1 := rfl
    omega
  subst hi0
  refine ⟨incHost, incContract, rfl, rfl, ?_⟩
  intro st args x hArgs
  subst hArgs
  rfl

/-- Abstract version of `inc_call_wp`: holds for *any* `env` satisfying
the spec. The concrete-host proof above is one specialisation — other
implementations of `inc` (different language, different runtime) get
the same theorem for free. -/
theorem inc_call_wp_abstract
    (env : HostEnv Unit) (hSat : env.Satisfies incModule incSpec)
    (st : Store Unit) (n : UInt32) :
    wp incModule [.call 0]
      (fun c => c = .Fallthrough st ⟨[], [], [.i32 (n + 1)]⟩)
      st ⟨[], [], [.i32 n]⟩ env := by
  -- Pull the resolver + contract for import 0 out of the satisfaction.
  obtain ⟨hf, c, hEnv, hC, hInvariant⟩ := hSat 0 (by decide)
  -- The contract entry is exactly `incContract` (by definition of incSpec).
  have hC0 : incSpec.contracts[0]? = some incContract := rfl
  rw [hC0] at hC
  injection hC with hC'
  subst hC'
  -- Apply the host-call WP rule against the abstract resolver `hf`.
  refine wp_call_host_cons (imp := ⟨"env", "inc", [.i32], [.i32]⟩) (hf := hf)
    rfl hEnv ?_ ?_
  · -- Return: the contract gives the exact shape of the result.
    intro vs st' hInv
    simp only [List.take, List.reverse_cons, List.reverse_nil,
               List.nil_append] at hInv
    have hContract := hInvariant st [.i32 n] n rfl
    rw [hInv] at hContract
    injection hContract with hvs hst
    subst hvs
    subst hst
    simp
  · -- Trap: the contract forbids it (forces .Return), so the assumption is False.
    intro st' msg hInv
    simp only [List.take, List.reverse_cons, List.reverse_nil,
               List.nil_append] at hInv
    have hContract := hInvariant st [.i32 n] n rfl
    rw [hInv] at hContract
    cases hContract

end HostDispatch
end Wasm
