import Interpreter.Wasm.Wp.Tactic
import Interpreter.Wasm.Wp.Call

/-! ## Example: `call_indirect` through a single-entry table

    A two-function module: `incr` is a leaf `x ↦ x + 1`; `dispatch`
    forwards its argument to `incr` via an indirect call through
    `table 0` at slot 0. The point is to exercise `wp_callIndirect_cons`
    end-to-end — table lookup, signature check, and chaining the
    callee's `FuncSpec`.

    Unlike `incr`, `dispatch`'s correctness depends on the store
    (specifically `tables[0][0]` resolving to `incr`), so its spec is
    stated as a `wp` on the module's canonical `initialStore` rather
    than as a fully store-polymorphic `FuncSpec`. -/

namespace Wasm

def Incr     : Program := [.localGet 0, .const 1, .add]
def Dispatch : Program := [.localGet 0, .const 0, .callIndirect 0 0]

/-- Module with one function type, two functions, one table of size 1
preinitialised by an active element segment pointing slot 0 at `incr`. -/
def callIndirectModule : Module :=
  { types    := [{ params := [.i32], results := [.i32] }]
    funcs    := [{ params := [.i32], body := Incr,     results := [.i32] },
                 { params := [.i32], body := Dispatch, results := [.i32] }]
    tables   := [{ min := 1 }]
    elements := [{ tableIdx := some 0, offset := some 0, funcs := [some 0] }] }

/-- `incr` adds one to its argument. Holds for any initial store —
the body never reads the store. -/
theorem incrSpec (n : UInt32) :
    FuncSpec ({} : HostEnv Unit) callIndirectModule 0 (· = [.i32 n])
      (fun _ vs => vs = [.i32 (n + 1)]) := by
  apply FuncSpec.of_wp_body
    (f := { params := [.i32], body := Incr, results := [.i32] })
  · rfl
  · rintro args rfl initial
    simp [Function.toLocals, Function.numParams]
    unfold Incr
    wp_run
    simp [UInt32.add_comm]

/-- `dispatch` returns `arg + 1` when run from the module's canonical
initial store. The indirect call resolves through table slot 0 to
`incr`, whose spec discharges the callee obligation. -/
theorem dispatchSpec (n : UInt32) :
    wp callIndirectModule Dispatch
      (fun c => ∃ st' s', c = .Fallthrough st' s' ∧ s'.values = [.i32 (n + 1)])
      (callIndirectModule.initialStore (α := Unit))
      { params := [.i32 n], locals := [], values := [] } ({} : HostEnv Unit) := by
  unfold Dispatch
  wp_run
  simp
  -- After `wp_run`, the stack holds `[.i32 0, .i32 n]` and the head
  -- instruction is `.callIndirect 0 0`. Resolve the indirect call
  -- through the (initial) table by supplying the witnesses below,
  -- then chain into `incrSpec`.
  apply wp_callIndirect_cons
    (i := 0) (vs0 := [.i32 n])
    (tbl := [.funcref (some 0)]) (fid := 0)
    (fn := { params := [.i32], results := [.i32] })
    (ty := { params := [.i32], results := [.i32] })
    (Pre  := (· = [.i32 n]))
    (Post := fun _ vs => vs = [.i32 (n + 1)])
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact ⟨rfl, rfl⟩
  · exact incrSpec n
  · rfl
  · rintro st' vs rfl
    wp_run
    simp

end Wasm
