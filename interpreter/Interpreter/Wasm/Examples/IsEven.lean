import Interpreter.Wasm.Wp.Tactic

/-! ## Example: IsEven

    Straight-line; the whole proof is symbolic execution plus an arithmetic
    step (`v &&& 1 = 0 ↔ v is even`) discharged by `grind`. -/

namespace Wasm

def IsEven : Program := [.localGet 0, .const 1, .and, .eqz]

#eval
  let m : Module := { funcs := [{ params := [.i32], body := IsEven, results := [.i32] }] }
  run 10 m 0 m.initialStore [.i32 3]

theorem isEvenSpec (m : Module) (st : Store) (v : UInt32) :
    wp m IsEven
        (fun c => c = .Fallthrough st
                    { params := [.i32 v], locals := [],
                      values := [.i32 (if (1 : UInt32) &&& v = 0 then 1 else 0)] })
        st { params := [.i32 v], locals := [], values := [] } := by
  unfold IsEven
  wp_run
  simp

end Wasm
