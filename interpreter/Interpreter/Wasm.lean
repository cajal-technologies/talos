import Interpreter.Wasm.Syntax
import Interpreter.Wasm.Locals
import Interpreter.Wasm.Continuation
import Interpreter.Wasm.Semantics
import Interpreter.Wasm.Semantics.Lemmas
import Interpreter.Wasm.Wp.Defs
import Interpreter.Wasm.Wp.Atomic
import Interpreter.Wasm.Wp.Block
import Interpreter.Wasm.Wp.Loop
import Interpreter.Wasm.Wp.Call
import Interpreter.Wasm.Wp.Tactic
import Interpreter.Wasm.Spec.Termination
import Interpreter.Wasm.Decoder.Wat
import Interpreter.Wasm.Examples.IsEven
import Interpreter.Wasm.Examples.SimpleLoop
import Interpreter.Wasm.Examples.Factorial
import Interpreter.Wasm.Examples.InfiniteLoop
import Interpreter.Wasm.Examples.EvenOddRec
import Interpreter.Wasm.Examples.SumI64
import Interpreter.Wasm.Examples.IfAbs
import Interpreter.Wasm.Examples.Switch
import Interpreter.Wasm.Examples.SelectMin
import Interpreter.Wasm.Examples.EarlyReturn
import Interpreter.Wasm.Examples.TrapDivZero
import Interpreter.Wasm.Examples.MemDataSection
import Interpreter.Wasm.Examples.MemReplace
import Interpreter.Wasm.Examples.MemNarrowI32
import Interpreter.Wasm.Examples.MemI64
import Interpreter.Wasm.Examples.MemGrow
import Interpreter.Wasm.Examples.MemFill
import Interpreter.Wasm.Examples.MemCopy
import Interpreter.Wasm.Examples.GlobalCounter
import Interpreter.Wasm.Examples.HostDispatch
import Interpreter.Wasm.Examples.Counter

/-! # Wasm

A minimal Wasm core paired with a weakest-precondition reasoning framework.
This umbrella module re-exports the public surface; the implementation is
split into:

* `Wasm.Syntax`            — instructions, programs, functions, modules
* `Wasm.Locals`            — per-frame locals/value-stack state + helpers
* `Wasm.Continuation`      — `Continuation` / `Result` outcome types
* `Wasm.Semantics`         — `execOne` / `exec` / `run` mutual interpreter
* `Wasm.Semantics.Lemmas`  — bridge lemmas between `exec` and `wp`
                                 (fuel monotonicity, atomic unfoldings, …)
* `Wasm.Wp.*`              — `wp` framework: definitions, atomic
                                 equations, block / loop / call rules, and
                                 the `wp_run` / `wp_done` tactics
* `Wasm.Spec.Termination`  — fuel-free `TerminatesWith` /
                                 `PartiallyMeets` predicates (user-facing
                                 spec API)
* `Wasm.Examples.*`        — worked examples (IsEven, SimpleLoop,
                                 Factorial, InfiniteLoop, EvenOddRec,
                                 SumI64, IfAbs, Switch, SelectMin,
                                 EarlyReturn, TrapDivZero,
                                 MemDataSection, MemReplace,
                                 MemNarrowI32, MemI64, MemGrow,
                                 MemFill, MemCopy, GlobalCounter)
-/
