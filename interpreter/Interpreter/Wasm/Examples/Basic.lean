import Interpreter.Wasm.Examples.IsEven
import Interpreter.Wasm.Examples.SimpleLoop
import Interpreter.Wasm.Examples.Factorial
import Interpreter.Wasm.Examples.InfiniteLoop
import Interpreter.Wasm.Examples.EvenOddRec
import Interpreter.Wasm.Examples.CallIndirect
import Interpreter.Wasm.Examples.SumI64
import Interpreter.Wasm.Examples.IfAbs
import Interpreter.Wasm.Examples.Switch
import Interpreter.Wasm.Examples.SelectMin
import Interpreter.Wasm.Examples.RefIsNull
import Interpreter.Wasm.Examples.TableDispatch
import Interpreter.Wasm.Examples.EarlyReturn
import Interpreter.Wasm.Examples.EarlyBr
import Interpreter.Wasm.Examples.EarlyBrInvalid
import Interpreter.Wasm.Examples.TrapDivZero
import Interpreter.Wasm.Examples.TrapUnreachable
import Interpreter.Wasm.Examples.MemDataSection
import Interpreter.Wasm.Examples.MemReplace
import Interpreter.Wasm.Examples.MemNarrowI32
import Interpreter.Wasm.Examples.MemI64
import Interpreter.Wasm.Examples.MemGrow
import Interpreter.Wasm.Examples.MemFill
import Interpreter.Wasm.Examples.MemCopy
import Interpreter.Wasm.Examples.GlobalCounter
import Interpreter.Wasm.Examples.MultiValue
import Interpreter.Wasm.Examples.ClzPopcnt
import Interpreter.Wasm.Examples.HostDispatch
import Interpreter.Wasm.Examples.Counter
import Interpreter.Wasm.Examples.DecoderImport
import Interpreter.Wasm.Examples.DecoderImportedGlobal
import Interpreter.Wasm.Examples.FloatOps
import Interpreter.Wasm.Examples.Gcd
import Interpreter.Wasm.Examples.SelectAbs
import Interpreter.Wasm.Examples.GlobalInitExpr
import Interpreter.Wasm.Examples.SegmentOffsetExpr
import Interpreter.Wasm.Examples.CallIndirectSubtype
import Interpreter.Wasm.Examples.RefCastFuncType

/-! # Wasm.Examples.Basic

Umbrella import for the bundled worked examples. Every example file under
`Interpreter/Wasm/Examples/` must be imported here: this module is the only
thing the CI `Interpreter` build reaches, so an example missing from this list
is never compiled and its `native_decide` checks never run. -/
