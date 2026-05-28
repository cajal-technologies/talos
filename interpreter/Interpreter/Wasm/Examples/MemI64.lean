import Interpreter.Wasm.Wp.Tactic

/-! ## Example: i64 memory loads/stores

    Sanity checks for the i64 memory accesses:

    * full-width:    `i64.load`, `i64.store`
    * narrow loads:  `i64.load8_u/_s`, `i64.load16_u/_s`, `i64.load32_u/_s`
    * narrow stores: `i64.store8`, `i64.store16`, `i64.store32`

    The data segment is laid out so the narrow loads exercise both zero-
    and sign-extension. Stores are exercised round-trip: write a known
    constant, then read it back through the matching unsigned load. -/

namespace Wasm

private def initBytes : List UInt8 :=
  [0x88, 0xFF, 0x66, 0x55, 0x44, 0x33, 0x22, 0xFF]

/-- 8 little-endian bytes at address 0 reassembled as i64. -/
def load64Body : Program := [.const 0, .load64 0]

def load8UI64Body : Program := [.const 1, .load8UI64 0]   -- byte 0xFF → 0xFF
def load8SI64Body : Program := [.const 1, .load8SI64 0]   -- byte 0xFF → -1
def load16UI64Body : Program := [.const 0, .load16UI64 0] -- 0xFF88
def load16SI64Body : Program := [.const 0, .load16SI64 0] -- 0xFF88 (sign bit set)
def load32UI64Body : Program := [.const 4, .load32UI64 0] -- 0xFF223344
def load32SI64Body : Program := [.const 4, .load32SI64 0] -- 0xFF223344 (sign bit set)

/-- Write the low byte of `0xABCD` at address 8, read back via `i64.load8_u`. -/
def store8I64RoundtripBody : Program := [
  .const 8, .constI64 0xABCD, .store8I64 0,
  .const 8, .load8UI64 0
]

def store16I64RoundtripBody : Program := [
  .const 8, .constI64 0xABCDEF, .store16I64 0,
  .const 8, .load16UI64 0
]

def store32I64RoundtripBody : Program := [
  .const 8, .constI64 0xABCDEF01, .store32I64 0,
  .const 8, .load32UI64 0
]

def store64RoundtripBody : Program := [
  .const 16, .constI64 0x1122334455667788, .store64 0,
  .const 16, .load64 0
]

def i64MemModule : Module :=
  { funcs :=
      [ { body := load64Body,             results := [.i64] }  -- 0
      , { body := load8UI64Body,          results := [.i64] }  -- 1
      , { body := load8SI64Body,          results := [.i64] }  -- 2
      , { body := load16UI64Body,         results := [.i64] }  -- 3
      , { body := load16SI64Body,         results := [.i64] }  -- 4
      , { body := load32UI64Body,         results := [.i64] }  -- 5
      , { body := load32SI64Body,         results := [.i64] }  -- 6
      , { body := store8I64RoundtripBody,  results := [.i64] }  -- 7
      , { body := store16I64RoundtripBody, results := [.i64] }  -- 8
      , { body := store32I64RoundtripBody, results := [.i64] }  -- 9
      , { body := store64RoundtripBody,    results := [.i64] }  -- 10
      ]
    memory := some { pagesMin := 1, data := [{ offset := some 0, bytes := initBytes }] } }

/-- Project the value stack out of a `Result`; see `MemNarrowI32.lean`. -/
private def runValues (fuel : Nat) (m : Module) (idx : Nat)
    (st : Store) (args : List Value) : List Value :=
  match run fuel m idx st args with
  | .Success vs _ => vs
  | _ => []

theorem load64_returns_word :
    runValues 10 i64MemModule 0 i64MemModule.initialStore [] = [.i64 0xFF2233445566FF88] := by
  native_decide

theorem load8UI64_zero_extends :
    runValues 10 i64MemModule 1 i64MemModule.initialStore [] = [.i64 0xFF] := by
  native_decide

theorem load8SI64_sign_extends :
    runValues 10 i64MemModule 2 i64MemModule.initialStore [] = [.i64 0xFFFFFFFFFFFFFFFF] := by
  native_decide

theorem load16UI64_zero_extends :
    runValues 10 i64MemModule 3 i64MemModule.initialStore [] = [.i64 0xFF88] := by
  native_decide

theorem load16SI64_sign_extends :
    runValues 10 i64MemModule 4 i64MemModule.initialStore [] = [.i64 0xFFFFFFFFFFFFFF88] := by
  native_decide

theorem load32UI64_zero_extends :
    runValues 10 i64MemModule 5 i64MemModule.initialStore [] = [.i64 0xFF223344] := by
  native_decide

theorem load32SI64_sign_extends :
    runValues 10 i64MemModule 6 i64MemModule.initialStore [] = [.i64 0xFFFFFFFFFF223344] := by
  native_decide

theorem store8I64_roundtrip :
    runValues 10 i64MemModule 7 i64MemModule.initialStore [] = [.i64 0xCD] := by
  native_decide

theorem store16I64_roundtrip :
    runValues 10 i64MemModule 8 i64MemModule.initialStore [] = [.i64 0xCDEF] := by
  native_decide

theorem store32I64_roundtrip :
    runValues 10 i64MemModule 9 i64MemModule.initialStore [] = [.i64 0xABCDEF01] := by
  native_decide

theorem store64_roundtrip :
    runValues 10 i64MemModule 10 i64MemModule.initialStore []
      = [.i64 0x1122334455667788] := by
  native_decide

end Wasm
