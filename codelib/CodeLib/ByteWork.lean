import CodeLib.CostedSteps

/-! # Byte costs for finite Wasm executions -/

namespace Wasm.SmallStep

/-- Bulk instructions keep their length on top of the operand stack. -/
def operandLength (config : Config α) : Nat :=
  match config.expr with
  | .running thread =>
      match thread.locals.values with
      | .i32 len :: _ => len.toNat
      | .i64 len :: _ => len.toNat
      | _ => 0
  | _ => 0

/-- Concrete byte-work charge. The host callback must describe the concrete
host's transferred bytes; it receives both states and the host function index. -/
def byteWork (hostBytes : Config α → Nat → Config α → Nat) : StepCost α :=
  fun before kind after => 1 +
    match kind with
    | .instruction .memoryCopy | .instruction .memoryFill
    | .instruction (.memoryCopyBetween _ _)
    | .instruction (.memoryInit _) => operandLength before
    | .instruction .memoryGrow =>
        65536 * (after.store.wasm.mem.pages - before.store.wasm.mem.pages)
    | .host index => hostBytes before index after
    | _ => 0

theorem byteWork_positive (hostBytes) (before : Config α) kind after :
    1 ≤ byteWork hostBytes before kind after := by
  simp only [byteWork]
  omega

/-- Symbolic successful memory.copy consumer. The bulk copy costs its entire
byte length even though the authoritative semantics executes it atomically. -/
theorem memoryCopy32_costed
    (store : MachineStore α) (params localValues values : List Value)
    (code : Program) (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame)
    (destination source len : UInt32)
    (hdestination : destination.toNat + len.toNat ≤ store.wasm.mem.pages * 65536)
    (hsource : source.toNat + len.toNat ≤ store.wasm.mem.pages * 65536)
    (hostBytes : Config α → Nat → Config α → Nat) :
    CostedSteps (byteWork hostBytes)
      ⟨.running ⟨⟨params, localValues,
        .i32 len :: .i32 source :: .i32 destination :: values⟩,
        .memoryCopy :: code, arity, remainder, controls, calls⟩, store⟩
      [.instruction .memoryCopy]
      ⟨.running ⟨⟨params, localValues, values⟩,
        code, arity, remainder, controls, calls⟩,
        { store with wasm := { store.wasm with
          mem := store.wasm.mem.copy destination.toNat source.toNat len.toNat } }⟩
      (1 + len.toNat) := by
  exact CostedSteps.single (Step.memoryCopy32 hdestination hsource)

end Wasm.SmallStep
