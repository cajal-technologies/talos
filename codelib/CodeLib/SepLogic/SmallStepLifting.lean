import CodeLib.SepLogic.SmallStepState
import Iris.ProgramLogic.Lifting

/-!
# Primitive Iris lifting rules for Wasm small steps

These rules are proved from `Wasm.SmallStep.Step` through the iris-lean
`PrimStep` adapter. They do not mention the legacy big-step interpreter.
-/

namespace Wasm.SmallStep

open Iris Iris.ProgramLogic Language.Notation
open Wasm.SepLogic

variable [WasmSmallStepGS hlc]
local instance instWasmIrisGS :
    IrisGS_gen hlc (Expr α) WasmHeapGF :=
  instIrisGS
variable {s : Stuckness} {E : CoPset}
variable {Φ : List Value → IProp WasmHeapGF}

/-- Generic lifting rule for a store-preserving deterministic Wasm step.
Most operand, control-frame, and administrative rules are thin specializations
of this theorem; stateful instructions use dedicated rules below. -/
theorem wp_pureStep
    (kind : StepKind) (current next : ThreadState α)
    (hstep : ∀ store : MachineStore α,
      Step ⟨.running current, store⟩ kind ⟨.running next, store⟩) :
    ▷ WP (Expr.running next : Expr α) @ s; E {{ Φ }} ⊢
      WP (Expr.running current : Expr α) @ s; E {{ Φ }} := by
  iintro Hwp
  iapply wp_lift_step rfl
  iintro %store %ns %obs %obs' %nt Hσ
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro
    cases s <;> simp only [Stuckness.MaybeReducible]
    exact ⟨[kind], .running next, store, [],
      ⟨rfl, _, rfl, hstep store⟩⟩
  iintro !> %e₂ %store₂ %forks %Hprim Hcredit
  rcases Hprim with ⟨hforks, actualKind, hobs, wasmStep⟩
  change forks = [] at hforks
  subst forks
  subst obs
  obtain ⟨rfl, hconfig⟩ :=
    step_deterministic (hstep store) wasmStep
  have parts := Config.mk.inj hconfig
  have hexpr := parts.1
  have hstore := parts.2
  simp only at hexpr hstore
  subst e₂
  subst store₂
  simp only [List.length_nil, Nat.add_zero, Iris.Algebra.BigOpL.bigOpL_nil]
  imod Hclose
  imodintro
  isplitl [Hσ]
  · iexact Hσ
  isplitl [Hwp]
  · iexact Hwp
  · itrivial

/-! ## Generic scalar numeric rules

The float/conversion family is exposed through the evaluator functions used
by `Step`, so generated proofs can specialize results by reduction without a
separate lifting theorem for every opcode.
-/

theorem wp_scalarFloat0
    {params localValues values : List Value}
    {instruction : Instruction} {value : Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    (heval : evalScalarFloat0? instruction = some value) :
    ▷ WP (.running
      ⟨⟨params, localValues, value :: values⟩,
        code, arity, remainder, controls, calls⟩ : Expr α) @ s; E {{ Φ }} ⊢
    WP (.running
      ⟨⟨params, localValues, values⟩,
        instruction :: code, arity, remainder, controls, calls⟩ : Expr α) @ s; E
      {{ Φ }} :=
  wp_pureStep _ _ _ (fun _ => Step.scalarFloat0 heval)

theorem wp_scalarFloat1
    {params localValues values : List Value}
    {instruction : Instruction} {operand value : Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    (hzero : evalScalarFloat0? instruction = none)
    (heval : evalScalarFloat1? instruction operand = some value) :
    ▷ WP (.running
      ⟨⟨params, localValues, value :: values⟩,
        code, arity, remainder, controls, calls⟩ : Expr α) @ s; E {{ Φ }} ⊢
    WP (.running
      ⟨⟨params, localValues, operand :: values⟩,
        instruction :: code, arity, remainder, controls, calls⟩ : Expr α) @ s; E
      {{ Φ }} :=
  wp_pureStep _ _ _ (fun _ => Step.scalarFloat1 hzero heval)

theorem wp_scalarFloat2
    {params localValues values : List Value}
    {instruction : Instruction} {lhs rhs value : Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    (hzero : evalScalarFloat0? instruction = none)
    (hunary : evalScalarFloat1? instruction rhs = none)
    (heval : evalScalarFloat2? instruction lhs rhs = some value) :
    ▷ WP (.running
      ⟨⟨params, localValues, value :: values⟩,
        code, arity, remainder, controls, calls⟩ : Expr α) @ s; E {{ Φ }} ⊢
    WP (.running
      ⟨⟨params, localValues, rhs :: lhs :: values⟩,
        instruction :: code, arity, remainder, controls, calls⟩ : Expr α) @ s; E
      {{ Φ }} :=
  wp_pureStep _ _ _ (fun _ => Step.scalarFloat2 hzero hunary heval)

theorem wp_scalarTruncSuccess
    {params localValues values : List Value}
    {instruction : Instruction} {operand value : Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    (heval : evalScalarTrunc? instruction operand = some (.ok value)) :
    ▷ WP (.running
      ⟨⟨params, localValues, value :: values⟩,
        code, arity, remainder, controls, calls⟩ : Expr α) @ s; E {{ Φ }} ⊢
    WP (.running
      ⟨⟨params, localValues, operand :: values⟩,
        instruction :: code, arity, remainder, controls, calls⟩ : Expr α) @ s; E
      {{ Φ }} :=
  wp_pureStep _ _ _ (fun _ => Step.scalarTruncSuccess heval)

theorem wp_finish
    {params localValues values remainder : List Value} {arity : Nat} :
    ▷ WP (.done (values.take arity ++ remainder) : Expr α) @ s; E {{ Φ }} ⊢
      WP (.running
        ⟨⟨params, localValues, values⟩, [], arity, remainder, [], []⟩ :
        Expr α) @ s; E {{ Φ }} := by
  iintro Hwp
  iapply wp_lift_step rfl
  iintro %store %ns %obs %obs' %nt Hσ
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro
    cases s <;> simp only [Stuckness.MaybeReducible]
    exact ⟨[.administrative .finish],
      .done (values.take arity ++ remainder), store, [],
      ⟨rfl, _, rfl, Step.finish⟩⟩
  iintro !> %e₂ %store₂ %forks %Hstep Hcredit
  rcases Hstep with ⟨hforks, kind, hobs, wasmStep⟩
  change forks = [] at hforks
  subst forks
  subst obs
  obtain ⟨rfl, hconfig⟩ := step_deterministic Step.finish wasmStep
  have parts := Config.mk.inj hconfig
  have hexpr := parts.1
  have hstore := parts.2
  simp only at hexpr hstore
  subst e₂
  subst store₂
  simp only [List.length_nil, Nat.add_zero, Iris.Algebra.BigOpL.bigOpL_nil]
  imod Hclose
  imodintro
  isplitl [Hσ]
  · iexact Hσ
  isplitl [Hwp]
  · iexact Hwp
  · itrivial

/-- Explicit return from a top-level invocation. The instruction discards the
remaining code and control frames and exposes the declared function results as
an Iris value. -/
theorem wp_returnFromFunction
    {locals : Locals} {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame} :
    ▷ WP (.done (locals.values.take arity ++ remainder) : Expr α) @ s; E
        {{ Φ }} ⊢
      WP (.running
        ⟨locals, .ret :: code, arity, remainder, controls, []⟩ : Expr α) @
        s; E {{ Φ }} := by
  iintro Hwp
  iapply wp_lift_step rfl
  iintro %store %ns %obs %obs' %nt Hσ
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro
    cases s <;> simp only [Stuckness.MaybeReducible]
    exact ⟨[.administrative .returnFromFunction],
      .done (locals.values.take arity ++ remainder), store, [],
      ⟨rfl, _, rfl, Step.returnFromFunction⟩⟩
  iintro !> %e₂ %store₂ %forks %Hstep Hcredit
  rcases Hstep with ⟨hforks, kind, hobs, wasmStep⟩
  change forks = [] at hforks
  subst forks
  subst obs
  obtain ⟨rfl, hconfig⟩ :=
    step_deterministic Step.returnFromFunction wasmStep
  have parts := Config.mk.inj hconfig
  have hexpr := parts.1
  have hstore := parts.2
  simp only at hexpr hstore
  subst e₂
  subst store₂
  simp only [List.length_nil, Nat.add_zero,
    Iris.Algebra.BigOpL.bigOpL_nil]
  imod Hclose
  imodintro
  isplitl [Hσ]
  · iexact Hσ
  isplitl [Hwp]
  · iexact Hwp
  · itrivial

theorem wp_const
    {params localValues values : List Value}
    {value : UInt32} {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame} :
    let current : ThreadState α :=
      ⟨⟨params, localValues, values⟩, .const value :: code, arity, remainder, controls, calls⟩
    let next : ThreadState α :=
      ⟨⟨params, localValues, .i32 value :: values⟩, code, arity, remainder, controls, calls⟩
    ▷ WP (Expr.running next : Expr α) @ s; E {{ Φ }} ⊢
      WP (Expr.running current : Expr α) @ s; E {{ Φ }} := by
  dsimp only
  iintro Hwp
  iapply wp_lift_step rfl
  iintro %store %ns %obs %obs' %nt Hσ
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro
    cases s <;> simp only [Stuckness.MaybeReducible]
    exact ⟨[.instruction (.const value)],
      .running ⟨⟨params, localValues, .i32 value :: values⟩,
        code, arity, remainder, controls, calls⟩,
      store, [], ⟨rfl, _, rfl, Step.const⟩⟩
  iintro !> %e₂ %store₂ %forks %Hstep Hcredit
  rcases Hstep with ⟨hforks, kind, hobs, wasmStep⟩
  change forks = [] at hforks
  subst forks
  subst obs
  obtain ⟨rfl, hconfig⟩ := step_deterministic Step.const wasmStep
  have parts := Config.mk.inj hconfig
  have hexpr := parts.1
  have hstore := parts.2
  simp only at hexpr hstore
  subst e₂
  subst store₂
  simp only [List.length_nil, Nat.add_zero, Iris.Algebra.BigOpL.bigOpL_nil]
  imod Hclose
  imodintro
  isplitl [Hσ]
  · iexact Hσ
  isplitl [Hwp]
  · iexact Hwp
  · itrivial

/-- Pure primitive rule for wrapping i32 subtraction. -/
theorem wp_sub
    {params localValues values : List Value}
    {lhs rhs : UInt32} {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame} :
    let current : ThreadState α :=
      ⟨⟨params, localValues, .i32 rhs :: .i32 lhs :: values⟩,
        .sub :: code, arity, remainder, controls, calls⟩
    let next : ThreadState α :=
      ⟨⟨params, localValues, .i32 (lhs - rhs) :: values⟩,
        code, arity, remainder, controls, calls⟩
    ▷ WP (Expr.running next : Expr α) @ s; E {{ Φ }} ⊢
      WP (Expr.running current : Expr α) @ s; E {{ Φ }} := by
  dsimp only
  iintro Hwp
  iapply wp_lift_step rfl
  iintro %store %ns %obs %obs' %nt Hσ
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro
    cases s <;> simp only [Stuckness.MaybeReducible]
    exact ⟨[.instruction .sub],
      .running
        ⟨⟨params, localValues, .i32 (lhs - rhs) :: values⟩,
          code, arity, remainder, controls, calls⟩,
      store, [], ⟨rfl, _, rfl, Step.sub⟩⟩
  iintro !> %e₂ %store₂ %forks %Hstep Hcredit
  rcases Hstep with ⟨hforks, kind, hobs, wasmStep⟩
  change forks = [] at hforks
  subst forks
  subst obs
  obtain ⟨rfl, hconfig⟩ := step_deterministic Step.sub wasmStep
  have parts := Config.mk.inj hconfig
  have hexpr := parts.1
  have hstore := parts.2
  simp only at hexpr hstore
  subst e₂
  subst store₂
  simp only [List.length_nil, Nat.add_zero,
    Iris.Algebra.BigOpL.bigOpL_nil]
  imod Hclose
  imodintro
  isplitl [Hσ]
  · iexact Hσ
  isplitl [Hwp]
  · iexact Hwp
  · itrivial

theorem wp_add
    {params localValues values : List Value}
    {lhs rhs : UInt32} {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame} :
    ▷ WP (.running
      ⟨⟨params, localValues, .i32 (rhs + lhs) :: values⟩,
        code, arity, remainder, controls, calls⟩ : Expr α) @ s; E {{ Φ }} ⊢
    WP (.running
      ⟨⟨params, localValues, .i32 rhs :: .i32 lhs :: values⟩,
        .add :: code, arity, remainder, controls, calls⟩ : Expr α) @ s; E
      {{ Φ }} :=
  wp_pureStep _ _ _ (fun _ => Step.add)

theorem wp_mul
    {params localValues values : List Value}
    {lhs rhs : UInt32} {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame} :
    ▷ WP (.running
      ⟨⟨params, localValues, .i32 (rhs * lhs) :: values⟩,
        code, arity, remainder, controls, calls⟩ : Expr α) @ s; E {{ Φ }} ⊢
    WP (.running
      ⟨⟨params, localValues, .i32 rhs :: .i32 lhs :: values⟩,
        .mul :: code, arity, remainder, controls, calls⟩ : Expr α) @ s; E
      {{ Φ }} :=
  wp_pureStep _ _ _ (fun _ => Step.mul)

theorem wp_remU
    {params localValues values : List Value}
    {dividend divisor : UInt32} {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame}
    (hdivisor : divisor ≠ 0) :
    ▷ WP (.running
      ⟨⟨params, localValues, .i32 (dividend % divisor) :: values⟩,
        code, arity, remainder, controls, calls⟩ : Expr α) @ s; E {{ Φ }} ⊢
    WP (.running
      ⟨⟨params, localValues, .i32 divisor :: .i32 dividend :: values⟩,
        .remU :: code, arity, remainder, controls, calls⟩ : Expr α) @ s; E
      {{ Φ }} :=
  wp_pureStep _ _ _ (fun _ => Step.remU hdivisor)

theorem wp_addI64
    {params localValues values : List Value}
    {lhs rhs : UInt64} {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame} :
    ▷ WP (.running
      ⟨⟨params, localValues, .i64 (lhs + rhs) :: values⟩,
        code, arity, remainder, controls, calls⟩ : Expr α) @ s; E {{ Φ }} ⊢
    WP (.running
      ⟨⟨params, localValues, .i64 rhs :: .i64 lhs :: values⟩,
        .addI64 :: code, arity, remainder, controls, calls⟩ : Expr α) @ s; E
      {{ Φ }} :=
  wp_pureStep _ _ _ (fun _ => Step.addI64)

theorem wp_subI64
    {params localValues values : List Value}
    {lhs rhs : UInt64} {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame} :
    ▷ WP (.running
      ⟨⟨params, localValues, .i64 (lhs - rhs) :: values⟩,
        code, arity, remainder, controls, calls⟩ : Expr α) @ s; E {{ Φ }} ⊢
    WP (.running
      ⟨⟨params, localValues, .i64 rhs :: .i64 lhs :: values⟩,
        .subI64 :: code, arity, remainder, controls, calls⟩ : Expr α) @ s; E
      {{ Φ }} :=
  wp_pureStep _ _ _ (fun _ => Step.subI64)

theorem wp_mulI64
    {params localValues values : List Value}
    {lhs rhs : UInt64} {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame} :
    ▷ WP (.running
      ⟨⟨params, localValues, .i64 (lhs * rhs) :: values⟩,
        code, arity, remainder, controls, calls⟩ : Expr α) @ s; E {{ Φ }} ⊢
    WP (.running
      ⟨⟨params, localValues, .i64 rhs :: .i64 lhs :: values⟩,
        .mulI64 :: code, arity, remainder, controls, calls⟩ : Expr α) @ s; E
      {{ Φ }} :=
  wp_pureStep _ _ _ (fun _ => Step.mulI64)

theorem wp_constI64
    {params localValues values : List Value}
    {value : UInt64} {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame} :
    ▷ WP (.running
      ⟨⟨params, localValues, .i64 value :: values⟩,
        code, arity, remainder, controls, calls⟩ : Expr α) @ s; E {{ Φ }} ⊢
    WP (.running
      ⟨⟨params, localValues, values⟩,
        .constI64 value :: code, arity, remainder, controls, calls⟩ : Expr α) @ s; E
      {{ Φ }} :=
  wp_pureStep _ _ _ (fun _ => Step.constI64)

theorem wp_andI64
    {params localValues values : List Value}
    {lhs rhs : UInt64} {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame} :
    ▷ WP (.running
      ⟨⟨params, localValues, .i64 (lhs &&& rhs) :: values⟩,
        code, arity, remainder, controls, calls⟩ : Expr α) @ s; E {{ Φ }} ⊢
    WP (.running
      ⟨⟨params, localValues, .i64 rhs :: .i64 lhs :: values⟩,
        .andI64 :: code, arity, remainder, controls, calls⟩ : Expr α) @ s; E
      {{ Φ }} :=
  wp_pureStep _ _ _ (fun _ => Step.andI64)

theorem wp_orI64
    {params localValues values : List Value}
    {lhs rhs : UInt64} {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame} :
    ▷ WP (.running
      ⟨⟨params, localValues, .i64 (lhs ||| rhs) :: values⟩,
        code, arity, remainder, controls, calls⟩ : Expr α) @ s; E {{ Φ }} ⊢
    WP (.running
      ⟨⟨params, localValues, .i64 rhs :: .i64 lhs :: values⟩,
        .orI64 :: code, arity, remainder, controls, calls⟩ : Expr α) @ s; E
      {{ Φ }} :=
  wp_pureStep _ _ _ (fun _ => Step.orI64)

theorem wp_xorI64
    {params localValues values : List Value}
    {lhs rhs : UInt64} {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame} :
    ▷ WP (.running
      ⟨⟨params, localValues, .i64 (lhs ^^^ rhs) :: values⟩,
        code, arity, remainder, controls, calls⟩ : Expr α) @ s; E {{ Φ }} ⊢
    WP (.running
      ⟨⟨params, localValues, .i64 rhs :: .i64 lhs :: values⟩,
        .xorI64 :: code, arity, remainder, controls, calls⟩ : Expr α) @ s; E
      {{ Φ }} :=
  wp_pureStep _ _ _ (fun _ => Step.xorI64)

theorem wp_shlI64
    {params localValues values : List Value}
    {lhs rhs : UInt64} {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame} :
    ▷ WP (.running
      ⟨⟨params, localValues, .i64 (lhs <<< (rhs % 64)) :: values⟩,
        code, arity, remainder, controls, calls⟩ : Expr α) @ s; E {{ Φ }} ⊢
    WP (.running
      ⟨⟨params, localValues, .i64 rhs :: .i64 lhs :: values⟩,
        .shlI64 :: code, arity, remainder, controls, calls⟩ : Expr α) @ s; E
      {{ Φ }} :=
  wp_pureStep _ _ _ (fun _ => Step.shlI64)

theorem wp_shrUI64
    {params localValues values : List Value}
    {lhs rhs : UInt64} {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame} :
    ▷ WP (.running
      ⟨⟨params, localValues, .i64 (lhs >>> (rhs % 64)) :: values⟩,
        code, arity, remainder, controls, calls⟩ : Expr α) @ s; E {{ Φ }} ⊢
    WP (.running
      ⟨⟨params, localValues, .i64 rhs :: .i64 lhs :: values⟩,
        .shrUI64 :: code, arity, remainder, controls, calls⟩ : Expr α) @ s; E
      {{ Φ }} :=
  wp_pureStep _ _ _ (fun _ => Step.shrUI64)

theorem wp_ctzI64
    {params localValues values : List Value}
    {value : UInt64} {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame} :
    ▷ WP (.running
      ⟨⟨params, localValues,
          .i64 (UInt64.ofNat (ctz64 64 value)) :: values⟩,
        code, arity, remainder, controls, calls⟩ : Expr α) @ s; E {{ Φ }} ⊢
    WP (.running
      ⟨⟨params, localValues, .i64 value :: values⟩,
        .ctzI64 :: code, arity, remainder, controls, calls⟩ : Expr α) @ s; E
      {{ Φ }} :=
  wp_pureStep _ _ _ (fun _ => Step.ctzI64)

theorem wp_wrapI64
    {params localValues values : List Value}
    {value : UInt64} {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame} :
    ▷ WP (.running
      ⟨⟨params, localValues,
          .i32 (UInt32.ofNat (value.toNat % 2 ^ 32)) :: values⟩,
        code, arity, remainder, controls, calls⟩ : Expr α) @ s; E {{ Φ }} ⊢
    WP (.running
      ⟨⟨params, localValues, .i64 value :: values⟩,
        .wrapI64 :: code, arity, remainder, controls, calls⟩ : Expr α) @ s; E
      {{ Φ }} :=
  wp_pureStep _ _ _ (fun _ => Step.wrapI64)

theorem wp_extendUI32
    {params localValues values : List Value}
    {value : UInt32} {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame} :
    ▷ WP (.running
      ⟨⟨params, localValues, .i64 (UInt64.ofNat value.toNat) :: values⟩,
        code, arity, remainder, controls, calls⟩ : Expr α) @ s; E {{ Φ }} ⊢
    WP (.running
      ⟨⟨params, localValues, .i32 value :: values⟩,
        .extendUI32 :: code, arity, remainder, controls, calls⟩ : Expr α) @ s; E
      {{ Φ }} :=
  wp_pureStep _ _ _ (fun _ => Step.extendUI32)

theorem wp_and
    {params localValues values : List Value}
    {lhs rhs : UInt32} {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame} :
    ▷ WP (.running
      ⟨⟨params, localValues, .i32 (lhs &&& rhs) :: values⟩,
        code, arity, remainder, controls, calls⟩ : Expr α) @ s; E {{ Φ }} ⊢
    WP (.running
      ⟨⟨params, localValues, .i32 rhs :: .i32 lhs :: values⟩,
        .and :: code, arity, remainder, controls, calls⟩ : Expr α) @ s; E
      {{ Φ }} :=
  wp_pureStep _ _ _ (fun _ => Step.and)

theorem wp_or
    {params localValues values : List Value}
    {lhs rhs : UInt32} {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame} :
    ▷ WP (.running
      ⟨⟨params, localValues, .i32 (lhs ||| rhs) :: values⟩,
        code, arity, remainder, controls, calls⟩ : Expr α) @ s; E {{ Φ }} ⊢
    WP (.running
      ⟨⟨params, localValues, .i32 rhs :: .i32 lhs :: values⟩,
        .or :: code, arity, remainder, controls, calls⟩ : Expr α) @ s; E
      {{ Φ }} :=
  wp_pureStep _ _ _ (fun _ => Step.or)

theorem wp_xor
    {params localValues values : List Value}
    {lhs rhs : UInt32} {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame} :
    ▷ WP (.running
      ⟨⟨params, localValues, .i32 (lhs ^^^ rhs) :: values⟩,
        code, arity, remainder, controls, calls⟩ : Expr α) @ s; E {{ Φ }} ⊢
    WP (.running
      ⟨⟨params, localValues, .i32 rhs :: .i32 lhs :: values⟩,
        .xor :: code, arity, remainder, controls, calls⟩ : Expr α) @ s; E
      {{ Φ }} :=
  wp_pureStep _ _ _ (fun _ => Step.xor)

theorem wp_shl
    {params localValues values : List Value}
    {lhs rhs : UInt32} {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame} :
    ▷ WP (.running
      ⟨⟨params, localValues, .i32 (lhs <<< (rhs % 32)) :: values⟩,
        code, arity, remainder, controls, calls⟩ : Expr α) @ s; E {{ Φ }} ⊢
    WP (.running
      ⟨⟨params, localValues, .i32 rhs :: .i32 lhs :: values⟩,
        .shl :: code, arity, remainder, controls, calls⟩ : Expr α) @ s; E
      {{ Φ }} :=
  wp_pureStep _ _ _ (fun _ => Step.shl)

theorem wp_eqz
    {params localValues values : List Value}
    {value result : UInt32} {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame}
    (hresult : result = if value = 0 then 1 else 0) :
    ▷ WP (.running
      ⟨⟨params, localValues, .i32 result :: values⟩,
        code, arity, remainder, controls, calls⟩ : Expr α) @ s; E {{ Φ }} ⊢
    WP (.running
      ⟨⟨params, localValues, .i32 value :: values⟩,
        .eqz :: code, arity, remainder, controls, calls⟩ : Expr α) @ s; E
      {{ Φ }} :=
  wp_pureStep _ _ _ (fun _ => Step.eqz hresult)

theorem wp_eq
    {params localValues values : List Value}
    {lhs rhs result : UInt32} {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame}
    (hresult : result = if lhs = rhs then 1 else 0) :
    ▷ WP (.running
      ⟨⟨params, localValues, .i32 result :: values⟩,
        code, arity, remainder, controls, calls⟩ : Expr α) @ s; E {{ Φ }} ⊢
    WP (.running
      ⟨⟨params, localValues, .i32 rhs :: .i32 lhs :: values⟩,
        .eq :: code, arity, remainder, controls, calls⟩ : Expr α) @ s; E
      {{ Φ }} :=
  wp_pureStep _ _ _ (fun _ => Step.eq hresult)

theorem wp_ne
    {params localValues values : List Value}
    {lhs rhs result : UInt32} {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame}
    (hresult : result = if lhs ≠ rhs then 1 else 0) :
    ▷ WP (.running
      ⟨⟨params, localValues, .i32 result :: values⟩,
        code, arity, remainder, controls, calls⟩ : Expr α) @ s; E {{ Φ }} ⊢
    WP (.running
      ⟨⟨params, localValues, .i32 rhs :: .i32 lhs :: values⟩,
        .ne :: code, arity, remainder, controls, calls⟩ : Expr α) @ s; E
      {{ Φ }} :=
  wp_pureStep _ _ _ (fun _ => Step.ne hresult)

theorem wp_ltU
    {params localValues values : List Value}
    {lhs rhs result : UInt32} {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame}
    (hresult : result = if lhs < rhs then 1 else 0) :
    ▷ WP (.running
      ⟨⟨params, localValues, .i32 result :: values⟩,
        code, arity, remainder, controls, calls⟩ : Expr α) @ s; E {{ Φ }} ⊢
    WP (.running
      ⟨⟨params, localValues, .i32 rhs :: .i32 lhs :: values⟩,
        .ltU :: code, arity, remainder, controls, calls⟩ : Expr α) @ s; E
      {{ Φ }} :=
  wp_pureStep _ _ _ (fun _ => Step.ltU hresult)

theorem wp_geU
    {params localValues values : List Value}
    {lhs rhs result : UInt32} {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame}
    (hresult : result = if lhs ≥ rhs then 1 else 0) :
    ▷ WP (.running
      ⟨⟨params, localValues, .i32 result :: values⟩,
        code, arity, remainder, controls, calls⟩ : Expr α) @ s; E {{ Φ }} ⊢
    WP (.running
      ⟨⟨params, localValues, .i32 rhs :: .i32 lhs :: values⟩,
        .geU :: code, arity, remainder, controls, calls⟩ : Expr α) @ s; E
      {{ Φ }} :=
  wp_pureStep _ _ _ (fun _ => Step.geU hresult)

theorem wp_ltUI64
    {params localValues values : List Value}
    {lhs rhs : UInt64} {result : UInt32}
    {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame}
    (hresult : result = if lhs < rhs then 1 else 0) :
    ▷ WP (.running
      ⟨⟨params, localValues, .i32 result :: values⟩,
        code, arity, remainder, controls, calls⟩ : Expr α) @ s; E {{ Φ }} ⊢
    WP (.running
      ⟨⟨params, localValues, .i64 rhs :: .i64 lhs :: values⟩,
        .ltUI64 :: code, arity, remainder, controls, calls⟩ : Expr α) @ s; E
      {{ Φ }} :=
  wp_pureStep _ _ _ (fun _ => Step.ltUI64 hresult)

theorem wp_eqI64
    {params localValues values : List Value}
    {lhs rhs : UInt64} {result : UInt32}
    {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame}
    (hresult : result = if lhs = rhs then 1 else 0) :
    ▷ WP (.running
      ⟨⟨params, localValues, .i32 result :: values⟩,
        code, arity, remainder, controls, calls⟩ : Expr α) @ s; E {{ Φ }} ⊢
    WP (.running
      ⟨⟨params, localValues, .i64 rhs :: .i64 lhs :: values⟩,
        .eqI64 :: code, arity, remainder, controls, calls⟩ : Expr α) @ s; E
      {{ Φ }} :=
  wp_pureStep _ _ _ (fun _ => Step.eqI64 hresult)

theorem wp_eqzI64
    {params localValues values : List Value}
    {value : UInt64} {result : UInt32} {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame}
    (hresult : result = if value = 0 then 1 else 0) :
    ▷ WP (.running
      ⟨⟨params, localValues, .i32 result :: values⟩,
        code, arity, remainder, controls, calls⟩ : Expr α) @ s; E {{ Φ }} ⊢
    WP (.running
      ⟨⟨params, localValues, .i64 value :: values⟩,
        .eqzI64 :: code, arity, remainder, controls, calls⟩ : Expr α) @ s; E
      {{ Φ }} :=
  wp_pureStep _ _ _ (fun _ => Step.eqzI64 hresult)

theorem wp_neI64
    {params localValues values : List Value}
    {lhs rhs : UInt64} {result : UInt32} {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame}
    (hresult : result = if lhs ≠ rhs then 1 else 0) :
    ▷ WP (.running
      ⟨⟨params, localValues, .i32 result :: values⟩,
        code, arity, remainder, controls, calls⟩ : Expr α) @ s; E {{ Φ }} ⊢
    WP (.running
      ⟨⟨params, localValues, .i64 rhs :: .i64 lhs :: values⟩,
        .neI64 :: code, arity, remainder, controls, calls⟩ : Expr α) @ s; E
      {{ Φ }} :=
  wp_pureStep _ _ _ (fun _ => Step.neI64 hresult)

theorem wp_gtUI64
    {params localValues values : List Value}
    {lhs rhs : UInt64} {result : UInt32} {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame}
    (hresult : result = if lhs > rhs then 1 else 0) :
    ▷ WP (.running
      ⟨⟨params, localValues, .i32 result :: values⟩,
        code, arity, remainder, controls, calls⟩ : Expr α) @ s; E {{ Φ }} ⊢
    WP (.running
      ⟨⟨params, localValues, .i64 rhs :: .i64 lhs :: values⟩,
        .gtUI64 :: code, arity, remainder, controls, calls⟩ : Expr α) @ s; E
      {{ Φ }} :=
  wp_pureStep _ _ _ (fun _ => Step.gtUI64 hresult)

theorem wp_divUI64
    {params localValues values : List Value}
    {dividend divisor : UInt64} {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame}
    (hdivisor : divisor ≠ 0) :
    ▷ WP (.running
      ⟨⟨params, localValues, .i64 (dividend / divisor) :: values⟩,
        code, arity, remainder, controls, calls⟩ : Expr α) @ s; E {{ Φ }} ⊢
    WP (.running
      ⟨⟨params, localValues, .i64 divisor :: .i64 dividend :: values⟩,
        .divUI64 :: code, arity, remainder, controls, calls⟩ : Expr α) @ s; E
      {{ Φ }} :=
  wp_pureStep _ _ _ (fun _ => Step.divUI64 hdivisor)

theorem wp_remUI64
    {params localValues values : List Value}
    {dividend divisor : UInt64} {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame}
    (hdivisor : divisor ≠ 0) :
    ▷ WP (.running
      ⟨⟨params, localValues, .i64 (dividend % divisor) :: values⟩,
        code, arity, remainder, controls, calls⟩ : Expr α) @ s; E {{ Φ }} ⊢
    WP (.running
      ⟨⟨params, localValues, .i64 divisor :: .i64 dividend :: values⟩,
        .remUI64 :: code, arity, remainder, controls, calls⟩ : Expr α) @ s; E
      {{ Φ }} :=
  wp_pureStep _ _ _ (fun _ => Step.remUI64 hdivisor)

theorem wp_block
    {locals : Locals} {paramArity resultArity arity : Nat}
    {body code : Program} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame} :
    let frame : ControlFrame :=
      { kind := .block
        paramArity
        resultArity
        body
        continuation := code
        belowStack := locals.values.drop paramArity }
    ▷ WP (.running
      ⟨locals, body, arity, remainder, frame :: controls, calls⟩ :
        Expr α) @ s; E {{ Φ }} ⊢
    WP (.running
      ⟨locals, .block paramArity resultArity body :: code,
        arity, remainder, controls, calls⟩ : Expr α) @ s; E {{ Φ }} := by
  dsimp only
  exact wp_pureStep _ _ _ (fun _ => Step.block)

theorem wp_loop
    {locals : Locals} {paramArity resultArity arity : Nat}
    {body code : Program} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame} :
    let frame : ControlFrame :=
      { kind := .loop
        paramArity
        resultArity
        body
        continuation := code
        belowStack := locals.values.drop paramArity }
    ▷ WP (.running
      ⟨locals, body, arity, remainder, frame :: controls, calls⟩ :
        Expr α) @ s; E {{ Φ }} ⊢
    WP (.running
      ⟨locals, .loop paramArity resultArity body :: code,
        arity, remainder, controls, calls⟩ : Expr α) @ s; E {{ Φ }} := by
  dsimp only
  exact wp_pureStep _ _ _ (fun _ => Step.loop)

/-- Löb-induction wrapper for a Wasm loop body.

The premise is the reusable loop-body proof: assuming the guarded recursive
call, ownership of `I` establishes the WP at the top of the administrative
loop frame.  The conclusion packages the Löb argument and the initial
`.loop` transition.  Concrete loop proofs can therefore concentrate on
showing that their body either exits or re-establishes `I` before `br 0`.
-/
theorem wp_loop_löb
    {locals : Locals} {paramArity resultArity arity : Nat}
    {body code : Program} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    (I : IProp WasmHeapGF)
    (body_closes :
        (▷ (I -∗
          WP (.running
            ⟨locals, body, arity, remainder,
              { kind := .loop, paramArity, resultArity, body,
                continuation := code,
                belowStack := locals.values.drop paramArity } :: controls,
              calls⟩ : Expr α) @ s; E {{ Φ }})) ⊢@{IProp WasmHeapGF}
        (I -∗
          WP (.running
            ⟨locals, body, arity, remainder,
              { kind := .loop, paramArity, resultArity, body,
                continuation := code,
                belowStack := locals.values.drop paramArity } :: controls,
              calls⟩ : Expr α) @ s; E {{ Φ }})) :
    I ⊢
      WP (.running
        ⟨locals, .loop paramArity resultArity body :: code,
          arity, remainder, controls, calls⟩ : Expr α) @ s; E {{ Φ }} := by
  iintro HI
  iapply wp_loop
  inext
  iloeb as Hrec generalizing HI
  iapply body_closes
  · iexact Hrec
  · iexact HI

/-- Family-indexed Löb rule for loops whose locals and owned invariant change
at each back-edge.

`belowStack` is fixed when the loop is entered, exactly as in the operational
control frame.  The guarded hypothesis quantifies over every family index, so
a body proof may establish `I next` and branch back to `locals next`.
-/
def loopBodyExpr (locals : Locals)
    (paramArity resultArity arity : Nat)
    (body code : Program) (remainder belowStack : List Value)
    (controls : List ControlFrame) (calls : List CallFrame) : Expr α :=
  .running
    ⟨locals, body, arity, remainder,
      { kind := .loop, paramArity, resultArity, body,
        continuation := code, belowStack } :: controls,
      calls⟩

theorem wp_loop_löb_family
    {ι : Type} (locals : ι → Locals) (I : ι → IProp WasmHeapGF)
    (initial : ι)
    {paramArity resultArity arity : Nat}
    {body code : Program} {remainder belowStack : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    (hbelow : belowStack = (locals initial).values.drop paramArity)
    (body_closes : ∀ i,
      ⊢@{IProp WasmHeapGF} (iprop%
        ▷ (∀ (j : ι), I j -∗
          WP (loopBodyExpr (α := α) (locals j)
            paramArity resultArity arity body code remainder belowStack
            controls calls) @ s; E {{ Φ }}) -∗
        I i -∗
          WP (loopBodyExpr (α := α) (locals i)
            paramArity resultArity arity body code remainder belowStack
            controls calls) @ s; E {{ Φ }})) :
    I initial ⊢
      WP (.running
        ⟨locals initial, .loop paramArity resultArity body :: code,
          arity, remainder, controls, calls⟩ : Expr α) @ s; E {{ Φ }} := by
  iintro HI
  iapply wp_loop
  inext
  rw [← hbelow]
  clear hbelow
  simp only [loopBodyExpr] at body_closes
  iloeb as IH generalizing %initial HI
  iapply body_closes initial
  · iexact IH
  · iexact HI

theorem wp_iff
    {params localValues values : List Value}
    {condition : UInt32}
    {paramArity resultArity arity : Nat}
    {thenBody elseBody selectedBody code : Program}
    {paramTypes resultTypes : List ValueType}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame}
    (hselected :
      selectedBody = if condition ≠ 0 then thenBody else elseBody) :
    ▷ WP (.running
      ⟨⟨params, localValues, values⟩, selectedBody, arity, remainder,
        { kind := .block, paramArity, resultArity,
          body := selectedBody, continuation := code,
          belowStack := values.drop paramArity } :: controls,
        calls⟩ : Expr α) @ s; E {{ Φ }} ⊢
    WP (.running
      ⟨⟨params, localValues, .i32 condition :: values⟩,
        .iff paramArity resultArity thenBody elseBody
          paramTypes resultTypes :: code,
        arity, remainder, controls, calls⟩ : Expr α) @ s; E {{ Φ }} :=
  wp_pureStep _ _ _ (fun _ => Step.iff hselected)

theorem wp_exitControl
    {locals : Locals} {frame : ControlFrame}
    {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    (hkind : frame.kind.isThrowing = false) :
    ▷ WP (.running
      ⟨{ locals with
          values := locals.values.take frame.resultArity ++ frame.belowStack },
        frame.continuation, arity, remainder, controls, calls⟩ :
        Expr α) @ s; E {{ Φ }} ⊢
    WP (.running
      ⟨locals, [], arity, remainder, frame :: controls, calls⟩ :
        Expr α) @ s; E {{ Φ }} :=
  wp_pureStep _ _ _ (fun _ => Step.exitControl hkind)

theorem wp_brIfZero
    {params localValues values : List Value}
    {depth arity : Nat} {code : Program} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame} :
    ▷ WP (.running
      ⟨⟨params, localValues, values⟩, code,
        arity, remainder, controls, calls⟩ : Expr α) @ s; E {{ Φ }} ⊢
    WP (.running
      ⟨⟨params, localValues, .i32 0 :: values⟩, .br_if depth :: code,
        arity, remainder, controls, calls⟩ : Expr α) @ s; E {{ Φ }} :=
  wp_pureStep _ _ _ (fun _ => Step.brIfZero)

theorem wp_brIf
    {params localValues values targetValues : List Value}
    {condition : UInt32} {depth arity : Nat}
    {code targetCode : Program} {remainder : List Value}
    {controls targetControl : List ControlFrame} {calls : List CallFrame}
    (hcondition : condition ≠ 0)
    (htarget : branchTarget? arity depth controls values =
      some (targetCode, targetControl, targetValues)) :
    ▷ WP (.running
      ⟨⟨params, localValues, targetValues⟩, targetCode,
        arity, remainder, targetControl, calls⟩ : Expr α) @ s; E {{ Φ }} ⊢
    WP (.running
      ⟨⟨params, localValues, .i32 condition :: values⟩,
        .br_if depth :: code, arity, remainder, controls, calls⟩ :
        Expr α) @ s; E {{ Φ }} :=
  wp_pureStep _ _ _ (fun _ => Step.brIf hcondition htarget)

theorem wp_br
    {params localValues values targetValues : List Value}
    {depth arity : Nat} {code targetCode : Program}
    {remainder : List Value}
    {controls targetControl : List ControlFrame} {calls : List CallFrame}
    (htarget : branchTarget? arity depth controls values =
      some (targetCode, targetControl, targetValues)) :
    ▷ WP (.running
      ⟨⟨params, localValues, targetValues⟩, targetCode,
        arity, remainder, targetControl, calls⟩ : Expr α) @ s; E {{ Φ }} ⊢
    WP (.running
      ⟨⟨params, localValues, values⟩, .br depth :: code,
        arity, remainder, controls, calls⟩ : Expr α) @ s; E {{ Φ }} :=
  wp_pureStep _ _ _ (fun _ => Step.br htarget)

/-- Pure primitive rule for `ref.is_null`; all supported reference kinds use
the same `Value.isNullRef?` observation. -/
theorem wp_refIsNull
    {params localValues values : List Value}
    {value : Value} {isNull : Bool} {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame}
    (hnull : value.isNullRef? = some isNull) :
    let current : ThreadState α :=
      ⟨⟨params, localValues, value :: values⟩,
        .refIsNull :: code, arity, remainder, controls, calls⟩
    let next : ThreadState α :=
      ⟨⟨params, localValues,
          .i32 (if isNull then 1 else 0) :: values⟩,
        code, arity, remainder, controls, calls⟩
    ▷ WP (Expr.running next : Expr α) @ s; E {{ Φ }} ⊢
      WP (Expr.running current : Expr α) @ s; E {{ Φ }} := by
  dsimp only
  iintro Hwp
  iapply wp_lift_step rfl
  iintro %store %ns %obs %obs' %nt Hσ
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro
    cases s <;> simp only [Stuckness.MaybeReducible]
    cases isNull
    · exact ⟨[.instruction .refIsNull],
        .running ⟨⟨params, localValues, .i32 0 :: values⟩,
          code, arity, remainder, controls, calls⟩,
        store, [], ⟨rfl, _, rfl, Step.refIsNullFalse hnull⟩⟩
    · exact ⟨[.instruction .refIsNull],
        .running ⟨⟨params, localValues, .i32 1 :: values⟩,
          code, arity, remainder, controls, calls⟩,
        store, [], ⟨rfl, _, rfl, Step.refIsNullTrue hnull⟩⟩
  iintro !> %e₂ %store₂ %forks %Hstep Hcredit
  rcases Hstep with ⟨hforks, kind, hobs, wasmStep⟩
  change forks = [] at hforks
  subst forks
  subst obs
  have expectedStep : Step
      ⟨.running ⟨⟨params, localValues, value :: values⟩,
        .refIsNull :: code, arity, remainder, controls, calls⟩, store⟩
      (.instruction .refIsNull)
      ⟨.running ⟨⟨params, localValues,
          .i32 (if isNull then 1 else 0) :: values⟩,
        code, arity, remainder, controls, calls⟩, store⟩ := by
    cases isNull
    · exact Step.refIsNullFalse hnull
    · exact Step.refIsNullTrue hnull
  obtain ⟨rfl, hconfig⟩ := step_deterministic expectedStep wasmStep
  have parts := Config.mk.inj hconfig
  have hexpr := parts.1
  have hstore := parts.2
  simp only at hexpr hstore
  subst e₂
  subst store₂
  simp only [List.length_nil, Nat.add_zero, Iris.Algebra.BigOpL.bigOpL_nil]
  imod Hclose
  imodintro
  isplitl [Hσ]
  · iexact Hσ
  isplitl [Hwp]
  · iexact Hwp
  · itrivial

theorem wp_localGet
    {params localValues values : List Value}
    {index : Nat} {value : Value} {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame}
    (hget : (⟨params, localValues, values⟩ : Locals).get index = some value) :
    let current : ThreadState α :=
      ⟨⟨params, localValues, values⟩, .localGet index :: code,
        arity, remainder, controls, calls⟩
    let next : ThreadState α :=
      ⟨⟨params, localValues, value :: values⟩, code,
        arity, remainder, controls, calls⟩
    ▷ WP (Expr.running next : Expr α) @ s; E {{ Φ }} ⊢
      WP (Expr.running current : Expr α) @ s; E {{ Φ }} := by
  dsimp only
  iintro Hwp
  iapply wp_lift_step rfl
  iintro %store %ns %obs %obs' %nt Hσ
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro
    cases s <;> simp only [Stuckness.MaybeReducible]
    exact ⟨[.instruction (.localGet index)],
      .running ⟨⟨params, localValues, value :: values⟩,
        code, arity, remainder, controls, calls⟩,
      store, [], ⟨rfl, _, rfl, Step.localGet hget⟩⟩
  iintro !> %e₂ %store₂ %forks %Hstep Hcredit
  rcases Hstep with ⟨hforks, kind, hobs, wasmStep⟩
  change forks = [] at hforks
  subst forks
  subst obs
  obtain ⟨rfl, hconfig⟩ :=
    step_deterministic (Step.localGet (α := α) hget) wasmStep
  have parts := Config.mk.inj hconfig
  have hexpr := parts.1
  have hstore := parts.2
  simp only at hexpr hstore
  subst e₂
  subst store₂
  simp only [List.length_nil, Nat.add_zero, Iris.Algebra.BigOpL.bigOpL_nil]
  imod Hclose
  imodintro
  isplitl [Hσ]
  · iexact Hσ
  isplitl [Hwp]
  · iexact Hwp
  · itrivial

theorem wp_localSet
    {params localValues values : List Value}
    {index : Nat} {value : Value} {locals' : Locals}
    {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame}
    (hset : (⟨params, localValues, value :: values⟩ : Locals).set? index value =
      some locals') :
    let current : ThreadState α :=
      ⟨⟨params, localValues, value :: values⟩, .localSet index :: code,
        arity, remainder, controls, calls⟩
    let next : ThreadState α :=
      ⟨{ locals' with values }, code, arity, remainder, controls, calls⟩
    ▷ WP (Expr.running next : Expr α) @ s; E {{ Φ }} ⊢
      WP (Expr.running current : Expr α) @ s; E {{ Φ }} := by
  dsimp only
  iintro Hwp
  iapply wp_lift_step rfl
  iintro %store %ns %obs %obs' %nt Hσ
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro
    cases s <;> simp only [Stuckness.MaybeReducible]
    exact ⟨[.instruction (.localSet index)],
      .running ⟨{ locals' with values },
        code, arity, remainder, controls, calls⟩,
      store, [], ⟨rfl, _, rfl, Step.localSet hset⟩⟩
  iintro !> %e₂ %store₂ %forks %Hstep Hcredit
  rcases Hstep with ⟨hforks, kind, hobs, wasmStep⟩
  change forks = [] at hforks
  subst forks
  subst obs
  obtain ⟨rfl, hconfig⟩ :=
    step_deterministic (Step.localSet (α := α) hset) wasmStep
  have parts := Config.mk.inj hconfig
  have hexpr := parts.1
  have hstore := parts.2
  simp only at hexpr hstore
  subst e₂
  subst store₂
  simp only [List.length_nil, Nat.add_zero, Iris.Algebra.BigOpL.bigOpL_nil]
  imod Hclose
  imodintro
  isplitl [Hσ]
  · iexact Hσ
  isplitl [Hwp]
  · iexact Hwp
  · itrivial

/-- Enter a defined Wasm function. Immutable runtime-module ownership ties the
function lookup used by the rule to the actual `MachineStore` seen by
`PrimStep`; it is returned unchanged for subsequent calls. -/
theorem wp_call
    (runtimeModule : Module) (functionIndex : Nat) (fn : Function)
    (himports : ¬functionIndex < runtimeModule.imports.length)
    (hfn : runtimeModule.funcs[
      functionIndex - runtimeModule.imports.length]? = some fn)
    {params localValues values : List Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame} :
    let caller : CallFrame :=
      { locals := ⟨params, localValues, values.drop fn.numParams⟩
        continuation := code
        resultArity := arity
        callerRemainder := remainder
        control := controls }
    let current : ThreadState α :=
      ⟨⟨params, localValues, values⟩, .call functionIndex :: code,
        arity, remainder, controls, calls⟩
    let next : ThreadState α :=
      ⟨fn.toLocals (values.take fn.numParams).reverse,
        fn.body, fn.results.length, [], [], caller :: calls⟩
    ▷ runtimeModuleOwn runtimeModule -∗
    ▷ (runtimeModuleOwn runtimeModule -∗
      WP (Expr.running next : Expr α) @ s; E {{ Φ }}) -∗
      WP (Expr.running current : Expr α) @ s; E {{ Φ }} := by
  dsimp only
  iintro >Hruntime Hwp
  iapply wp_lift_step rfl
  iintro %store %ns %obs %obs' %nt Hσ
  ihave %Hmodule : ⌜store.runtime.module = runtimeModule⌝ $$
      [Hσ Hruntime]
  · imod stateInterp_runtimeModule_agree store ns (obs ++ obs') nt
      runtimeModule $$ [$Hσ $Hruntime] with %Hmodule
    ipureintro
    exact Hmodule
  have himports' :
      ¬functionIndex < store.runtime.module.imports.length := by
    simpa only [Hmodule] using himports
  have hfn' : store.runtime.module.funcs[
      functionIndex - store.runtime.module.imports.length]? = some fn := by
    simpa only [Hmodule] using hfn
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro
    cases s <;> simp only [Stuckness.MaybeReducible]
    exact ⟨[.instruction (.call functionIndex)],
      .running
        ⟨fn.toLocals (values.take fn.numParams).reverse,
          fn.body, fn.results.length, [], [],
          { locals := ⟨params, localValues, values.drop fn.numParams⟩
            continuation := code
            resultArity := arity
            callerRemainder := remainder
            control := controls } :: calls⟩,
      store, [], ⟨rfl, _, rfl, Step.call himports' hfn'⟩⟩
  iintro !> %e₂ %store₂ %forks %Hstep Hcredit
  rcases Hstep with ⟨hforks, kind, hobs, wasmStep⟩
  change forks = [] at hforks
  subst forks
  subst obs
  obtain ⟨rfl, hconfig⟩ :=
    step_deterministic (Step.call (α := α) himports' hfn') wasmStep
  have parts := Config.mk.inj hconfig
  have hexpr := parts.1
  have hstore := parts.2
  simp only at hexpr hstore
  subst e₂
  subst store₂
  simp only [List.length_nil, Nat.add_zero, Iris.Algebra.BigOpL.bigOpL_nil]
  imod Hclose
  imodintro
  isplitl [Hσ]
  · iexact Hσ
  isplitl [Hwp Hruntime]
  · iapply Hwp
    iexact Hruntime
  · itrivial

/-- Resume a suspended caller after an explicit callee return. -/
theorem wp_returnFromCallExplicit
    {calleeLocals callerLocals : Locals}
    {calleeCode callerCode : Program}
    {calleeArity callerArity : Nat}
    {calleeRemainder callerRemainder : List Value}
    {calleeControls callerControls : List ControlFrame}
    {calls : List CallFrame} :
    let caller : CallFrame :=
      { locals := callerLocals
        continuation := callerCode
        resultArity := callerArity
        callerRemainder := callerRemainder
        control := callerControls }
    let current : ThreadState α :=
      ⟨calleeLocals, .ret :: calleeCode, calleeArity, calleeRemainder,
        calleeControls, caller :: calls⟩
    let next : ThreadState α :=
      ⟨{ callerLocals with
          values :=
            calleeLocals.values.take calleeArity ++ callerLocals.values },
        callerCode, callerArity, callerRemainder, callerControls, calls⟩
    ▷ WP (Expr.running next : Expr α) @ s; E {{ Φ }} ⊢
      WP (Expr.running current : Expr α) @ s; E {{ Φ }} := by
  dsimp only
  iintro Hwp
  iapply wp_lift_step rfl
  iintro %store %ns %obs %obs' %nt Hσ
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro
    cases s <;> simp only [Stuckness.MaybeReducible]
    exact ⟨[.administrative .returnFromCall],
      .running
        ⟨{ callerLocals with
            values :=
              calleeLocals.values.take calleeArity ++ callerLocals.values },
          callerCode, callerArity, callerRemainder, callerControls, calls⟩,
      store, [], ⟨rfl, _, rfl, Step.returnFromCallExplicit⟩⟩
  iintro !> %e₂ %store₂ %forks %Hstep Hcredit
  rcases Hstep with ⟨hforks, kind, hobs, wasmStep⟩
  change forks = [] at hforks
  subst forks
  subst obs
  obtain ⟨rfl, hconfig⟩ :=
    step_deterministic
      (Step.returnFromCallExplicit (α := α)) wasmStep
  have parts := Config.mk.inj hconfig
  have hexpr := parts.1
  have hstore := parts.2
  simp only at hexpr hstore
  subst e₂
  subst store₂
  simp only [List.length_nil, Nat.add_zero, Iris.Algebra.BigOpL.bigOpL_nil]
  simp only [resumeCaller]
  imod Hclose
  imodintro
  isplitl [Hσ]
  · iexact Hσ
  isplitl [Hwp]
  · iexact Hwp
  · itrivial

/-- Primitive rule for `global.get`. Authoritative global ownership connects
the logical value to the instantiated global read by the machine, and the
read-only instruction returns that ownership unchanged. -/
theorem wp_globalGet_of_canonical
    {params localValues values : List Value}
    {index : Nat} {value : Value} {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame}
    (hcanonical : ∀ store : MachineStore α,
      canonicalGlobalIndex store index = index) :
    let current : ThreadState α :=
      ⟨⟨params, localValues, values⟩, .globalGet index :: code,
        arity, remainder, controls, calls⟩
    let next : ThreadState α :=
      ⟨⟨params, localValues, value :: values⟩, code,
        arity, remainder, controls, calls⟩
    ▷ globalPointsTo index value -∗
    ▷ (globalPointsTo index value -∗
      WP (Expr.running next : Expr α) @ s; E {{ Φ }}) -∗
      WP (Expr.running current : Expr α) @ s; E {{ Φ }} := by
  dsimp only
  iintro >Hglobal Hwp
  iapply wp_lift_step rfl
  iintro %store %ns %obs %obs' %nt Hσ
  ihave %Hget :
      ⌜store.wasm.globals.globals[index]? = some value⌝ $$ [Hσ Hglobal]
  · imod stateInterp_global_facts store ns (obs ++ obs') nt index value $$
        [$Hσ $Hglobal] with %Hget
    ipureintro
    exact Hget
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro
    cases s <;> simp only [Stuckness.MaybeReducible]
    exact ⟨[.instruction (.globalGet index)],
      .running ⟨⟨params, localValues, value :: values⟩,
        code, arity, remainder, controls, calls⟩,
      store, [], ⟨rfl, _, rfl, Step.globalGet (by
        simpa [globalAt?, hcanonical] using Hget)⟩⟩
  iintro !> %e₂ %store₂ %forks %Hstep Hcredit
  rcases Hstep with ⟨hforks, kind, hobs, wasmStep⟩
  change forks = [] at hforks
  subst forks
  subst obs
  obtain ⟨rfl, hconfig⟩ :=
    step_deterministic (Step.globalGet (α := α) (by
      simpa [globalAt?, hcanonical] using Hget)) wasmStep
  have parts := Config.mk.inj hconfig
  have hexpr := parts.1
  have hstore := parts.2
  simp only at hexpr hstore
  subst e₂
  subst store₂
  simp only [List.length_nil, Nat.add_zero, Iris.Algebra.BigOpL.bigOpL_nil]
  imod Hclose
  imodintro
  isplitl [Hσ]
  · iexact Hσ
  isplitl [Hwp Hglobal]
  · iapply Hwp
    iexact Hglobal
  · itrivial

/-- Primitive rule for `global.set`. Exclusive authoritative ownership is
updated together with the physical instantiated global in `StateInterp`. -/
theorem wp_globalSet_of_canonical
    {params localValues values : List Value}
    {index : Nat} {oldValue newValue : Value}
    {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame}
    (hcanonical : ∀ store : MachineStore α,
      canonicalGlobalIndex store index = index) :
    let current : ThreadState α :=
      ⟨⟨params, localValues, newValue :: values⟩,
        .globalSet index :: code, arity, remainder, controls, calls⟩
    let next : ThreadState α :=
      ⟨⟨params, localValues, values⟩,
        code, arity, remainder, controls, calls⟩
    ▷ globalPointsTo index oldValue -∗
    ▷ (globalPointsTo index newValue -∗
      WP (Expr.running next : Expr α) @ s; E {{ Φ }}) -∗
      WP (Expr.running current : Expr α) @ s; E {{ Φ }} := by
  dsimp only
  iintro >Hglobal Hwp
  iapply wp_lift_step rfl
  iintro %store %ns %obs %obs' %nt Hσ
  ihave %Hget :
      ⌜store.wasm.globals.globals[index]? = some oldValue⌝ $$
      [Hσ Hglobal]
  · imod stateInterp_global_facts store ns (obs ++ obs') nt
        index oldValue $$ [$Hσ $Hglobal] with %Hget
    ipureintro
    exact Hget
  have hsome :
      (globalAt? store index).isSome = true := by
    simp [globalAt?, hcanonical, Hget]
  let updatedStore : MachineStore α :=
    { store with wasm :=
        { store.wasm with globals :=
            { globals := store.wasm.globals.globals.set index newValue } } }
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro
    cases s <;> simp only [Stuckness.MaybeReducible]
    exact ⟨[.instruction (.globalSet index)],
      .running ⟨⟨params, localValues, values⟩,
        code, arity, remainder, controls, calls⟩,
      updatedStore, [], ⟨rfl, _, rfl, by
        dsimp [updatedStore]
        rw [← setGlobal_eq_of_canonical store index newValue
          (hcanonical store)]
        exact Step.globalSet hsome⟩⟩
  iintro !> %e₂ %store₂ %forks %Hstep Hcredit
  rcases Hstep with ⟨hforks, kind, hobs, wasmStep⟩
  change forks = [] at hforks
  subst forks
  subst obs
  have expectedStep : Step
      ⟨.running
        ⟨⟨params, localValues, newValue :: values⟩,
          .globalSet index :: code, arity, remainder, controls, calls⟩,
        store⟩
      (.instruction (.globalSet index))
      ⟨.running
        ⟨⟨params, localValues, values⟩,
          code, arity, remainder, controls, calls⟩,
        updatedStore⟩ :=
    by
      dsimp [updatedStore]
      rw [← setGlobal_eq_of_canonical store index newValue
        (hcanonical store)]
      exact Step.globalSet hsome
  obtain ⟨rfl, hconfig⟩ := step_deterministic expectedStep wasmStep
  have parts := Config.mk.inj hconfig
  have hexpr := parts.1
  have hstore := parts.2
  simp only at hexpr hstore
  subst e₂
  subst store₂
  simp only [List.length_nil, Nat.add_zero,
    Iris.Algebra.BigOpL.bigOpL_nil]
  imod stateInterp_global_set store ns
      ([.instruction (.globalSet index)] ++ obs') nt
      index oldValue newValue $$ [$Hσ $Hglobal] with ⟨Hσ, Hglobal⟩
  imod Hclose
  imodintro
  isplitl [Hσ]
  · iexact Hσ
  isplitl [Hwp Hglobal]
  · iapply Hwp
    iexact Hglobal
  · itrivial

/-- Common non-aliased rule for the distinguished global at index zero.
Index zero is definitionally canonical even when other local indices alias
the same instantiated global. -/
theorem wp_globalGet
    {params localValues values : List Value}
    {value : Value} {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame} :
    let current : ThreadState α :=
      ⟨⟨params, localValues, values⟩, .globalGet 0 :: code,
        arity, remainder, controls, calls⟩
    let next : ThreadState α :=
      ⟨⟨params, localValues, value :: values⟩, code,
        arity, remainder, controls, calls⟩
    ▷ globalPointsTo 0 value -∗
    ▷ (globalPointsTo 0 value -∗
      WP (Expr.running next : Expr α) @ s; E {{ Φ }}) -∗
      WP (Expr.running current : Expr α) @ s; E {{ Φ }} :=
  wp_globalGet_of_canonical (fun _ => rfl)

theorem wp_globalSet
    {params localValues values : List Value}
    {oldValue newValue : Value}
    {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame} :
    let current : ThreadState α :=
      ⟨⟨params, localValues, newValue :: values⟩,
        .globalSet 0 :: code, arity, remainder, controls, calls⟩
    let next : ThreadState α :=
      ⟨⟨params, localValues, values⟩,
        code, arity, remainder, controls, calls⟩
    ▷ globalPointsTo 0 oldValue -∗
    ▷ (globalPointsTo 0 newValue -∗
      WP (Expr.running next : Expr α) @ s; E {{ Φ }}) -∗
      WP (Expr.running current : Expr α) @ s; E {{ Φ }} :=
  wp_globalSet_of_canonical (fun _ => rfl)

/-- Primitive rule for an in-bounds `table.get`. The owned table fragment
identifies the physical table and is returned unchanged after the read. -/
theorem wp_tableGet
    {params localValues values : List Value}
    {tableIndex elementIndex : Nat} {index value : Value}
    {table : TableInst} {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame}
    (hindex : index.addrNat? = some elementIndex)
    (helement : table[elementIndex]? = some value) :
    let current : ThreadState α :=
      ⟨⟨params, localValues, index :: values⟩,
        .tableGet tableIndex :: code, arity, remainder, controls, calls⟩
    let next : ThreadState α :=
      ⟨⟨params, localValues, value :: values⟩,
        code, arity, remainder, controls, calls⟩
    ▷ tablePointsTo tableIndex table -∗
    ▷ (tablePointsTo tableIndex table -∗
      WP (Expr.running next : Expr α) @ s; E {{ Φ }}) -∗
      WP (Expr.running current : Expr α) @ s; E {{ Φ }} := by
  dsimp only
  iintro >Htable Hwp
  iapply wp_lift_step rfl
  iintro %store %ns %obs %obs' %nt Hσ
  ihave %Hphysical :
      ⌜store.wasm.tables[tableIndex]? = some table⌝ $$ [Hσ Htable]
  · imod stateInterp_table_facts_frame store ns (obs ++ obs') nt
        tableIndex table $$ [$Hσ $Htable] with
      ⟨Hσ, Htable, %Hphysical⟩
    ipureintro
    exact Hphysical
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro
    cases s <;> simp only [Stuckness.MaybeReducible]
    exact ⟨[.instruction (.tableGet tableIndex)],
      .running ⟨⟨params, localValues, value :: values⟩,
        code, arity, remainder, controls, calls⟩,
      store, [],
      ⟨rfl, _, rfl, Step.tableGet hindex Hphysical helement⟩⟩
  iintro !> %e₂ %store₂ %forks %Hstep Hcredit
  rcases Hstep with ⟨hforks, kind, hobs, wasmStep⟩
  change forks = [] at hforks
  subst forks
  subst obs
  obtain ⟨rfl, hconfig⟩ :=
    step_deterministic
      (Step.tableGet (α := α) hindex Hphysical helement) wasmStep
  have parts := Config.mk.inj hconfig
  have hexpr := parts.1
  have hstore := parts.2
  simp only at hexpr hstore
  subst e₂
  subst store₂
  simp only [List.length_nil, Nat.add_zero,
    Iris.Algebra.BigOpL.bigOpL_nil]
  imod Hclose
  imodintro
  isplitl [Hσ]
  · iexact Hσ
  isplitl [Hwp Htable]
  · iapply Hwp
    iexact Htable
  · itrivial

/-- Primitive rule for `table.size`. Runtime-module ownership determines
whether the result is represented as an `i32` or `i64`; table ownership
determines the physical length. Both resources are read-only. -/
theorem wp_tableSize
    (runtimeModule : Module)
    {params localValues values : List Value}
    {tableIndex : Nat} {table : TableInst}
    {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame} :
    let current : ThreadState α :=
      ⟨⟨params, localValues, values⟩,
        .tableSize tableIndex :: code, arity, remainder, controls, calls⟩
    let next : ThreadState α :=
      ⟨⟨params, localValues,
          sizeValue (runtimeModule.tableIs64 tableIndex) table.length ::
            values⟩,
        code, arity, remainder, controls, calls⟩
    (tablePointsTo tableIndex table ∗
      runtimeModuleOwn runtimeModule) -∗
    ▷ (tablePointsTo tableIndex table -∗
      runtimeModuleOwn runtimeModule -∗
      WP (Expr.running next : Expr α) @ s; E {{ Φ }}) -∗
      WP (Expr.running current : Expr α) @ s; E {{ Φ }} := by
  dsimp only
  iintro ⟨Htable, Hruntime⟩ Hwp
  iapply wp_lift_step rfl
  iintro %store %ns %obs %obs' %nt Hσ
  ihave %Hphysical :
      ⌜store.wasm.tables[tableIndex]? = some table⌝ $$ [Hσ Htable]
  · imod stateInterp_table_facts_frame store ns (obs ++ obs') nt
        tableIndex table $$ [$Hσ $Htable] with
      ⟨Hσ, Htable, %Hphysical⟩
    ipureintro
    exact Hphysical
  ihave %Hmodule : ⌜store.runtime.module = runtimeModule⌝ $$
      [Hσ Hruntime]
  · imod stateInterp_runtimeModule_agree store ns (obs ++ obs') nt
        runtimeModule $$ [$Hσ $Hruntime] with %Hmodule
    ipureintro
    exact Hmodule
  subst runtimeModule
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro
    cases s <;> simp only [Stuckness.MaybeReducible]
    exact ⟨[.instruction (.tableSize tableIndex)],
      .running ⟨⟨params, localValues,
          sizeValue (store.runtime.module.tableIs64 tableIndex) table.length ::
            values⟩,
        code, arity, remainder, controls, calls⟩,
      store, [], ⟨rfl, _, rfl, Step.tableSize Hphysical⟩⟩
  iintro !> %e₂ %store₂ %forks %Hstep Hcredit
  rcases Hstep with ⟨hforks, kind, hobs, wasmStep⟩
  change forks = [] at hforks
  subst forks
  subst obs
  have expectedStep : Step
      ⟨.running
        ⟨⟨params, localValues, values⟩,
          .tableSize tableIndex :: code, arity, remainder, controls, calls⟩,
        store⟩
      (.instruction (.tableSize tableIndex))
      ⟨.running
        ⟨⟨params, localValues,
            sizeValue (store.runtime.module.tableIs64 tableIndex)
              table.length :: values⟩,
          code, arity, remainder, controls, calls⟩,
        store⟩ :=
    Step.tableSize Hphysical
  obtain ⟨rfl, hconfig⟩ := step_deterministic expectedStep wasmStep
  have parts := Config.mk.inj hconfig
  have hexpr := parts.1
  have hstore := parts.2
  simp only at hexpr hstore
  subst e₂
  subst store₂
  simp only [List.length_nil, Nat.add_zero,
    Iris.Algebra.BigOpL.bigOpL_nil]
  imod Hclose
  imodintro
  isplitl [Hσ]
  · iexact Hσ
  isplitl [Hwp Htable Hruntime]
  · iapply Hwp $$ Htable Hruntime
  · itrivial

/-- Primitive rule for an in-bounds `table.set`. The table keeps its stable
identity while its complete owned contents and physical instance update
together. -/
theorem wp_tableSet
    {params localValues values : List Value}
    {tableIndex elementIndex : Nat} {index value : Value}
    {table : TableInst} {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame}
    (hindex : index.addrNat? = some elementIndex)
    (hbound : elementIndex < table.length) :
    let newTable := listSetAt table elementIndex value
    let current : ThreadState α :=
      ⟨⟨params, localValues, value :: index :: values⟩,
        .tableSet tableIndex :: code, arity, remainder, controls, calls⟩
    let next : ThreadState α :=
      ⟨⟨params, localValues, values⟩,
        code, arity, remainder, controls, calls⟩
    ▷ tablePointsTo tableIndex table -∗
    ▷ (tablePointsTo tableIndex newTable -∗
      WP (Expr.running next : Expr α) @ s; E {{ Φ }}) -∗
      WP (Expr.running current : Expr α) @ s; E {{ Φ }} := by
  dsimp only
  iintro >Htable Hwp
  iapply wp_lift_step rfl
  iintro %store %ns %obs %obs' %nt Hσ
  ihave %Hphysical :
      ⌜store.wasm.tables[tableIndex]? = some table⌝ $$ [Hσ Htable]
  · imod stateInterp_table_facts_frame store ns (obs ++ obs') nt
        tableIndex table $$ [$Hσ $Htable] with
      ⟨Hσ, Htable, %Hphysical⟩
    ipureintro
    exact Hphysical
  let newTable := listSetAt table elementIndex value
  let updatedStore : MachineStore α :=
    { store with wasm :=
        { store.wasm with tables :=
            (listSetAt store.wasm.tables tableIndex newTable) } }
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro
    cases s <;> simp only [Stuckness.MaybeReducible]
    exact ⟨[.instruction (.tableSet tableIndex)],
      .running ⟨⟨params, localValues, values⟩,
        code, arity, remainder, controls, calls⟩,
      updatedStore, [],
      ⟨rfl, _, rfl, Step.tableSet hindex Hphysical hbound⟩⟩
  iintro !> %e₂ %store₂ %forks %Hstep Hcredit
  rcases Hstep with ⟨hforks, kind, hobs, wasmStep⟩
  change forks = [] at hforks
  subst forks
  subst obs
  have expectedStep : Step
      ⟨.running
        ⟨⟨params, localValues, value :: index :: values⟩,
          .tableSet tableIndex :: code, arity, remainder, controls, calls⟩,
        store⟩
      (.instruction (.tableSet tableIndex))
      ⟨.running
        ⟨⟨params, localValues, values⟩,
          code, arity, remainder, controls, calls⟩,
        updatedStore⟩ :=
    Step.tableSet hindex Hphysical hbound
  obtain ⟨rfl, hconfig⟩ := step_deterministic expectedStep wasmStep
  have parts := Config.mk.inj hconfig
  have hexpr := parts.1
  have hstore := parts.2
  simp only at hexpr hstore
  subst e₂
  subst store₂
  simp only [List.length_nil, Nat.add_zero,
    Iris.Algebra.BigOpL.bigOpL_nil]
  imod stateInterp_table_set store ns
      ([.instruction (.tableSet tableIndex)] ++ obs') nt
      tableIndex table newTable $$ [$Hσ $Htable] with ⟨Hσ, Htable⟩
  imod Hclose
  imodintro
  isplitl [Hσ]
  · iexact Hσ
  isplitl [Hwp Htable]
  · iapply Hwp
    iexact Htable
  · itrivial

/-- Successful 32-bit `table.grow`. Stable table identity is preserved while
the physical table and its authoritative contents are extended together. -/
theorem wp_tableGrow32
    (runtimeModule : Module)
    {params localValues values : List Value}
    {tableIndex : Nat} {table : TableInst}
    {delta : UInt32} {initial : Value}
    {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame}
    (hbound :
      table.length + delta.toNat ≤ runtimeModule.tableCap tableIndex) :
    let newTable := table ++ List.replicate delta.toNat initial
    let current : ThreadState α :=
      ⟨⟨params, localValues, .i32 delta :: initial :: values⟩,
        .tableGrow tableIndex :: code, arity, remainder, controls, calls⟩
    let next : ThreadState α :=
      ⟨⟨params, localValues, .i32 table.length.toUInt32 :: values⟩,
        code, arity, remainder, controls, calls⟩
    (tablePointsTo tableIndex table ∗
      runtimeModuleOwn runtimeModule) -∗
    ▷ (tablePointsTo tableIndex newTable -∗
      runtimeModuleOwn runtimeModule -∗
      WP (Expr.running next : Expr α) @ s; E {{ Φ }}) -∗
      WP (Expr.running current : Expr α) @ s; E {{ Φ }} := by
  dsimp only
  iintro ⟨Htable, Hruntime⟩ Hwp
  iapply wp_lift_step rfl
  iintro %store %ns %obs %obs' %nt Hσ
  ihave %Hphysical :
      ⌜store.wasm.tables[tableIndex]? = some table⌝ $$ [Hσ Htable]
  · imod stateInterp_table_facts_frame store ns (obs ++ obs') nt
        tableIndex table $$ [$Hσ $Htable] with
      ⟨Hσ, Htable, %Hphysical⟩
    ipureintro
    exact Hphysical
  ihave %Hmodule : ⌜store.runtime.module = runtimeModule⌝ $$
      [Hσ Hruntime]
  · imod stateInterp_runtimeModule_agree store ns (obs ++ obs') nt
        runtimeModule $$ [$Hσ $Hruntime] with %Hmodule
    ipureintro
    exact Hmodule
  have hbound' :
      table.length + delta.toNat ≤
        store.runtime.module.tableCap tableIndex := by
    simpa only [Hmodule] using hbound
  let newTable := table ++ List.replicate delta.toNat initial
  let updatedStore : MachineStore α :=
    { store with wasm :=
        { store.wasm with tables :=
            (listSetAt store.wasm.tables tableIndex newTable) } }
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro
    cases s <;> simp only [Stuckness.MaybeReducible]
    exact ⟨[.instruction (.tableGrow tableIndex)],
      .running
        ⟨⟨params, localValues, .i32 table.length.toUInt32 :: values⟩,
          code, arity, remainder, controls, calls⟩,
      updatedStore, [],
      ⟨rfl, _, rfl, Step.tableGrow32 Hphysical hbound'⟩⟩
  iintro !> %e₂ %store₂ %forks %Hstep Hcredit
  rcases Hstep with ⟨hforks, kind, hobs, wasmStep⟩
  change forks = [] at hforks
  subst forks
  subst obs
  have expectedStep : Step
      ⟨.running
        ⟨⟨params, localValues, .i32 delta :: initial :: values⟩,
          .tableGrow tableIndex :: code, arity, remainder, controls, calls⟩,
        store⟩
      (.instruction (.tableGrow tableIndex))
      ⟨.running
        ⟨⟨params, localValues, .i32 table.length.toUInt32 :: values⟩,
          code, arity, remainder, controls, calls⟩,
        updatedStore⟩ :=
    Step.tableGrow32 Hphysical hbound'
  obtain ⟨rfl, hconfig⟩ := step_deterministic expectedStep wasmStep
  have parts := Config.mk.inj hconfig
  have hexpr := parts.1
  have hstore := parts.2
  simp only at hexpr hstore
  subst e₂
  subst store₂
  simp only [List.length_nil, Nat.add_zero,
    Iris.Algebra.BigOpL.bigOpL_nil]
  imod stateInterp_table_set store ns
      ([.instruction (.tableGrow tableIndex)] ++ obs') nt
      tableIndex table newTable $$ [$Hσ $Htable] with ⟨Hσ, Htable⟩
  imod Hclose
  imodintro
  isplitl [Hσ]
  · iexact Hσ
  isplitl [Hwp Htable Hruntime]
  · iapply Hwp $$ Htable Hruntime
  · itrivial

/-- Successful 64-bit `table.grow`. This is the table64 counterpart of
`wp_tableGrow32`; it updates the same stable authoritative table identity. -/
theorem wp_tableGrow64
    (runtimeModule : Module)
    {params localValues values : List Value}
    {tableIndex : Nat} {table : TableInst}
    {delta : UInt64} {initial : Value}
    {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame}
    (hbound :
      table.length + delta.toNat ≤ runtimeModule.tableCap tableIndex) :
    let newTable := table ++ List.replicate delta.toNat initial
    let current : ThreadState α :=
      ⟨⟨params, localValues, .i64 delta :: initial :: values⟩,
        .tableGrow tableIndex :: code, arity, remainder, controls, calls⟩
    let next : ThreadState α :=
      ⟨⟨params, localValues, .i64 table.length.toUInt64 :: values⟩,
        code, arity, remainder, controls, calls⟩
    (tablePointsTo tableIndex table ∗
      runtimeModuleOwn runtimeModule) -∗
    ▷ (tablePointsTo tableIndex newTable -∗
      runtimeModuleOwn runtimeModule -∗
      WP (Expr.running next : Expr α) @ s; E {{ Φ }}) -∗
      WP (Expr.running current : Expr α) @ s; E {{ Φ }} := by
  dsimp only
  iintro ⟨Htable, Hruntime⟩ Hwp
  iapply wp_lift_step rfl
  iintro %store %ns %obs %obs' %nt Hσ
  ihave %Hphysical :
      ⌜store.wasm.tables[tableIndex]? = some table⌝ $$ [Hσ Htable]
  · imod stateInterp_table_facts_frame store ns (obs ++ obs') nt
        tableIndex table $$ [$Hσ $Htable] with
      ⟨Hσ, Htable, %Hphysical⟩
    ipureintro
    exact Hphysical
  ihave %Hmodule : ⌜store.runtime.module = runtimeModule⌝ $$
      [Hσ Hruntime]
  · imod stateInterp_runtimeModule_agree store ns (obs ++ obs') nt
        runtimeModule $$ [$Hσ $Hruntime] with %Hmodule
    ipureintro
    exact Hmodule
  have hbound' :
      table.length + delta.toNat ≤
        store.runtime.module.tableCap tableIndex := by
    simpa only [Hmodule] using hbound
  let newTable := table ++ List.replicate delta.toNat initial
  let updatedStore : MachineStore α :=
    { store with wasm :=
        { store.wasm with tables :=
            (listSetAt store.wasm.tables tableIndex newTable) } }
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro
    cases s <;> simp only [Stuckness.MaybeReducible]
    exact ⟨[.instruction (.tableGrow tableIndex)],
      .running
        ⟨⟨params, localValues, .i64 table.length.toUInt64 :: values⟩,
          code, arity, remainder, controls, calls⟩,
      updatedStore, [],
      ⟨rfl, _, rfl, Step.tableGrow64 Hphysical hbound'⟩⟩
  iintro !> %e₂ %store₂ %forks %Hstep Hcredit
  rcases Hstep with ⟨hforks, kind, hobs, wasmStep⟩
  change forks = [] at hforks
  subst forks
  subst obs
  have expectedStep : Step
      ⟨.running
        ⟨⟨params, localValues, .i64 delta :: initial :: values⟩,
          .tableGrow tableIndex :: code, arity, remainder, controls, calls⟩,
        store⟩
      (.instruction (.tableGrow tableIndex))
      ⟨.running
        ⟨⟨params, localValues, .i64 table.length.toUInt64 :: values⟩,
          code, arity, remainder, controls, calls⟩,
        updatedStore⟩ :=
    Step.tableGrow64 Hphysical hbound'
  obtain ⟨rfl, hconfig⟩ := step_deterministic expectedStep wasmStep
  have parts := Config.mk.inj hconfig
  have hexpr := parts.1
  have hstore := parts.2
  simp only at hexpr hstore
  subst e₂
  subst store₂
  simp only [List.length_nil, Nat.add_zero,
    Iris.Algebra.BigOpL.bigOpL_nil]
  imod stateInterp_table_set store ns
      ([.instruction (.tableGrow tableIndex)] ++ obs') nt
      tableIndex table newTable $$ [$Hσ $Htable] with ⟨Hσ, Htable⟩
  imod Hclose
  imodintro
  isplitl [Hσ]
  · iexact Hσ
  isplitl [Hwp Htable Hruntime]
  · iapply Hwp $$ Htable Hruntime
  · itrivial

/-- Failed 32-bit `table.grow`. Capacity failure is an ordinary successful
instruction result (`-1`), not a trap, and leaves the authoritative table and
physical store unchanged. -/
theorem wp_tableGrow32Failure
    (runtimeModule : Module)
    {params localValues values : List Value}
    {tableIndex : Nat} {table : TableInst}
    {delta : UInt32} {initial : Value}
    {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame}
    (hbound :
      ¬table.length + delta.toNat ≤ runtimeModule.tableCap tableIndex) :
    let current : ThreadState α :=
      ⟨⟨params, localValues, .i32 delta :: initial :: values⟩,
        .tableGrow tableIndex :: code, arity, remainder, controls, calls⟩
    let next : ThreadState α :=
      ⟨⟨params, localValues, .i32 (0xFFFFFFFF : UInt32) :: values⟩,
        code, arity, remainder, controls, calls⟩
    (tablePointsTo tableIndex table ∗
      runtimeModuleOwn runtimeModule) -∗
    ▷ (tablePointsTo tableIndex table -∗
      runtimeModuleOwn runtimeModule -∗
      WP (Expr.running next : Expr α) @ s; E {{ Φ }}) -∗
      WP (Expr.running current : Expr α) @ s; E {{ Φ }} := by
  dsimp only
  iintro ⟨Htable, Hruntime⟩ Hwp
  iapply wp_lift_step rfl
  iintro %store %ns %obs %obs' %nt Hσ
  ihave %Hphysical :
      ⌜store.wasm.tables[tableIndex]? = some table⌝ $$ [Hσ Htable]
  · imod stateInterp_table_facts_frame store ns (obs ++ obs') nt
        tableIndex table $$ [$Hσ $Htable] with
      ⟨Hσ, Htable, %Hphysical⟩
    ipureintro
    exact Hphysical
  ihave %Hmodule : ⌜store.runtime.module = runtimeModule⌝ $$
      [Hσ Hruntime]
  · imod stateInterp_runtimeModule_agree store ns (obs ++ obs') nt
        runtimeModule $$ [$Hσ $Hruntime] with %Hmodule
    ipureintro
    exact Hmodule
  have hbound' :
      ¬table.length + delta.toNat ≤
        store.runtime.module.tableCap tableIndex := by
    simpa only [Hmodule] using hbound
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro
    cases s <;> simp only [Stuckness.MaybeReducible]
    exact ⟨[.instruction (.tableGrow tableIndex)],
      .running
        ⟨⟨params, localValues,
            .i32 (0xFFFFFFFF : UInt32) :: values⟩,
          code, arity, remainder, controls, calls⟩,
      store, [],
      ⟨rfl, _, rfl, Step.tableGrow32Failure Hphysical hbound'⟩⟩
  iintro !> %e₂ %store₂ %forks %Hstep Hcredit
  rcases Hstep with ⟨hforks, kind, hobs, wasmStep⟩
  change forks = [] at hforks
  subst forks
  subst obs
  have expectedStep : Step
      ⟨.running
        ⟨⟨params, localValues, .i32 delta :: initial :: values⟩,
          .tableGrow tableIndex :: code, arity, remainder, controls, calls⟩,
        store⟩
      (.instruction (.tableGrow tableIndex))
      ⟨.running
        ⟨⟨params, localValues,
            .i32 (0xFFFFFFFF : UInt32) :: values⟩,
          code, arity, remainder, controls, calls⟩,
        store⟩ :=
    Step.tableGrow32Failure Hphysical hbound'
  obtain ⟨rfl, hconfig⟩ := step_deterministic expectedStep wasmStep
  have parts := Config.mk.inj hconfig
  have hexpr := parts.1
  have hstore := parts.2
  simp only at hexpr hstore
  subst e₂
  subst store₂
  simp only [List.length_nil, Nat.add_zero,
    Iris.Algebra.BigOpL.bigOpL_nil]
  imod Hclose
  imodintro
  isplitl [Hσ]
  · iexact Hσ
  isplitl [Hwp Htable Hruntime]
  · iapply Hwp $$ Htable Hruntime
  · itrivial

/-- Failed table64 `table.grow`; returns the 64-bit all-ones sentinel and
preserves complete ownership of the unchanged table. -/
theorem wp_tableGrow64Failure
    (runtimeModule : Module)
    {params localValues values : List Value}
    {tableIndex : Nat} {table : TableInst}
    {delta : UInt64} {initial : Value}
    {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame}
    (hbound :
      ¬table.length + delta.toNat ≤ runtimeModule.tableCap tableIndex) :
    let current : ThreadState α :=
      ⟨⟨params, localValues, .i64 delta :: initial :: values⟩,
        .tableGrow tableIndex :: code, arity, remainder, controls, calls⟩
    let next : ThreadState α :=
      ⟨⟨params, localValues,
          .i64 (0xFFFFFFFFFFFFFFFF : UInt64) :: values⟩,
        code, arity, remainder, controls, calls⟩
    (tablePointsTo tableIndex table ∗
      runtimeModuleOwn runtimeModule) -∗
    ▷ (tablePointsTo tableIndex table -∗
      runtimeModuleOwn runtimeModule -∗
      WP (Expr.running next : Expr α) @ s; E {{ Φ }}) -∗
      WP (Expr.running current : Expr α) @ s; E {{ Φ }} := by
  dsimp only
  iintro ⟨Htable, Hruntime⟩ Hwp
  iapply wp_lift_step rfl
  iintro %store %ns %obs %obs' %nt Hσ
  ihave %Hphysical :
      ⌜store.wasm.tables[tableIndex]? = some table⌝ $$ [Hσ Htable]
  · imod stateInterp_table_facts_frame store ns (obs ++ obs') nt
        tableIndex table $$ [$Hσ $Htable] with
      ⟨Hσ, Htable, %Hphysical⟩
    ipureintro
    exact Hphysical
  ihave %Hmodule : ⌜store.runtime.module = runtimeModule⌝ $$
      [Hσ Hruntime]
  · imod stateInterp_runtimeModule_agree store ns (obs ++ obs') nt
        runtimeModule $$ [$Hσ $Hruntime] with %Hmodule
    ipureintro
    exact Hmodule
  have hbound' :
      ¬table.length + delta.toNat ≤
        store.runtime.module.tableCap tableIndex := by
    simpa only [Hmodule] using hbound
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro
    cases s <;> simp only [Stuckness.MaybeReducible]
    exact ⟨[.instruction (.tableGrow tableIndex)],
      .running
        ⟨⟨params, localValues,
            .i64 (0xFFFFFFFFFFFFFFFF : UInt64) :: values⟩,
          code, arity, remainder, controls, calls⟩,
      store, [],
      ⟨rfl, _, rfl, Step.tableGrow64Failure Hphysical hbound'⟩⟩
  iintro !> %e₂ %store₂ %forks %Hstep Hcredit
  rcases Hstep with ⟨hforks, kind, hobs, wasmStep⟩
  change forks = [] at hforks
  subst forks
  subst obs
  have expectedStep : Step
      ⟨.running
        ⟨⟨params, localValues, .i64 delta :: initial :: values⟩,
          .tableGrow tableIndex :: code, arity, remainder, controls, calls⟩,
        store⟩
      (.instruction (.tableGrow tableIndex))
      ⟨.running
        ⟨⟨params, localValues,
            .i64 (0xFFFFFFFFFFFFFFFF : UInt64) :: values⟩,
          code, arity, remainder, controls, calls⟩,
        store⟩ :=
    Step.tableGrow64Failure Hphysical hbound'
  obtain ⟨rfl, hconfig⟩ := step_deterministic expectedStep wasmStep
  have parts := Config.mk.inj hconfig
  have hexpr := parts.1
  have hstore := parts.2
  simp only at hexpr hstore
  subst e₂
  subst store₂
  simp only [List.length_nil, Nat.add_zero,
    Iris.Algebra.BigOpL.bigOpL_nil]
  imod Hclose
  imodintro
  isplitl [Hσ]
  · iexact Hσ
  isplitl [Hwp Htable Hruntime]
  · iapply Hwp $$ Htable Hruntime
  · itrivial

/-- In-bounds `table.fill`. The complete authoritative table fragment is
updated to the same `listWriteAt` result as the physical machine table. -/
theorem wp_tableFill
    {params localValues values : List Value}
    {tableIndex destinationNat lengthNat : Nat}
    {destination length value : Value}
    {table : TableInst} {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame}
    (hlength : length.addrNat? = some lengthNat)
    (hdestination : destination.addrNat? = some destinationNat)
    (hbound : destinationNat + lengthNat ≤ table.length) :
    let newTable :=
      listWriteAt table destinationNat (List.replicate lengthNat value)
    let current : ThreadState α :=
      ⟨⟨params, localValues, length :: value :: destination :: values⟩,
        .tableFill tableIndex :: code, arity, remainder, controls, calls⟩
    let next : ThreadState α :=
      ⟨⟨params, localValues, values⟩,
        code, arity, remainder, controls, calls⟩
    ▷ tablePointsTo tableIndex table -∗
    ▷ (tablePointsTo tableIndex newTable -∗
      WP (Expr.running next : Expr α) @ s; E {{ Φ }}) -∗
      WP (Expr.running current : Expr α) @ s; E {{ Φ }} := by
  dsimp only
  iintro >Htable Hwp
  iapply wp_lift_step rfl
  iintro %store %ns %obs %obs' %nt Hσ
  ihave %Hphysical :
      ⌜store.wasm.tables[tableIndex]? = some table⌝ $$ [Hσ Htable]
  · imod stateInterp_table_facts_frame store ns (obs ++ obs') nt
        tableIndex table $$ [$Hσ $Htable] with
      ⟨Hσ, Htable, %Hphysical⟩
    ipureintro
    exact Hphysical
  let newTable :=
    listWriteAt table destinationNat (List.replicate lengthNat value)
  let updatedStore : MachineStore α :=
    { store with wasm :=
        { store.wasm with tables :=
            (listSetAt store.wasm.tables tableIndex newTable) } }
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro
    cases s <;> simp only [Stuckness.MaybeReducible]
    exact ⟨[.instruction (.tableFill tableIndex)],
      .running ⟨⟨params, localValues, values⟩,
        code, arity, remainder, controls, calls⟩,
      updatedStore, [],
      ⟨rfl, _, rfl,
        Step.tableFill hlength hdestination Hphysical hbound⟩⟩
  iintro !> %e₂ %store₂ %forks %Hstep Hcredit
  rcases Hstep with ⟨hforks, kind, hobs, wasmStep⟩
  change forks = [] at hforks
  subst forks
  subst obs
  have expectedStep : Step
      ⟨.running
        ⟨⟨params, localValues, length :: value :: destination :: values⟩,
          .tableFill tableIndex :: code, arity, remainder, controls, calls⟩,
        store⟩
      (.instruction (.tableFill tableIndex))
      ⟨.running
        ⟨⟨params, localValues, values⟩,
          code, arity, remainder, controls, calls⟩,
        updatedStore⟩ :=
    Step.tableFill hlength hdestination Hphysical hbound
  obtain ⟨rfl, hconfig⟩ := step_deterministic expectedStep wasmStep
  have parts := Config.mk.inj hconfig
  have hexpr := parts.1
  have hstore := parts.2
  simp only at hexpr hstore
  subst e₂
  subst store₂
  simp only [List.length_nil, Nat.add_zero,
    Iris.Algebra.BigOpL.bigOpL_nil]
  imod stateInterp_table_set store ns
      ([.instruction (.tableFill tableIndex)] ++ obs') nt
      tableIndex table newTable $$ [$Hσ $Htable] with ⟨Hσ, Htable⟩
  imod Hclose
  imodintro
  isplitl [Hσ]
  · iexact Hσ
  isplitl [Hwp Htable]
  · iapply Hwp
    iexact Htable
  · itrivial

/-- In-bounds copy within one table, including overlapping ranges. The source
slice is taken from the pre-step table before the authoritative table is
updated, matching Wasm's memmove-style `table.copy` semantics. -/
theorem wp_tableCopySame
    {params localValues values : List Value}
    {tableIndex destinationNat sourceNat lengthNat : Nat}
    {destination source length : Value}
    {table : TableInst} {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame}
    (hlength : length.addrNat? = some lengthNat)
    (hsource : source.addrNat? = some sourceNat)
    (hdestination : destination.addrNat? = some destinationNat)
    (hdestinationBound : destinationNat + lengthNat ≤ table.length)
    (hsourceBound : sourceNat + lengthNat ≤ table.length) :
    let newTable :=
      listWriteAt table destinationNat
        ((table.drop sourceNat).take lengthNat)
    let current : ThreadState α :=
      ⟨⟨params, localValues, length :: source :: destination :: values⟩,
        .tableCopy tableIndex tableIndex :: code,
        arity, remainder, controls, calls⟩
    let next : ThreadState α :=
      ⟨⟨params, localValues, values⟩,
        code, arity, remainder, controls, calls⟩
    ▷ tablePointsTo tableIndex table -∗
    ▷ (tablePointsTo tableIndex newTable -∗
      WP (Expr.running next : Expr α) @ s; E {{ Φ }}) -∗
      WP (Expr.running current : Expr α) @ s; E {{ Φ }} := by
  dsimp only
  iintro >Htable Hwp
  iapply wp_lift_step rfl
  iintro %store %ns %obs %obs' %nt Hσ
  ihave %Hphysical :
      ⌜store.wasm.tables[tableIndex]? = some table⌝ $$ [Hσ Htable]
  · imod stateInterp_table_facts_frame store ns (obs ++ obs') nt
        tableIndex table $$ [$Hσ $Htable] with
      ⟨Hσ, Htable, %Hphysical⟩
    ipureintro
    exact Hphysical
  let newTable :=
    listWriteAt table destinationNat
      ((table.drop sourceNat).take lengthNat)
  let updatedStore : MachineStore α :=
    { store with wasm :=
        { store.wasm with tables :=
            (listSetAt store.wasm.tables tableIndex newTable) } }
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro
    cases s <;> simp only [Stuckness.MaybeReducible]
    exact ⟨[.instruction (.tableCopy tableIndex tableIndex)],
      .running ⟨⟨params, localValues, values⟩,
        code, arity, remainder, controls, calls⟩,
      updatedStore, [],
      ⟨rfl, _, rfl,
        Step.tableCopy hlength hsource hdestination
          Hphysical Hphysical hdestinationBound hsourceBound⟩⟩
  iintro !> %e₂ %store₂ %forks %Hstep Hcredit
  rcases Hstep with ⟨hforks, kind, hobs, wasmStep⟩
  change forks = [] at hforks
  subst forks
  subst obs
  have expectedStep : Step
      ⟨.running
        ⟨⟨params, localValues, length :: source :: destination :: values⟩,
          .tableCopy tableIndex tableIndex :: code,
          arity, remainder, controls, calls⟩,
        store⟩
      (.instruction (.tableCopy tableIndex tableIndex))
      ⟨.running
        ⟨⟨params, localValues, values⟩,
          code, arity, remainder, controls, calls⟩,
        updatedStore⟩ :=
    Step.tableCopy hlength hsource hdestination
      Hphysical Hphysical hdestinationBound hsourceBound
  obtain ⟨rfl, hconfig⟩ := step_deterministic expectedStep wasmStep
  have parts := Config.mk.inj hconfig
  have hexpr := parts.1
  have hstore := parts.2
  simp only at hexpr hstore
  subst e₂
  subst store₂
  simp only [List.length_nil, Nat.add_zero,
    Iris.Algebra.BigOpL.bigOpL_nil]
  imod stateInterp_table_set store ns
      ([.instruction (.tableCopy tableIndex tableIndex)] ++ obs') nt
      tableIndex table newTable $$ [$Hσ $Htable] with ⟨Hσ, Htable⟩
  imod Hclose
  imodintro
  isplitl [Hσ]
  · iexact Hσ
  isplitl [Hwp Htable]
  · iapply Hwp
    iexact Htable
  · itrivial

/-- In-bounds copy between two separately owned tables. The source fragment is
framed unchanged while only the destination table's authoritative contents and
physical instance are updated. -/
theorem wp_tableCopyDistinct
    {params localValues values : List Value}
    {destinationTableIndex sourceTableIndex : Nat}
    {destinationNat sourceNat lengthNat : Nat}
    {destination source length : Value}
    {destinationTable sourceTable : TableInst}
    {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame}
    (hlength : length.addrNat? = some lengthNat)
    (hsource : source.addrNat? = some sourceNat)
    (hdestination : destination.addrNat? = some destinationNat)
    (hdestinationBound :
      destinationNat + lengthNat ≤ destinationTable.length)
    (hsourceBound : sourceNat + lengthNat ≤ sourceTable.length) :
    let newDestinationTable :=
      listWriteAt destinationTable destinationNat
        ((sourceTable.drop sourceNat).take lengthNat)
    let current : ThreadState α :=
      ⟨⟨params, localValues, length :: source :: destination :: values⟩,
        .tableCopy destinationTableIndex sourceTableIndex :: code,
        arity, remainder, controls, calls⟩
    let next : ThreadState α :=
      ⟨⟨params, localValues, values⟩,
        code, arity, remainder, controls, calls⟩
    ▷ (tablePointsTo destinationTableIndex destinationTable ∗
      tablePointsTo sourceTableIndex sourceTable) -∗
    ▷ (tablePointsTo destinationTableIndex newDestinationTable -∗
      tablePointsTo sourceTableIndex sourceTable -∗
      WP (Expr.running next : Expr α) @ s; E {{ Φ }}) -∗
      WP (Expr.running current : Expr α) @ s; E {{ Φ }} := by
  dsimp only
  iintro >⟨Hdestination, Hsource⟩ Hwp
  iapply wp_lift_step rfl
  iintro %store %ns %obs %obs' %nt Hσ
  ihave %HdestinationPhysical :
      ⌜store.wasm.tables[destinationTableIndex]? =
        some destinationTable⌝ $$ [Hσ Hdestination]
  · imod stateInterp_table_facts_frame store ns (obs ++ obs') nt
        destinationTableIndex destinationTable $$
        [$Hσ $Hdestination] with
      ⟨Hσ, Hdestination, %HdestinationPhysical⟩
    ipureintro
    exact HdestinationPhysical
  ihave %HsourcePhysical :
      ⌜store.wasm.tables[sourceTableIndex]? = some sourceTable⌝ $$
      [Hσ Hsource]
  · imod stateInterp_table_facts_frame store ns (obs ++ obs') nt
        sourceTableIndex sourceTable $$ [$Hσ $Hsource] with
      ⟨Hσ, Hsource, %HsourcePhysical⟩
    ipureintro
    exact HsourcePhysical
  let newDestinationTable :=
    listWriteAt destinationTable destinationNat
      ((sourceTable.drop sourceNat).take lengthNat)
  let updatedStore : MachineStore α :=
    { store with wasm :=
        { store.wasm with tables :=
            (listSetAt store.wasm.tables destinationTableIndex
              newDestinationTable) } }
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro
    cases s <;> simp only [Stuckness.MaybeReducible]
    exact ⟨[.instruction
        (.tableCopy destinationTableIndex sourceTableIndex)],
      .running ⟨⟨params, localValues, values⟩,
        code, arity, remainder, controls, calls⟩,
      updatedStore, [],
      ⟨rfl, _, rfl,
        Step.tableCopy hlength hsource hdestination
          HdestinationPhysical HsourcePhysical
          hdestinationBound hsourceBound⟩⟩
  iintro !> %e₂ %store₂ %forks %Hstep Hcredit
  rcases Hstep with ⟨hforks, kind, hobs, wasmStep⟩
  change forks = [] at hforks
  subst forks
  subst obs
  have expectedStep : Step
      ⟨.running
        ⟨⟨params, localValues, length :: source :: destination :: values⟩,
          .tableCopy destinationTableIndex sourceTableIndex :: code,
          arity, remainder, controls, calls⟩,
        store⟩
      (.instruction
        (.tableCopy destinationTableIndex sourceTableIndex))
      ⟨.running
        ⟨⟨params, localValues, values⟩,
          code, arity, remainder, controls, calls⟩,
        updatedStore⟩ :=
    Step.tableCopy hlength hsource hdestination
      HdestinationPhysical HsourcePhysical
      hdestinationBound hsourceBound
  obtain ⟨rfl, hconfig⟩ := step_deterministic expectedStep wasmStep
  have parts := Config.mk.inj hconfig
  have hexpr := parts.1
  have hstore := parts.2
  simp only at hexpr hstore
  subst e₂
  subst store₂
  simp only [List.length_nil, Nat.add_zero,
    Iris.Algebra.BigOpL.bigOpL_nil]
  imod stateInterp_table_set store ns
      ([.instruction
        (.tableCopy destinationTableIndex sourceTableIndex)] ++ obs') nt
      destinationTableIndex destinationTable newDestinationTable $$
      [$Hσ $Hdestination] with ⟨Hσ, Hdestination⟩
  imod Hclose
  imodintro
  isplitl [Hσ]
  · iexact Hσ
  isplitl [Hwp Hdestination Hsource]
  · iapply Hwp $$ Hdestination Hsource
  · itrivial

/-- Primitive rule for `i32.load8_u`. The arithmetic premise rules out
32-bit effective-address wraparound; physical bounds follow from ownership
through `StateInterp`, rather than being assumed about an external store. -/
theorem wp_load8U
    {params localValues values : List Value}
    {address offset : UInt32} {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame} (byte : UInt8)
    (hnowrap :
      (address + offset).toNat = address.toNat + offset.toNat) :
    let current : ThreadState α :=
      ⟨⟨params, localValues, .i32 address :: values⟩,
        .load8U offset :: code, arity, remainder, controls, calls⟩
    let next : ThreadState α :=
      ⟨⟨params, localValues, .i32 byte.toUInt32 :: values⟩,
        code, arity, remainder, controls, calls⟩
    ▷ pointsTo (GF := WasmHeapGF) (H := WasmHeapMap)
        (address + offset) (DFrac.own 1) (some byte) -∗
    ▷ (pointsTo (GF := WasmHeapGF) (H := WasmHeapMap)
        (address + offset) (DFrac.own 1) (some byte) -∗
      WP (Expr.running next : Expr α) @ s; E {{ Φ }}) -∗
      WP (Expr.running current : Expr α) @ s; E {{ Φ }} := by
  dsimp only
  iintro >Hpt Hwp
  iapply wp_lift_step rfl
  iintro %store %ns %obs %obs' %nt Hσ
  ihave %Hfacts : ⌜store.wasm.mem.read8 (address + offset) = byte ∧
      (address + offset).toNat < store.wasm.mem.pages * 65536⌝ $$ [Hσ Hpt]
  · imod stateInterp_pointsTo_facts store ns (obs ++ obs') nt
      (address + offset) byte $$ [$Hσ $Hpt] with %Hfacts
    ipureintro
    exact Hfacts
  obtain ⟨Hread, HinBounds⟩ := Hfacts
  have hbound : address.toNat + offset.toNat + 1 ≤
      store.wasm.mem.pages * 65536 := by
    omega
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro
    cases s <;> simp only [Stuckness.MaybeReducible]
    exact ⟨[.instruction (.load8U offset)],
      .running ⟨⟨params, localValues, .i32 byte.toUInt32 :: values⟩,
        code, arity, remainder, controls, calls⟩,
      store, [], ⟨rfl, _, rfl, by simpa [Hread] using Step.load8U hbound⟩⟩
  iintro !> %e₂ %store₂ %forks %Hstep Hcredit
  rcases Hstep with ⟨hforks, kind, hobs, wasmStep⟩
  change forks = [] at hforks
  subst forks
  subst obs
  have expectedStep : Step
      ⟨.running ⟨⟨params, localValues, .i32 address :: values⟩,
        .load8U offset :: code, arity, remainder, controls, calls⟩, store⟩
      (.instruction (.load8U offset))
      ⟨.running ⟨⟨params, localValues, .i32 byte.toUInt32 :: values⟩,
        code, arity, remainder, controls, calls⟩, store⟩ := by
    simpa [Hread] using (Step.load8U (α := α) hbound)
  obtain ⟨rfl, hconfig⟩ := step_deterministic expectedStep wasmStep
  have parts := Config.mk.inj hconfig
  have hexpr := parts.1
  have hstore := parts.2
  simp only at hexpr hstore
  subst e₂
  subst store₂
  simp only [List.length_nil, Nat.add_zero, Iris.Algebra.BigOpL.bigOpL_nil]
  imod Hclose
  imodintro
  isplitl [Hσ]
  · iexact Hσ
  isplitl [Hwp Hpt]
  · iapply Hwp
    iexact Hpt
  · itrivial

/-- Primitive rule for `i64.load8_u` with an i32 memory address.  The loaded
byte is zero-extended to i64; ownership remains at the physical UInt32 key. -/
theorem wp_load8UI64
    {params localValues values : List Value}
    {address offset : UInt32} {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame} (byte : UInt8)
    (hnowrap :
      (address + offset).toNat = address.toNat + offset.toNat) :
    let current : ThreadState α :=
      ⟨⟨params, localValues, .i32 address :: values⟩,
        .load8UI64 offset :: code, arity, remainder, controls, calls⟩
    let next : ThreadState α :=
      ⟨⟨params, localValues, .i64 byte.toUInt64 :: values⟩,
        code, arity, remainder, controls, calls⟩
    ▷ pointsTo (GF := WasmHeapGF) (H := WasmHeapMap)
        (address + offset) (DFrac.own 1) (some byte) -∗
    ▷ (pointsTo (GF := WasmHeapGF) (H := WasmHeapMap)
        (address + offset) (DFrac.own 1) (some byte) -∗
      WP (Expr.running next : Expr α) @ s; E {{ Φ }}) -∗
      WP (Expr.running current : Expr α) @ s; E {{ Φ }} := by
  dsimp only
  iintro >Hpt Hwp
  iapply wp_lift_step rfl
  iintro %store %ns %obs %obs' %nt Hσ
  ihave %Hfacts : ⌜store.wasm.mem.read8 (address + offset) = byte ∧
      (address + offset).toNat < store.wasm.mem.pages * 65536⌝ $$ [Hσ Hpt]
  · imod stateInterp_pointsTo_facts store ns (obs ++ obs') nt
      (address + offset) byte $$ [$Hσ $Hpt] with %Hfacts
    ipureintro
    exact Hfacts
  obtain ⟨Hread, HinBounds⟩ := Hfacts
  have hbound : address.toNat + offset.toNat + 1 ≤
      store.wasm.mem.pages * 65536 := by
    omega
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro
    cases s <;> simp only [Stuckness.MaybeReducible]
    exact ⟨[.instruction (.load8UI64 offset)],
      .running ⟨⟨params, localValues, .i64 byte.toUInt64 :: values⟩,
        code, arity, remainder, controls, calls⟩,
      store, [], ⟨rfl, _, rfl,
        by simpa [Hread] using
          Step.load8UI64 (α := α) (address := Value.i32 address) rfl hbound⟩⟩
  iintro !> %e₂ %store₂ %forks %Hstep Hcredit
  rcases Hstep with ⟨hforks, kind, hobs, wasmStep⟩
  change forks = [] at hforks
  subst forks
  subst obs
  have expectedStep : Step
      ⟨.running ⟨⟨params, localValues, .i32 address :: values⟩,
        .load8UI64 offset :: code, arity, remainder, controls, calls⟩, store⟩
      (.instruction (.load8UI64 offset))
      ⟨.running ⟨⟨params, localValues, .i64 byte.toUInt64 :: values⟩,
        code, arity, remainder, controls, calls⟩, store⟩ := by
    simpa [Hread] using
      (Step.load8UI64 (α := α) (address := Value.i32 address) rfl hbound)
  obtain ⟨rfl, hconfig⟩ := step_deterministic expectedStep wasmStep
  have parts := Config.mk.inj hconfig
  have hexpr := parts.1
  have hstore := parts.2
  simp only at hexpr hstore
  subst e₂
  subst store₂
  simp only [List.length_nil, Nat.add_zero, Iris.Algebra.BigOpL.bigOpL_nil]
  imod Hclose
  imodintro
  isplitl [Hσ]
  · iexact Hσ
  isplitl [Hwp Hpt]
  · iapply Hwp
    iexact Hpt
  · itrivial

/-- Primitive rule for `i32.store8`. The physical `Mem.write8` transition and
the authoritative GenHeap update happen in the same Iris step. -/
theorem wp_store8
    {params localValues values : List Value}
    {address offset value : UInt32} {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame} (oldByte : UInt8)
    (hnowrap :
      (address + offset).toNat = address.toNat + offset.toNat) :
    let current : ThreadState α :=
      ⟨⟨params, localValues, .i32 value :: .i32 address :: values⟩,
        .store8 offset :: code, arity, remainder, controls, calls⟩
    let next : ThreadState α :=
      ⟨⟨params, localValues, values⟩, code, arity, remainder, controls, calls⟩
    ▷ pointsTo (GF := WasmHeapGF) (H := WasmHeapMap)
        (address + offset) (DFrac.own 1) (some oldByte) -∗
    ▷ (pointsTo (GF := WasmHeapGF) (H := WasmHeapMap)
        (address + offset) (DFrac.own 1) (some value.toUInt8) -∗
      WP (Expr.running next : Expr α) @ s; E {{ Φ }}) -∗
      WP (Expr.running current : Expr α) @ s; E {{ Φ }} := by
  dsimp only
  iintro >Hpt Hwp
  iapply wp_lift_step rfl
  iintro %store %ns %obs %obs' %nt Hσ
  ihave %HinBounds :
      ⌜(address + offset).toNat < store.wasm.mem.pages * 65536⌝ $$ [Hσ Hpt]
  · imod stateInterp_pointsTo_inBounds store ns (obs ++ obs') nt
      (address + offset) oldByte $$ [$Hσ $Hpt] with %HinBounds
    ipureintro
    exact HinBounds
  have hbound : address.toNat + offset.toNat + 1 ≤
      store.wasm.mem.pages * 65536 := by
    omega
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro
    cases s <;> simp only [Stuckness.MaybeReducible]
    exact ⟨[.instruction (.store8 offset)],
      .running ⟨⟨params, localValues, values⟩, code, arity, remainder, controls, calls⟩,
      { store with wasm :=
          { store.wasm with
            mem := store.wasm.mem.write8 (address + offset) value.toUInt8 } },
      [], ⟨rfl, _, rfl, Step.store8 hbound⟩⟩
  iintro !> %e₂ %store₂ %forks %Hstep Hcredit
  rcases Hstep with ⟨hforks, kind, hobs, wasmStep⟩
  change forks = [] at hforks
  subst forks
  subst obs
  have expectedStep : Step
      ⟨.running
        ⟨⟨params, localValues, .i32 value :: .i32 address :: values⟩,
          .store8 offset :: code, arity, remainder, controls, calls⟩, store⟩
      (.instruction (.store8 offset))
      ⟨.running ⟨⟨params, localValues, values⟩, code, arity, remainder, controls, calls⟩,
        { store with wasm :=
            { store.wasm with
              mem := store.wasm.mem.write8
                (address + offset) value.toUInt8 } }⟩ :=
    Step.store8 hbound
  obtain ⟨rfl, hconfig⟩ := step_deterministic expectedStep wasmStep
  have parts := Config.mk.inj hconfig
  have hexpr := parts.1
  have hstore := parts.2
  simp only at hexpr hstore
  subst e₂
  subst store₂
  simp only [List.length_nil, Nat.add_zero, Iris.Algebra.BigOpL.bigOpL_nil]
  imod stateInterp_store8 store ns ([.instruction (.store8 offset)] ++ obs') nt
      (address + offset) oldByte value.toUInt8
      (by simpa [hnowrap] using HinBounds) $$ [$Hσ $Hpt] with ⟨Hσ, Hpt⟩
  imod Hclose
  imodintro
  isplitl [Hσ]
  · iexact Hσ
  isplitl [Hwp Hpt]
  · iapply Hwp
    iexact Hpt
  · itrivial

/-- Primitive rule for `i64.store8` with an i32 memory address. -/
theorem wp_store8I64
    {params localValues values : List Value}
    {address offset : UInt32} {value : UInt64} {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame} (oldByte : UInt8)
    (hnowrap :
      (address + offset).toNat = address.toNat + offset.toNat) :
    let current : ThreadState α :=
      ⟨⟨params, localValues, .i64 value :: .i32 address :: values⟩,
        .store8I64 offset :: code, arity, remainder, controls, calls⟩
    let next : ThreadState α :=
      ⟨⟨params, localValues, values⟩, code, arity, remainder, controls, calls⟩
    ▷ pointsTo (GF := WasmHeapGF) (H := WasmHeapMap)
        (address + offset) (DFrac.own 1) (some oldByte) -∗
    ▷ (pointsTo (GF := WasmHeapGF) (H := WasmHeapMap)
        (address + offset) (DFrac.own 1) (some value.toUInt8) -∗
      WP (Expr.running next : Expr α) @ s; E {{ Φ }}) -∗
      WP (Expr.running current : Expr α) @ s; E {{ Φ }} := by
  dsimp only
  iintro >Hpt Hwp
  iapply wp_lift_step rfl
  iintro %store %ns %obs %obs' %nt Hσ
  ihave %HinBounds :
      ⌜(address + offset).toNat < store.wasm.mem.pages * 65536⌝ $$ [Hσ Hpt]
  · imod stateInterp_pointsTo_inBounds store ns (obs ++ obs') nt
      (address + offset) oldByte $$ [$Hσ $Hpt] with %HinBounds
    ipureintro
    exact HinBounds
  have hbound : address.toNat + offset.toNat + 1 ≤
      store.wasm.mem.pages * 65536 := by
    omega
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro
    cases s <;> simp only [Stuckness.MaybeReducible]
    exact ⟨[.instruction (.store8I64 offset)],
      .running ⟨⟨params, localValues, values⟩, code, arity, remainder, controls, calls⟩,
      { store with wasm :=
          { store.wasm with
            mem := store.wasm.mem.write8 (address + offset) value.toUInt8 } },
      [], ⟨rfl, _, rfl,
        Step.store8I64 (α := α) (address := Value.i32 address) rfl hbound⟩⟩
  iintro !> %e₂ %store₂ %forks %Hstep Hcredit
  rcases Hstep with ⟨hforks, kind, hobs, wasmStep⟩
  change forks = [] at hforks
  subst forks
  subst obs
  have expectedStep : Step
      ⟨.running
        ⟨⟨params, localValues, .i64 value :: .i32 address :: values⟩,
          .store8I64 offset :: code, arity, remainder, controls, calls⟩, store⟩
      (.instruction (.store8I64 offset))
      ⟨.running ⟨⟨params, localValues, values⟩, code, arity, remainder, controls, calls⟩,
        { store with wasm :=
            { store.wasm with
              mem := store.wasm.mem.write8 (address + offset) value.toUInt8 } }⟩ :=
    Step.store8I64 (α := α) (address := Value.i32 address) rfl hbound
  obtain ⟨rfl, hconfig⟩ := step_deterministic expectedStep wasmStep
  have parts := Config.mk.inj hconfig
  have hexpr := parts.1
  have hstore := parts.2
  simp only at hexpr hstore
  subst e₂
  subst store₂
  simp only [List.length_nil, Nat.add_zero, Iris.Algebra.BigOpL.bigOpL_nil]
  imod stateInterp_store8 store ns ([.instruction (.store8I64 offset)] ++ obs') nt
      (address + offset) oldByte value.toUInt8
      (by simpa [hnowrap] using HinBounds) $$ [$Hσ $Hpt] with ⟨Hσ, Hpt⟩
  imod Hclose
  imodintro
  isplitl [Hσ]
  · iexact Hσ
  isplitl [Hwp Hpt]
  · iapply Hwp
    iexact Hpt
  · itrivial

theorem wp_load32
    {params localValues values : List Value}
    {address offset : UInt32} {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame} (word : UInt32)
    (hnowrap : (address + offset).toNat = address.toNat + offset.toNat)
    (h1 : ((address + offset) + 1).toNat = (address + offset).toNat + 1)
    (h2 : ((address + offset) + 2).toNat = (address + offset).toNat + 2)
    (h3 : ((address + offset) + 3).toNat = (address + offset).toNat + 3) :
    let current : ThreadState α :=
      ⟨⟨params, localValues, .i32 address :: values⟩,
        .load32 offset :: code, arity, remainder, controls, calls⟩
    let next : ThreadState α :=
      ⟨⟨params, localValues, .i32 word :: values⟩,
        code, arity, remainder, controls, calls⟩
    ▷ pointsTo_u32 (address + offset) word -∗
    ▷ (pointsTo_u32 (address + offset) word -∗
      WP (Expr.running next : Expr α) @ s; E {{ Φ }}) -∗
      WP (Expr.running current : Expr α) @ s; E {{ Φ }} := by
  dsimp only
  iintro >Hword Hwp
  iapply wp_lift_step rfl
  iintro %store %ns %obs %obs' %nt Hσ
  ihave %Hfacts :
      ⌜store.wasm.mem.read32 (address + offset) = word ∧
        (address + offset).toNat + 4 ≤ store.wasm.mem.pages * 65536⌝ $$
      [Hσ Hword]
  · imod stateInterp_pointsTo_u32_facts store ns (obs ++ obs') nt
      (address + offset) word h1 h2 h3 $$ [$Hσ $Hword] with %Hfacts
    ipureintro
    exact Hfacts
  obtain ⟨Hread, HinBounds⟩ := Hfacts
  have hbound : address.toNat + offset.toNat + 4 ≤
      store.wasm.mem.pages * 65536 := by
    simpa only [hnowrap] using HinBounds
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro
    cases s <;> simp only [Stuckness.MaybeReducible]
    exact ⟨[.instruction (.load32 offset)],
      .running ⟨⟨params, localValues, .i32 word :: values⟩,
        code, arity, remainder, controls, calls⟩,
      store, [], ⟨rfl, _, rfl, by simpa [Hread] using Step.load32 hbound⟩⟩
  iintro !> %e₂ %store₂ %forks %Hstep Hcredit
  rcases Hstep with ⟨hforks, kind, hobs, wasmStep⟩
  change forks = [] at hforks
  subst forks
  subst obs
  have expectedStep : Step
      ⟨.running ⟨⟨params, localValues, .i32 address :: values⟩,
        .load32 offset :: code, arity, remainder, controls, calls⟩, store⟩
      (.instruction (.load32 offset))
      ⟨.running ⟨⟨params, localValues, .i32 word :: values⟩,
        code, arity, remainder, controls, calls⟩, store⟩ := by
    simpa [Hread] using (Step.load32 (α := α) hbound)
  obtain ⟨rfl, hconfig⟩ := step_deterministic expectedStep wasmStep
  have parts := Config.mk.inj hconfig
  have hexpr := parts.1
  have hstore := parts.2
  simp only at hexpr hstore
  subst e₂
  subst store₂
  simp only [List.length_nil, Nat.add_zero, Iris.Algebra.BigOpL.bigOpL_nil]
  imod Hclose
  imodintro
  isplitl [Hσ]
  · iexact Hσ
  isplitl [Hwp Hword]
  · iapply Hwp
    iexact Hword
  · itrivial

theorem wp_store32
    {params localValues values : List Value}
    {address offset value : UInt32} {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame} (oldWord : UInt32)
    (hnowrap : (address + offset).toNat = address.toNat + offset.toNat)
    (h1 : ((address + offset) + 1).toNat = (address + offset).toNat + 1)
    (h2 : ((address + offset) + 2).toNat = (address + offset).toNat + 2)
    (h3 : ((address + offset) + 3).toNat = (address + offset).toNat + 3) :
    let current : ThreadState α :=
      ⟨⟨params, localValues, .i32 value :: .i32 address :: values⟩,
        .store32 offset :: code, arity, remainder, controls, calls⟩
    let next : ThreadState α :=
      ⟨⟨params, localValues, values⟩,
        code, arity, remainder, controls, calls⟩
    ▷ pointsTo_u32 (address + offset) oldWord -∗
    ▷ (pointsTo_u32 (address + offset) value -∗
      WP (Expr.running next : Expr α) @ s; E {{ Φ }}) -∗
      WP (Expr.running current : Expr α) @ s; E {{ Φ }} := by
  dsimp only
  iintro >Hword Hwp
  iapply wp_lift_step rfl
  iintro %store %ns %obs %obs' %nt Hσ
  ihave %Hfacts :
      ⌜store.wasm.mem.read32 (address + offset) = oldWord ∧
        (address + offset).toNat + 4 ≤ store.wasm.mem.pages * 65536⌝ $$
      [Hσ Hword]
  · imod stateInterp_pointsTo_u32_facts store ns (obs ++ obs') nt
      (address + offset) oldWord h1 h2 h3 $$ [$Hσ $Hword] with %Hfacts
    ipureintro
    exact Hfacts
  have hbound : address.toNat + offset.toNat + 4 ≤
      store.wasm.mem.pages * 65536 := by
    simpa only [hnowrap] using Hfacts.2
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro
    cases s <;> simp only [Stuckness.MaybeReducible]
    exact ⟨[.instruction (.store32 offset)],
      .running ⟨⟨params, localValues, values⟩,
        code, arity, remainder, controls, calls⟩,
      { store with wasm :=
          { store.wasm with
            mem := store.wasm.mem.write32 (address + offset) value } },
      [], ⟨rfl, _, rfl, Step.store32 hbound⟩⟩
  iintro !> %e₂ %store₂ %forks %Hstep Hcredit
  rcases Hstep with ⟨hforks, kind, hobs, wasmStep⟩
  change forks = [] at hforks
  subst forks
  subst obs
  have expectedStep : Step
      ⟨.running
        ⟨⟨params, localValues, .i32 value :: .i32 address :: values⟩,
          .store32 offset :: code, arity, remainder, controls, calls⟩, store⟩
      (.instruction (.store32 offset))
      ⟨.running
        ⟨⟨params, localValues, values⟩,
          code, arity, remainder, controls, calls⟩,
        { store with wasm :=
            { store.wasm with
              mem := store.wasm.mem.write32 (address + offset) value } }⟩ :=
    Step.store32 hbound
  obtain ⟨rfl, hconfig⟩ := step_deterministic expectedStep wasmStep
  have parts := Config.mk.inj hconfig
  have hexpr := parts.1
  have hstore := parts.2
  simp only at hexpr hstore
  subst e₂
  subst store₂
  simp only [List.length_nil, Nat.add_zero, Iris.Algebra.BigOpL.bigOpL_nil]
  imod stateInterp_store32 store ns ([.instruction (.store32 offset)] ++ obs') nt
      (address + offset) oldWord value h1 h2 h3 Hfacts.2 $$
      [$Hσ $Hword] with ⟨Hσ, Hword⟩
  imod Hclose
  imodintro
  isplitl [Hσ]
  · iexact Hσ
  isplitl [Hwp Hword]
  · iapply Hwp
    iexact Hword
  · itrivial

theorem wp_f32Load
    {params localValues values : List Value}
    {address offset : UInt32} {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame} (word : UInt32)
    (hnowrap : (address + offset).toNat = address.toNat + offset.toNat)
    (h1 : ((address + offset) + 1).toNat = (address + offset).toNat + 1)
    (h2 : ((address + offset) + 2).toNat = (address + offset).toNat + 2)
    (h3 : ((address + offset) + 3).toNat = (address + offset).toNat + 3) :
    let current : ThreadState α :=
      ⟨⟨params, localValues, .i32 address :: values⟩,
        .f32Load offset :: code, arity, remainder, controls, calls⟩
    let next : ThreadState α :=
      ⟨⟨params, localValues, .f32 word :: values⟩,
        code, arity, remainder, controls, calls⟩
    ▷ pointsTo_u32 (address + offset) word -∗
    ▷ (pointsTo_u32 (address + offset) word -∗
      WP (Expr.running next : Expr α) @ s; E {{ Φ }}) -∗
      WP (Expr.running current : Expr α) @ s; E {{ Φ }} := by
  dsimp only
  iintro >Hword Hwp
  iapply wp_lift_step rfl
  iintro %store %ns %obs %obs' %nt Hσ
  ihave %Hfacts :
      ⌜store.wasm.mem.read32 (address + offset) = word ∧
        (address + offset).toNat + 4 ≤ store.wasm.mem.pages * 65536⌝ $$
      [Hσ Hword]
  · imod stateInterp_pointsTo_u32_facts store ns (obs ++ obs') nt
      (address + offset) word h1 h2 h3 $$ [$Hσ $Hword] with %Hfacts
    ipureintro
    exact Hfacts
  obtain ⟨Hread, HinBounds⟩ := Hfacts
  have hbound : address.toNat + offset.toNat + 4 ≤
      store.wasm.mem.pages * 65536 := by
    simpa only [hnowrap] using HinBounds
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro
    cases s <;> simp only [Stuckness.MaybeReducible]
    exact ⟨[.instruction (.f32Load offset)],
      .running ⟨⟨params, localValues, .f32 word :: values⟩,
        code, arity, remainder, controls, calls⟩,
      store, [], ⟨rfl, _, rfl,
        by simpa [Hread] using Step.f32Load (address := .i32 address) rfl hbound⟩⟩
  iintro !> %e₂ %store₂ %forks %Hstep Hcredit
  rcases Hstep with ⟨hforks, kind, hobs, wasmStep⟩
  change forks = [] at hforks
  subst forks
  subst obs
  have expectedStep : Step
      ⟨.running ⟨⟨params, localValues, .i32 address :: values⟩,
        .f32Load offset :: code, arity, remainder, controls, calls⟩, store⟩
      (.instruction (.f32Load offset))
      ⟨.running ⟨⟨params, localValues, .f32 word :: values⟩,
        code, arity, remainder, controls, calls⟩, store⟩ := by
    simpa [Hread] using
      (Step.f32Load (α := α) (address := .i32 address) rfl hbound)
  obtain ⟨rfl, hconfig⟩ := step_deterministic expectedStep wasmStep
  have parts := Config.mk.inj hconfig
  have hexpr := parts.1
  have hstore := parts.2
  simp only at hexpr hstore
  subst e₂
  subst store₂
  simp only [List.length_nil, Nat.add_zero, Iris.Algebra.BigOpL.bigOpL_nil]
  imod Hclose
  imodintro
  isplitl [Hσ]
  · iexact Hσ
  isplitl [Hwp Hword]
  · iapply Hwp
    iexact Hword
  · itrivial

theorem wp_f32Store
    {params localValues values : List Value}
    {address offset value : UInt32} {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame} (oldWord : UInt32)
    (hnowrap : (address + offset).toNat = address.toNat + offset.toNat)
    (h1 : ((address + offset) + 1).toNat = (address + offset).toNat + 1)
    (h2 : ((address + offset) + 2).toNat = (address + offset).toNat + 2)
    (h3 : ((address + offset) + 3).toNat = (address + offset).toNat + 3) :
    let current : ThreadState α :=
      ⟨⟨params, localValues, .f32 value :: .i32 address :: values⟩,
        .f32Store offset :: code, arity, remainder, controls, calls⟩
    let next : ThreadState α :=
      ⟨⟨params, localValues, values⟩,
        code, arity, remainder, controls, calls⟩
    ▷ pointsTo_u32 (address + offset) oldWord -∗
    ▷ (pointsTo_u32 (address + offset) value -∗
      WP (Expr.running next : Expr α) @ s; E {{ Φ }}) -∗
      WP (Expr.running current : Expr α) @ s; E {{ Φ }} := by
  dsimp only
  iintro >Hword Hwp
  iapply wp_lift_step rfl
  iintro %store %ns %obs %obs' %nt Hσ
  ihave %Hfacts :
      ⌜store.wasm.mem.read32 (address + offset) = oldWord ∧
        (address + offset).toNat + 4 ≤ store.wasm.mem.pages * 65536⌝ $$
      [Hσ Hword]
  · imod stateInterp_pointsTo_u32_facts store ns (obs ++ obs') nt
      (address + offset) oldWord h1 h2 h3 $$ [$Hσ $Hword] with %Hfacts
    ipureintro
    exact Hfacts
  have hbound : address.toNat + offset.toNat + 4 ≤
      store.wasm.mem.pages * 65536 := by
    simpa only [hnowrap] using Hfacts.2
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro
    cases s <;> simp only [Stuckness.MaybeReducible]
    exact ⟨[.instruction (.f32Store offset)],
      .running ⟨⟨params, localValues, values⟩,
        code, arity, remainder, controls, calls⟩,
      { store with wasm :=
          { store.wasm with
            mem := store.wasm.mem.write32 (address + offset) value } },
      [], ⟨rfl, _, rfl,
        by simpa only [Wasm.SmallStep.setMemory_eq] using
          Step.f32Store (address := .i32 address) rfl hbound⟩⟩
  iintro !> %e₂ %store₂ %forks %Hstep Hcredit
  rcases Hstep with ⟨hforks, kind, hobs, wasmStep⟩
  change forks = [] at hforks
  subst forks
  subst obs
  have expectedStep : Step
      ⟨.running
        ⟨⟨params, localValues, .f32 value :: .i32 address :: values⟩,
          .f32Store offset :: code, arity, remainder, controls, calls⟩, store⟩
      (.instruction (.f32Store offset))
      ⟨.running
        ⟨⟨params, localValues, values⟩,
          code, arity, remainder, controls, calls⟩,
        { store with wasm :=
            { store.wasm with
              mem := store.wasm.mem.write32 (address + offset) value } }⟩ := by
    simpa only [Wasm.SmallStep.setMemory_eq] using
      Step.f32Store (address := .i32 address) rfl hbound
  obtain ⟨rfl, hconfig⟩ := step_deterministic expectedStep wasmStep
  have parts := Config.mk.inj hconfig
  have hexpr := parts.1
  have hstore := parts.2
  simp only at hexpr hstore
  subst e₂
  subst store₂
  simp only [List.length_nil, Nat.add_zero, Iris.Algebra.BigOpL.bigOpL_nil]
  imod stateInterp_store32 store ns ([.instruction (.f32Store offset)] ++ obs') nt
      (address + offset) oldWord value h1 h2 h3 Hfacts.2 $$
      [$Hσ $Hword] with ⟨Hσ, Hword⟩
  imod Hclose
  imodintro
  isplitl [Hσ]
  · iexact Hσ
  isplitl [Hwp Hword]
  · iapply Hwp
    iexact Hword
  · itrivial

theorem wp_load64
    {params localValues values : List Value}
    {address offset : UInt32} {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame} (word : UInt64)
    (hnowrap : (address + offset).toNat = address.toNat + offset.toNat)
    (h1 : ((address + offset) + 1).toNat = (address + offset).toNat + 1)
    (h2 : ((address + offset) + 2).toNat = (address + offset).toNat + 2)
    (h3 : ((address + offset) + 3).toNat = (address + offset).toNat + 3)
    (h4 : ((address + offset) + 4).toNat = (address + offset).toNat + 4)
    (h5 : ((address + offset) + 5).toNat = (address + offset).toNat + 5)
    (h6 : ((address + offset) + 6).toNat = (address + offset).toNat + 6)
    (h7 : ((address + offset) + 7).toNat = (address + offset).toNat + 7) :
    let current : ThreadState α :=
      ⟨⟨params, localValues, .i32 address :: values⟩,
        .load64 offset :: code, arity, remainder, controls, calls⟩
    let next : ThreadState α :=
      ⟨⟨params, localValues, .i64 word :: values⟩,
        code, arity, remainder, controls, calls⟩
    ▷ pointsTo_u64 (address + offset) word -∗
    ▷ (pointsTo_u64 (address + offset) word -∗
      WP (Expr.running next : Expr α) @ s; E {{ Φ }}) -∗
      WP (Expr.running current : Expr α) @ s; E {{ Φ }} := by
  dsimp only
  iintro >Hword Hwp
  iapply wp_lift_step rfl
  iintro %store %ns %obs %obs' %nt Hσ
  ihave %Hfacts :
      ⌜store.wasm.mem.read64 (address + offset) = word ∧
        (address + offset).toNat + 8 ≤ store.wasm.mem.pages * 65536⌝ $$
      [Hσ Hword]
  · imod stateInterp_pointsTo_u64_facts store ns (obs ++ obs') nt
      (address + offset) word h1 h2 h3 h4 h5 h6 h7 $$
      [$Hσ $Hword] with %Hfacts
    ipureintro
    exact Hfacts
  obtain ⟨Hread, HinBounds⟩ := Hfacts
  have hbound : address.toNat + offset.toNat + 8 ≤
      store.wasm.mem.pages * 65536 := by
    simpa only [hnowrap] using HinBounds
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro
    cases s <;> simp only [Stuckness.MaybeReducible]
    exact ⟨[.instruction (.load64 offset)],
      .running ⟨⟨params, localValues, .i64 word :: values⟩,
        code, arity, remainder, controls, calls⟩,
      store, [], ⟨rfl, _, rfl, by
        simpa [Hread] using
          Step.load64 (α := α) (address := Value.i32 address) rfl hbound⟩⟩
  iintro !> %e₂ %store₂ %forks %Hstep Hcredit
  rcases Hstep with ⟨hforks, kind, hobs, wasmStep⟩
  change forks = [] at hforks
  subst forks
  subst obs
  have expectedStep : Step
      ⟨.running ⟨⟨params, localValues, .i32 address :: values⟩,
        .load64 offset :: code, arity, remainder, controls, calls⟩, store⟩
      (.instruction (.load64 offset))
      ⟨.running ⟨⟨params, localValues, .i64 word :: values⟩,
        code, arity, remainder, controls, calls⟩, store⟩ := by
    simpa [Hread] using
      (Step.load64 (α := α) (address := Value.i32 address) rfl hbound)
  obtain ⟨rfl, hconfig⟩ := step_deterministic expectedStep wasmStep
  have parts := Config.mk.inj hconfig
  have hexpr := parts.1
  have hstore := parts.2
  simp only at hexpr hstore
  subst e₂
  subst store₂
  simp only [List.length_nil, Nat.add_zero, Iris.Algebra.BigOpL.bigOpL_nil]
  imod Hclose
  imodintro
  isplitl [Hσ]
  · iexact Hσ
  isplitl [Hwp Hword]
  · iapply Hwp
    iexact Hword
  · itrivial

theorem wp_store64
    {params localValues values : List Value}
    {address offset : UInt32} {value : UInt64}
    {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame} (oldWord : UInt64)
    (hnowrap : (address + offset).toNat = address.toNat + offset.toNat)
    (h1 : ((address + offset) + 1).toNat = (address + offset).toNat + 1)
    (h2 : ((address + offset) + 2).toNat = (address + offset).toNat + 2)
    (h3 : ((address + offset) + 3).toNat = (address + offset).toNat + 3)
    (h4 : ((address + offset) + 4).toNat = (address + offset).toNat + 4)
    (h5 : ((address + offset) + 5).toNat = (address + offset).toNat + 5)
    (h6 : ((address + offset) + 6).toNat = (address + offset).toNat + 6)
    (h7 : ((address + offset) + 7).toNat = (address + offset).toNat + 7) :
    let current : ThreadState α :=
      ⟨⟨params, localValues, .i64 value :: .i32 address :: values⟩,
        .store64 offset :: code, arity, remainder, controls, calls⟩
    let next : ThreadState α :=
      ⟨⟨params, localValues, values⟩,
        code, arity, remainder, controls, calls⟩
    ▷ pointsTo_u64 (address + offset) oldWord -∗
    ▷ (pointsTo_u64 (address + offset) value -∗
      WP (Expr.running next : Expr α) @ s; E {{ Φ }}) -∗
      WP (Expr.running current : Expr α) @ s; E {{ Φ }} := by
  dsimp only
  iintro >Hword Hwp
  iapply wp_lift_step rfl
  iintro %store %ns %obs %obs' %nt Hσ
  ihave %Hfacts :
      ⌜store.wasm.mem.read64 (address + offset) = oldWord ∧
        (address + offset).toNat + 8 ≤ store.wasm.mem.pages * 65536⌝ $$
      [Hσ Hword]
  · imod stateInterp_pointsTo_u64_facts store ns (obs ++ obs') nt
      (address + offset) oldWord h1 h2 h3 h4 h5 h6 h7 $$
      [$Hσ $Hword] with %Hfacts
    ipureintro
    exact Hfacts
  have hbound : address.toNat + offset.toNat + 8 ≤
      store.wasm.mem.pages * 65536 := by
    simpa only [hnowrap] using Hfacts.2
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro
    cases s <;> simp only [Stuckness.MaybeReducible]
    exact ⟨[.instruction (.store64 offset)],
      .running ⟨⟨params, localValues, values⟩,
        code, arity, remainder, controls, calls⟩,
      { store with wasm :=
          { store.wasm with
            mem := store.wasm.mem.write64 (address + offset) value } },
      [], ⟨rfl, _, rfl,
        Step.store64 (α := α) (address := Value.i32 address) rfl hbound⟩⟩
  iintro !> %e₂ %store₂ %forks %Hstep Hcredit
  rcases Hstep with ⟨hforks, kind, hobs, wasmStep⟩
  change forks = [] at hforks
  subst forks
  subst obs
  have expectedStep : Step
      ⟨.running
        ⟨⟨params, localValues, .i64 value :: .i32 address :: values⟩,
          .store64 offset :: code, arity, remainder, controls, calls⟩, store⟩
      (.instruction (.store64 offset))
      ⟨.running
        ⟨⟨params, localValues, values⟩,
          code, arity, remainder, controls, calls⟩,
        { store with wasm :=
            { store.wasm with
              mem := store.wasm.mem.write64 (address + offset) value } }⟩ :=
    Step.store64 (α := α) (address := Value.i32 address) rfl hbound
  obtain ⟨rfl, hconfig⟩ := step_deterministic expectedStep wasmStep
  have parts := Config.mk.inj hconfig
  have hexpr := parts.1
  have hstore := parts.2
  simp only at hexpr hstore
  subst e₂
  subst store₂
  simp only [List.length_nil, Nat.add_zero, Iris.Algebra.BigOpL.bigOpL_nil]
  imod stateInterp_store64 store ns ([.instruction (.store64 offset)] ++ obs') nt
      (address + offset) oldWord value h1 h2 h3 h4 h5 h6 h7 Hfacts.2 $$
      [$Hσ $Hword] with ⟨Hσ, Hword⟩
  imod Hclose
  imodintro
  isplitl [Hσ]
  · iexact Hσ
  isplitl [Hwp Hword]
  · iapply Hwp
    iexact Hword
  · itrivial

theorem wp_f64Load
    {params localValues values : List Value}
    {address offset : UInt32} {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame} (word : UInt64)
    (hnowrap : (address + offset).toNat = address.toNat + offset.toNat)
    (h1 : ((address + offset) + 1).toNat = (address + offset).toNat + 1)
    (h2 : ((address + offset) + 2).toNat = (address + offset).toNat + 2)
    (h3 : ((address + offset) + 3).toNat = (address + offset).toNat + 3)
    (h4 : ((address + offset) + 4).toNat = (address + offset).toNat + 4)
    (h5 : ((address + offset) + 5).toNat = (address + offset).toNat + 5)
    (h6 : ((address + offset) + 6).toNat = (address + offset).toNat + 6)
    (h7 : ((address + offset) + 7).toNat = (address + offset).toNat + 7) :
    let current : ThreadState α :=
      ⟨⟨params, localValues, .i32 address :: values⟩,
        .f64Load offset :: code, arity, remainder, controls, calls⟩
    let next : ThreadState α :=
      ⟨⟨params, localValues, .f64 word :: values⟩,
        code, arity, remainder, controls, calls⟩
    ▷ pointsTo_u64 (address + offset) word -∗
    ▷ (pointsTo_u64 (address + offset) word -∗
      WP (Expr.running next : Expr α) @ s; E {{ Φ }}) -∗
      WP (Expr.running current : Expr α) @ s; E {{ Φ }} := by
  dsimp only
  iintro >Hword Hwp
  iapply wp_lift_step rfl
  iintro %store %ns %obs %obs' %nt Hσ
  ihave %Hfacts :
      ⌜store.wasm.mem.read64 (address + offset) = word ∧
        (address + offset).toNat + 8 ≤ store.wasm.mem.pages * 65536⌝ $$
      [Hσ Hword]
  · imod stateInterp_pointsTo_u64_facts store ns (obs ++ obs') nt
      (address + offset) word h1 h2 h3 h4 h5 h6 h7 $$
      [$Hσ $Hword] with %Hfacts
    ipureintro
    exact Hfacts
  obtain ⟨Hread, HinBounds⟩ := Hfacts
  have hbound : address.toNat + offset.toNat + 8 ≤
      store.wasm.mem.pages * 65536 := by
    simpa only [hnowrap] using HinBounds
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro
    cases s <;> simp only [Stuckness.MaybeReducible]
    exact ⟨[.instruction (.f64Load offset)],
      .running ⟨⟨params, localValues, .f64 word :: values⟩,
        code, arity, remainder, controls, calls⟩,
      store, [], ⟨rfl, _, rfl, by
        simpa [Hread] using
          Step.f64Load (α := α) (address := Value.i32 address) rfl hbound⟩⟩
  iintro !> %e₂ %store₂ %forks %Hstep Hcredit
  rcases Hstep with ⟨hforks, kind, hobs, wasmStep⟩
  change forks = [] at hforks
  subst forks
  subst obs
  have expectedStep : Step
      ⟨.running ⟨⟨params, localValues, .i32 address :: values⟩,
        .f64Load offset :: code, arity, remainder, controls, calls⟩, store⟩
      (.instruction (.f64Load offset))
      ⟨.running ⟨⟨params, localValues, .f64 word :: values⟩,
        code, arity, remainder, controls, calls⟩, store⟩ := by
    simpa [Hread] using
      (Step.f64Load (α := α) (address := Value.i32 address) rfl hbound)
  obtain ⟨rfl, hconfig⟩ := step_deterministic expectedStep wasmStep
  have parts := Config.mk.inj hconfig
  have hexpr := parts.1
  have hstore := parts.2
  simp only at hexpr hstore
  subst e₂
  subst store₂
  simp only [List.length_nil, Nat.add_zero, Iris.Algebra.BigOpL.bigOpL_nil]
  imod Hclose
  imodintro
  isplitl [Hσ]
  · iexact Hσ
  isplitl [Hwp Hword]
  · iapply Hwp
    iexact Hword
  · itrivial

theorem wp_f64Store
    {params localValues values : List Value}
    {address offset : UInt32} {value : UInt64}
    {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame} (oldWord : UInt64)
    (hnowrap : (address + offset).toNat = address.toNat + offset.toNat)
    (h1 : ((address + offset) + 1).toNat = (address + offset).toNat + 1)
    (h2 : ((address + offset) + 2).toNat = (address + offset).toNat + 2)
    (h3 : ((address + offset) + 3).toNat = (address + offset).toNat + 3)
    (h4 : ((address + offset) + 4).toNat = (address + offset).toNat + 4)
    (h5 : ((address + offset) + 5).toNat = (address + offset).toNat + 5)
    (h6 : ((address + offset) + 6).toNat = (address + offset).toNat + 6)
    (h7 : ((address + offset) + 7).toNat = (address + offset).toNat + 7) :
    let current : ThreadState α :=
      ⟨⟨params, localValues, .f64 value :: .i32 address :: values⟩,
        .f64Store offset :: code, arity, remainder, controls, calls⟩
    let next : ThreadState α :=
      ⟨⟨params, localValues, values⟩,
        code, arity, remainder, controls, calls⟩
    ▷ pointsTo_u64 (address + offset) oldWord -∗
    ▷ (pointsTo_u64 (address + offset) value -∗
      WP (Expr.running next : Expr α) @ s; E {{ Φ }}) -∗
      WP (Expr.running current : Expr α) @ s; E {{ Φ }} := by
  dsimp only
  iintro >Hword Hwp
  iapply wp_lift_step rfl
  iintro %store %ns %obs %obs' %nt Hσ
  ihave %Hfacts :
      ⌜store.wasm.mem.read64 (address + offset) = oldWord ∧
        (address + offset).toNat + 8 ≤ store.wasm.mem.pages * 65536⌝ $$
      [Hσ Hword]
  · imod stateInterp_pointsTo_u64_facts store ns (obs ++ obs') nt
      (address + offset) oldWord h1 h2 h3 h4 h5 h6 h7 $$
      [$Hσ $Hword] with %Hfacts
    ipureintro
    exact Hfacts
  have hbound : address.toNat + offset.toNat + 8 ≤
      store.wasm.mem.pages * 65536 := by
    simpa only [hnowrap] using Hfacts.2
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro
    cases s <;> simp only [Stuckness.MaybeReducible]
    exact ⟨[.instruction (.f64Store offset)],
      .running ⟨⟨params, localValues, values⟩,
        code, arity, remainder, controls, calls⟩,
      { store with wasm :=
          { store.wasm with
            mem := store.wasm.mem.write64 (address + offset) value } },
      [], ⟨rfl, _, rfl, by
        simpa only [Wasm.SmallStep.setMemory_eq] using
          Step.f64Store (α := α) (address := Value.i32 address) rfl hbound⟩⟩
  iintro !> %e₂ %store₂ %forks %Hstep Hcredit
  rcases Hstep with ⟨hforks, kind, hobs, wasmStep⟩
  change forks = [] at hforks
  subst forks
  subst obs
  have expectedStep : Step
      ⟨.running
        ⟨⟨params, localValues, .f64 value :: .i32 address :: values⟩,
          .f64Store offset :: code, arity, remainder, controls, calls⟩, store⟩
      (.instruction (.f64Store offset))
      ⟨.running
        ⟨⟨params, localValues, values⟩,
          code, arity, remainder, controls, calls⟩,
        { store with wasm :=
            { store.wasm with
              mem := store.wasm.mem.write64 (address + offset) value } }⟩ := by
    simpa only [Wasm.SmallStep.setMemory_eq] using
      Step.f64Store (α := α) (address := Value.i32 address) rfl hbound
  obtain ⟨rfl, hconfig⟩ := step_deterministic expectedStep wasmStep
  have parts := Config.mk.inj hconfig
  have hexpr := parts.1
  have hstore := parts.2
  simp only at hexpr hstore
  subst e₂
  subst store₂
  simp only [List.length_nil, Nat.add_zero, Iris.Algebra.BigOpL.bigOpL_nil]
  imod stateInterp_store64 store ns ([.instruction (.f64Store offset)] ++ obs') nt
      (address + offset) oldWord value h1 h2 h3 h4 h5 h6 h7 Hfacts.2 $$
      [$Hσ $Hword] with ⟨Hσ, Hword⟩
  imod Hclose
  imodintro
  isplitl [Hσ]
  · iexact Hσ
  isplitl [Hwp Hword]
  · iapply Hwp
    iexact Hword
  · itrivial

/-- Primitive Iris rule for the concrete four-byte fill used by the manual
example. The caller owns the complete affected range; disjoint ownership is
framed by ordinary separation logic. -/
theorem wp_fill16_four_AB
    {params localValues values : List Value}
    {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame} (oldWord : UInt32) :
    let current : ThreadState α :=
      ⟨⟨params, localValues,
          .i32 4 :: .i32 0xAB :: .i32 16 :: values⟩,
        .memoryFill :: code, arity, remainder, controls, calls⟩
    let next : ThreadState α :=
      ⟨⟨params, localValues, values⟩,
        code, arity, remainder, controls, calls⟩
    ▷ pointsTo_u32 16 oldWord -∗
    ▷ (pointsTo_u32 16 0xABABABAB -∗
      WP (Expr.running next : Expr α) @ s; E {{ Φ }}) -∗
      WP (Expr.running current : Expr α) @ s; E {{ Φ }} := by
  dsimp only
  iintro >Hword Hwp
  iapply wp_lift_step rfl
  iintro %store %ns %obs %obs' %nt Hσ
  ihave %Hfacts :
      ⌜store.wasm.mem.read32 16 = oldWord ∧
        20 ≤ store.wasm.mem.pages * 65536⌝ $$ [Hσ Hword]
  · imod stateInterp_pointsTo_u32_facts store ns (obs ++ obs') nt
      16 oldWord rfl rfl rfl $$ [$Hσ $Hword] with %Hfacts
    ipureintro
    exact Hfacts
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro
    cases s <;> simp only [Stuckness.MaybeReducible]
    exact ⟨[.instruction .memoryFill],
      .running ⟨⟨params, localValues, values⟩,
        code, arity, remainder, controls, calls⟩,
      { store with wasm :=
          { store.wasm with mem := store.wasm.mem.fill 16 4 0xAB } },
      [], ⟨rfl, _, rfl, Step.memoryFill32 Hfacts.2⟩⟩
  iintro !> %e₂ %store₂ %forks %Hstep Hcredit
  rcases Hstep with ⟨hforks, kind, hobs, wasmStep⟩
  change forks = [] at hforks
  subst forks
  subst obs
  have expectedStep : Step
      ⟨.running
        ⟨⟨params, localValues, .i32 4 :: .i32 0xAB :: .i32 16 :: values⟩,
          .memoryFill :: code, arity, remainder, controls, calls⟩, store⟩
      (.instruction .memoryFill)
      ⟨.running
        ⟨⟨params, localValues, values⟩,
          code, arity, remainder, controls, calls⟩,
        { store with wasm :=
            { store.wasm with mem := store.wasm.mem.fill 16 4 0xAB } }⟩ :=
    Step.memoryFill32 Hfacts.2
  obtain ⟨rfl, hconfig⟩ := step_deterministic expectedStep wasmStep
  have parts := Config.mk.inj hconfig
  have hexpr := parts.1
  have hstore := parts.2
  simp only at hexpr hstore
  subst e₂
  subst store₂
  simp only [List.length_nil, Nat.add_zero, Iris.Algebra.BigOpL.bigOpL_nil]
  imod stateInterp_fill16_four_AB store ns
      ([.instruction .memoryFill] ++ obs') nt oldWord Hfacts.2 $$
      [$Hσ $Hword] with ⟨Hσ, Hword⟩
  imod Hclose
  imodintro
  isplitl [Hσ]
  · iexact Hσ
  isplitl [Hwp Hword]
  · iapply Hwp
    iexact Hword
  · itrivial

/-- Primitive Iris rule for initializing four bytes from passive data segment
zero. Segment ownership proves that the bytes used by the relational
transition are the bytes in the physical instantiated store. -/
theorem wp_memoryInit16_four
    {params localValues values : List Value}
    {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame} (oldWord : UInt32) :
    let current : ThreadState α :=
      ⟨⟨params, localValues,
          .i32 4 :: .i32 0 :: .i32 16 :: values⟩,
        .memoryInit 0 :: code, arity, remainder, controls, calls⟩
    let next : ThreadState α :=
      ⟨⟨params, localValues, values⟩,
        code, arity, remainder, controls, calls⟩
    ▷ (pointsTo_u32 16 oldWord ∗
      dataSegmentPointsTo 0 (some [1, 2, 3, 4])) -∗
    ▷ (pointsTo_u32 16 0x04030201 ∗
      dataSegmentPointsTo 0 (some [1, 2, 3, 4]) -∗
      WP (Expr.running next : Expr α) @ s; E {{ Φ }}) -∗
      WP (Expr.running current : Expr α) @ s; E {{ Φ }} := by
  dsimp only
  iintro >⟨Hword, Hsegment⟩ Hwp
  iapply wp_lift_step rfl
  iintro %store %ns %obs %obs' %nt Hσ
  imod stateInterp_dataSegment_facts_frame store ns (obs ++ obs') nt
      0 (some [1, 2, 3, 4]) $$ [$Hσ $Hsegment] with
    ⟨Hσ, Hsegment, %hsegment⟩
  ihave %HwordFacts :
      ⌜store.wasm.mem.read32 16 = oldWord ∧
        20 ≤ store.wasm.mem.pages * 65536⌝ $$ [Hσ Hword]
  · imod stateInterp_pointsTo_u32_facts store ns (obs ++ obs') nt
      16 oldWord rfl rfl rfl $$ [$Hσ $Hword] with %HwordFacts
    ipureintro
    exact HwordFacts
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro
    cases s <;> simp only [Stuckness.MaybeReducible]
    exact ⟨[.instruction (.memoryInit 0)],
      .running ⟨⟨params, localValues, values⟩,
        code, arity, remainder, controls, calls⟩,
      { store with wasm :=
          { store.wasm with mem :=
              store.wasm.mem.writeBytesFrom 16 [1, 2, 3, 4] 0 4 } },
      [], ⟨rfl, _, rfl,
        Step.memoryInit32 hsegment (by decide) HwordFacts.2⟩⟩
  iintro !> %e₂ %store₂ %forks %Hstep Hcredit
  rcases Hstep with ⟨hforks, kind, hobs, wasmStep⟩
  change forks = [] at hforks
  subst forks
  subst obs
  have expectedStep : Step
      ⟨.running
        ⟨⟨params, localValues, .i32 4 :: .i32 0 :: .i32 16 :: values⟩,
          .memoryInit 0 :: code, arity, remainder, controls, calls⟩, store⟩
      (.instruction (.memoryInit 0))
      ⟨.running
        ⟨⟨params, localValues, values⟩,
          code, arity, remainder, controls, calls⟩,
        { store with wasm :=
            { store.wasm with mem :=
                store.wasm.mem.writeBytesFrom 16 [1, 2, 3, 4] 0 4 } }⟩ :=
    Step.memoryInit32 hsegment (by decide) HwordFacts.2
  obtain ⟨rfl, hconfig⟩ := step_deterministic expectedStep wasmStep
  have parts := Config.mk.inj hconfig
  have hexpr := parts.1
  have hstore := parts.2
  simp only at hexpr hstore
  subst e₂
  subst store₂
  simp only [List.length_nil, Nat.add_zero, Iris.Algebra.BigOpL.bigOpL_nil]
  imod stateInterp_init16_four store ns
      ([.instruction (.memoryInit 0)] ++ obs') nt oldWord HwordFacts.2 $$
      [$Hσ $Hword] with ⟨Hσ, Hword⟩
  imod Hclose
  imodintro
  isplitl [Hσ]
  · iexact Hσ
  isplitl [Hwp Hword Hsegment]
  · iapply Hwp
    iframe
  · itrivial

/-- Primitive Iris rule for consuming passive data segment zero. The post owns
the dropped status, preventing the old bytes from being reused. -/
theorem wp_dataDrop0
    {params localValues values : List Value}
    {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame} (bytes : List UInt8) :
    let current : ThreadState α :=
      ⟨⟨params, localValues, values⟩,
        .dataDrop 0 :: code, arity, remainder, controls, calls⟩
    let next : ThreadState α :=
      ⟨⟨params, localValues, values⟩,
        code, arity, remainder, controls, calls⟩
    ▷ dataSegmentPointsTo 0 (some bytes) -∗
    ▷ (dataSegmentPointsTo 0 none -∗
      WP (Expr.running next : Expr α) @ s; E {{ Φ }}) -∗
      WP (Expr.running current : Expr α) @ s; E {{ Φ }} := by
  dsimp only
  iintro >Hsegment Hwp
  iapply wp_lift_step rfl
  iintro %store %ns %obs %obs' %nt Hσ
  imod stateInterp_dataSegment_facts_frame store ns (obs ++ obs') nt
      0 (some bytes) $$ [$Hσ $Hsegment] with
    ⟨Hσ, Hsegment, %hsegment⟩
  have hisSome :
      (store.wasm.dataSegments[0]?).isSome = true := by
    rw [hsegment]
    rfl
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro
    cases s <;> simp only [Stuckness.MaybeReducible]
    exact ⟨[.instruction (.dataDrop 0)],
      .running ⟨⟨params, localValues, values⟩,
        code, arity, remainder, controls, calls⟩,
      { store with wasm :=
          { store.wasm with dataSegments :=
              store.wasm.dataSegments.set 0 none } },
      [], ⟨rfl, _, rfl, Step.dataDrop hisSome⟩⟩
  iintro !> %e₂ %store₂ %forks %Hstep Hcredit
  rcases Hstep with ⟨hforks, kind, hobs, wasmStep⟩
  change forks = [] at hforks
  subst forks
  subst obs
  have expectedStep : Step
      ⟨.running
        ⟨⟨params, localValues, values⟩,
          .dataDrop 0 :: code, arity, remainder, controls, calls⟩, store⟩
      (.instruction (.dataDrop 0))
      ⟨.running
        ⟨⟨params, localValues, values⟩,
          code, arity, remainder, controls, calls⟩,
        { store with wasm :=
            { store.wasm with dataSegments :=
                store.wasm.dataSegments.set 0 none } }⟩ :=
    Step.dataDrop hisSome
  obtain ⟨rfl, hconfig⟩ := step_deterministic expectedStep wasmStep
  have parts := Config.mk.inj hconfig
  have hexpr := parts.1
  have hstore := parts.2
  simp only at hexpr hstore
  subst e₂
  subst store₂
  simp only [List.length_nil, Nat.add_zero, Iris.Algebra.BigOpL.bigOpL_nil]
  imod stateInterp_dataSegment_drop store ns
      ([.instruction (.dataDrop 0)] ++ obs') nt 0 (some bytes) $$
      [$Hσ $Hsegment] with ⟨Hσ, Hsegment⟩
  imod Hclose
  imodintro
  isplitl [Hσ]
  · iexact Hσ
  isplitl [Hwp Hsegment]
  · iapply Hwp
    iexact Hsegment
  · itrivial

/-- Primitive Iris rule for `elem.drop`. A live element-segment fragment is
consumed and replaced by ownership of its dropped physical state. -/
theorem wp_elemDrop
    {params localValues values : List Value}
    {elementIndex : Nat} {entries : List (Option Nat)}
    {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame} :
    let current : ThreadState α :=
      ⟨⟨params, localValues, values⟩,
        .elemDrop elementIndex :: code,
        arity, remainder, controls, calls⟩
    let next : ThreadState α :=
      ⟨⟨params, localValues, values⟩,
        code, arity, remainder, controls, calls⟩
    ▷ elementSegmentPointsTo elementIndex (some entries) -∗
    ▷ (elementSegmentPointsTo elementIndex none -∗
      WP (Expr.running next : Expr α) @ s; E {{ Φ }}) -∗
      WP (Expr.running current : Expr α) @ s; E {{ Φ }} := by
  dsimp only
  iintro >Hsegment Hwp
  iapply wp_lift_step rfl
  iintro %store %ns %obs %obs' %nt Hσ
  imod stateInterp_elementSegment_facts_frame
      store ns (obs ++ obs') nt elementIndex (some entries) $$
      [$Hσ $Hsegment] with
    ⟨Hσ, Hsegment, %hsegment⟩
  have hisSome :
      (store.wasm.elementSegments[elementIndex]?).isSome = true := by
    rw [hsegment]
    rfl
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro
    cases s <;> simp only [Stuckness.MaybeReducible]
    exact ⟨[.instruction (.elemDrop elementIndex)],
      .running ⟨⟨params, localValues, values⟩,
        code, arity, remainder, controls, calls⟩,
      { store with wasm :=
          { store.wasm with elementSegments :=
              store.wasm.elementSegments.set elementIndex none } },
      [], ⟨rfl, _, rfl, Step.elemDrop hisSome⟩⟩
  iintro !> %e₂ %store₂ %forks %Hstep Hcredit
  rcases Hstep with ⟨hforks, kind, hobs, wasmStep⟩
  change forks = [] at hforks
  subst forks
  subst obs
  have expectedStep : Step
      ⟨.running
        ⟨⟨params, localValues, values⟩,
          .elemDrop elementIndex :: code,
          arity, remainder, controls, calls⟩, store⟩
      (.instruction (.elemDrop elementIndex))
      ⟨.running
        ⟨⟨params, localValues, values⟩,
          code, arity, remainder, controls, calls⟩,
        { store with wasm :=
            { store.wasm with elementSegments :=
                store.wasm.elementSegments.set elementIndex none } }⟩ :=
    Step.elemDrop hisSome
  obtain ⟨rfl, hconfig⟩ := step_deterministic expectedStep wasmStep
  have parts := Config.mk.inj hconfig
  have hexpr := parts.1
  have hstore := parts.2
  simp only at hexpr hstore
  subst e₂
  subst store₂
  simp only [List.length_nil, Nat.add_zero,
    Iris.Algebra.BigOpL.bigOpL_nil]
  imod stateInterp_elementSegment_drop store ns
      ([.instruction (.elemDrop elementIndex)] ++ obs') nt
      elementIndex (some entries) $$ [$Hσ $Hsegment] with
    ⟨Hσ, Hsegment⟩
  imod Hclose
  imodintro
  isplitl [Hσ]
  · iexact Hσ
  isplitl [Hwp Hsegment]
  · iapply Hwp
    iexact Hsegment
  · itrivial

/-- Initialize a table range from a live element segment. Runtime-module
ownership fixes the instantiated reference values while element and table
fragments connect both reads and the destination update to physical state. -/
theorem wp_tableInitLive
    (runtimeModule : Module)
    {params localValues values : List Value}
    {tableIndex elementIndex destinationNat : Nat}
    {destination : Value} {source length : UInt32}
    {entries : List (Option Nat)} {table : TableInst}
    {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame}
    (hdestination : destination.addrNat? = some destinationNat)
    (hsourceBound :
      source.toNat + length.toNat ≤
        ((runtimeModule.elements[elementIndex]?.map
          ElementSegment.values).getD []).length)
    (hdestinationBound :
      destinationNat + length.toNat ≤ table.length) :
    let segmentValues :=
      (runtimeModule.elements[elementIndex]?.map
        ElementSegment.values).getD []
    let newTable :=
      listWriteAt table destinationNat
        ((segmentValues.drop source.toNat).take length.toNat)
    let current : ThreadState α :=
      ⟨⟨params, localValues,
          .i32 length :: .i32 source :: destination :: values⟩,
        .tableInit tableIndex elementIndex :: code,
        arity, remainder, controls, calls⟩
    let next : ThreadState α :=
      ⟨⟨params, localValues, values⟩,
        code, arity, remainder, controls, calls⟩
    (tablePointsTo tableIndex table ∗
      elementSegmentPointsTo elementIndex (some entries) ∗
      runtimeModuleOwn runtimeModule) -∗
    ▷ (tablePointsTo tableIndex newTable -∗
      elementSegmentPointsTo elementIndex (some entries) -∗
      runtimeModuleOwn runtimeModule -∗
      WP (Expr.running next : Expr α) @ s; E {{ Φ }}) -∗
      WP (Expr.running current : Expr α) @ s; E {{ Φ }} := by
  dsimp only
  iintro ⟨Htable, Hsegment, Hruntime⟩ Hwp
  iapply wp_lift_step rfl
  iintro %store %ns %obs %obs' %nt Hσ
  ihave %HtablePhysical :
      ⌜store.wasm.tables[tableIndex]? = some table⌝ $$ [Hσ Htable]
  · imod stateInterp_table_facts_frame store ns (obs ++ obs') nt
        tableIndex table $$ [$Hσ $Htable] with
      ⟨Hσ, Htable, %HtablePhysical⟩
    ipureintro
    exact HtablePhysical
  ihave %HsegmentPhysical :
      ⌜store.wasm.elementSegments[elementIndex]? =
        some (some entries)⌝ $$ [Hσ Hsegment]
  · imod stateInterp_elementSegment_facts_frame
        store ns (obs ++ obs') nt elementIndex (some entries) $$
        [$Hσ $Hsegment] with
      ⟨Hσ, Hsegment, %HsegmentPhysical⟩
    ipureintro
    exact HsegmentPhysical
  ihave %Hmodule : ⌜store.runtime.module = runtimeModule⌝ $$
      [Hσ Hruntime]
  · imod stateInterp_runtimeModule_agree store ns (obs ++ obs') nt
        runtimeModule $$ [$Hσ $Hruntime] with %Hmodule
    ipureintro
    exact Hmodule
  let segmentValues :=
    (runtimeModule.elements[elementIndex]?.map
      ElementSegment.values).getD []
  have hvalues :
      segmentValues =
        _root_.Wasm.SmallStep.elementSegmentValues
          store elementIndex (some entries) := by
    simp [segmentValues, elementSegmentValues, Hmodule]
  have hsourceBound' :
      source.toNat + length.toNat ≤ segmentValues.length := by
    exact hsourceBound
  let newTable :=
    listWriteAt table destinationNat
      ((segmentValues.drop source.toNat).take length.toNat)
  let updatedStore : MachineStore α :=
    { store with wasm :=
        { store.wasm with tables :=
            (listSetAt store.wasm.tables tableIndex newTable) } }
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro
    cases s <;> simp only [Stuckness.MaybeReducible]
    exact ⟨[.instruction (.tableInit tableIndex elementIndex)],
      .running ⟨⟨params, localValues, values⟩,
        code, arity, remainder, controls, calls⟩,
      updatedStore, [],
      ⟨rfl, _, rfl,
        Step.tableInit hdestination HtablePhysical HsegmentPhysical
          hvalues hsourceBound' hdestinationBound⟩⟩
  iintro !> %e₂ %store₂ %forks %Hstep Hcredit
  rcases Hstep with ⟨hforks, kind, hobs, wasmStep⟩
  change forks = [] at hforks
  subst forks
  subst obs
  have expectedStep : Step
      ⟨.running
        ⟨⟨params, localValues,
            .i32 length :: .i32 source :: destination :: values⟩,
          .tableInit tableIndex elementIndex :: code,
          arity, remainder, controls, calls⟩,
        store⟩
      (.instruction (.tableInit tableIndex elementIndex))
      ⟨.running
        ⟨⟨params, localValues, values⟩,
          code, arity, remainder, controls, calls⟩,
        updatedStore⟩ :=
    Step.tableInit hdestination HtablePhysical HsegmentPhysical
      hvalues hsourceBound' hdestinationBound
  obtain ⟨rfl, hconfig⟩ := step_deterministic expectedStep wasmStep
  have parts := Config.mk.inj hconfig
  have hexpr := parts.1
  have hstore := parts.2
  simp only at hexpr hstore
  subst e₂
  subst store₂
  simp only [List.length_nil, Nat.add_zero,
    Iris.Algebra.BigOpL.bigOpL_nil]
  imod stateInterp_table_set store ns
      ([.instruction (.tableInit tableIndex elementIndex)] ++ obs') nt
      tableIndex table newTable $$ [$Hσ $Htable] with
    ⟨Hσ, Htable⟩
  imod Hclose
  imodintro
  isplitl [Hσ]
  · iexact Hσ
  isplitl [Hwp Htable Hsegment Hruntime]
  · iapply Hwp $$ Htable Hsegment Hruntime
  · itrivial

/-- Primitive Iris rule for the overlapping four-byte copy from address 0 to
address 2. One eight-byte owner represents the aliased source/destination
footprint, and the postcondition exposes the memmove result. -/
theorem wp_copy2_zero_four
    {params localValues values : List Value}
    {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame} :
    let current : ThreadState α :=
      ⟨⟨params, localValues,
          .i32 4 :: .i32 0 :: .i32 2 :: values⟩,
        .memoryCopy :: code, arity, remainder, controls, calls⟩
    let next : ThreadState α :=
      ⟨⟨params, localValues, values⟩,
        code, arity, remainder, controls, calls⟩
    ▷ pointsTo_u64 0 0x8877665544332211 -∗
    ▷ (pointsTo_u64 0 0x8877443322112211 -∗
      WP (Expr.running next : Expr α) @ s; E {{ Φ }}) -∗
      WP (Expr.running current : Expr α) @ s; E {{ Φ }} := by
  dsimp only
  iintro >Hword Hwp
  iapply wp_lift_step rfl
  iintro %store %ns %obs %obs' %nt Hσ
  ihave %Hfacts :
      ⌜store.wasm.mem.read64 0 = 0x8877665544332211 ∧
        8 ≤ store.wasm.mem.pages * 65536⌝ $$ [Hσ Hword]
  · imod stateInterp_pointsTo_u64_facts store ns (obs ++ obs') nt
      0 0x8877665544332211 rfl rfl rfl rfl rfl rfl rfl $$
      [$Hσ $Hword] with %Hfacts
    ipureintro
    exact Hfacts
  have hsource : 4 ≤ store.wasm.mem.pages * 65536 := by omega
  have hdestination : 2 + 4 ≤ store.wasm.mem.pages * 65536 := by omega
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro
    cases s <;> simp only [Stuckness.MaybeReducible]
    exact ⟨[.instruction .memoryCopy],
      .running ⟨⟨params, localValues, values⟩,
        code, arity, remainder, controls, calls⟩,
      { store with wasm :=
          { store.wasm with mem := store.wasm.mem.copy 2 0 4 } },
      [], ⟨rfl, _, rfl, Step.memoryCopy32 hdestination hsource⟩⟩
  iintro !> %e₂ %store₂ %forks %Hstep Hcredit
  rcases Hstep with ⟨hforks, kind, hobs, wasmStep⟩
  change forks = [] at hforks
  subst forks
  subst obs
  have expectedStep : Step
      ⟨.running
        ⟨⟨params, localValues, .i32 4 :: .i32 0 :: .i32 2 :: values⟩,
          .memoryCopy :: code, arity, remainder, controls, calls⟩, store⟩
      (.instruction .memoryCopy)
      ⟨.running
        ⟨⟨params, localValues, values⟩,
          code, arity, remainder, controls, calls⟩,
        { store with wasm :=
            { store.wasm with mem := store.wasm.mem.copy 2 0 4 } }⟩ :=
    Step.memoryCopy32 hdestination hsource
  obtain ⟨rfl, hconfig⟩ := step_deterministic expectedStep wasmStep
  have parts := Config.mk.inj hconfig
  have hexpr := parts.1
  have hstore := parts.2
  simp only at hexpr hstore
  subst e₂
  subst store₂
  simp only [List.length_nil, Nat.add_zero, Iris.Algebra.BigOpL.bigOpL_nil]
  imod stateInterp_copy2_zero_four store ns
      ([.instruction .memoryCopy] ++ obs') nt $$
      [$Hσ $Hword] with ⟨Hσ, Hword⟩
  imod Hclose
  imodintro
  isplitl [Hσ]
  · iexact Hσ
  isplitl [Hwp Hword]
  · iapply Hwp
    iexact Hword
  · itrivial

/-- Primitive Iris rule for an aligned four-byte copy from address 0 to 8.
Both source and destination ranges are owned; source ownership is preserved
and destination ownership receives the copied word. -/
theorem wp_copy8_zero_four
    {params localValues values : List Value}
    {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame} (oldDestination : UInt32) :
    let current : ThreadState α :=
      ⟨⟨params, localValues,
          .i32 4 :: .i32 0 :: .i32 8 :: values⟩,
        .memoryCopy :: code, arity, remainder, controls, calls⟩
    let next : ThreadState α :=
      ⟨⟨params, localValues, values⟩,
        code, arity, remainder, controls, calls⟩
    ▷ (pointsTo_u32 0 0x04030201 ∗
      pointsTo_u32 8 oldDestination) -∗
    ▷ (pointsTo_u32 0 0x04030201 ∗
      pointsTo_u32 8 0x04030201 -∗
      WP (Expr.running next : Expr α) @ s; E {{ Φ }}) -∗
      WP (Expr.running current : Expr α) @ s; E {{ Φ }} := by
  dsimp only
  iintro >⟨Hsource, Hdestination⟩ Hwp
  iapply wp_lift_step rfl
  iintro %store %ns %obs %obs' %nt Hσ
  ihave %HsourceFacts :
      ⌜store.wasm.mem.read32 0 = 0x04030201 ∧
        4 ≤ store.wasm.mem.pages * 65536⌝ $$ [Hσ Hsource]
  · imod stateInterp_pointsTo_u32_facts store ns (obs ++ obs') nt
      0 0x04030201 rfl rfl rfl $$ [$Hσ $Hsource] with %HsourceFacts
    ipureintro
    exact HsourceFacts
  ihave %HdestinationFacts :
      ⌜store.wasm.mem.read32 8 = oldDestination ∧
        12 ≤ store.wasm.mem.pages * 65536⌝ $$ [Hσ Hdestination]
  · imod stateInterp_pointsTo_u32_facts store ns (obs ++ obs') nt
      8 oldDestination rfl rfl rfl $$ [$Hσ $Hdestination]
      with %HdestinationFacts
    ipureintro
    exact HdestinationFacts
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro
    cases s <;> simp only [Stuckness.MaybeReducible]
    exact ⟨[.instruction .memoryCopy],
      .running ⟨⟨params, localValues, values⟩,
        code, arity, remainder, controls, calls⟩,
      { store with wasm :=
          { store.wasm with mem := store.wasm.mem.copy 8 0 4 } },
      [], ⟨rfl, _, rfl,
        Step.memoryCopy32 HdestinationFacts.2 HsourceFacts.2⟩⟩
  iintro !> %e₂ %store₂ %forks %Hstep Hcredit
  rcases Hstep with ⟨hforks, kind, hobs, wasmStep⟩
  change forks = [] at hforks
  subst forks
  subst obs
  have expectedStep : Step
      ⟨.running
        ⟨⟨params, localValues, .i32 4 :: .i32 0 :: .i32 8 :: values⟩,
          .memoryCopy :: code, arity, remainder, controls, calls⟩, store⟩
      (.instruction .memoryCopy)
      ⟨.running
        ⟨⟨params, localValues, values⟩,
          code, arity, remainder, controls, calls⟩,
        { store with wasm :=
            { store.wasm with mem := store.wasm.mem.copy 8 0 4 } }⟩ :=
    Step.memoryCopy32 HdestinationFacts.2 HsourceFacts.2
  obtain ⟨rfl, hconfig⟩ := step_deterministic expectedStep wasmStep
  have parts := Config.mk.inj hconfig
  have hexpr := parts.1
  have hstore := parts.2
  simp only at hexpr hstore
  subst e₂
  subst store₂
  simp only [List.length_nil, Nat.add_zero, Iris.Algebra.BigOpL.bigOpL_nil]
  imod stateInterp_copy8_zero_four store ns
      ([.instruction .memoryCopy] ++ obs') nt oldDestination $$
      [$Hσ $Hsource $Hdestination] with
      ⟨Hσ, Hsource, Hdestination⟩
  imod Hclose
  imodintro
  isplitl [Hσ]
  · iexact Hσ
  isplitl [Hwp Hsource Hdestination]
  · iapply Hwp
    iframe
  · itrivial

set_option maxHeartbeats 4000000 in
/-- Call-stack-polymorphic proof of the sixteen instructions before
`Project.SwapElements.func2`'s final `ret`. The continuation receives the
updated ownership and decides whether `ret` finishes a top-level invocation or
resumes a suspended caller. -/
theorem wp_swapElementsFunc2Prefix
    (ptrA ptrB : UInt32) (oldScratch oldA oldB : UInt64)
    (hroomA : ptrA.toNat + 8 ≤ 4294967296)
    (hroomB : ptrB.toNat + 8 ≤ 4294967296)
    {calls : List CallFrame} :
    (globalPointsTo 0 (.i32 1048560) ∗
      pointsTo_u64 1048552 oldScratch ∗
      pointsTo_u64 ptrA oldA ∗ pointsTo_u64 ptrB oldB) ∗
    ▷^[16] ((globalPointsTo 0 (.i32 1048560) ∗
      pointsTo_u64 1048552 oldA ∗
      pointsTo_u64 ptrA oldB ∗ pointsTo_u64 ptrB oldA) -∗
      WP (.running
        ⟨⟨[.i32 ptrA, .i32 ptrB], [.i32 1048544], []⟩,
          [.ret], 0, [], [], calls⟩ : Expr α) @ s; E {{ Φ }}) ⊢
    WP (.running
      ⟨⟨[.i32 ptrA, .i32 ptrB], [.i32 0], []⟩,
        [ .globalGet 0, .const 16, .sub, .localSet 2,
          .localGet 2, .localGet 0, .load64 0, .store64 8,
          .localGet 0, .localGet 1, .load64 0, .store64 0,
          .localGet 1, .localGet 2, .load64 8, .store64 0, .ret ],
        0, [], [], calls⟩ : Expr α) @ s; E {{ Φ }} := by
  have ha1 : (ptrA + 1).toNat = ptrA.toNat + 1 := by
    simpa using UInt32.add_ofNat_toNat_noWrap ptrA 1 (by omega) (by omega)
  have ha2 : (ptrA + 2).toNat = ptrA.toNat + 2 := by
    simpa using UInt32.add_ofNat_toNat_noWrap ptrA 2 (by omega) (by omega)
  have ha3 : (ptrA + 3).toNat = ptrA.toNat + 3 := by
    simpa using UInt32.add_ofNat_toNat_noWrap ptrA 3 (by omega) (by omega)
  have ha4 : (ptrA + 4).toNat = ptrA.toNat + 4 := by
    simpa using UInt32.add_ofNat_toNat_noWrap ptrA 4 (by omega) (by omega)
  have ha5 : (ptrA + 5).toNat = ptrA.toNat + 5 := by
    simpa using UInt32.add_ofNat_toNat_noWrap ptrA 5 (by omega) (by omega)
  have ha6 : (ptrA + 6).toNat = ptrA.toNat + 6 := by
    simpa using UInt32.add_ofNat_toNat_noWrap ptrA 6 (by omega) (by omega)
  have ha7 : (ptrA + 7).toNat = ptrA.toNat + 7 := by
    simpa using UInt32.add_ofNat_toNat_noWrap ptrA 7 (by omega) (by omega)
  have hb1 : (ptrB + 1).toNat = ptrB.toNat + 1 := by
    simpa using UInt32.add_ofNat_toNat_noWrap ptrB 1 (by omega) (by omega)
  have hb2 : (ptrB + 2).toNat = ptrB.toNat + 2 := by
    simpa using UInt32.add_ofNat_toNat_noWrap ptrB 2 (by omega) (by omega)
  have hb3 : (ptrB + 3).toNat = ptrB.toNat + 3 := by
    simpa using UInt32.add_ofNat_toNat_noWrap ptrB 3 (by omega) (by omega)
  have hb4 : (ptrB + 4).toNat = ptrB.toNat + 4 := by
    simpa using UInt32.add_ofNat_toNat_noWrap ptrB 4 (by omega) (by omega)
  have hb5 : (ptrB + 5).toNat = ptrB.toNat + 5 := by
    simpa using UInt32.add_ofNat_toNat_noWrap ptrB 5 (by omega) (by omega)
  have hb6 : (ptrB + 6).toNat = ptrB.toNat + 6 := by
    simpa using UInt32.add_ofNat_toNat_noWrap ptrB 6 (by omega) (by omega)
  have hb7 : (ptrB + 7).toNat = ptrB.toNat + 7 := by
    simpa using UInt32.add_ofNat_toNat_noWrap ptrB 7 (by omega) (by omega)
  iintro ⟨⟨Hglobal, Hscratch, HA, HB⟩, Hdone⟩
  iapply wp_globalGet $$ Hglobal
  inext
  iintro Hglobal
  iapply wp_const
  inext
  iapply wp_sub
  inext
  iapply wp_localSet rfl
  inext
  simp only [UInt32.reduceSub, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub, List.set]
  iapply wp_localGet rfl
  inext
  iapply wp_localGet rfl
  inext
  ihave HALater : ▷ pointsTo_u64 (ptrA + 0) oldA $$ [HA]
  · inext
    rw [UInt32.add_zero]
    iexact HA
  iapply wp_load64 oldA (by simp)
    (by simpa using ha1) (by simpa using ha2) (by simpa using ha3)
    (by simpa using ha4) (by simpa using ha5) (by simpa using ha6)
    (by simpa using ha7) $$ HALater
  inext
  iintro HA
  ihave HscratchLater :
      ▷ pointsTo_u64 ((1048544 : UInt32) + 8) oldScratch $$ [Hscratch]
  · inext
    rw [show (1048544 : UInt32) + 8 = 1048552 from rfl]
    iexact Hscratch
  iapply wp_store64 oldScratch rfl rfl rfl rfl rfl rfl rfl rfl $$
    HscratchLater
  inext
  iintro Hscratch
  iapply wp_localGet rfl
  inext
  iapply wp_localGet rfl
  inext
  ihave HBLater : ▷ pointsTo_u64 (ptrB + 0) oldB $$ [HB]
  · inext
    rw [UInt32.add_zero]
    iexact HB
  iapply wp_load64 oldB (by simp)
    (by simpa using hb1) (by simpa using hb2) (by simpa using hb3)
    (by simpa using hb4) (by simpa using hb5) (by simpa using hb6)
    (by simpa using hb7) $$ HBLater
  inext
  iintro HB
  ihave HALater : ▷ pointsTo_u64 (ptrA + 0) oldA $$ [HA]
  · inext
    rw [UInt32.add_zero]
    iexact HA
  iapply wp_store64 oldA (by simp)
    (by simpa using ha1) (by simpa using ha2) (by simpa using ha3)
    (by simpa using ha4) (by simpa using ha5) (by simpa using ha6)
    (by simpa using ha7) $$ HALater
  inext
  iintro HA
  iapply wp_localGet rfl
  inext
  iapply wp_localGet rfl
  inext
  ihave HscratchLater :
      ▷ pointsTo_u64 ((1048544 : UInt32) + 8) oldA $$ [Hscratch]
  · inext
    rw [show (1048544 : UInt32) + 8 = 1048552 from rfl]
    iexact Hscratch
  iapply wp_load64 oldA rfl rfl rfl rfl rfl rfl rfl rfl $$
    HscratchLater
  inext
  iintro Hscratch
  ihave HBLater : ▷ pointsTo_u64 (ptrB + 0) oldB $$ [HB]
  · inext
    rw [UInt32.add_zero]
    iexact HB
  iapply wp_store64 oldB (by simp)
    (by simpa using hb1) (by simpa using hb2) (by simpa using hb3)
    (by simpa using hb4) (by simpa using hb5) (by simpa using hb6)
    (by simpa using hb7) $$ HBLater
  inext
  iintro HB
  iapply Hdone
  simp only [UInt32.add_zero, UInt32.reduceAdd]
  iframe

/-- Aliasing specialization of the generated exchange leaf. When both
pointers are equal there is only one exclusive eight-byte ownership token;
the two stores leave that word unchanged while the scratch word receives its
value. -/
theorem wp_swapElementsFunc2AliasPrefix
    (ptr : UInt32) (oldScratch oldValue : UInt64)
    (hroom : ptr.toNat + 8 ≤ 4294967296)
    {calls : List CallFrame} :
    (globalPointsTo 0 (.i32 1048560) ∗
      pointsTo_u64 1048552 oldScratch ∗ pointsTo_u64 ptr oldValue) ∗
    ▷^[16] ((globalPointsTo 0 (.i32 1048560) ∗
      pointsTo_u64 1048552 oldValue ∗ pointsTo_u64 ptr oldValue) -∗
      WP (.running
        ⟨⟨[.i32 ptr, .i32 ptr], [.i32 1048544], []⟩,
          [.ret], 0, [], [], calls⟩ : Expr α) @ s; E {{ Φ }}) ⊢
    WP (.running
      ⟨⟨[.i32 ptr, .i32 ptr], [.i32 0], []⟩,
        [ .globalGet 0, .const 16, .sub, .localSet 2,
          .localGet 2, .localGet 0, .load64 0, .store64 8,
          .localGet 0, .localGet 1, .load64 0, .store64 0,
          .localGet 1, .localGet 2, .load64 8, .store64 0, .ret ],
        0, [], [], calls⟩ : Expr α) @ s; E {{ Φ }} := by
  have h1 : (ptr + 1).toNat = ptr.toNat + 1 := by
    simpa using UInt32.add_ofNat_toNat_noWrap ptr 1 (by omega) (by omega)
  have h2 : (ptr + 2).toNat = ptr.toNat + 2 := by
    simpa using UInt32.add_ofNat_toNat_noWrap ptr 2 (by omega) (by omega)
  have h3 : (ptr + 3).toNat = ptr.toNat + 3 := by
    simpa using UInt32.add_ofNat_toNat_noWrap ptr 3 (by omega) (by omega)
  have h4 : (ptr + 4).toNat = ptr.toNat + 4 := by
    simpa using UInt32.add_ofNat_toNat_noWrap ptr 4 (by omega) (by omega)
  have h5 : (ptr + 5).toNat = ptr.toNat + 5 := by
    simpa using UInt32.add_ofNat_toNat_noWrap ptr 5 (by omega) (by omega)
  have h6 : (ptr + 6).toNat = ptr.toNat + 6 := by
    simpa using UInt32.add_ofNat_toNat_noWrap ptr 6 (by omega) (by omega)
  have h7 : (ptr + 7).toNat = ptr.toNat + 7 := by
    simpa using UInt32.add_ofNat_toNat_noWrap ptr 7 (by omega) (by omega)
  iintro ⟨⟨Hglobal, Hscratch, Hcell⟩, Hdone⟩
  iapply wp_globalGet $$ Hglobal
  inext
  iintro Hglobal
  iapply wp_const
  inext
  iapply wp_sub
  inext
  iapply wp_localSet rfl
  inext
  simp only [UInt32.reduceSub, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub, List.set]
  iapply wp_localGet rfl
  inext
  iapply wp_localGet rfl
  inext
  ihave HcellLater : ▷ pointsTo_u64 (ptr + 0) oldValue $$ [Hcell]
  · inext
    rw [UInt32.add_zero]
    iexact Hcell
  iapply wp_load64 oldValue (by simp)
    (by simpa using h1) (by simpa using h2) (by simpa using h3)
    (by simpa using h4) (by simpa using h5) (by simpa using h6)
    (by simpa using h7) $$ HcellLater
  inext
  iintro Hcell
  ihave HscratchLater :
      ▷ pointsTo_u64 ((1048544 : UInt32) + 8) oldScratch $$ [Hscratch]
  · inext
    rw [show (1048544 : UInt32) + 8 = 1048552 from rfl]
    iexact Hscratch
  iapply wp_store64 oldScratch rfl rfl rfl rfl rfl rfl rfl rfl $$
    HscratchLater
  inext
  iintro Hscratch
  iapply wp_localGet rfl
  inext
  iapply wp_localGet rfl
  inext
  ihave HcellLater : ▷ pointsTo_u64 (ptr + 0) oldValue $$ [Hcell]
  · inext
    rw [UInt32.add_zero]
    iexact Hcell
  iapply wp_load64 oldValue (by simp)
    (by simpa using h1) (by simpa using h2) (by simpa using h3)
    (by simpa using h4) (by simpa using h5) (by simpa using h6)
    (by simpa using h7) $$ HcellLater
  inext
  iintro Hcell
  ihave HcellLater : ▷ pointsTo_u64 (ptr + 0) oldValue $$ [Hcell]
  · inext
    rw [UInt32.add_zero]
    iexact Hcell
  iapply wp_store64 oldValue (by simp)
    (by simpa using h1) (by simpa using h2) (by simpa using h3)
    (by simpa using h4) (by simpa using h5) (by simpa using h6)
    (by simpa using h7) $$ HcellLater
  inext
  iintro Hcell
  iapply wp_localGet rfl
  inext
  iapply wp_localGet rfl
  inext
  ihave HscratchLater :
      ▷ pointsTo_u64 ((1048544 : UInt32) + 8) oldValue $$ [Hscratch]
  · inext
    rw [show (1048544 : UInt32) + 8 = 1048552 from rfl]
    iexact Hscratch
  iapply wp_load64 oldValue rfl rfl rfl rfl rfl rfl rfl rfl $$
    HscratchLater
  inext
  iintro Hscratch
  ihave HcellLater : ▷ pointsTo_u64 (ptr + 0) oldValue $$ [Hcell]
  · inext
    rw [UInt32.add_zero]
    iexact Hcell
  iapply wp_store64 oldValue (by simp)
    (by simpa using h1) (by simpa using h2) (by simpa using h3)
    (by simpa using h4) (by simpa using h5) (by simpa using h6)
    (by simpa using h7) $$ HcellLater
  inext
  iintro Hcell
  iapply Hdone
  simp only [UInt32.add_zero, UInt32.reduceAdd]
  iframe

/-- Top-level specialization of `wp_swapElementsFunc2Prefix`. -/
theorem wp_swapElementsFunc2
    (ptrA ptrB : UInt32) (oldScratch oldA oldB : UInt64)
    (hroomA : ptrA.toNat + 8 ≤ 4294967296)
    (hroomB : ptrB.toNat + 8 ≤ 4294967296) :
    globalPointsTo 0 (.i32 1048560) ∗
      pointsTo_u64 1048552 oldScratch ∗
      pointsTo_u64 ptrA oldA ∗ pointsTo_u64 ptrB oldB ⊢
    WP (.running
      ⟨⟨[.i32 ptrA, .i32 ptrB], [.i32 0], []⟩,
        [ .globalGet 0, .const 16, .sub, .localSet 2,
          .localGet 2, .localGet 0, .load64 0, .store64 8,
          .localGet 0, .localGet 1, .load64 0, .store64 0,
          .localGet 1, .localGet 2, .load64 8, .store64 0, .ret ],
        0, [], [], []⟩ : Expr α) @ s; E
      {{ result, ⌜result = []⌝ ∗
        globalPointsTo 0 (.i32 1048560) ∗
        pointsTo_u64 1048552 oldA ∗
        pointsTo_u64 ptrA oldB ∗ pointsTo_u64 ptrB oldA }} := by
  iintro Hresources
  iapply wp_swapElementsFunc2Prefix ptrA ptrB oldScratch oldA oldB
    hroomA hroomB (calls := [])
  isplitl [Hresources]
  · iexact Hresources
  · inext
    iintro Hresources
    iapply wp_returnFromFunction
    inext
    iapply wp_value'
    isplitr
    · ipureintro
      rfl
    · iexact Hresources

/-- Top-level one-cell specialization for equal exchange pointers. -/
theorem wp_swapElementsFunc2Alias
    (ptr : UInt32) (oldScratch oldValue : UInt64)
    (hroom : ptr.toNat + 8 ≤ 4294967296) :
    globalPointsTo 0 (.i32 1048560) ∗
      pointsTo_u64 1048552 oldScratch ∗ pointsTo_u64 ptr oldValue ⊢
    WP (.running
      ⟨⟨[.i32 ptr, .i32 ptr], [.i32 0], []⟩,
        [ .globalGet 0, .const 16, .sub, .localSet 2,
          .localGet 2, .localGet 0, .load64 0, .store64 8,
          .localGet 0, .localGet 1, .load64 0, .store64 0,
          .localGet 1, .localGet 2, .load64 8, .store64 0, .ret ],
        0, [], [], []⟩ : Expr α) @ s; E
      {{ result, ⌜result = []⌝ ∗
        globalPointsTo 0 (.i32 1048560) ∗
        pointsTo_u64 1048552 oldValue ∗
        pointsTo_u64 ptr oldValue }} := by
  iintro Hresources
  iapply wp_swapElementsFunc2AliasPrefix ptr oldScratch oldValue
    hroom (calls := [])
  isplitl [Hresources]
  · iexact Hresources
  · inext
    iintro Hresources
    iapply wp_returnFromFunction
    inext
    iapply wp_value'
    isplitr
    · ipureintro
      rfl
    · iexact Hresources

/-- Small-step Iris contract for the exact generated body of
`Project.SwapElements.func3`. It spills `len` and `ptr` into two adjacent
32-bit words and returns no Wasm values. -/
theorem wp_swapElementsFunc3
    (oldPtr oldLen ptr len : UInt32) :
    pointsTo_u32 1048568 oldPtr ∗ pointsTo_u32 1048572 oldLen ⊢
    WP (.running
      ⟨⟨[.i32 1048568, .i32 ptr, .i32 len, .i32 1048652], [], []⟩,
        [ .localGet 0, .localGet 2, .store32 4,
          .localGet 0, .localGet 1, .store32 0, .ret ],
        0, [], [], []⟩ : Expr α) @ s; E
      {{ result, ⌜result = []⌝ ∗
        pointsTo_u32 1048568 ptr ∗ pointsTo_u32 1048572 len }} := by
  iintro ⟨Hptr, Hlen⟩
  iapply wp_localGet rfl
  inext
  iapply wp_localGet rfl
  inext
  ihave HlenLater :
      ▷ pointsTo_u32 ((1048568 : UInt32) + 4) oldLen $$ [Hlen]
  · inext
    rw [show (1048568 : UInt32) + 4 = 1048572 from rfl]
    iexact Hlen
  iapply wp_store32 oldLen rfl rfl rfl rfl $$ HlenLater
  inext
  iintro Hlen
  iapply wp_localGet rfl
  inext
  iapply wp_localGet rfl
  inext
  ihave HptrLater :
      ▷ pointsTo_u32 ((1048568 : UInt32) + 0) oldPtr $$ [Hptr]
  · inext
    rw [UInt32.add_zero]
    iexact Hptr
  iapply wp_store32 oldPtr rfl rfl rfl rfl $$ HptrLater
  inext
  iintro Hptr
  iapply wp_returnFromFunction
  inext
  iapply wp_value'
  isplitr
  · ipureintro
    rfl
  · isplitl [Hptr]
    · rw [UInt32.add_zero]
      iexact Hptr
    · rw [← show (1048568 : UInt32) + 4 = 1048572 from rfl]
      iexact Hlen

/-- End-to-end Iris contract for the hand-written byte-memory roundtrip used
by `Interpreter.Wasm.Examples.SmallStep`. -/
theorem wp_byteRoundtrip (oldByte : UInt8) :
    pointsTo (GF := WasmHeapGF) (H := WasmHeapMap)
      24 (DFrac.own 1) (some oldByte) ⊢
    WP (.running
      ⟨⟨[], [], []⟩,
        [ .const 24, .const 0x1234AB, .store8 0,
          .const 24, .load8U 0 ],
        1, [], [], []⟩ : Expr α) @ s; E
      {{ result, ⌜result = [.i32 0xAB]⌝ ∗
        pointsTo (GF := WasmHeapGF) (H := WasmHeapMap)
          24 (DFrac.own 1) (some (0xAB : UInt8)) }} := by
  iintro Hpt
  iapply wp_const
  inext
  iapply wp_const
  inext
  ihave HptLater :
      ▷ pointsTo (GF := WasmHeapGF) (H := WasmHeapMap)
        (24 + 0) (DFrac.own 1) (some oldByte) $$ [Hpt]
  · inext
    rw [UInt32.add_zero]
    iexact Hpt
  iapply wp_store8 oldByte rfl $$ HptLater
  inext
  iintro Hpt
  iapply wp_const
  inext
  ihave HptLater :
      ▷ pointsTo (GF := WasmHeapGF) (H := WasmHeapMap)
        (24 + 0) (DFrac.own 1) (some (0xAB : UInt8)) $$ [Hpt]
  · inext
    rw [show (0x1234AB : UInt32).toUInt8 = (0xAB : UInt8) by decide]
    iexact Hpt
  iapply wp_load8U (0xAB : UInt8) rfl $$ HptLater
  inext
  iintro Hpt
  iapply wp_finish
  inext
  iapply wp_value'
  isplitr
  · ipureintro
    rfl
  · rw [UInt32.add_zero]
    iexact Hpt

/-- End-to-end Iris contract for the hand-written 32-bit memory roundtrip.
The physical word and its four authoritative ghost bytes are updated by the
same `store32` transition. -/
theorem wp_wordRoundtrip (oldWord : UInt32) :
    pointsTo_u32 16 oldWord ⊢
    WP (.running
      ⟨⟨[], [], []⟩,
        [ .const 16, .const 0x12345678, .store32 0,
          .const 16, .load32 0 ],
        1, [], [], []⟩ : Expr α) @ s; E
      {{ result, ⌜result = [.i32 0x12345678]⌝ ∗
        pointsTo_u32 16 0x12345678 }} := by
  iintro Hword
  iapply wp_const
  inext
  iapply wp_const
  inext
  ihave HwordLater : ▷ pointsTo_u32 (16 + 0) oldWord $$ [Hword]
  · inext
    rw [UInt32.add_zero]
    iexact Hword
  iapply wp_store32 oldWord rfl rfl rfl rfl $$ HwordLater
  inext
  iintro Hword
  iapply wp_const
  inext
  ihave HwordLater : ▷ pointsTo_u32 (16 + 0) 0x12345678 $$ [Hword]
  · inext
    rw [UInt32.add_zero]
    iexact Hword
  iapply wp_load32 0x12345678 rfl rfl rfl rfl $$ HwordLater
  inext
  iintro Hword
  iapply wp_finish
  inext
  iapply wp_value'
  isplitr
  · ipureintro
    rfl
  · rw [UInt32.add_zero]
    iexact Hword

/-- End-to-end Iris contract for the four-byte `memory.fill` example. The
filled word is updated while ownership of the disjoint word at address 32 is
framed unchanged. -/
theorem wp_fillFourBytes (oldWord : UInt32) :
    pointsTo_u32 16 oldWord ∗ pointsTo_u32 32 0x12345678 ⊢
    WP (.running
      ⟨⟨[], [], []⟩,
        [ .const 16, .const 0xAB, .const 4, .memoryFill,
          .const 16, .load32 0,
          .const 32, .load32 0 ],
        2, [], [], []⟩ : Expr α) @ s; E
      {{ result,
        ⌜result = [.i32 0x12345678, .i32 0xABABABAB]⌝ ∗
        pointsTo_u32 16 0xABABABAB ∗
        pointsTo_u32 32 0x12345678 }} := by
  iintro ⟨H16, H32⟩
  iapply wp_const
  inext
  iapply wp_const
  inext
  iapply wp_const
  inext
  ihave H16Later : ▷ pointsTo_u32 16 oldWord $$ [H16]
  · inext
    iexact H16
  iapply wp_fill16_four_AB oldWord $$ H16Later
  inext
  iintro H16
  iapply wp_const
  inext
  ihave H16Later : ▷ pointsTo_u32 (16 + 0) 0xABABABAB $$ [H16]
  · inext
    rw [UInt32.add_zero]
    iexact H16
  iapply wp_load32 0xABABABAB rfl rfl rfl rfl $$ H16Later
  inext
  iintro H16
  iapply wp_const
  inext
  ihave H32Later : ▷ pointsTo_u32 (32 + 0) 0x12345678 $$ [H32]
  · inext
    rw [UInt32.add_zero]
    iexact H32
  iapply wp_load32 0x12345678 rfl rfl rfl rfl $$ H32Later
  inext
  iintro H32
  iapply wp_finish
  inext
  iapply wp_value'
  isplitr
  · ipureintro
    rfl
  · isplitl [H16]
    · rw [UInt32.add_zero]
      iexact H16
    · rw [UInt32.add_zero]
      iexact H32

/-- End-to-end Iris contract for an aligned four-byte copy. The source word
is preserved and the destination word receives the source value. -/
theorem wp_copyWord (oldDestination : UInt32) :
    pointsTo_u32 0 0x04030201 ∗
      pointsTo_u32 8 oldDestination ⊢
    WP (.running
      ⟨⟨[], [], []⟩,
        [ .const 8, .const 0, .const 4, .memoryCopy,
          .const 8, .load32 0 ],
        1, [], [], []⟩ : Expr α) @ s; E
      {{ result,
        ⌜result = [.i32 0x04030201]⌝ ∗
        pointsTo_u32 0 0x04030201 ∗
        pointsTo_u32 8 0x04030201 }} := by
  iintro ⟨Hsource, Hdestination⟩
  iapply wp_const
  inext
  iapply wp_const
  inext
  iapply wp_const
  inext
  ihave HwordsLater :
      ▷ (pointsTo_u32 0 0x04030201 ∗
        pointsTo_u32 8 oldDestination) $$ [Hsource Hdestination]
  · inext
    iframe
  iapply wp_copy8_zero_four oldDestination $$ HwordsLater
  inext
  iintro ⟨Hsource, Hdestination⟩
  iapply wp_const
  inext
  ihave HdestinationLater :
      ▷ pointsTo_u32 (8 + 0) 0x04030201 $$ [Hdestination]
  · inext
    rw [UInt32.add_zero]
    iexact Hdestination
  iapply wp_load32 0x04030201 rfl rfl rfl rfl $$ HdestinationLater
  inext
  iintro Hdestination
  iapply wp_finish
  inext
  iapply wp_value'
  isplitr
  · ipureintro
    rfl
  · isplitl [Hsource]
    · iexact Hsource
    · rw [UInt32.add_zero]
      iexact Hdestination

/-- End-to-end Iris contract for passive data initialization followed by
`data.drop`. The result exposes both the initialized physical word ownership
and authoritative knowledge that the segment has been consumed. -/
theorem wp_memoryInitDrop (oldWord : UInt32) :
    pointsTo_u32 16 oldWord ∗
      dataSegmentPointsTo 0 (some [1, 2, 3, 4]) ⊢
    WP (.running
      ⟨⟨[], [], []⟩,
        [ .const 16, .const 0, .const 4, .memoryInit 0,
          .dataDrop 0, .const 16, .load32 0 ],
        1, [], [], []⟩ : Expr α) @ s; E
      {{ result,
        ⌜result = [.i32 0x04030201]⌝ ∗
        pointsTo_u32 16 0x04030201 ∗
        dataSegmentPointsTo 0 none }} := by
  iintro ⟨Hword, Hsegment⟩
  iapply wp_const
  inext
  iapply wp_const
  inext
  iapply wp_const
  inext
  ihave HresourcesLater :
      ▷ (pointsTo_u32 16 oldWord ∗
        dataSegmentPointsTo 0 (some [1, 2, 3, 4])) $$
      [Hword Hsegment]
  · inext
    iframe
  iapply wp_memoryInit16_four oldWord $$ HresourcesLater
  inext
  iintro ⟨Hword, Hsegment⟩
  ihave HsegmentLater :
      ▷ dataSegmentPointsTo 0 (some [1, 2, 3, 4]) $$ Hsegment
  iapply wp_dataDrop0 [1, 2, 3, 4] $$ HsegmentLater
  inext
  iintro Hsegment
  iapply wp_const
  inext
  ihave HwordLater :
      ▷ pointsTo_u32 (16 + 0) 0x04030201 $$ [Hword]
  · inext
    rw [UInt32.add_zero]
    iexact Hword
  iapply wp_load32 0x04030201 rfl rfl rfl rfl $$ HwordLater
  inext
  iintro Hword
  iapply wp_finish
  inext
  iapply wp_value'
  isplitr
  · ipureintro
    rfl
  · rw [UInt32.add_zero]
    iframe

/-- End-to-end Iris contract for overlapping `memory.copy`. The single owner
is essential: source and destination alias, and the resulting word records
that the source bytes were read before any destination byte was overwritten. -/
theorem wp_copyOverlapWord :
    pointsTo_u64 0 0x8877665544332211 ⊢
    WP (.running
      ⟨⟨[], [], []⟩,
        [ .const 2, .const 0, .const 4, .memoryCopy,
          .const 0, .load64 0 ],
        1, [], [], []⟩ : Expr α) @ s; E
      {{ result,
        ⌜result = [.i64 0x8877443322112211]⌝ ∗
        pointsTo_u64 0 0x8877443322112211 }} := by
  iintro Hword
  iapply wp_const
  inext
  iapply wp_const
  inext
  iapply wp_const
  inext
  ihave HwordLater :
      ▷ pointsTo_u64 0 0x8877665544332211 $$ [Hword]
  · inext
    iexact Hword
  iapply wp_copy2_zero_four $$ HwordLater
  inext
  iintro Hword
  iapply wp_const
  inext
  ihave HwordLater :
      ▷ pointsTo_u64 (0 + 0) 0x8877443322112211 $$ [Hword]
  · inext
    rw [UInt32.add_zero]
    iexact Hword
  iapply wp_load64 0x8877443322112211
    rfl rfl rfl rfl rfl rfl rfl rfl $$ HwordLater
  inext
  iintro Hword
  iapply wp_finish
  inext
  iapply wp_value'
  isplitr
  · ipureintro
    rfl
  · rw [UInt32.add_zero]
    iexact Hword

/-- Iris proof of an in-place swap of two 32-bit memory cells. This composes
word ownership through locals and returns ownership of both updated cells. -/
theorem wp_swapWords :
    pointsTo_u32 0 11 ∗ pointsTo_u32 4 22 ⊢
    WP (.running
      ⟨⟨[], [.i32 0, .i32 0], []⟩,
        [ .const 0, .load32 0, .localSet 0,
          .const 4, .load32 0, .localSet 1,
          .const 0, .localGet 1, .store32 0,
          .const 4, .localGet 0, .store32 0,
          .const 0, .load32 0,
          .const 4, .load32 0 ],
        2, [], [], []⟩ : Expr α) @ s; E
      {{ result, ⌜result = [.i32 11, .i32 22]⌝ ∗
        pointsTo_u32 0 22 ∗ pointsTo_u32 4 11 }} := by
  iintro ⟨H0, H4⟩
  iapply wp_const
  inext
  ihave H0Later : ▷ pointsTo_u32 (0 + 0) 11 $$ [H0]
  · inext
    rw [UInt32.add_zero]
    iexact H0
  iapply wp_load32 11 rfl rfl rfl rfl $$ H0Later
  inext
  iintro H0
  iapply wp_localSet rfl
  inext
  iapply wp_const
  inext
  ihave H4Later : ▷ pointsTo_u32 (4 + 0) 22 $$ [H4]
  · inext
    rw [UInt32.add_zero]
    iexact H4
  iapply wp_load32 22 rfl rfl rfl rfl $$ H4Later
  inext
  iintro H4
  iapply wp_localSet rfl
  inext
  iapply wp_const
  inext
  iapply wp_localGet rfl
  inext
  ihave H0Later : ▷ pointsTo_u32 (0 + 0) 11 $$ [H0]
  · inext
    rw [UInt32.add_zero]
    iexact H0
  iapply wp_store32 11 rfl rfl rfl rfl $$ H0Later
  inext
  iintro H0
  iapply wp_const
  inext
  iapply wp_localGet rfl
  inext
  ihave H4Later : ▷ pointsTo_u32 (4 + 0) 22 $$ [H4]
  · inext
    rw [UInt32.add_zero]
    iexact H4
  iapply wp_store32 22 rfl rfl rfl rfl $$ H4Later
  inext
  iintro H4
  iapply wp_const
  inext
  ihave H0Later : ▷ pointsTo_u32 (0 + 0) 22 $$ [H0]
  · inext
    rw [UInt32.add_zero]
    iexact H0
  iapply wp_load32 22 rfl rfl rfl rfl $$ H0Later
  inext
  iintro H0
  iapply wp_const
  inext
  ihave H4Later : ▷ pointsTo_u32 (4 + 0) 11 $$ [H4]
  · inext
    rw [UInt32.add_zero]
    iexact H4
  iapply wp_load32 11 rfl rfl rfl rfl $$ H4Later
  inext
  iintro H4
  iapply wp_finish
  inext
  iapply wp_value'
  isplitr
  · ipureintro
    rfl
  · isplitl [H0]
    · rw [UInt32.add_zero]
      iexact H0
    · rw [UInt32.add_zero]
      iexact H4

/-- Iris contract for reversing three adjacent words. The endpoint swap uses
the same primitive loads and stores as `wp_swapWords`; ownership of the middle
word is framed throughout and returned unchanged. -/
theorem wp_reverseThreeWords :
    pointsTo_u32 0 11 ∗ pointsTo_u32 4 22 ∗ pointsTo_u32 8 33 ⊢
    WP (.running
      ⟨⟨[], [.i32 0, .i32 0], []⟩,
        [ .const 0, .load32 0, .localSet 0,
          .const 8, .load32 0, .localSet 1,
          .const 0, .localGet 1, .store32 0,
          .const 8, .localGet 0, .store32 0,
          .const 0, .load32 0,
          .const 8, .load32 0 ],
        2, [], [], []⟩ : Expr α) @ s; E
      {{ result, ⌜result = [.i32 11, .i32 33]⌝ ∗
        pointsTo_u32 0 33 ∗ pointsTo_u32 4 22 ∗ pointsTo_u32 8 11 }} := by
  iintro ⟨H0, H4, H8⟩
  iapply wp_const
  inext
  ihave H0Later : ▷ pointsTo_u32 (0 + 0) 11 $$ [H0]
  · inext
    rw [UInt32.add_zero]
    iexact H0
  iapply wp_load32 11 rfl rfl rfl rfl $$ H0Later
  inext
  iintro H0
  iapply wp_localSet rfl
  inext
  iapply wp_const
  inext
  ihave H8Later : ▷ pointsTo_u32 (8 + 0) 33 $$ [H8]
  · inext
    rw [UInt32.add_zero]
    iexact H8
  iapply wp_load32 33 rfl rfl rfl rfl $$ H8Later
  inext
  iintro H8
  iapply wp_localSet rfl
  inext
  iapply wp_const
  inext
  iapply wp_localGet rfl
  inext
  ihave H0Later : ▷ pointsTo_u32 (0 + 0) 11 $$ [H0]
  · inext
    rw [UInt32.add_zero]
    iexact H0
  iapply wp_store32 11 rfl rfl rfl rfl $$ H0Later
  inext
  iintro H0
  iapply wp_const
  inext
  iapply wp_localGet rfl
  inext
  ihave H8Later : ▷ pointsTo_u32 (8 + 0) 33 $$ [H8]
  · inext
    rw [UInt32.add_zero]
    iexact H8
  iapply wp_store32 33 rfl rfl rfl rfl $$ H8Later
  inext
  iintro H8
  iapply wp_const
  inext
  ihave H0Later : ▷ pointsTo_u32 (0 + 0) 33 $$ [H0]
  · inext
    rw [UInt32.add_zero]
    iexact H0
  iapply wp_load32 33 rfl rfl rfl rfl $$ H0Later
  inext
  iintro H0
  iapply wp_const
  inext
  ihave H8Later : ▷ pointsTo_u32 (8 + 0) 11 $$ [H8]
  · inext
    rw [UInt32.add_zero]
    iexact H8
  iapply wp_load32 11 rfl rfl rfl rfl $$ H8Later
  inext
  iintro H8
  iapply wp_finish
  inext
  iapply wp_value'
  isplitr
  · ipureintro
    rfl
  · isplitl [H0]
    · rw [UInt32.add_zero]
      iexact H0
    · isplitl [H4]
      · iexact H4
      · rw [UInt32.add_zero]
        iexact H8

/-- Iris proof of the concrete three-word partition kernel.  The final word is
the pivot; all three input words remain exclusively owned, with the pivot
placed between the lower and upper partitions. -/
theorem wp_partitionThreeWords :
    pointsTo_u32 0 33 ∗ pointsTo_u32 4 11 ∗ pointsTo_u32 8 22 ⊢
    WP (.running
      ⟨⟨[], [.i32 0, .i32 0, .i32 0], []⟩,
        [ .const 0, .load32 0, .localSet 0,
          .const 4, .load32 0, .localSet 1,
          .const 8, .load32 0, .localSet 2,
          .const 0, .localGet 1, .store32 0,
          .const 4, .localGet 2, .store32 0,
          .const 8, .localGet 0, .store32 0 ],
        0, [], [], []⟩ : Expr α) @ s; E
      {{ result, ⌜result = []⌝ ∗
        pointsTo_u32 0 11 ∗ pointsTo_u32 4 22 ∗
          pointsTo_u32 8 33 }} := by
  iintro ⟨H0, H4, H8⟩
  iapply wp_const
  inext
  ihave H0Later : ▷ pointsTo_u32 (0 + 0) 33 $$ [H0]
  · inext
    rw [UInt32.add_zero]
    iexact H0
  iapply wp_load32 33 rfl rfl rfl rfl $$ H0Later
  inext
  iintro H0
  iapply wp_localSet rfl
  inext
  iapply wp_const
  inext
  ihave H4Later : ▷ pointsTo_u32 (4 + 0) 11 $$ [H4]
  · inext
    rw [UInt32.add_zero]
    iexact H4
  iapply wp_load32 11 rfl rfl rfl rfl $$ H4Later
  inext
  iintro H4
  iapply wp_localSet rfl
  inext
  iapply wp_const
  inext
  ihave H8Later : ▷ pointsTo_u32 (8 + 0) 22 $$ [H8]
  · inext
    rw [UInt32.add_zero]
    iexact H8
  iapply wp_load32 22 rfl rfl rfl rfl $$ H8Later
  inext
  iintro H8
  iapply wp_localSet rfl
  inext
  iapply wp_const
  inext
  iapply wp_localGet rfl
  inext
  ihave H0Later : ▷ pointsTo_u32 (0 + 0) 33 $$ [H0]
  · inext
    rw [UInt32.add_zero]
    iexact H0
  iapply wp_store32 33 rfl rfl rfl rfl $$ H0Later
  inext
  iintro H0
  iapply wp_const
  inext
  iapply wp_localGet rfl
  inext
  ihave H4Later : ▷ pointsTo_u32 (4 + 0) 11 $$ [H4]
  · inext
    rw [UInt32.add_zero]
    iexact H4
  iapply wp_store32 11 rfl rfl rfl rfl $$ H4Later
  inext
  iintro H4
  iapply wp_const
  inext
  iapply wp_localGet rfl
  inext
  ihave H8Later : ▷ pointsTo_u32 (8 + 0) 22 $$ [H8]
  · inext
    rw [UInt32.add_zero]
    iexact H8
  iapply wp_store32 22 rfl rfl rfl rfl $$ H8Later
  inext
  iintro H8
  iapply wp_finish
  inext
  iapply wp_value'
  isplitr
  · ipureintro
    rfl
  · isplitl [H0]
    · rw [UInt32.add_zero]
      iexact H0
    · isplitl [H4]
      · rw [UInt32.add_zero]
        iexact H4
      · rw [UInt32.add_zero]
        iexact H8

/-- Iris proof for merging two singleton sorted runs. The Wasm comparison
selects the swapping branch for the concrete input `[9, 4]`; both exclusive
word owners are returned in ascending order. -/
theorem wp_mergeTwoWords :
    pointsTo_u32 0 9 ∗ pointsTo_u32 4 4 ⊢
    WP (.running
      ⟨⟨[], [.i32 0, .i32 0], []⟩,
        [ .const 0, .load32 0, .localSet 0,
          .const 4, .load32 0, .localSet 1,
          .localGet 0, .localGet 1, .ltU,
          .iff 0 0
            [ .const 0, .localGet 0, .store32 0,
              .const 4, .localGet 1, .store32 0 ]
            [ .const 0, .localGet 1, .store32 0,
              .const 4, .localGet 0, .store32 0 ] ],
        0, [], [], []⟩ : Expr α) @ s; E
      {{ result, ⌜result = []⌝ ∗
        pointsTo_u32 0 4 ∗ pointsTo_u32 4 9 }} := by
  iintro ⟨H0, H4⟩
  iapply wp_const
  inext
  ihave H0Later : ▷ pointsTo_u32 (0 + 0) 9 $$ [H0]
  · inext
    rw [UInt32.add_zero]
    iexact H0
  iapply wp_load32 9 rfl rfl rfl rfl $$ H0Later
  inext
  iintro H0
  iapply wp_localSet rfl
  inext
  iapply wp_const
  inext
  ihave H4Later : ▷ pointsTo_u32 (4 + 0) 4 $$ [H4]
  · inext
    rw [UInt32.add_zero]
    iexact H4
  iapply wp_load32 4 rfl rfl rfl rfl $$ H4Later
  inext
  iintro H4
  iapply wp_localSet rfl
  inext
  iapply wp_localGet rfl
  inext
  iapply wp_localGet rfl
  inext
  iapply wp_ltU (result := 0) (by decide)
  inext
  iapply wp_iff
    (selectedBody :=
      [ .const 0, .localGet 1, .store32 0,
        .const 4, .localGet 0, .store32 0 ])
    rfl
  inext
  iapply wp_const
  inext
  iapply wp_localGet rfl
  inext
  ihave H0Later : ▷ pointsTo_u32 (0 + 0) 9 $$ [H0]
  · inext
    rw [UInt32.add_zero]
    iexact H0
  iapply wp_store32 9 rfl rfl rfl rfl $$ H0Later
  inext
  iintro H0
  iapply wp_const
  inext
  iapply wp_localGet rfl
  inext
  ihave H4Later : ▷ pointsTo_u32 (4 + 0) 4 $$ [H4]
  · inext
    rw [UInt32.add_zero]
    iexact H4
  iapply wp_store32 4 rfl rfl rfl rfl $$ H4Later
  inext
  iintro H4
  iapply wp_exitControl rfl
  inext
  iapply wp_finish
  inext
  iapply wp_value'
  isplitr
  · ipureintro
    rfl
  · isplitl [H0]
    · rw [UInt32.add_zero]
      iexact H0
    · rw [UInt32.add_zero]
      iexact H4

end Wasm.SmallStep
