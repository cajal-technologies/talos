import Project.Mergesort.DriverProof
import CodeLib.SepLogic.CostedLoop

/-! Actual scalar and four-word generated decode-loop costs. -/
namespace Project.Mergesort.DecodeLoopCost

open Wasm Wasm.SmallStep Project.Mergesort.DriverProof
open Project.Mergesort.Representations

structure State where
  dataPtr : UInt32
  current : UInt32
  length : UInt32
  aux2 : UInt32
  aux4 : UInt32
  aux5 : UInt32
  aux7 : UInt32
  aux8 : UInt32
  aux9 : UInt32
  aux10 : UInt32

structure Context where
  stack : List Value := []
  code : Program := []
  arity : Nat := 0
  remainder : List Value := []
  controls : List ControlFrame := []
  calls : List CallFrame := []

def locals (v : State) (stack : List Value) : Locals :=
  func3AppendLocals v.dataPtr v.current v.length v.aux2 v.aux4 v.aux5
    v.aux7 v.aux8 v.aux9 v.aux10 stack

def config (store : MachineStore α) (v : State) (ctx : Context) : Config α :=
  ⟨.running ⟨locals v ctx.stack, ctx.code, ctx.arity, ctx.remainder,
    ctx.controls, ctx.calls⟩, store⟩

def tailBody : Program :=
  [.localGet 6, .localGet 3, .load32 0, .store32 0,
    .localGet 6, .const 4, .add, .localSet 6,
    .localGet 3, .const 4, .add, .localSet 3,
    .localGet 8, .const 4294967295, .add, .localTee 8, .br_if 0]

def bulkBody : Program :=
  [.localGet 2, .localGet 3, .add, .localTee 6,
    .localGet 4, .localGet 3, .add, .localTee 1,
    .load32 0, .store32 0,
    .localGet 6, .const 4, .add,
    .localGet 1, .const 4, .add, .load32 0, .store32 0,
    .localGet 6, .const 8, .add,
    .localGet 1, .const 8, .add, .load32 0, .store32 0,
    .localGet 6, .const 12, .add,
    .localGet 1, .const 12, .add, .load32 0, .store32 0,
    .localGet 3, .const 16, .add, .localSet 3,
    .localGet 5, .localGet 9, .const 4, .add, .localTee 9,
    .ne, .br_if 0]

def frame (body : Program) (ctx : Context) : ControlFrame :=
  { kind := .loop, paramArity := 0, resultArity := 0,
    body := body, continuation := ctx.code, belowStack := ctx.stack }

def head (body : Program) (store : MachineStore α) (v : State) (ctx : Context) : Config α :=
  config store v { ctx with code := body, controls := frame body ctx :: ctx.controls }

def copyWord (store : MachineStore α) (source destination : UInt32) : MachineStore α :=
  { store with wasm := { store.wasm with
    mem := store.wasm.mem.write32 (destination + 0) (store.wasm.mem.read32 (source + 0)) } }

def tailNext (v : State) : State :=
  { v with
    current := 4 + v.current, length := 4 + v.length,
    aux8 := 4294967295 + v.aux8 }

/-- Sixteen scalar instructions copy one word and prepare the back-edge value. -/
theorem tail_prefix_cost (store : MachineStore α) (v : State) (ctx : Context)
    (hsource : v.current.toNat + 4 ≤ store.wasm.mem.pages * 65536)
    (hdestination : v.length.toNat + 4 ≤ store.wasm.mem.pages * 65536)
    (hostBytes : Config α → Nat → Config α → Nat) :
    CostedSteps (byteWork hostBytes) (head tailBody store v ctx)
      ((tailBody.take 16).map StepKind.instruction)
      (config (copyWord store v.current v.length) (tailNext v)
        { ctx with
          stack := .i32 (tailNext v).aux8 :: ctx.stack,
          code := [.br_if 0], controls := frame tailBody ctx :: ctx.controls }) 16 := by
  apply Steps.with_unit_cost
  · unfold head config tailBody
    simp only [List.take, List.map]
    unfold locals tailNext
    wasm_steps [(.localGet rfl), (.localGet rfl), (.load32 rfl (by simpa using hsource)),
      (.store32 rfl (by simpa using hdestination)), (.localGet rfl), .const, .add,
      (.localSet rfl), (.localGet rfl), .const, .add, (.localSet rfl),
      (.localGet rfl), .const, .add]
    exact Steps.single (.localTee rfl)
  · intro before kind after member
    simp only [tailBody, List.take, List.map, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

def tailCopy (store : MachineStore α) (v : State) : Nat → MachineStore α
  | 0 => store
  | n+1 => tailCopy (copyWord store v.current v.length) (tailNext v) n

def tailAdvance (v : State) : Nat → State
  | 0 => v
  | n+1 => tailAdvance (tailNext v) n

theorem copyWord_pages (store : MachineStore α) (source destination : UInt32) :
    (copyWord store source destination).wasm.mem.pages = store.wasm.mem.pages := rfl

theorem tailCopy_pages (store : MachineStore α) (v : State) (n : Nat) :
    (tailCopy store v n).wasm.mem.pages = store.wasm.mem.pages := by
  induction n generalizing store v with
  | zero => rfl
  | succ n ih =>
    simpa only [tailCopy, copyWord_pages] using ih (copyWord store v.current v.length) (tailNext v)

theorem tailCopy_store (store : MachineStore α) (v : State) (n : Nat) :
    tailCopy store v n = { store with wasm := { store.wasm with mem := (tailCopy store v n).wasm.mem } } := by
  induction n generalizing store v with
  | zero => rfl
  | succ n ih =>
    simpa only [tailCopy, copyWord] using ih (copyWord store v.current v.length) (tailNext v)

theorem tailAdvance_eq (v : State) (n : Nat) :
    tailAdvance v n = { v with
    current := UInt32.ofNat (4*n) + v.current,
      length := UInt32.ofNat (4*n) + v.length, aux8 := -UInt32.ofNat n + v.aux8 } := by
  induction n generalizing v with
  | zero => simp [tailAdvance]
  | succ n ih =>
    simp only [tailAdvance, ih, tailNext, Nat.mul_add, Nat.mul_one, UInt32.ofNat_add,
      UInt32.neg_add, UInt32.sub_eq_add_neg, UInt32.add_assoc,
      show UInt32.ofNat 4 = (4 : UInt32) from rfl,
      show UInt32.ofNat 1 = (1 : UInt32) from rfl, UInt32.neg_one_eq]

/-- Positive scalar remainder; physical ranges justify every successive access.
Includes final loop-frame exit, with its continuation still pending. -/
theorem tail_loop_cost (store : MachineStore α) (v : State) (ctx : Context) (n : Nat)
    (hpositive : 0 < n) (hcounter : v.aux8 = UInt32.ofNat n)
    (hsourceWord : v.current.toNat + 4*n < UInt32.size)
    (hdestinationWord : v.length.toNat + 4*n < UInt32.size)
    (hsource : v.current.toNat + 4*n ≤ store.wasm.mem.pages * 65536)
    (hdestination : v.length.toNat + 4*n ≤ store.wasm.mem.pages * 65536)
    (hostBytes : Config α → Nat → Config α → Nat) :
    ∃ trace, CostedSteps (byteWork hostBytes) (head tailBody store v ctx) trace
      (config (tailCopy store v n) (tailAdvance v n) ctx) (17*n+1) := by
  induction n generalizing store v with
  | zero => omega
  | succ n ih =>
    have hnext : (tailNext v).aux8 = UInt32.ofNat n := by
      change 4294967295 + v.aux8 = _
      rw [hcounter, UInt32.ofNat_add]
      change 4294967295 + (UInt32.ofNat n + 1) = _
      calc
        _ = ((4294967295 : UInt32) + 1) + UInt32.ofNat n := by ac_rfl
        _ = _ := UInt32.zero_add _
    have pre := tail_prefix_cost store v ctx (by omega) (by omega) hostBytes
    by_cases hz : n = 0
    · subst n
      have branch : CostedSteps (byteWork hostBytes)
          (config (copyWord store v.current v.length) (tailNext v)
            { ctx with
              stack := .i32 (tailNext v).aux8 :: ctx.stack,
              code := [.br_if 0], controls := frame tailBody ctx :: ctx.controls })
          [.instruction (.br_if 0)]
          (config (copyWord store v.current v.length) (tailNext v)
            { ctx with code := [], controls := frame tailBody ctx :: ctx.controls }) 1 := by
        rw [hnext]
        exact CostedSteps.single .brIfZero
      have leave : CostedSteps (byteWork hostBytes)
          (config (copyWord store v.current v.length) (tailNext v)
            { ctx with code := [], controls := frame tailBody ctx :: ctx.controls })
          [.administrative .exitControl]
          (config (copyWord store v.current v.length) (tailNext v) ctx) 1 :=
        CostedSteps.single (.exitControl rfl)
      exact ⟨_, (pre.trans branch).trans leave⟩
    · have hne : (tailNext v).aux8 ≠ 0 := by
        rw [hnext]
        intro heq
        have hnat := congrArg UInt32.toNat heq
        rw [UInt32.toNat_ofNat_of_lt' (by omega : n < UInt32.size)] at hnat
        change n = 0 at hnat
        omega
      have branch : CostedSteps (byteWork hostBytes)
          (config (copyWord store v.current v.length) (tailNext v)
            { ctx with
              stack := .i32 (tailNext v).aux8 :: ctx.stack,
              code := [.br_if 0], controls := frame tailBody ctx :: ctx.controls })
          [.instruction (.br_if 0)]
          (head tailBody (copyWord store v.current v.length) (tailNext v) ctx) 1 :=
        CostedSteps.single (.brIf hne rfl)
      have hs : (tailNext v).current.toNat = v.current.toNat + 4 := by
        change (4 + v.current : UInt32).toNat = _
        rw [UInt32.toNat_add]
        change (4 + v.current.toNat) % UInt32.size = _
        rw [Nat.mod_eq_of_lt (by omega)]; omega
      have hd : (tailNext v).length.toNat = v.length.toNat + 4 := by
        change (4 + v.length : UInt32).toNat = _
        rw [UInt32.toNat_add]
        change (4 + v.length.toNat) % UInt32.size = _
        rw [Nat.mod_eq_of_lt (by omega)]; omega
      obtain ⟨tr, run⟩ := ih (copyWord store v.current v.length) (tailNext v)
        (by omega) hnext (by rw [hs]; omega) (by rw [hd]; omega)
        (by rw [hs, copyWord_pages]; omega) (by rw [hd, copyWord_pages]; omega)
      refine ⟨((tailBody.take 16).map StepKind.instruction ++ [.instruction (.br_if 0)]) ++ tr, ?_⟩
      simpa only [tailCopy, tailAdvance,
        show 16+1+(17*n+1)=17*(n+1)+1 by omega] using (pre.trans branch).trans run

theorem addNat_toNat (a : UInt32) (n : Nat) (h : a.toNat + n < UInt32.size) :
    (UInt32.ofNat n + a).toNat = a.toNat+n := by
  rw [UInt32.toNat_add, UInt32.toNat_ofNat_of_lt' (by omega : n < UInt32.size)]
  change (n+a.toNat)%UInt32.size = a.toNat+n
  rw [Nat.mod_eq_of_lt (by omega)]
  omega

def bulkNext (v : State) : State :=
  { v with
    dataPtr := v.current + v.aux4, length := v.current + v.aux2,
    current := 16 + v.current, aux9 := 4 + v.aux9 }

def bulkWritten (store : MachineStore α) (v : State) : MachineStore α :=
  let source := v.current + v.aux4
  let destination := v.current + v.aux2
  copyWord (copyWord (copyWord (copyWord store source destination)
    (4 + source) (4 + destination)) (8 + source) (8 + destination))
    (12 + source) (12 + destination)

/-- The generated unrolled body performs four physical reads and writes before
its final branch; it costs forty-four scalar transitions. -/
theorem bulk_prefix_cost (store : MachineStore α) (v : State) (ctx : Context)
    (hsourceWord : (v.current + v.aux4).toNat + 16 < UInt32.size)
    (hdestinationWord : (v.current + v.aux2).toNat + 16 < UInt32.size)
    (hsource : (v.current + v.aux4).toNat + 16 ≤ store.wasm.mem.pages*65536)
    (hdestination : (v.current + v.aux2).toNat + 16 ≤ store.wasm.mem.pages*65536)
    (hostBytes : Config α → Nat → Config α → Nat) :
    CostedSteps (byteWork hostBytes) (head bulkBody store v ctx)
      ((bulkBody.take 44).map StepKind.instruction)
      (config (bulkWritten store v) (bulkNext v)
        { ctx with
          stack := .i32 (if v.aux5 ≠ (bulkNext v).aux9 then 1 else 0) :: ctx.stack,
          code := [.br_if 0], controls := frame bulkBody ctx :: ctx.controls }) 44 := by
  have hs4 := addNat_toNat (v.current+v.aux4) 4 (by omega)
  change (4+(v.current+v.aux4):UInt32).toNat = (v.current+v.aux4).toNat+4 at hs4
  have hs8 := addNat_toNat (v.current+v.aux4) 8 (by omega)
  change (8+(v.current+v.aux4):UInt32).toNat = (v.current+v.aux4).toNat+8 at hs8
  have hs12 := addNat_toNat (v.current+v.aux4) 12 (by omega)
  change (12+(v.current+v.aux4):UInt32).toNat = (v.current+v.aux4).toNat+12 at hs12
  have hd4 := addNat_toNat (v.current+v.aux2) 4 (by omega)
  change (4+(v.current+v.aux2):UInt32).toNat = (v.current+v.aux2).toNat+4 at hd4
  have hd8 := addNat_toNat (v.current+v.aux2) 8 (by omega)
  change (8+(v.current+v.aux2):UInt32).toNat = (v.current+v.aux2).toNat+8 at hd8
  have hd12 := addNat_toNat (v.current+v.aux2) 12 (by omega)
  change (12+(v.current+v.aux2):UInt32).toNat = (v.current+v.aux2).toNat+12 at hd12
  apply Steps.with_unit_cost
  · unfold head config bulkBody
    simp only [List.take, List.map]
    unfold locals bulkNext
    wasm_steps [(.localGet rfl), (.localGet rfl), .add, (.localTee rfl),
      (.localGet rfl), (.localGet rfl), .add, (.localTee rfl),
      (.load32 rfl (by simpa using (show (v.current+v.aux4).toNat+4 ≤ store.wasm.mem.pages*65536 by omega))),
      (.store32 rfl (by simpa using (show (v.current+v.aux2).toNat+4 ≤ store.wasm.mem.pages*65536 by omega))),
      (.localGet rfl), .const, .add, (.localGet rfl), .const, .add,
      (.load32 rfl (by
        change (4+(v.current+v.aux4) : UInt32).toNat+4 ≤ store.wasm.mem.pages*65536
        rw [hs4]; omega)),
      (.store32 rfl (by
        change (4+(v.current+v.aux2) : UInt32).toNat+4 ≤ store.wasm.mem.pages*65536
        rw [hd4]; omega)),
      (.localGet rfl), .const, .add, (.localGet rfl), .const, .add,
      (.load32 rfl (by
        change (8+(v.current+v.aux4) : UInt32).toNat+4 ≤ store.wasm.mem.pages*65536
        rw [hs8]; omega)),
      (.store32 rfl (by
        change (8+(v.current+v.aux2) : UInt32).toNat+4 ≤ store.wasm.mem.pages*65536
        rw [hd8]; omega)),
      (.localGet rfl), .const, .add, (.localGet rfl), .const, .add,
      (.load32 rfl (by
        change (12+(v.current+v.aux4) : UInt32).toNat+4 ≤ store.wasm.mem.pages*65536
        rw [hs12]; omega)),
      (.store32 rfl (by
        change (12+(v.current+v.aux2) : UInt32).toNat+4 ≤ store.wasm.mem.pages*65536
        rw [hd12]; omega)),
      (.localGet rfl), .const, .add, (.localSet rfl),
      (.localGet rfl), (.localGet rfl), .const, .add, (.localTee rfl)]
    exact Steps.single (.ne rfl)
  · intro before kind after member
    simp only [bulkBody, List.take, List.map, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

def bulkCopy (store : MachineStore α) (v : State) : Nat → MachineStore α
  | 0 => store
  | n+1 => bulkCopy (bulkWritten store v) (bulkNext v) n

def bulkAdvance (v : State) : Nat → State
  | 0 => v
  | n+1 => bulkAdvance (bulkNext v) n

theorem bulkWritten_pages (store : MachineStore α) (v : State) :
    (bulkWritten store v).wasm.mem.pages = store.wasm.mem.pages := rfl

theorem bulkCopy_pages (store : MachineStore α) (v : State) (n : Nat) :
    (bulkCopy store v n).wasm.mem.pages = store.wasm.mem.pages := by
  induction n generalizing store v with
  | zero => rfl
  | succ n ih => simpa only [bulkCopy, bulkWritten_pages] using ih (bulkWritten store v) (bulkNext v)

theorem bulkCopy_store (store : MachineStore α) (v : State) (n : Nat) :
    bulkCopy store v n = { store with wasm := { store.wasm with mem := (bulkCopy store v n).wasm.mem } } := by
  induction n generalizing store v with
  | zero => rfl
  | succ n ih => simpa only [bulkCopy, bulkWritten, copyWord] using ih (bulkWritten store v) (bulkNext v)

theorem offset_toNat (base : UInt32) (i : Nat)
    (h : base.toNat+4*i < UInt32.size) :
    (UInt32.ofNat (4*i) + base).toNat = base.toNat+4*i :=
  addNat_toNat base (4*i) h

/-- Every bulk back edge advances four words. Natural counters and complete
physical ranges justify the comparison and all four writes at each iteration. -/
theorem bulk_loop_cost (groups : Nat) :
    ∀ (store : MachineStore α) (v : State) (ctx : Context) (copied : Nat),
    0 < groups → v.current = UInt32.ofNat (4*copied) →
    v.aux9 = UInt32.ofNat copied → v.aux5 = UInt32.ofNat (copied+4*groups) →
    v.aux4.toNat+4*(copied+4*groups) < UInt32.size →
    v.aux2.toNat+4*(copied+4*groups) < UInt32.size →
    v.aux4.toNat+4*(copied+4*groups) ≤ store.wasm.mem.pages*65536 →
    v.aux2.toNat+4*(copied+4*groups) ≤ store.wasm.mem.pages*65536 →
    ∀ (hostBytes : Config α → Nat → Config α → Nat),
    ∃ trace, CostedSteps (byteWork hostBytes) (head bulkBody store v ctx) trace
      (config (bulkCopy store v groups) (bulkAdvance v groups) ctx) (45*groups+1) := by
  induction groups with
  | zero => intros; omega
  | succ groups ih =>
    intro store v ctx copied hpositive hcurrent hcounter hstop hsw hdw hs hd hostBytes
    have hsa : (v.current+v.aux4).toNat = v.aux4.toNat+4*copied := by
      rw [hcurrent]; exact offset_toNat _ _ (by omega)
    have hda : (v.current+v.aux2).toNat = v.aux2.toNat+4*copied := by
      rw [hcurrent]; exact offset_toNat _ _ (by omega)
    have hnextCurrent : (bulkNext v).current = UInt32.ofNat (4*(copied+4)) := by
      change 16+v.current = _
      rw [hcurrent, show 4*(copied+4)=16+4*copied by omega, UInt32.ofNat_add]
      rfl
    have hnextCounter : (bulkNext v).aux9 = UInt32.ofNat (copied+4) := by
      change 4+v.aux9 = _
      rw [hcounter, UInt32.ofNat_add]
      exact UInt32.add_comm _ _
    have pre := bulk_prefix_cost store v ctx
      (by rw [hsa]; omega) (by rw [hda]; omega)
      (by rw [hsa]; omega) (by rw [hda]; omega) hostBytes
    by_cases hz : groups=0
    · subst groups
      have heq : v.aux5 = (bulkNext v).aux9 := by rw [hnextCounter, hstop]
      simp only [heq, ne_eq, not_true_eq_false, if_false] at pre
      have branch : CostedSteps (byteWork hostBytes)
          (config (bulkWritten store v) (bulkNext v)
            { ctx with
              stack := .i32 0 :: ctx.stack, code := [.br_if 0],
              controls := frame bulkBody ctx :: ctx.controls })
          [.instruction (.br_if 0)]
          (config (bulkWritten store v) (bulkNext v)
            { ctx with code := [], controls := frame bulkBody ctx :: ctx.controls }) 1 :=
        CostedSteps.single .brIfZero
      have leave : CostedSteps (byteWork hostBytes)
          (config (bulkWritten store v) (bulkNext v)
            { ctx with code := [], controls := frame bulkBody ctx :: ctx.controls })
          [.administrative .exitControl]
          (config (bulkWritten store v) (bulkNext v) ctx) 1 :=
        CostedSteps.single (.exitControl rfl)
      exact ⟨_, (pre.trans branch).trans leave⟩
    · have hne : v.aux5 ≠ (bulkNext v).aux9 := by
        rw [hstop, hnextCounter]
        intro heq
        have hnat := congrArg UInt32.toNat heq
        rw [UInt32.toNat_ofNat_of_lt' (by omega : copied+4*(groups+1)<UInt32.size),
          UInt32.toNat_ofNat_of_lt' (by omega : copied+4<UInt32.size)] at hnat
        omega
      simp only [if_pos hne] at pre
      have branch : CostedSteps (byteWork hostBytes)
          (config (bulkWritten store v) (bulkNext v)
            { ctx with
              stack := .i32 1 :: ctx.stack, code := [.br_if 0],
              controls := frame bulkBody ctx :: ctx.controls })
          [.instruction (.br_if 0)] (head bulkBody (bulkWritten store v) (bulkNext v) ctx) 1 :=
        CostedSteps.single (.brIf (by decide) rfl)
      have ht : copied+4+4*groups = copied+4*(groups+1) := by omega
      obtain ⟨tr, run⟩ := ih (bulkWritten store v) (bulkNext v) ctx (copied+4)
        (by omega) hnextCurrent hnextCounter (by change v.aux5 = _; rw [ht]; exact hstop)
        (by change v.aux4.toNat+4*(copied+4+4*groups)<UInt32.size; rw [ht]; exact hsw)
        (by change v.aux2.toNat+4*(copied+4+4*groups)<UInt32.size; rw [ht]; exact hdw)
        (by change v.aux4.toNat+4*(copied+4+4*groups)≤store.wasm.mem.pages*65536; rw [ht]; exact hs)
        (by change v.aux2.toNat+4*(copied+4+4*groups)≤store.wasm.mem.pages*65536; rw [ht]; exact hd)
        hostBytes
      refine ⟨((bulkBody.take 44).map StepKind.instruction ++ [.instruction (.br_if 0)]) ++ tr, ?_⟩
      simpa only [bulkCopy, bulkAdvance,
        show 44+1+(45*groups+1)=45*(groups+1)+1 by omega] using (pre.trans branch).trans run

/-- Exact final register values after a positive number of unrolled groups. -/
theorem bulkAdvance_succ (v : State) (n : Nat) :
    bulkAdvance v (n+1) = { v with
      dataPtr := UInt32.ofNat (16*n)+v.current+v.aux4,
      length := UInt32.ofNat (16*n)+v.current+v.aux2,
      current := UInt32.ofNat (16*(n+1))+v.current,
      aux9 := UInt32.ofNat (4*(n+1))+v.aux9 } := by
  induction n generalizing v with
  | zero => simp [bulkAdvance, bulkNext]
  | succ n ih =>
    rw [bulkAdvance, ih]
    simp only [bulkNext, Nat.mul_add, Nat.mul_one, UInt32.ofNat_add,
      UInt32.add_assoc, show UInt32.ofNat 16 = (16 : UInt32) from rfl,
      show UInt32.ofNat 4 = (4 : UInt32) from rfl]

/-- A read entirely before the destination is unaffected by the actual write. -/
theorem copyWord_prefix (store : MachineStore α) (source destination address : UInt32)
    (h : address.toNat+4 ≤ destination.toNat) :
    (copyWord store source destination).wasm.mem.read32 address = store.wasm.mem.read32 address := by
  exact Mem.read32_write32_disjoint _ _ _ _ (Or.inl (by simpa using h))

theorem tailCopy_prefix (store : MachineStore α) (v : State) (n : Nat) (address : UInt32)
    (hword : v.length.toNat+4*n < UInt32.size)
    (hbefore : address.toNat+4 ≤ v.length.toNat) :
    (tailCopy store v n).wasm.mem.read32 address = store.wasm.mem.read32 address := by
  induction n generalizing store v with
  | zero => rfl
  | succ n ih =>
    have hd : (tailNext v).length.toNat = v.length.toNat+4 :=
      addNat_toNat v.length 4 (by omega)
    rw [tailCopy, ih (copyWord store v.current v.length) (tailNext v)
      (by rw [hd]; omega) (by rw [hd]; omega)]
    exact copyWord_prefix store v.current v.length address hbefore

theorem bulkWritten_prefix (store : MachineStore α) (v : State) (address : UInt32)
    (hword : (v.current+v.aux2).toNat+16 < UInt32.size)
    (hbefore : address.toNat+4 ≤ (v.current+v.aux2).toNat) :
    (bulkWritten store v).wasm.mem.read32 address = store.wasm.mem.read32 address := by
  have hd4 := addNat_toNat (v.current+v.aux2) 4 (by omega)
  change (4+(v.current+v.aux2):UInt32).toNat = (v.current+v.aux2).toNat+4 at hd4
  have hd8 := addNat_toNat (v.current+v.aux2) 8 (by omega)
  change (8+(v.current+v.aux2):UInt32).toNat = (v.current+v.aux2).toNat+8 at hd8
  have hd12 := addNat_toNat (v.current+v.aux2) 12 (by omega)
  change (12+(v.current+v.aux2):UInt32).toNat = (v.current+v.aux2).toNat+12 at hd12
  dsimp only [bulkWritten]
  rw [copyWord_prefix _ _ _ _ (by rw [hd12]; omega),
    copyWord_prefix _ _ _ _ (by rw [hd8]; omega),
    copyWord_prefix _ _ _ _ (by rw [hd4]; omega),
    copyWord_prefix _ _ _ _ hbefore]

theorem bulkCopy_prefix (groups : Nat) :
    ∀ (store : MachineStore α) (v : State) (copied : Nat) (address : UInt32),
    v.current = UInt32.ofNat (4*copied) →
    v.aux2.toNat+4*(copied+4*groups) < UInt32.size →
    address.toNat+4 ≤ v.aux2.toNat →
    (bulkCopy store v groups).wasm.mem.read32 address = store.wasm.mem.read32 address := by
  induction groups with
  | zero => intros; rfl
  | succ groups ih =>
    intro store v copied address hcurrent hword hbefore
    have hda : (v.current+v.aux2).toNat = v.aux2.toNat+4*copied := by
      rw [hcurrent]; exact offset_toNat _ _ (by omega)
    have hnext : (bulkNext v).current = UInt32.ofNat (4*(copied+4)) := by
      change 16+v.current = _
      rw [hcurrent, show 4*(copied+4)=16+4*copied by omega, UInt32.ofNat_add]
      rfl
    rw [bulkCopy, ih (bulkWritten store v) (bulkNext v) (copied+4) address hnext
      (by change v.aux2.toNat+4*(copied+4+4*groups)<UInt32.size; omega) hbefore]
    exact bulkWritten_prefix store v address (by rw [hda]; omega) (by rw [hda]; omega)

end Project.Mergesort.DecodeLoopCost
