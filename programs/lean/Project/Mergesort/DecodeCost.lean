import Project.Mergesort.DecodeLoopCost

/-! Numerical work of the actual generated driver decode, including its
bulk/tail dispatchers, setup, allocation-result guard and block exits. -/
namespace Project.Mergesort.DecodeCost

open Wasm Wasm.SmallStep Project.Mergesort.DriverProof
open Project.Mergesort.DecodeLoopCost Project.Mergesort.Representations

def tailContinuation : Program :=
  [.localGet 9, .localGet 8, .add, .localSet 1,
    .localGet 2, .localGet 9, .const 2, .shl, .add, .localSet 6,
    .loop 0 0 tailBody, .localGet 1, .localSet 9]

def bulkBlock : Program :=
  [.localGet 6, .const 12, .ltU, .br_if 0,
    .localGet 1, .const 2147483644, .and, .localSet 5,
    .const 0, .localSet 9, .const 0, .localSet 3,
    .loop 0 0 bulkBody, .localGet 8, .eqz, .br_if 1,
    .localGet 4, .localGet 3, .add, .localSet 3]

theorem outer_shape : func3DecodeOuterBlockBody =
    .block 0 0 bulkBlock :: tailContinuation := rfl

def outerFrame (ctx : Context) : ControlFrame :=
  { kind := .block, paramArity := 0, resultArity := 0,
    body := func3DecodeOuterBlockBody, continuation := ctx.code, belowStack := ctx.stack }

def bulkFrame (ctx : Context) : ControlFrame :=
  { kind := .block, paramArity := 0, resultArity := 0,
    body := bulkBlock, continuation := tailContinuation, belowStack := ctx.stack }

def initial (source destination : UInt32) (n : Nat) (aux10 : UInt32) : State :=
  ⟨UInt32.ofNat n, source, UInt32.ofNat (4*n-4), destination, source,
    0, UInt32.ofNat (4*n), UInt32.ofNat (n%4), 0, aux10⟩

def bulkInitial (source destination : UInt32) (n groups tail : Nat) (aux10 : UInt32) : State :=
  ⟨UInt32.ofNat n, 0, UInt32.ofNat (4*n-4), destination, source,
    UInt32.ofNat (4*groups), UInt32.ofNat (4*n), UInt32.ofNat tail, 0, aux10⟩

def tailInitial (source destination : UInt32) (n bulk tail : Nat) (aux10 : UInt32) : State :=
  ⟨UInt32.ofNat n, source+4*UInt32.ofNat bulk, destination+4*UInt32.ofNat bulk,
    destination, source, UInt32.ofNat bulk, UInt32.ofNat (4*n), UInt32.ofNat tail,
    UInt32.ofNat bulk, aux10⟩

private theorem sub_four (n : Nat) (hp : 0<n) :
    UInt32.ofNat (4*n)+4294967292 = UInt32.ofNat (4*n-4) := by
  have hsplit : 4*n-4+4=4*n := by omega
  have hm : (4294967292 : UInt32)=0-4 := by decide
  calc
    _ = (UInt32.ofNat (4*n-4)+4)+(0-4) := by rw [← hsplit, UInt32.ofNat_add, hm]; rfl
    _ = UInt32.ofNat (4*n-4)+((0-4)+4) := by ac_rfl
    _ = _ := by rw [UInt32.sub_add_cancel, UInt32.add_zero]

private theorem shift_two (n : Nat) (hp : 0<n) (hb : 4*n<UInt32.size) :
    UInt32.ofNat (4*n-4) >>> (2 : UInt32) = UInt32.ofNat (n-1) := by
  apply UInt32.toNat.inj
  rw [UInt32.toNat_shiftRight, UInt32.toNat_ofNat_of_lt' (by omega : 4*n-4<UInt32.size),
    UInt32.toNat_ofNat_of_lt' (by omega : n-1<UInt32.size)]
  rw [show (2 : UInt32).toNat%32=2 by decide, Nat.shiftRight_eq_div_pow,
    show 4*n-4=4*(n-1) by omega]
  norm_num

private theorem tail_mask (n : Nat) (hb : n<UInt32.size) :
    UInt32.ofNat n &&& (3 : UInt32) = UInt32.ofNat (n%4) := by
  apply UInt32.toNat.inj
  rw [UInt32.toNat_and, UInt32.toNat_ofNat_of_lt' hb,
    show (3 : UInt32).toNat=3 by decide,
    UInt32.toNat_ofNat_of_lt' (by have := Nat.mod_lt n (by decide : 0<4); omega),
    show (3 : Nat)=2^2-1 by decide, Nat.and_two_pow_sub_one_eq_mod]

/-- The sixteen actual arithmetic initializers establish the generated bulk
and tail counters, including both wrapping subtraction constants. -/
theorem setup_cost (store : MachineStore α) (source destination : UInt32)
    (n : Nat) (current aux8 aux9 aux10 : UInt32) (ctx : Context)
    (hp : 0<n) (hb : 4*n<UInt32.size)
    (hostBytes : Config α → Nat → Config α → Nat) :
    CostedSteps (byteWork hostBytes)
      (config store ⟨source, current, UInt32.ofNat (4*n), destination, source,
        0, UInt32.ofNat (4*n), aux8, aux9, aux10⟩
        { ctx with code := func3DecodeSetup ++ ctx.code })
      (func3DecodeSetup.map StepKind.instruction)
      (config store (initial source destination n aux10) ctx) 16 := by
  have hsub := sub_four n hp
  have hshift := shift_two n hp hb
  have hsucc : UInt32.ofNat (n-1)+1=UInt32.ofNat n := by
    rw [UInt32.ofNat_succ, show n-1+1=n by omega]
  have hmask := tail_mask n (by omega)
  apply Steps.with_unit_cost
  · unfold config locals func3DecodeSetup initial
    simp only [List.map, List.cons_append, List.nil_append]
    wasm_steps [(.localGet rfl), .const, .add]
    rw [UInt32.add_comm (4294967292 : UInt32), hsub]
    wasm_steps [(.localTee rfl), .const, .shrU]
    rw [show (2%32 : UInt32)=2 by decide, hshift]
    wasm_steps [.const, .add]
    rw [UInt32.add_comm (1 : UInt32), hsucc]
    wasm_steps [(.localTee rfl), .const, .and]
    rw [hmask]
    wasm_steps [(.localSet rfl), .const, (.localSet rfl), (.localGet rfl)]
    exact Steps.single (.localSet (locals' := locals (initial source destination n aux10)
      (.i32 source :: ctx.stack)) rfl)
  · intro before kind after member
    simp only [func3DecodeSetup, List.map, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-- Scalar-tail setup recomputes the total length and destination cursor. -/
theorem tail_setup_cost (store : MachineStore α) (source destination : UInt32)
    (n bulk tail : Nat) (a1 a6 aux10 : UInt32) (ctx : Context)
    (hpartition : bulk+tail=n) (hostBytes : Config α → Nat → Config α → Nat) :
    CostedSteps (byteWork hostBytes)
      (config store ⟨a1, source+4*UInt32.ofNat bulk, a6, destination, source,
        UInt32.ofNat bulk, UInt32.ofNat (4*n), UInt32.ofNat tail, UInt32.ofNat bulk, aux10⟩
        { ctx with code := tailContinuation, controls := outerFrame ctx :: ctx.controls })
      ((tailContinuation.take 10).map StepKind.instruction)
      (config store (tailInitial source destination n bulk tail aux10)
        { ctx with code := tailContinuation.drop 10, controls := outerFrame ctx :: ctx.controls }) 10 := by
  have hsum : UInt32.ofNat tail+UInt32.ofNat bulk=UInt32.ofNat n := by
    rw [UInt32.add_comm, ← UInt32.ofNat_add, hpartition]
  apply Steps.with_unit_cost
  · unfold config locals tailContinuation tailInitial
    simp only [List.take, List.map, List.drop]
    wasm_steps [(.localGet rfl), (.localGet rfl), .add]
    rw [hsum]
    wasm_steps [(.localSet rfl), (.localGet rfl), (.localGet rfl), .const, .shl]
    rw [MemRegion.shl2_eq_mul4]
    wasm_steps [.add]
    rw [UInt32.add_comm (4*UInt32.ofNat bulk)]
    exact Steps.single (.localSet (locals' := locals
      (tailInitial source destination n bulk tail aux10)
      (.i32 (destination+4*UInt32.ofNat bulk) :: ctx.stack)) rfl)
  · intro before kind after member
    simp only [tailContinuation, List.take, List.map, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-- The tail's count postlude and outer block exit cost three transitions. -/
theorem tail_finish_cost (store : MachineStore α) (v : State) (ctx : Context)
    (hostBytes : Config α → Nat → Config α → Nat) :
    CostedSteps (byteWork hostBytes)
      (config store v { ctx with code := [.localGet 1, .localSet 9], controls := outerFrame ctx :: ctx.controls })
      [.instruction (.localGet 1), .instruction (.localSet 9), .administrative .exitControl]
      (config store { v with aux9 := v.dataPtr } ctx) 3 := by
  apply Steps.with_unit_cost
  · unfold config locals
    wasm_steps [(.localGet rfl), (.localSet rfl)]
    exact Steps.single (.exitControl rfl)
  · intro before kind after member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl <;> rfl

def tailFinal (source destination : UInt32) (n bulk : Nat) (aux10 : UInt32) : State :=
  ⟨UInt32.ofNat n, source+4*UInt32.ofNat n, destination+4*UInt32.ofNat n,
    destination, source, UInt32.ofNat bulk, UInt32.ofNat (4*n), 0, UInt32.ofNat n, aux10⟩

theorem tail_final_eq (source destination : UInt32) (n bulk tail : Nat) (aux10 : UInt32)
    (hpartition : bulk+tail=n) :
    let v := tailInitial source destination n bulk tail aux10
    { tailAdvance v tail with aux9 := (tailAdvance v tail).dataPtr } =
      tailFinal source destination n bulk aux10 := by
  dsimp only
  rw [tailAdvance_eq]
  have hadd (base : UInt32) : UInt32.ofNat (4*tail)+(base+4*UInt32.ofNat bulk) =
      base+4*UInt32.ofNat n := by
    rw [← hpartition, UInt32.ofNat_add, UInt32.mul_add, UInt32.ofNat_mul]
    change 4*UInt32.ofNat tail+(base+4*UInt32.ofNat bulk)=_
    ac_rfl
  have hneg : -UInt32.ofNat tail+UInt32.ofNat tail = 0 := by
    rw [UInt32.add_comm, ← UInt32.sub_eq_add_neg, UInt32.sub_self]
  simp only [tailInitial, tailFinal, hadd, hneg]

/-- Actual positive tail, including setup, loop entry/exit, count postlude and
outer block exit. It ends before the driver's next instruction. -/
theorem positive_tail_cost (store : MachineStore α) (source destination : UInt32)
    (n bulk tail : Nat) (a1 a6 aux10 : UInt32) (ctx : Context)
    (hpartition : bulk+tail=n) (hp : 0<tail)
    (hsw : source.toNat+4*n < UInt32.size)
    (hdw : destination.toNat+4*n < UInt32.size)
    (hs : source.toNat+4*n ≤ store.wasm.mem.pages*65536)
    (hd : destination.toNat+4*n ≤ store.wasm.mem.pages*65536)
    (hostBytes : Config α → Nat → Config α → Nat) :
    ∃ trace, CostedSteps (byteWork hostBytes)
      (config store ⟨a1, source+4*UInt32.ofNat bulk, a6, destination, source,
        UInt32.ofNat bulk, UInt32.ofNat (4*n), UInt32.ofNat tail, UInt32.ofNat bulk, aux10⟩
        { ctx with code := tailContinuation, controls := outerFrame ctx :: ctx.controls }) trace
      (config (tailCopy store (tailInitial source destination n bulk tail aux10) tail)
        (tailFinal source destination n bulk aux10) ctx) (17*tail+15) := by
  let v := tailInitial source destination n bulk tail aux10
  let lc : Context := { ctx with code := [.localGet 1, .localSet 9], controls := outerFrame ctx :: ctx.controls }
  have hsa : v.current.toNat=source.toNat+4*bulk := wordOffset_toNat source bulk (by omega)
  have hda : v.length.toNat=destination.toNat+4*bulk := wordOffset_toNat destination bulk (by omega)
  obtain ⟨tr, loop⟩ := tail_loop_cost store v lc tail hp rfl
    (by rw [hsa]; omega) (by rw [hda]; omega)
    (by rw [hsa]; omega) (by rw [hda]; omega) hostBytes
  have enter : CostedSteps (byteWork hostBytes)
      (config store v { ctx with
        code := tailContinuation.drop 10,
        controls := outerFrame ctx :: ctx.controls })
      [.instruction (.loop 0 0 tailBody)] (head tailBody store v lc) 1 :=
    CostedSteps.single .loop
  have setup := tail_setup_cost store source destination n bulk tail a1 a6 aux10 ctx hpartition hostBytes
  have finish := tail_finish_cost (tailCopy store v tail) (tailAdvance v tail) ctx hostBytes
  have run := ((setup.trans enter).trans loop).trans finish
  rw [tail_final_eq source destination n bulk tail aux10 hpartition] at run
  refine ⟨((tailContinuation.take 10).map StepKind.instruction ++
    [.instruction (.loop 0 0 tailBody)]) ++ tr ++
    [.instruction (.localGet 1), .instruction (.localSet 9), .administrative .exitControl], ?_⟩
  simpa only [show 10+1+(17*tail+1)+3=17*tail+15 by omega] using run

def bulkFinal (source destination : UInt32) (n groups tail : Nat) (aux10 : UInt32) : State :=
  ⟨UInt32.ofNat (16*(groups-1))+source, UInt32.ofNat (16*groups),
    UInt32.ofNat (16*(groups-1))+destination, destination, source,
    UInt32.ofNat (4*groups), UInt32.ofNat (4*n), UInt32.ofNat tail, UInt32.ofNat (4*groups), aux10⟩

theorem bulk_final_eq (source destination : UInt32) (n groups tail : Nat) (aux10 : UInt32)
    (hp : 0<groups) :
    bulkAdvance (bulkInitial source destination n groups tail aux10) groups =
      bulkFinal source destination n groups tail aux10 := by
  obtain ⟨g, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : groups≠0)
  rw [bulkAdvance_succ]
  simp [bulkInitial, bulkFinal]

/-- Enter the bulk loop along the generated non-small branch. -/
theorem bulk_setup_cost (store : MachineStore α) (source destination : UInt32)
    (n : Nat) (aux10 : UInt32) (ctx : Context)
    (hlarge : 4≤n) (hb : 4*n<UInt32.size)
    (hostBytes : Config α → Nat → Config α → Nat) :
    let lc : Context := { ctx with
      code := bulkBlock.drop 13,
      controls := bulkFrame ctx :: outerFrame ctx :: ctx.controls }
    ∃ trace, CostedSteps (byteWork hostBytes)
      (config store (initial source destination n aux10)
        { ctx with code := .block 0 0 func3DecodeOuterBlockBody :: ctx.code }) trace
      (head bulkBody store (bulkInitial source destination n (n/4) (n%4) aux10) lc) 15 := by
  dsimp only
  have hnotlt : ¬ UInt32.ofNat (4*n-4)<(12:UInt32) := by
    rw [UInt32.lt_iff_toNat_lt, UInt32.toNat_ofNat_of_lt' (by omega : 4*n-4<UInt32.size)]
    change ¬4*n-4<12
    omega
  have hmask := bulk4_signedMask_eq n (by norm_num [UInt32.size] at hb; omega)
  let trace := [.instruction (.block 0 0 func3DecodeOuterBlockBody),
    .instruction (.block 0 0 bulkBlock)] ++ (bulkBlock.take 13).map StepKind.instruction
  refine ⟨trace, ?_⟩
  apply Steps.with_unit_cost
  · unfold trace config head
    simp only [List.cons_append, List.nil_append]
    wasm_steps [.block]
    rw [outer_shape]
    wasm_steps [.block]
    unfold bulkBlock
    simp only [List.take, List.map, List.drop]
    simp only [config, locals, initial, bulkInitial]
    wasm_steps [(.localGet rfl), .const, (.ltU (result := 0) (by simp [hnotlt])), .brIfZero,
      (.localGet rfl), .const, .and]
    rw [hmask]
    wasm_steps [(.localSet rfl), .const, (.localSet rfl), .const, (.localSet rfl)]
    exact Steps.single .loop
  · intro before kind after member
    simp only [trace, bulkBlock, List.take, List.map, List.cons_append, List.nil_append,
      List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-- The small-input branch bypasses the unrolled loop in six transitions. -/
theorem small_setup_cost (store : MachineStore α) (source destination : UInt32)
    (n : Nat) (aux10 : UInt32) (ctx : Context) (hp : 0<n) (hsmall : n<4)
    (hostBytes : Config α → Nat → Config α → Nat) :
    CostedSteps (byteWork hostBytes)
      (config store (initial source destination n aux10)
        { ctx with code := .block 0 0 func3DecodeOuterBlockBody :: ctx.code })
      [.instruction (.block 0 0 func3DecodeOuterBlockBody), .instruction (.block 0 0 bulkBlock),
        .instruction (.localGet 6), .instruction (.const 12), .instruction .ltU, .instruction (.br_if 0)]
      (config store (initial source destination n aux10)
        { ctx with code := tailContinuation, controls := outerFrame ctx :: ctx.controls }) 6 := by
  have hlt : UInt32.ofNat (4*n-4)<(12:UInt32) := by
    rw [UInt32.lt_iff_toNat_lt, UInt32.toNat_ofNat_of_lt' (by norm_num [UInt32.size]; omega)]
    change 4*n-4<12
    omega
  apply Steps.with_unit_cost
  · unfold config
    wasm_steps [.block]
    rw [outer_shape]
    wasm_steps [.block]
    unfold bulkBlock locals initial
    wasm_steps [(.localGet rfl), .const, (.ltU (result := 1) (by simp [hlt]))]
    exact Steps.single (.brIf (by decide) rfl)
  · intro before kind after member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-- Zero tail leaves both generated decode blocks by their actual depth-one branch. -/
theorem zero_tail_cost (store : MachineStore α) (v : State) (ctx : Context)
    (hz : v.aux8=0) (hostBytes : Config α → Nat → Config α → Nat) :
    CostedSteps (byteWork hostBytes)
      (config store v { ctx with
        code := bulkBlock.drop 13,
        controls := bulkFrame ctx :: outerFrame ctx :: ctx.controls })
      [.instruction (.localGet 8), .instruction .eqz, .instruction (.br_if 1)]
      (config store v ctx) 3 := by
  apply Steps.with_unit_cost
  · unfold config bulkBlock
    simp only [List.drop, locals, func3AppendLocals]
    wasm_steps [(.localGet rfl)]
    rw [hz]
    wasm_steps [(.eqz (result := 1) (by simp))]
    exact Steps.single (.brIf (condition := 1) (by decide) rfl)
  · intro before kind after member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl <;> rfl

/-- A nonzero tail converts the byte offset to a source cursor and exits only
the inner block, retaining the outer block for the scalar continuation. -/
theorem after_bulk_cost (store : MachineStore α) (v : State) (ctx : Context)
    (hn : v.aux8≠0) (hostBytes : Config α → Nat → Config α → Nat) :
    CostedSteps (byteWork hostBytes)
      (config store v { ctx with
        code := bulkBlock.drop 13,
        controls := bulkFrame ctx :: outerFrame ctx :: ctx.controls })
      [.instruction (.localGet 8), .instruction .eqz, .instruction (.br_if 1),
        .instruction (.localGet 4), .instruction (.localGet 3), .instruction .add,
        .instruction (.localSet 3), .administrative .exitControl]
      (config store { v with current := v.current+v.aux4 }
        { ctx with code := tailContinuation, controls := outerFrame ctx :: ctx.controls }) 8 := by
  apply Steps.with_unit_cost
  · unfold config bulkBlock
    simp only [List.drop]
    wasm_steps [(.localGet rfl), (.eqz (result := 0) (by simp [hn])), .brIfZero,
      (.localGet rfl), (.localGet rfl), .add, (.localSet rfl)]
    exact Steps.single (.exitControl rfl)
  · intro before kind after member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-- Complete generated bulk/tail blocks, returning the authoritative decoded
count. The same execution preserves every read32 entirely before destination. -/
theorem blocks_cost (store : MachineStore α) (source destination : UInt32)
    (n : Nat) (aux10 : UInt32) (ctx : Context) (hp : 0<n)
    (hsw : source.toNat+4*n < UInt32.size)
    (hdw : destination.toNat+4*n < UInt32.size)
    (hs : source.toNat+4*n ≤ store.wasm.mem.pages*65536)
    (hd : destination.toNat+4*n ≤ store.wasm.mem.pages*65536)
    (hostBytes : Config α → Nat → Config α → Nat) :
    ∃ trace memory f1 f3 f6 f5 f8 amount,
      CostedSteps (byteWork hostBytes)
        (config store (initial source destination n aux10)
          { ctx with code := .block 0 0 func3DecodeOuterBlockBody :: ctx.code }) trace
        (config { store with wasm := { store.wasm with mem := memory } }
          ⟨f1, f3, f6, destination, source, f5, UInt32.ofNat (4*n), f8, UInt32.ofNat n, aux10⟩ ctx) amount ∧
      memory.pages = store.wasm.mem.pages ∧ amount ≤ 17*n+39 ∧
      (∀ address : UInt32, address.toNat+4≤destination.toNat →
        memory.read32 address = store.wasm.mem.read32 address) := by
  by_cases hsmall : n<4
  · have ht : n%4=n := Nat.mod_eq_of_lt hsmall
    have small := small_setup_cost store source destination n aux10 ctx hp hsmall hostBytes
    obtain ⟨tr, tail⟩ := positive_tail_cost store source destination n 0 n
      (UInt32.ofNat n) (UInt32.ofNat (4*n-4)) aux10 ctx (by omega) hp hsw hdw hs hd hostBytes
    have startEq : initial source destination n aux10 =
        ⟨UInt32.ofNat n, source+4*UInt32.ofNat 0, UInt32.ofNat (4*n-4), destination, source,
          UInt32.ofNat 0, UInt32.ofNat (4*n), UInt32.ofNat n, UInt32.ofNat 0, aux10⟩ := by
      simp [initial, ht]
    rw [← startEq] at tail
    have run := small.trans tail
    let v := tailInitial source destination n 0 n aux10
    have hstore := tailCopy_store store v n
    rw [hstore] at run
    refine ⟨[.instruction (.block 0 0 func3DecodeOuterBlockBody), .instruction (.block 0 0 bulkBlock),
        .instruction (.localGet 6), .instruction (.const 12), .instruction .ltU, .instruction (.br_if 0)] ++ tr,
      (tailCopy store v n).wasm.mem, UInt32.ofNat n, source+4*UInt32.ofNat n,
      destination+4*UInt32.ofNat n, 0, 0, 6+(17*n+15), ?_, tailCopy_pages store v n, by omega, ?_⟩
    · exact run
    · intro address hbefore
      exact tailCopy_prefix store v n address (by simpa [v, tailInitial] using hdw)
        (by simpa [v, tailInitial] using hbefore)
  · let g := n/4
    let b := 4*g
    let t := n%4
    have hg : 0<g := by dsimp [g]; omega
    have hpartition : b+t=n := by dsimp [b,g,t]; exact bulk4_add_tail n
    let v := bulkInitial source destination n g t aux10
    let lc : Context := { ctx with code := bulkBlock.drop 13, controls := bulkFrame ctx :: outerFrame ctx :: ctx.controls }
    obtain ⟨setupTrace, setup⟩ := bulk_setup_cost store source destination n aux10 ctx (by omega) (by omega) hostBytes
    obtain ⟨loopTrace, loop⟩ := bulk_loop_cost g store v lc 0 hg rfl rfl
      (by simp [v, bulkInitial])
      (by change source.toNat+4*(0+4*g)<UInt32.size; omega)
      (by change destination.toNat+4*(0+4*g)<UInt32.size; omega)
      (by change source.toNat+4*(0+4*g)≤store.wasm.mem.pages*65536; omega)
      (by change destination.toNat+4*(0+4*g)≤store.wasm.mem.pages*65536; omega)
      hostBytes
    have full := setup.trans loop
    rw [bulk_final_eq source destination n g t aux10 hg] at full
    let bs := bulkCopy store v g
    have bsp : bs.wasm.mem.pages=store.wasm.mem.pages := bulkCopy_pages store v g
    have bsframe : bs = { store with wasm := { store.wasm with mem := bs.wasm.mem } } :=
      bulkCopy_store store v g
    have bsprefix (address : UInt32) (hbefore : address.toNat+4≤destination.toNat) :
        bs.wasm.mem.read32 address = store.wasm.mem.read32 address :=
      bulkCopy_prefix g store v 0 address rfl
        (by change destination.toNat+4*(0+4*g)<UInt32.size; omega) hbefore
    by_cases ht : t=0
    · have hbn : b=n := by omega
      have leave := zero_tail_cost bs (bulkFinal source destination n g t aux10) ctx
        (by simp [bulkFinal,ht]) hostBytes
      have run := full.trans leave
      rw [bsframe] at run
      refine ⟨(setupTrace ++ loopTrace) ++
        [.instruction (.localGet 8), .instruction .eqz, .instruction (.br_if 1)],
        bs.wasm.mem, UInt32.ofNat (16*(g-1))+source, UInt32.ofNat (16*g),
        UInt32.ofNat (16*(g-1))+destination, UInt32.ofNat n, 0,
        15+(45*g+1)+3, ?_, bsp, by omega, bsprefix⟩
      have hbn' : 4*g=n := hbn
      simpa only [bulkFinal, hbn', ht, show UInt32.ofNat 0 = (0 : UInt32) from rfl] using run
    · have htp : 0<t := by omega
      have hne : UInt32.ofNat t ≠0 := by
        intro hz
        have hnat := congrArg UInt32.toNat hz
        rw [UInt32.toNat_ofNat_of_lt' (by dsimp [t]; have := Nat.mod_lt n (by decide : 0<4); norm_num [UInt32.size]; omega)] at hnat
        change t=0 at hnat
        omega
      have afterRun := after_bulk_cost bs (bulkFinal source destination n g t aux10) ctx hne hostBytes
      have hptr : UInt32.ofNat (16*g)+source=source+4*UInt32.ofNat b := by
        rw [show 16*g=4*b by dsimp [b]; omega, UInt32.ofNat_mul]
        change 4*UInt32.ofNat b+source=source+4*UInt32.ofNat b
        exact UInt32.add_comm _ _
      obtain ⟨tailTrace, tail⟩ := positive_tail_cost bs source destination n b t
        (UInt32.ofNat (16*(g-1))+source) (UInt32.ofNat (16*(g-1))+destination)
        aux10 ctx hpartition htp hsw hdw (by rw [bsp]; exact hs) (by rw [bsp]; exact hd) hostBytes
      have afterRun' : CostedSteps (byteWork hostBytes)
          (config bs (bulkFinal source destination n g t aux10) lc)
          [.instruction (.localGet 8), .instruction .eqz, .instruction (.br_if 1),
            .instruction (.localGet 4), .instruction (.localGet 3), .instruction .add,
            .instruction (.localSet 3), .administrative .exitControl]
          (config bs ⟨UInt32.ofNat (16*(g-1))+source, source+4*UInt32.ofNat b,
            UInt32.ofNat (16*(g-1))+destination, destination, source, UInt32.ofNat b,
            UInt32.ofNat (4*n), UInt32.ofNat t, UInt32.ofNat b, aux10⟩
            { ctx with code := tailContinuation, controls := outerFrame ctx :: ctx.controls }) 8 := by
        simpa only [bulkFinal, hptr] using afterRun
      have run := (full.trans afterRun').trans tail
      let tv := tailInitial source destination n b t aux10
      have tf := tailCopy_store bs tv t
      rw [tf] at run
      have frameEq : { bs with wasm := { bs.wasm with mem := (tailCopy bs tv t).wasm.mem } } =
          { store with wasm := { store.wasm with mem := (tailCopy bs tv t).wasm.mem } } := by
        rw [bsframe]
      rw [frameEq] at run
      refine ⟨((setupTrace ++ loopTrace) ++
        [.instruction (.localGet 8), .instruction .eqz, .instruction (.br_if 1),
          .instruction (.localGet 4), .instruction (.localGet 3), .instruction .add,
          .instruction (.localSet 3), .administrative .exitControl]) ++ tailTrace,
        (tailCopy bs tv t).wasm.mem, UInt32.ofNat n, source+4*UInt32.ofNat n,
        destination+4*UInt32.ofNat n, UInt32.ofNat b, 0,
        (15+(45*g+1)+8)+(17*t+15), run, (tailCopy_pages bs tv t).trans bsp, by dsimp [b] at hpartition; omega, ?_⟩
      intro address hbefore
      have haddr : tv.length.toNat=destination.toNat+4*b := wordOffset_toNat destination b (by omega)
      exact (tailCopy_prefix bs tv t address (by rw [haddr]; omega) (by rw [haddr]; omega)).trans
        (bsprefix address hbefore)

/-- A successful allocation's nonzero pointer discharges the actual null guard. -/
theorem allocated_guard_cost (store : MachineStore α) (v : State) (destination : UInt32)
    (ctx : Context) (hnonnull : destination≠0)
    (hostBytes : Config α → Nat → Config α → Nat) :
    CostedSteps (byteWork hostBytes)
      (config store v { ctx with
        stack := .i32 destination :: ctx.stack,
        code := [.localTee 2, .eqz, .br_if 1] ++ ctx.code })
      [.instruction (.localTee 2), .instruction .eqz, .instruction (.br_if 1)]
      (config store { v with aux2 := destination } ctx) 3 := by
  apply Steps.with_unit_cost
  · unfold config locals
    simp only [List.cons_append, List.nil_append]
    wasm_steps [(.localTee (locals' := locals { v with aux2 := destination }
      (.i32 destination :: ctx.stack)) rfl),
      (.eqz (result := 0) (by simp [hnonnull]))]
    exact Steps.single .brIfZero
  · intro before kind after member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl <;> rfl

/-- Complete decode after the actual values-allocation return. This matches
DriverProof.twp_func3_decode_allocated's generated code and live result slots.
The numerical bound and prefix preservation concern the same physical trace. -/
theorem decode_allocated_cost (store : MachineStore α) (source destination : UInt32)
    (n : Nat) (current aux2 aux8 aux9 aux10 : UInt32) (ctx : Context)
    (hp : 0<n) (hnonnull : destination≠0)
    (hsw : source.toNat+4*n < UInt32.size)
    (hdw : destination.toNat+4*n < UInt32.size)
    (hs : source.toNat+4*n ≤ store.wasm.mem.pages*65536)
    (hd : destination.toNat+4*n ≤ store.wasm.mem.pages*65536)
    (hostBytes : Config α → Nat → Config α → Nat) :
    ∃ trace memory f1 f3 f6 f5 f8 amount,
      CostedSteps (byteWork hostBytes)
        ⟨.running ⟨func3AppendLocals source current (UInt32.ofNat (4*n)) aux2 source 0
            (UInt32.ofNat (4*n)) aux8 aux9 aux10 (.i32 destination :: ctx.stack),
          [.localTee 2, .eqz, .br_if 1] ++ func3DecodeSetup ++
            [.block 0 0 func3DecodeOuterBlockBody] ++ ctx.code,
          ctx.arity, ctx.remainder, ctx.controls, ctx.calls⟩, store⟩ trace
        ⟨.running ⟨func3AppendLocals f1 f3 f6 destination source f5
            (UInt32.ofNat (4*n)) f8 (UInt32.ofNat n) aux10 ctx.stack,
          ctx.code, ctx.arity, ctx.remainder, ctx.controls, ctx.calls⟩,
          { store with wasm := { store.wasm with mem := memory } }⟩ amount ∧
      memory.pages = store.wasm.mem.pages ∧ amount ≤ 17*n+58 ∧
      (∀ address : UInt32, address.toNat+4≤destination.toNat →
        memory.read32 address = store.wasm.mem.read32 address) := by
  let code := .block 0 0 func3DecodeOuterBlockBody :: ctx.code
  let v : State := ⟨source, current, UInt32.ofNat (4*n), aux2, source, 0,
    UInt32.ofNat (4*n), aux8, aux9, aux10⟩
  have guard := allocated_guard_cost store v destination
    { ctx with code := func3DecodeSetup ++ code } hnonnull hostBytes
  have setup := setup_cost store source destination n current aux8 aux9 aux10
    { ctx with code := code } hp (by omega) hostBytes
  obtain ⟨tr, memory, f1, f3, f6, f5, f8, amount, blocks, pages, bound, hprefix⟩ :=
    blocks_cost store source destination n aux10 ctx hp hsw hdw hs hd hostBytes
  have run := (guard.trans setup).trans blocks
  refine ⟨([.instruction (.localTee 2), .instruction .eqz, .instruction (.br_if 1)] ++
    func3DecodeSetup.map StepKind.instruction) ++ tr,
    memory, f1, f3, f6, f5, f8, 3+16+amount, ?_, pages, by omega, hprefix⟩
  simpa only [config, locals, v, code, List.append_assoc, List.cons_append, List.nil_append] using run

end Project.Mergesort.DecodeCost
