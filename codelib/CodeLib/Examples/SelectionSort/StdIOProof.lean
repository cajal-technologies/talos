import CodeLib.Examples.SelectionSort.StdIO

/-!
# Correctness of the selection-sort StdIO wrappers

The host-facing read and write phases are proved once for either executable.
The middle phase then uses the induction proof for `recursive` or the invariant
proof for `loop`, but both discharge the same stream-level contract.
-/

namespace Wasm.Examples.SelectionSort.StdIO

open Wasm SepLogic SmallStep
open Iris Iris.Std

theorem execute_read (program : Executable)
    (store wasm : Store Wasm.StdIO.State)
    (length pointer count : UInt32)
    (hinvoke : Wasm.StdIO.readHost.invoke store
      [.i32 length, .i32 pointer] = .Return [.i32 count] wasm) :
    execute program 2 0 store [.i32 pointer, .i32 length] =
      some ([.i32 count], wasm) := by
  let machine : MachineStore Wasm.StdIO.State :=
    { runtime := { module := program.module, host := Wasm.StdIO.env }, wasm := store }
  let initial : Config Wasm.StdIO.State :=
    { expr := .running
        ⟨⟨[], [], [.i32 pointer, .i32 length]⟩, [.call 0], 1, [], [], []⟩
      store := machine }
  let middle : Config Wasm.StdIO.State :=
    { expr := .running ⟨⟨[], [], [.i32 count]⟩, [], 1, [], [], []⟩
      store := { machine with wasm } }
  have hcallRaw := Step.callHostReturn
    (store := machine) (functionIndex := 0)
    (imp := Wasm.StdIO.imports[0])
    (hostFunction := Wasm.StdIO.readHost)
    (params := []) (localValues := [])
    (values := [.i32 pointer, .i32 length])
    (results := [.i32 count]) (wasm := wasm)
    (code := []) (arity := 1) (remainder := [])
    (controls := []) (calls := [])
    (by simp [machine, program.imports_eq, Wasm.StdIO.imports])
    (by simp [machine, program.imports_eq]) rfl hinvoke
  have hcall : Step initial (.host 0) middle := by
    simpa [initial, middle, machine, Wasm.StdIO.imports, Wasm.StdIO.env] using hcallRaw
  have hfinish : Step middle (.administrative .finish)
      ⟨.done [.i32 count], { machine with wasm }⟩ := Step.finish
  have hrun := runSteps_eq_success_of_steps
    (Steps.cons hcall (Steps.single hfinish))
  have hinit : SmallStep.initConfig
      { module := program.module, host := Wasm.StdIO.env } 0 store
        [.i32 pointer, .i32 length] = .ok initial := by
    simp [SmallStep.initConfig, initial, machine, program.imports_eq,
      Wasm.StdIO.imports, Wasm.StdIO.env]
  simp only [execute, hinit]
  rw [show (runSteps 2 initial).result =
      .success [.i32 count] { machine with wasm } by simpa using hrun]

theorem execute_write (program : Executable)
    (store wasm : Store Wasm.StdIO.State) (length pointer : UInt32)
    (hinvoke : Wasm.StdIO.writeHost.invoke store
      [.i32 length, .i32 pointer] = .Return [] wasm) :
    execute program 2 1 store [.i32 pointer, .i32 length] =
      some ([], wasm) := by
  let machine : MachineStore Wasm.StdIO.State :=
    { runtime := { module := program.module, host := Wasm.StdIO.env }, wasm := store }
  let initial : Config Wasm.StdIO.State :=
    { expr := .running
        ⟨⟨[], [], [.i32 pointer, .i32 length]⟩, [.call 1], 0, [], [], []⟩
      store := machine }
  let middle : Config Wasm.StdIO.State :=
    { expr := .running ⟨⟨[], [], []⟩, [], 0, [], [], []⟩
      store := { machine with wasm } }
  have hcallRaw := Step.callHostReturn
    (store := machine) (functionIndex := 1)
    (imp := Wasm.StdIO.imports[1])
    (hostFunction := Wasm.StdIO.writeHost)
    (params := []) (localValues := [])
    (values := [.i32 pointer, .i32 length]) (results := [])
    (wasm := wasm) (code := []) (arity := 0) (remainder := [])
    (controls := []) (calls := [])
    (by simp [machine, program.imports_eq, Wasm.StdIO.imports])
    (by simp [machine, program.imports_eq]) rfl hinvoke
  have hcall : Step initial (.host 1) middle := by
    simpa [initial, middle, machine, Wasm.StdIO.imports, Wasm.StdIO.env] using hcallRaw
  have hfinish : Step middle (.administrative .finish)
      ⟨.done [], { machine with wasm }⟩ := Step.finish
  have hrun := runSteps_eq_success_of_steps
    (Steps.cons hcall (Steps.single hfinish))
  have hinit : SmallStep.initConfig
      { module := program.module, host := Wasm.StdIO.env } 1 store
        [.i32 pointer, .i32 length] = .ok initial := by
    simp [SmallStep.initConfig, initial, machine, program.imports_eq,
      Wasm.StdIO.imports, Wasm.StdIO.env]
  simp only [execute, hinit]
  rw [show (runSteps 2 initial).result =
      .success [] { machine with wasm } by simpa using hrun]

theorem execute_write_bytes (program : Executable)
    (store : Store Wasm.StdIO.State) (length : UInt32)
    (hbound : array.toNat + length.toNat ≤ Wasm.StdIO.byteCapacity store) :
    execute program 2 1 store [.i32 array, .i32 length] =
      some ([], writtenStore store length) := by
  apply execute_write
  simp only [Wasm.StdIO.writeHost, Wasm.StdIO.writeResult]
  rw [if_pos]
  · rfl
  · simp only [Wasm.StdIO.rangeInBounds]
    exact decide_eq_true hbound

private theorem take_eq_self_of_length_le {β : Type} (xs : List β) (n : Nat)
    (h : xs.length ≤ n) : xs.take n = xs := by
  induction xs generalizing n with
  | nil => simp
  | cons x xs ih =>
      cases n with
      | zero => simp at h
      | succ n =>
          simp only [List.take_succ_cons, List.length_cons] at h ⊢
          rw [ih n (Nat.le_of_succ_le_succ h)]

@[simp] private theorem initialStore_host (program : Executable)
    (input : List UInt8) :
    (initialStore program input).host = Wasm.StdIO.State.ofInput input := rfl

set_option maxRecDepth 100000 in
private theorem initial_byteCapacity (program : Executable)
    (input : List UInt8) :
    Wasm.StdIO.byteCapacity (initialStore program input) = 65536 := by
  change (program.module.initialStore (α := Wasm.StdIO.State)).mem.pages * 65536 = 65536
  have hpages :
      (program.module.initialStore (α := Wasm.StdIO.State)).mem.pages = 1 := by
    simpa only using program.memory_pages
  rw [hpages]

def afterRead (program : Executable) (input : List UInt64) :
    Store Wasm.StdIO.State :=
  { initialStore program (serialize input) with
    mem := (initialStore program (serialize input)).mem.writeBytes
      array.toNat (serialize input)
    host := { input := [], output := [] } }

set_option maxRecDepth 10000 in
theorem read_fits (program : Executable) (input : List UInt64)
    (hfit : Fits input) :
    execute program 2 0 (initialStore program (serialize input))
      [.i32 array, .i32 (UInt32.ofNat bufferBytes)] =
      some ([.i32 (UInt32.ofNat (serialize input).length)],
        afterRead program input) := by
  apply execute_read
  simp only [Wasm.StdIO.readHost, Wasm.StdIO.readResult,
    initialStore_host, Wasm.StdIO.State.ofInput]
  have hbuffer : (UInt32.ofNat bufferBytes).toNat = bufferBytes :=
    UInt32.toNat_ofNat_of_lt' (by decide)
  rw [hbuffer, take_eq_self_of_length_le _ _ hfit]
  rw [if_pos (by
    simp only [Wasm.StdIO.rangeInBounds, array,
      initial_byteCapacity]
    apply decide_eq_true
    simpa only [Fits, bufferBytes, show (0 : UInt32).toNat = 0 by decide,
      Nat.zero_add] using hfit)]
  simp [afterRead, array]

private theorem afterRead_byteCapacity (program : Executable)
    (input : List UInt64) :
    Wasm.StdIO.byteCapacity (afterRead program input) = 65536 := by
  simpa only [afterRead, Wasm.StdIO.byteCapacity, Mem.writeBytes] using
    initial_byteCapacity program (serialize input)

theorem probe_afterRead (program : Executable) (input : List UInt64) :
    execute program 2 0 (afterRead program input)
      [.i32 (UInt32.ofNat 65536), .i32 1] =
      some ([.i32 0], afterRead program input) := by
  apply execute_read
  apply Wasm.StdIO.read_empty
  · rfl
  · rw [afterRead_byteCapacity]
    decide

theorem encodedLength_toNat (input : List UInt64) (hfit : Fits input) :
    (UInt32.ofNat (serialize input).length).toNat =
      (serialize input).length := by
  apply UInt32.toNat_ofNat_of_lt'
  simp only [Fits, serialize_length, bufferBytes] at hfit ⊢
  simp only [UInt32.size]
  omega

theorem encodedLength_words (input : List UInt64) (hfit : Fits input) :
    (UInt32.ofNat (serialize input).length).toNat / 8 = input.length := by
  rw [encodedLength_toNat input hfit, serialize_length]
  omega

/-! ## The packed stream and the u64 separation-logic array agree -/

def writeWordArray64 (mem : Mem) (base : UInt32) : List UInt64 → Mem
  | [] => mem
  | value :: values => writeWordArray64 (mem.write64 base value) (base + 8) values

def heap64Aux (heap : WasmHeapMap (Option UInt8)) (base : UInt32) :
    List UInt64 → WasmHeapMap (Option UInt8)
  | [] => heap
  | value :: values => heap64Aux (store64Heap heap base value) (base + 8) values

def inputHeap (input : List UInt64) : WasmHeapMap (Option UInt8) :=
  heap64Aux ∅ array input

theorem writeBytes_encodeWord (mem : Mem) (base : UInt32) (value : UInt64) :
    mem.writeBytes base.toNat (encodeWord value) = mem.write64 base value := by
  cases mem with
  | mk pages bytes =>
    simp only [Mem.writeBytes, encodeWord, List.length_cons, List.length_nil,
      Mem.write64]
    congr
    funext i
    by_cases h0 : i = base.toNat
    · subst i; simp
    by_cases h1 : i = base.toNat + 1
    · subst i; simp
    by_cases h2 : i = base.toNat + 2
    · subst i; simp
    by_cases h3 : i = base.toNat + 3
    · subst i; simp
    by_cases h4 : i = base.toNat + 4
    · subst i; simp
    by_cases h5 : i = base.toNat + 5
    · subst i; simp
    by_cases h6 : i = base.toNat + 6
    · subst i; simp
    by_cases h7 : i = base.toNat + 7
    · subst i; simp
    rw [dif_neg (by omega)]
    simp [h0, h1, h2, h3, h4, h5, h6, h7]

theorem writeBytes_serialize (mem : Mem) (base : UInt32)
    (values : List UInt64)
    (hfit : base.toNat + 8 * values.length < UInt32.size) :
    mem.writeBytes base.toNat (serialize values) =
      writeWordArray64 mem base values := by
  induction values generalizing mem base with
  | nil =>
      simp only [serialize, List.flatMap_nil, writeWordArray64]
      cases mem
      simp only [Mem.writeBytes, List.length_nil, Nat.add_zero]
      congr
      funext i
      rw [dif_neg (by omega)]
  | cons value values ih =>
      simp only [serialize, List.flatMap_cons, writeWordArray64]
      rw [Mem.writeBytes_append, writeBytes_encodeWord]
      simp only [List.length_cons, Nat.mul_add] at hfit
      have hbase : (base + 8).toNat = base.toNat + 8 :=
        UInt32.add_ofNat_toNat_noWrap base 8 (by decide) (by
          simp only [UInt32.size] at hfit ⊢
          omega)
      rw [show base.toNat + (encodeWord value).length = (base + 8).toNat by
        simp [encodeWord, hbase]]
      apply ih
      rw [hbase]
      omega

theorem heap64Aux_agrees
    (heap : WasmHeapMap (Option UInt8)) (mem : Mem) (base : UInt32)
    (values : List UInt64) (hagree : heapAgreesWithMem heap mem)
    (hfit : base.toNat + 8 * values.length < UInt32.size) :
    heapAgreesWithMem (heap64Aux heap base values)
      (writeWordArray64 mem base values) := by
  induction values generalizing heap mem base with
  | nil => simpa [heap64Aux, writeWordArray64]
  | cons value values ih =>
      simp only [heap64Aux, writeWordArray64, List.length_cons] at *
      simp only [UInt32.size] at hfit
      apply ih
      · apply store64_sound
        · exact UInt32.add_ofNat_toNat_noWrap base 1 (by decide) (by omega)
        · exact UInt32.add_ofNat_toNat_noWrap base 2 (by decide) (by omega)
        · exact UInt32.add_ofNat_toNat_noWrap base 3 (by decide) (by omega)
        · exact UInt32.add_ofNat_toNat_noWrap base 4 (by decide) (by omega)
        · exact UInt32.add_ofNat_toNat_noWrap base 5 (by decide) (by omega)
        · exact UInt32.add_ofNat_toNat_noWrap base 6 (by decide) (by omega)
        · exact UInt32.add_ofNat_toNat_noWrap base 7 (by decide) (by omega)
        · exact hagree
      · have h8 : (base + 8 : UInt32).toNat = base.toNat + 8 :=
          UInt32.add_ofNat_toNat_noWrap base 8 (by decide) (by omega)
        rw [h8]
        simp only [UInt32.size]
        omega

theorem heap64Aux_inBounds
    (heap : WasmHeapMap (Option UInt8)) (mem : Mem) (base : UInt32)
    (values : List UInt64) (hinBounds : heapAddressesInBounds heap mem)
    (hfit : base.toNat + 8 * values.length < UInt32.size)
    (hmem : base.toNat + 8 * values.length ≤ mem.pages * 65536) :
    heapAddressesInBounds (heap64Aux heap base values)
      (writeWordArray64 mem base values) := by
  induction values generalizing heap mem base with
  | nil => simpa [heap64Aux, writeWordArray64]
  | cons value values ih =>
      simp only [heap64Aux, writeWordArray64, List.length_cons] at *
      simp only [UInt32.size] at hfit
      have h8 : (base + 8 : UInt32).toNat = base.toNat + 8 :=
        UInt32.add_ofNat_toNat_noWrap base 8 (by decide) (by omega)
      apply ih
      · apply store64_inBounds
        · exact UInt32.add_ofNat_toNat_noWrap base 1 (by decide) (by omega)
        · exact UInt32.add_ofNat_toNat_noWrap base 2 (by decide) (by omega)
        · exact UInt32.add_ofNat_toNat_noWrap base 3 (by decide) (by omega)
        · exact UInt32.add_ofNat_toNat_noWrap base 4 (by decide) (by omega)
        · exact UInt32.add_ofNat_toNat_noWrap base 5 (by decide) (by omega)
        · exact UInt32.add_ofNat_toNat_noWrap base 6 (by decide) (by omega)
        · exact UInt32.add_ofNat_toNat_noWrap base 7 (by decide) (by omega)
        · exact hinBounds
        · omega
      · rw [h8]
        simp only [UInt32.size]
        omega
      · simp only [Mem.write64]
        rw [h8]
        omega

private theorem empty_agrees (mem : Mem) :
    heapAgreesWithMem (∅ : WasmHeapMap (Option UInt8)) mem := by
  intro address byte hget
  rw [get?_empty] at hget
  contradiction

private theorem empty_inBounds (mem : Mem) :
    heapAddressesInBounds (∅ : WasmHeapMap (Option UInt8)) mem := by
  intro address byte hget
  rw [get?_empty] at hget
  contradiction

theorem afterRead_mem_eq (program : Executable) (input : List UInt64)
    (hfit : Fits input) :
    (afterRead program input).mem =
      writeWordArray64 (initialStore program (serialize input)).mem array input := by
  unfold afterRead
  simp only
  apply writeBytes_serialize
  simp only [array, UInt32.reduceToNat, Nat.zero_add, UInt32.size,
    Fits, serialize_length, bufferBytes] at hfit ⊢
  omega

theorem inputHeap_agrees (program : Executable) (input : List UInt64)
    (hfit : Fits input) :
    heapAgreesWithMem (inputHeap input) (afterRead program input).mem := by
  rw [afterRead_mem_eq program input hfit]
  unfold inputHeap
  apply heap64Aux_agrees
  · apply empty_agrees
  · simp only [array, UInt32.reduceToNat, Nat.zero_add, UInt32.size,
      Fits, serialize_length, bufferBytes] at hfit ⊢
    omega

theorem inputHeap_inBounds (program : Executable) (input : List UInt64)
    (hfit : Fits input) :
    heapAddressesInBounds (inputHeap input) (afterRead program input).mem := by
  rw [afterRead_mem_eq program input hfit]
  unfold inputHeap
  apply heap64Aux_inBounds
  · apply empty_inBounds
  · simp only [array, UInt32.reduceToNat, Nat.zero_add, UInt32.size,
      Fits, serialize_length, bufferBytes] at hfit ⊢
    omega
  · have hpages :
        (initialStore program (serialize input)).mem.pages = 1 := by
      exact program.memory_pages
    rw [hpages]
    simp only [array, UInt32.reduceToNat, Nat.zero_add, Nat.one_mul,
      Fits, serialize_length, bufferBytes] at hfit ⊢
    exact hfit

set_option maxHeartbeats 6000000 in
theorem heap64Aux_pointsTo [WasmHeapGS]
    (heap : WasmHeapMap (Option UInt8)) (base : UInt32)
    (values : List UInt64)
    (hdisjoint : ∀ address byte, get? heap address = some byte →
      address.toNat < base.toNat)
    (hfit : base.toNat + 8 * values.length < UInt32.size) :
    ([∗map] address ↦ value ∈ heap64Aux heap base values,
      pointsTo (GF := WasmHeapGF) (H := WasmHeapMap)
        address (DFrac.own 1) value) ⊢
      array64At base values ∗
      ([∗map] address ↦ value ∈ heap,
        pointsTo (GF := WasmHeapGF) (H := WasmHeapMap)
          address (DFrac.own 1) value) := by
  induction values generalizing heap base with
  | nil =>
      simp only [heap64Aux, array64At, BI.emp_sep.to_eq]
      iintro Hheap
      iexact Hheap
  | cons value values ih =>
      simp only [heap64Aux, List.length_cons] at *
      simp only [UInt32.size] at hfit
      have hn (n : Nat) (hn : n ≤ 8) :
          (base + UInt32.ofNat n).toNat = base.toNat + n := by
        apply UInt32.add_ofNat_toNat_noWrap base n
        · omega
        · omega
      have hn1 := hn 1 (by omega)
      have hn2 := hn 2 (by omega)
      have hn3 := hn 3 (by omega)
      have hn4 := hn 4 (by omega)
      have hn5 := hn 5 (by omega)
      have hn6 := hn 6 (by omega)
      have hn7 := hn 7 (by omega)
      have hn8 := hn 8 (by omega)
      have hl1 : (base + 1 : UInt32).toNat = base.toNat + 1 := by
        apply UInt32.add_ofNat_toNat_noWrap base 1 (by decide)
        omega
      have hl2 : (base + 2 : UInt32).toNat = base.toNat + 2 := by
        apply UInt32.add_ofNat_toNat_noWrap base 2 (by decide)
        omega
      have hl3 : (base + 3 : UInt32).toNat = base.toNat + 3 := by
        apply UInt32.add_ofNat_toNat_noWrap base 3 (by decide)
        omega
      have hl4 : (base + 4 : UInt32).toNat = base.toNat + 4 := by
        apply UInt32.add_ofNat_toNat_noWrap base 4 (by decide)
        omega
      have hl5 : (base + 5 : UInt32).toNat = base.toNat + 5 := by
        apply UInt32.add_ofNat_toNat_noWrap base 5 (by decide)
        omega
      have hl6 : (base + 6 : UInt32).toNat = base.toNat + 6 := by
        apply UInt32.add_ofNat_toNat_noWrap base 6 (by decide)
        omega
      have hl7 : (base + 7 : UInt32).toNat = base.toNat + 7 := by
        apply UInt32.add_ofNat_toNat_noWrap base 7 (by decide)
        omega
      have hl8 : (base + 8 : UInt32).toNat = base.toNat + 8 := by
        apply UInt32.add_ofNat_toNat_noWrap base 8 (by decide)
        omega
      have hget (n : Nat) (hnle : n < 8) :
          get? heap (base + UInt32.ofNat n) = none := by
        by_contra h
        obtain ⟨byte, hbyte⟩ := Option.ne_none_iff_exists.mp h
        have hlt := hdisjoint _ _ hbyte.symm
        rw [hn n (by omega)] at hlt
        omega
      have hget0 : get? heap base = none := by
        simpa using hget 0 (by omega)
      have hget1 := hget 1 (by omega)
      have hget2 := hget 2 (by omega)
      have hget3 := hget 3 (by omega)
      have hget4 := hget 4 (by omega)
      have hget5 := hget 5 (by omega)
      have hget6 := hget 6 (by omega)
      have hget7 := hget 7 (by omega)
      have hgetL1 : get? heap (base + 1) = none := by simpa using hget1
      have hgetL2 : get? heap (base + 2) = none := by simpa using hget2
      have hgetL3 : get? heap (base + 3) = none := by simpa using hget3
      have hgetL4 : get? heap (base + 4) = none := by simpa using hget4
      have hgetL5 : get? heap (base + 5) = none := by simpa using hget5
      have hgetL6 : get? heap (base + 6) = none := by simpa using hget6
      have hgetL7 : get? heap (base + 7) = none := by simpa using hget7
      have hne (i j : Nat) (hi : i ≤ 7) (hj : j ≤ 7) (hij : i ≠ j) :
          base + UInt32.ofNat i ≠ base + UInt32.ofNat j := by
        intro heq
        have heq' := congrArg UInt32.toNat heq
        rw [hn i (by omega), hn j (by omega)] at heq'
        omega
      have hneU (i j : UInt32) (hi : i.toNat ≤ 7) (hj : j.toNat ≤ 7)
          (hij : i ≠ j) : base + i ≠ base + j := by
        simpa only [UInt32.ofNat_toNat] using
          hne i.toNat j.toNat hi hj (fun h => hij (UInt32.toNat_inj.mp h))
      have hbaseNe (n : UInt32) (hn : n.toNat ≤ 7) (hpos : 0 < n.toNat) :
          base ≠ base + n := by
        have h := hneU 0 n (by decide) hn (by
          intro heq
          have := congrArg UInt32.toNat heq
          exact hpos.ne' this.symm)
        simpa using h
      have hdisjoint' : ∀ address byte,
          get? (store64Heap heap base value) address = some byte →
          address.toNat < (base + 8).toNat := by
        intro address byte haddress
        change address.toNat < (base + UInt32.ofNat 8).toNat
        rw [hn8]
        by_cases h7 : address = base + 7
        · subst address; rw [hl7]; omega
        by_cases h6 : address = base + 6
        · subst address; rw [hl6]; omega
        by_cases h5 : address = base + 5
        · subst address; rw [hl5]; omega
        by_cases h4 : address = base + 4
        · subst address; rw [hl4]; omega
        by_cases h3 : address = base + 3
        · subst address; rw [hl3]; omega
        by_cases h2 : address = base + 2
        · subst address; rw [hl2]; omega
        by_cases h1 : address = base + 1
        · subst address; rw [hl1]; omega
        by_cases h0 : address = base
        · subst address; omega
        simp only [store64Heap, get?_insert_ne (Ne.symm h7),
          get?_insert_ne (Ne.symm h6), get?_insert_ne (Ne.symm h5),
          get?_insert_ne (Ne.symm h4), get?_insert_ne (Ne.symm h3),
          get?_insert_ne (Ne.symm h2), get?_insert_ne (Ne.symm h1),
          get?_insert_ne (Ne.symm h0)] at haddress
        have hlt := hdisjoint address byte haddress
        omega
      have hfit' : (base + 8).toNat + 8 * values.length < UInt32.size := by
        change (base + UInt32.ofNat 8).toNat + 8 * values.length < UInt32.size
        rw [hn8]
        simp only [UInt32.size]
        omega
      iintro Hheap
      ihave Hsplit := ih (store64Heap heap base value) (base + 8)
        hdisjoint' hfit' $$ Hheap
      icases Hsplit with ⟨Hvalues, Hstored⟩
      ihave Hword := store64Heap_pointsTo heap base value
        hget0
        (by simpa only [get?_insert_ne (hbaseNe 1 (by decide) (by decide))]
          using hgetL1)
        (by
          simp only [get?_insert_ne (hneU 1 2 (by decide) (by decide) (by decide)),
            get?_insert_ne (hbaseNe 2 (by decide) (by decide))]
          exact hgetL2)
        (by
          simp only [get?_insert_ne (hneU 2 3 (by decide) (by decide) (by decide)),
            get?_insert_ne (hneU 1 3 (by decide) (by decide) (by decide)),
            get?_insert_ne (hbaseNe 3 (by decide) (by decide))]
          exact hgetL3)
        (by
          simp only [get?_insert_ne (hneU 3 4 (by decide) (by decide) (by decide)),
            get?_insert_ne (hneU 2 4 (by decide) (by decide) (by decide)),
            get?_insert_ne (hneU 1 4 (by decide) (by decide) (by decide)),
            get?_insert_ne (hbaseNe 4 (by decide) (by decide))]
          exact hgetL4)
        (by
          simp only [get?_insert_ne (hneU 4 5 (by decide) (by decide) (by decide)),
            get?_insert_ne (hneU 3 5 (by decide) (by decide) (by decide)),
            get?_insert_ne (hneU 2 5 (by decide) (by decide) (by decide)),
            get?_insert_ne (hneU 1 5 (by decide) (by decide) (by decide)),
            get?_insert_ne (hbaseNe 5 (by decide) (by decide))]
          exact hgetL5)
        (by
          simp only [get?_insert_ne (hneU 5 6 (by decide) (by decide) (by decide)),
            get?_insert_ne (hneU 4 6 (by decide) (by decide) (by decide)),
            get?_insert_ne (hneU 3 6 (by decide) (by decide) (by decide)),
            get?_insert_ne (hneU 2 6 (by decide) (by decide) (by decide)),
            get?_insert_ne (hneU 1 6 (by decide) (by decide) (by decide)),
            get?_insert_ne (hbaseNe 6 (by decide) (by decide))]
          exact hgetL6)
        (by
          simp only [get?_insert_ne (hneU 6 7 (by decide) (by decide) (by decide)),
            get?_insert_ne (hneU 5 7 (by decide) (by decide) (by decide)),
            get?_insert_ne (hneU 4 7 (by decide) (by decide) (by decide)),
            get?_insert_ne (hneU 3 7 (by decide) (by decide) (by decide)),
            get?_insert_ne (hneU 2 7 (by decide) (by decide) (by decide)),
            get?_insert_ne (hneU 1 7 (by decide) (by decide) (by decide)),
            get?_insert_ne (hbaseNe 7 (by decide) (by decide))]
          exact hgetL7) $$ Hstored
      icases Hword with ⟨Hword, Hheap⟩
      simp only [array64At]
      isplitl [Hword Hvalues]
      · isplitl [Hword]
        · iexact Hword
        · iexact Hvalues
      · iexact Hheap

theorem inputHeap_pointsTo [WasmHeapGS] (input : List UInt64)
    (hfit : Fits input) :
    ([∗map] address ↦ value ∈ inputHeap input,
      pointsTo (GF := WasmHeapGF) (H := WasmHeapMap)
        address (DFrac.own 1) value) ⊢ array64At array input := by
  unfold inputHeap
  iintro Hheap
  ihave Hsplit := heap64Aux_pointsTo ∅ array input
    (fun address byte hget => by simp [get?_empty] at hget)
    (by
      simp only [array, UInt32.reduceToNat, Nat.zero_add, UInt32.size,
        Fits, serialize_length, bufferBytes] at hfit ⊢
      omega) $$ Hheap
  icases Hsplit with ⟨Harray, _Hempty⟩
  iexact Harray

def readWordArray64 (mem : Mem) (base : UInt32) : Nat → List UInt64
  | 0 => []
  | n + 1 => mem.read64 base :: readWordArray64 mem (base + 8) n

theorem array64At_words [WasmSmallStepGS hlc]
    (store : MachineStore α) (steps : Nat) (obs : List StepKind)
    (threads : Nat) (base : UInt32) (output : List UInt64)
    (hfit : base.toNat + 8 * output.length < UInt32.size) :
    stateInterp (GF := WasmHeapGF) store steps obs threads ∗
      array64At base output ==∗
    stateInterp (GF := WasmHeapGF) store steps obs threads ∗
      array64At base output ∗
      ⌜readWordArray64 store.wasm.mem base output.length = output⌝ := by
  induction output generalizing base with
  | nil =>
      simp only [array64At, List.length_nil, readWordArray64]
      iintro ⟨Hstate, Hempty⟩
      imodintro
      isplitl [Hstate]
      · iexact Hstate
      isplitl [Hempty]
      · iexact Hempty
      · ipureintro; trivial
  | cons value output ih =>
      simp only [array64At, List.length_cons] at *
      have hn (n : Nat) (hn : n ≤ 8) :
          (base + UInt32.ofNat n).toNat = base.toNat + n := by
        apply UInt32.add_ofNat_toNat_noWrap base n
        · omega
        · simp only [UInt32.size] at hfit ⊢; omega
      iintro ⟨Hstate, Hword, Houtput⟩
      imod stateInterp_pointsTo_u64_facts_frame store steps obs threads
        base value (hn 1 (by omega)) (hn 2 (by omega))
        (hn 3 (by omega)) (hn 4 (by omega)) (hn 5 (by omega))
        (hn 6 (by omega)) (hn 7 (by omega)) $$
        [$Hstate $Hword] with ⟨Hstate, Hword, %hword⟩
      have hfit' : (base + 8).toNat + 8 * output.length < UInt32.size := by
        change (base + UInt32.ofNat 8).toNat + 8 * output.length < UInt32.size
        rw [hn 8 (by omega)]
        simp only [UInt32.size] at hfit ⊢
        omega
      imod ih (base + 8) hfit' $$ [$Hstate $Houtput] with
        ⟨Hstate, Houtput, %hrest⟩
      imodintro
      isplitl [Hstate]
      · iexact Hstate
      isplitl [Hword Houtput]
      · isplitl [Hword]
        · iexact Hword
        · iexact Houtput
      · ipureintro
        simp only [readWordArray64]
        rw [hword.1]
        exact congrArg (value :: ·) hrest

theorem array64At_capacity [WasmSmallStepGS hlc]
    (store : MachineStore α) (steps : Nat)
    (observations : List StepKind) (threads : Nat)
    (base : UInt32) (values : List UInt64)
    (hfit : base.toNat + 8 * values.length < UInt32.size)
    (hbaseBound : base.toNat ≤ store.wasm.mem.pages * 65536) :
    stateInterp (GF := WasmHeapGF) store steps observations threads ∗
      array64At base values ==∗
    stateInterp (GF := WasmHeapGF) store steps observations threads ∗
      array64At base values ∗
      ⌜base.toNat + 8 * values.length ≤
        store.wasm.mem.pages * 65536⌝ := by
  by_cases hempty : values = []
  · subst values
    iintro ⟨Hstate, Harray⟩
    imodintro
    isplitl [Hstate]
    · iexact Hstate
    isplitl [Harray]
    · iexact Harray
    · ipureintro
      simpa using hbaseBound
  · have hlength : 0 < values.length := by
      cases values with
      | nil => contradiction
      | cons value values => simp
    let k := values.length - 1
    have hk : k < values.length := by simp [k, hlength]
    let address := base + 8 * UInt32.ofNat k
    have haddress : address.toNat = base.toNat + 8 * k := by
      exact Mem.words64_slotAddr_toNat base k (by
        simp only [UInt32.size] at hfit
        omega)
    have hn (n : Nat) (hn : n ≤ 7) :
        (address + UInt32.ofNat n).toNat = address.toNat + n := by
      apply UInt32.add_ofNat_toNat_noWrap address n
      · omega
      · simp only [UInt32.size] at hfit ⊢
        rw [haddress]
        omega
    iintro ⟨Hstate, Harray⟩
    ihave Hfocus := array64At_get base values k hk $$ Harray
    icases Hfocus with ⟨Hword, Hrestore⟩
    imod stateInterp_pointsTo_u64_facts_frame
      store steps observations threads address values[k]
      (hn 1 (by omega)) (hn 2 (by omega)) (hn 3 (by omega))
      (hn 4 (by omega)) (hn 5 (by omega)) (hn 6 (by omega))
      (hn 7 (by omega)) $$ [$Hstate $Hword] with
      ⟨Hstate, Hword, %hfacts⟩
    imodintro
    isplitl [Hstate]
    · iexact Hstate
    isplitl [Hrestore Hword]
    · iapply Hrestore
      iexact Hword
    · ipureintro
      rw [haddress] at hfacts
      dsimp only [k] at hfacts
      omega

/-! ## Adequacy of the two host-independent sort calls -/

def sortArguments (input : List UInt64) : List Value :=
  [.i32 (UInt32.ofNat input.length), .i32 array]

def concreteSortConfig (program : Executable) (input : List UInt64) : Config Unit :=
  sortConfig program (afterRead program input) (sortArguments input)

def SortPost (input : List UInt64)
    (_values : List Value) (store : MachineStore α) : Prop :=
  ∃ output,
    List.Perm input output ∧ Sorted output ∧
    readWordArray64 store.wasm.mem array input.length = output ∧
    8 * input.length ≤ store.wasm.mem.pages * 65536

set_option maxHeartbeats 6000000 in
theorem twp_recursiveSortCall [WasmSmallStepGS hlc]
    (input : List UInt64) (hfit : Fits input) :
    (([∗map] address ↦ value ∈ inputHeap input,
        pointsTo (GF := WasmHeapGF) (H := WasmHeapMap)
          address (DFrac.own 1) value) ∗
      ([∗map] index ↦ value ∈ (∅ : WasmGlobalMap Value),
        globalPointsTo index value) ∗
      runtimeModuleOwn (concreteSortConfig recursive input).store.runtime.module) ⊢
      WP (concreteSortConfig recursive input).expr @ Stuckness.NotStuck; ⊤
        [{ values,
          ∀ (store : MachineStore Unit) (_observations : List StepKind),
            stateInterp (GF := WasmHeapGF) store 0 [] 0 -∗
            ⌜SortPost input values store⌝ }] := by
  iintro ⟨Hheap, _Hglobals, Hruntime⟩
  ihave Harray := inputHeap_pointsTo input hfit $$ Hheap
  have hentry : recursive.sortEntry = 3 := rfl
  simp only [concreteSortConfig, sortConfig, sortArguments, hentry]
  iapply twp_recursiveSort recursive.module 2 3
    (by decide) (by rfl) (by decide) (by rfl) array input
    (by
      simp only [array, UInt32.reduceToNat, Nat.zero_add, UInt32.size,
        Fits, serialize_length, bufferBytes] at hfit ⊢
      omega)
    (callerLocals := ⟨[], [], []⟩) (stack := []) (code := [])
    (arity := 0) (remainder := []) (controls := []) (calls := [])
  isplitl [Hruntime]
  · iexact Hruntime
  isplitl [Harray]
  · iexact Harray
  · iintro %output %hpure Hruntime Harray
    iapply Wasm.SmallStep.twp_finish
    iapply twp.value rfl
    iintro %store %observations Hstate
    have hlength := hpure.1.length_eq
    have houtFit : array.toNat + 8 * output.length < UInt32.size := by
      simp only [array, UInt32.reduceToNat, Nat.zero_add, UInt32.size,
        Fits, serialize_length, bufferBytes] at hfit ⊢
      omega
    imod array64At_words store 0 [] 0 array output houtFit $$
      [$Hstate $Harray] with ⟨Hstate, Harray, %hwords⟩
    imod array64At_capacity store 0 [] 0 array output houtFit
      (by simp [array]) $$ [$Hstate $Harray] with
      ⟨_Hstate, _Harray, %hcapacity⟩
    ipureintro
    refine ⟨output, hpure.1, ?_, ?_, ?_⟩
    · simpa [Sorted, SelectionSort.Sorted] using hpure.2
    · simpa [hlength] using hwords
    · simpa [array, hlength] using hcapacity

set_option maxHeartbeats 6000000 in
theorem twp_loopSortCall [WasmSmallStepGS hlc]
    (input : List UInt64) (hfit : Fits input) :
    (([∗map] address ↦ value ∈ inputHeap input,
        pointsTo (GF := WasmHeapGF) (H := WasmHeapMap)
          address (DFrac.own 1) value) ∗
      ([∗map] index ↦ value ∈ (∅ : WasmGlobalMap Value),
        globalPointsTo index value) ∗
      runtimeModuleOwn (concreteSortConfig loop input).store.runtime.module) ⊢
      WP (concreteSortConfig loop input).expr @ Stuckness.NotStuck; ⊤
        [{ values,
          ∀ (store : MachineStore Unit) (_observations : List StepKind),
            stateInterp (GF := WasmHeapGF) store 0 [] 0 -∗
            ⌜SortPost input values store⌝ }] := by
  iintro ⟨Hheap, _Hglobals, Hruntime⟩
  ihave Harray := inputHeap_pointsTo input hfit $$ Hheap
  have hentry : loop.sortEntry = 2 := rfl
  simp only [concreteSortConfig, sortConfig, sortArguments, hentry]
  iapply twp_loopSort loop.module 2 (by decide) (by rfl) array input
    (by
      simp only [array, UInt32.reduceToNat, Nat.zero_add, UInt32.size,
        Fits, serialize_length, bufferBytes] at hfit ⊢
      omega)
    (callerLocals := ⟨[], [], []⟩) (stack := []) (code := [])
    (arity := 0) (remainder := []) (controls := []) (calls := [])
  isplitl [Hruntime]
  · iexact Hruntime
  isplitl [Harray]
  · iexact Harray
  · iintro %output %hpure Hruntime Harray
    iapply Wasm.SmallStep.twp_finish
    iapply twp.value rfl
    iintro %store %observations Hstate
    have hlength := hpure.1.length_eq
    have houtFit : array.toNat + 8 * output.length < UInt32.size := by
      simp only [array, UInt32.reduceToNat, Nat.zero_add, UInt32.size,
        Fits, serialize_length, bufferBytes] at hfit ⊢
      omega
    imod array64At_words store 0 [] 0 array output houtFit $$
      [$Hstate $Harray] with ⟨Hstate, Harray, %hwords⟩
    imod array64At_capacity store 0 [] 0 array output houtFit
      (by simp [array]) $$ [$Hstate $Harray] with
      ⟨_Hstate, _Harray, %hcapacity⟩
    ipureintro
    refine ⟨output, hpure.1, ?_, ?_, ?_⟩
    · simpa [Sorted, SelectionSort.Sorted] using hpure.2
    · simpa [hlength] using hwords
    · simpa [array, hlength] using hcapacity

theorem recursive_sort_stronglyNormalizing
    (input : List UInt64) (hfit : Fits input) :
    Iris.ProgramLogic.StronglyNormalizing
      (Iris.ProgramLogic.ExprErasedStep (Expr := Expr Unit)
        (State := MachineStore Unit) (Obs := StepKind))
      ((concreteSortConfig recursive input).expr,
        (concreteSortConfig recursive input).store) := by
  apply Wasm.SmallStep.wasm_smallStep_heap_globals_runtime_stronglyNormalizing.{0}
    (concreteSortConfig recursive input) (inputHeap input) ∅
    (fun _values => iprop(True))
  · exact inputHeap_agrees recursive input hfit
  · exact inputHeap_inBounds recursive input hfit
  · exact globalHeapAgrees_empty _
  · intro _
    iintro Hresources
    ihave Hsort := twp_recursiveSortCall input hfit $$ Hresources
    iapply twp.mono (fun _values => ?_) $$ Hsort
    iintro _Hpost
    itrivial

theorem recursive_sort_terminatesWith
    (input : List UInt64) (hfit : Fits input) :
    SmallStep.TerminatesWith
      (concreteSortConfig recursive input) (SortPost input) := by
  apply Wasm.SmallStep.stronglyNormalizing_adequate_terminates
    (concreteSortConfig recursive input) (SortPost input)
    (recursive_sort_stronglyNormalizing input hfit)
  apply wasm_smallStep_heap_globals_runtime_store_adequacy.{0}
    (concreteSortConfig recursive input) (inputHeap input) ∅ (SortPost input)
  · exact inputHeap_agrees recursive input hfit
  · exact inputHeap_inBounds recursive input hfit
  · exact globalHeapAgrees_empty _
  · intro _
    iintro Hresources
    iapply twp.to_wp
    iapply twp_recursiveSortCall input hfit
    iexact Hresources

theorem loop_sort_stronglyNormalizing
    (input : List UInt64) (hfit : Fits input) :
    Iris.ProgramLogic.StronglyNormalizing
      (Iris.ProgramLogic.ExprErasedStep (Expr := Expr Unit)
        (State := MachineStore Unit) (Obs := StepKind))
      ((concreteSortConfig loop input).expr,
        (concreteSortConfig loop input).store) := by
  apply Wasm.SmallStep.wasm_smallStep_heap_globals_runtime_stronglyNormalizing.{0}
    (concreteSortConfig loop input) (inputHeap input) ∅
    (fun _values => iprop(True))
  · exact inputHeap_agrees loop input hfit
  · exact inputHeap_inBounds loop input hfit
  · exact globalHeapAgrees_empty _
  · intro _
    iintro Hresources
    ihave Hsort := twp_loopSortCall input hfit $$ Hresources
    iapply twp.mono (fun _values => ?_) $$ Hsort
    iintro _Hpost
    itrivial

theorem loop_sort_terminatesWith
    (input : List UInt64) (hfit : Fits input) :
    SmallStep.TerminatesWith
      (concreteSortConfig loop input) (SortPost input) := by
  apply Wasm.SmallStep.stronglyNormalizing_adequate_terminates
    (concreteSortConfig loop input) (SortPost input)
    (loop_sort_stronglyNormalizing input hfit)
  apply wasm_smallStep_heap_globals_runtime_store_adequacy.{0}
    (concreteSortConfig loop input) (inputHeap input) ∅ (SortPost input)
  · exact inputHeap_agrees loop input hfit
  · exact inputHeap_inBounds loop input hfit
  · exact globalHeapAgrees_empty _
  · intro _
    iintro Hresources
    iapply twp.to_wp
    iapply twp_loopSortCall input hfit
    iexact Hresources

theorem executeSort_host (program : Executable) (fuel : Nat)
    (initial final : Store Wasm.StdIO.State) (args values : List Value)
    (hexecute : executeSort program fuel initial args = some (values, final)) :
    final.host = initial.host := by
  unfold executeSort at hexecute
  generalize hresult : (runSteps fuel _).result = result at hexecute
  cases result <;> simp_all [replaceHost]
  case success =>
    have hhost := congrArg
      (fun concrete : Store Wasm.StdIO.State => concrete.host) hexecute.2
    simpa [replaceHost] using hhost.symm

private theorem execute_sort_complete_of_terminates
    (program : Executable) (input : List UInt64)
    (hterminates : SmallStep.TerminatesWith
      (concreteSortConfig program input) (SortPost input)) :
    ∃ fuel values store,
      executeSort program fuel (afterRead program input) (sortArguments input) =
        some (values, store) ∧
      SortPost input values
        { runtime := { module := program.module, host := Wasm.StdIO.env }
          wasm := store } := by
  rcases hterminates with ⟨trace, values, finalStore, hsteps, hpost⟩
  let store : Store Wasm.StdIO.State :=
    replaceHost finalStore.wasm (afterRead program input).host
  refine ⟨trace.length, values, store, ?_, ?_⟩
  · unfold executeSort
    change (match
      (runSteps trace.length (concreteSortConfig program input)).result with
      | .success values finalStore =>
          some (values, replaceHost finalStore.wasm
            (afterRead program input).host)
      | _ => none) = some (values, store)
    rw [runSteps_eq_success_of_steps hsteps]
  · simpa [SortPost, store, replaceHost] using hpost

theorem recursive_execute_sort_complete
    (input : List UInt64) (hfit : Fits input) :
    ∃ fuel values store,
      executeSort recursive fuel (afterRead recursive input) (sortArguments input) =
        some (values, store) ∧
      SortPost input values
        { runtime := { module := recursive.module, host := Wasm.StdIO.env }
          wasm := store } :=
  execute_sort_complete_of_terminates recursive input
    (recursive_sort_terminatesWith input hfit)

theorem loop_execute_sort_complete
    (input : List UInt64) (hfit : Fits input) :
    ∃ fuel values store,
      executeSort loop fuel (afterRead loop input) (sortArguments input) =
        some (values, store) ∧
      SortPost input values
        { runtime := { module := loop.module, host := Wasm.StdIO.env }
          wasm := store } :=
  execute_sort_complete_of_terminates loop input
    (loop_sort_terminatesWith input hfit)

/-! ## Returning the sorted memory as a little-endian stream -/

private theorem readBytes_eight_add (mem : Mem) (offset n : Nat) :
    mem.readBytes offset (8 + n) =
      [mem.bytes offset, mem.bytes (offset + 1), mem.bytes (offset + 2),
       mem.bytes (offset + 3), mem.bytes (offset + 4),
       mem.bytes (offset + 5), mem.bytes (offset + 6),
       mem.bytes (offset + 7)] ++ mem.readBytes (offset + 8) n := by
  unfold Mem.readBytes
  rw [List.range_add]
  simp only [List.map_append, List.range_succ, List.range_zero,
    List.map_cons, List.map_nil, List.nil_append]
  congr 1
  simp [Nat.add_assoc]

/-- Deserializing complete little-endian words observes exactly `Mem.words64`. -/
theorem deserialize_readBytes64 (mem : Mem) (base : UInt32) (count : Nat)
    (hfit : base.toNat + 8 * count < UInt32.size) :
    deserialize (mem.readBytes base.toNat (8 * count)) =
      some (readWordArray64 mem base count) := by
  induction count generalizing base with
  | zero => rfl
  | succ count ih =>
      rw [show 8 * (count + 1) = 8 + 8 * count by omega]
      rw [readBytes_eight_add]
      simp only [List.cons_append, List.nil_append, deserialize]
      have hbase : (base + 8).toNat = base.toNat + 8 := by
        apply UInt32.add_ofNat_toNat_noWrap base 8 (by decide)
        simp only [UInt32.size] at hfit ⊢
        omega
      have hdecode : decodeWord
          (mem.bytes base.toNat) (mem.bytes (base.toNat + 1))
          (mem.bytes (base.toNat + 2)) (mem.bytes (base.toNat + 3))
          (mem.bytes (base.toNat + 4)) (mem.bytes (base.toNat + 5))
          (mem.bytes (base.toNat + 6)) (mem.bytes (base.toNat + 7)) =
          mem.read64 base := by
        rfl
      rw [hdecode]
      simp only [readWordArray64]
      change (deserialize (mem.readBytes (base.toNat + 8) (8 * count))).map
          (mem.read64 base :: ·) =
        some (mem.read64 base :: readWordArray64 mem (base + 8) count)
      rw [← hbase, ih]
      · rfl
      · rw [hbase]
        omega

set_option maxRecDepth 10000 in
theorem run_fits (program : Executable) (fuel : Nat)
    (input : List UInt64) (hfit : Fits input) :
    run program fuel (serialize input) =
      runAfterRead program fuel (UInt32.ofNat (serialize input).length)
        (afterRead program input) := by
  unfold run
  rw [read_fits program input hfit]
  simp only [Bind.bind, Option.bind]

private theorem correct_of_sort_complete
    (program : Executable)
    (hsortComplete : ∀ input, Fits input →
      ∃ fuel values store,
        executeSort program fuel (afterRead program input) (sortArguments input) =
          some (values, store) ∧
        SortPost input values
          { runtime := { module := program.module, host := Wasm.StdIO.env }
            wasm := store }) :
    Correct program := by
  intro input hfit
  rcases hsortComplete input hfit with
    ⟨fuel, values, afterSort, hsort, output, hperm, hsorted, hread,
      hcapacity⟩
  have hhost := executeSort_host program fuel
    (afterRead program input) afterSort (sortArguments input) values hsort
  have hbyteLength :
      (UInt32.ofNat (serialize input).length).toNat = 8 * input.length := by
    rw [encodedLength_toNat input hfit, serialize_length]
  have hwriteBound : array.toNat +
      (UInt32.ofNat (serialize input).length).toNat ≤
      Wasm.StdIO.byteCapacity afterSort := by
    simp only [array, UInt32.reduceToNat, Nat.zero_add,
      Wasm.StdIO.byteCapacity, hbyteLength]
    exact hcapacity
  have hwrite := execute_write_bytes program afterSort
    (UInt32.ofNat (serialize input).length) hwriteBound
  have houtput : afterSort.host.output = [] := by
    rw [hhost]
    rfl
  have hrun : run program fuel (serialize input) =
      some (afterSort.mem.readBytes array.toNat (8 * input.length)) := by
    rw [run_fits program fuel input hfit]
    unfold runAfterRead
    rw [probe_afterRead program input]
    simp only [guard]
    rw [encodedLength_words input hfit]
    simp only [Bind.bind, Option.bind, if_true, Pure.pure]
    unfold sortArguments at hsort
    rw [hsort]
    simp only []
    rw [hwrite]
    simp only [writtenStore, houtput, List.nil_append, hbyteLength]
  refine ⟨output, ⟨fuel, ?_⟩, hperm, hsorted⟩
  unfold runValues
  rw [hrun]
  simp only [Option.bind_some]
  rw [deserialize_readBytes64]
  · exact congrArg some hread
  · simp only [array, UInt32.reduceToNat, Nat.zero_add, UInt32.size,
      Fits, serialize_length, bufferBytes] at hfit ⊢
    omega

/-- The recursive StdIO selection sort terminates and returns a sorted
permutation. Its algorithmic proof is the induction proof in `TotalProof`. -/
theorem recursive_correct : RecursiveCorrect := by
  exact correct_of_sort_complete recursive recursive_execute_sort_complete

/-- The loop-based StdIO selection sort terminates and returns a sorted
permutation. Its algorithmic proof uses the inner and outer loop invariants in
`TotalProof`. -/
theorem loop_correct : LoopCorrect := by
  exact correct_of_sort_complete loop loop_execute_sort_complete

end Wasm.Examples.SelectionSort.StdIO
