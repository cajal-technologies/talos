import CodeLib.Examples.MergeSort.TotalProof
import CodeLib.Examples.Quicksort
import CodeLib.RustStd.MemArray
import Interpreter.Wasm.Host.StdIO

/-!
# Merge sort as a `StdIO` program

This layer turns the memory-oriented merge-sort implementation into a small
byte-stream program.  Its input and output format is a packed sequence of
little-endian `UInt32` values.  The entry point reads the input into the first
half of its one-page memory, uses the second half as scratch space, sorts the
words, and writes the sorted first half to the append-only output stream.
-/

namespace Wasm.Examples.MergeSort.StdIO

open Wasm SepLogic SmallStep
open Iris Iris.Std

/-- Each of the source and scratch arrays owns half of the 64-KiB page. -/
def bufferBytes : Nat := 32768

def source : UInt32 := 0
def scratch : UInt32 := UInt32.ofNat bufferBytes

/-- The four little-endian bytes of a 32-bit word. -/
def encodeWord (value : UInt32) : List UInt8 :=
  [ (value &&& 0xff).toUInt8
  , ((value >>> 8) &&& 0xff).toUInt8
  , ((value >>> 16) &&& 0xff).toUInt8
  , ((value >>> 24) &&& 0xff).toUInt8 ]

/-- Reassemble a 32-bit word from its four little-endian bytes. -/
def decodeWord (b₀ b₁ b₂ b₃ : UInt8) : UInt32 :=
  b₀.toUInt32 ||| (b₁.toUInt32 <<< 8) |||
    (b₂.toUInt32 <<< 16) ||| (b₃.toUInt32 <<< 24)

/-- Packed little-endian serialization of a list of 32-bit words. -/
def serialize (values : List UInt32) : List UInt8 :=
  values.flatMap encodeWord

/-- Decode a packed little-endian byte sequence. A trailing partial word is
rejected rather than silently ignored. -/
def deserialize : List UInt8 → Option (List UInt32)
  | [] => some []
  | b₀ :: b₁ :: b₂ :: b₃ :: rest =>
      (deserialize rest).map (decodeWord b₀ b₁ b₂ b₃ :: ·)
  | _ => none

@[simp] theorem decode_encode (value : UInt32) :
    decodeWord
      (value &&& 0xff).toUInt8
      (((value >>> 8) &&& 0xff).toUInt8)
      (((value >>> 16) &&& 0xff).toUInt8)
      (((value >>> 24) &&& 0xff).toUInt8) = value := by
  simp only [decodeWord]
  bv_decide

@[simp] theorem deserialize_serialize (values : List UInt32) :
    deserialize (serialize values) = some values := by
  induction values with
  | nil => rfl
  | cons value values ih =>
      simp only [serialize, List.flatMap_cons, encodeWord, List.cons_append,
        List.nil_append, deserialize, decode_encode]
      change (deserialize (serialize values)).map (value :: ·) = some (value :: values)
      rw [ih]
      rfl

@[simp] theorem serialize_length (values : List UInt32) :
    (serialize values).length = 4 * values.length := by
  induction values with
  | nil => rfl
  | cons value values ih =>
      change (List.flatMap encodeWord values).length = 4 * values.length at ih
      simp only [serialize, List.flatMap_cons, encodeWord, List.cons_append,
        List.nil_append, List.length_cons, Nat.mul_add]
      omega

theorem writeBytes_encodeWord (mem : Mem) (base value : UInt32) :
    mem.writeBytes base.toNat (encodeWord value) = mem.write32 base value := by
  cases mem with
  | mk pages bytes =>
    simp only [Mem.writeBytes, encodeWord, List.length_cons, List.length_nil,
      Mem.write32]
    congr
    funext i
    by_cases h0 : i = base.toNat
    · subst i
      simp
    by_cases h1 : i = base.toNat + 1
    · subst i
      simp
    by_cases h2 : i = base.toNat + 2
    · subst i
      simp
    by_cases h3 : i = base.toNat + 3
    · subst i
      simp
    rw [dif_neg (by omega)]
    simp [h0, h1, h2, h3]

/-- Packed stream serialization and the word-array model used by the
merge-sort proof describe exactly the same memory update. -/
theorem writeBytes_serialize (mem : Mem) (base : UInt32)
    (values : List UInt32)
    (hfit : base.toNat + 4 * values.length < UInt32.size) :
    mem.writeBytes base.toNat (serialize values) =
      writeWordArray mem base values := by
  induction values generalizing mem base with
  | nil =>
      simp only [serialize, List.flatMap_nil, writeWordArray]
      cases mem
      simp only [Mem.writeBytes, List.length_nil, Nat.add_zero]
      congr
      funext i
      rw [dif_neg (by omega)]
  | cons value values ih =>
      simp only [serialize, List.flatMap_cons, writeWordArray]
      rw [Mem.writeBytes_append, writeBytes_encodeWord]
      simp only [List.length_cons, Nat.mul_add] at hfit
      have hbase : (base + 4).toNat = base.toNat + 4 := by
        simp only [UInt32.toNat_add, UInt32.reduceToNat]
        rw [Nat.mod_eq_of_lt]
        change base.toNat + 4 < 4294967296
        change base.toNat + (4 * values.length + 4) < 4294967296 at hfit
        omega
      rw [show base.toNat + (encodeWord value).length =
          (base + 4).toNat by simp [encodeWord, hbase]]
      apply ih
      rw [hbase]
      change base.toNat + 4 + 4 * values.length < 4294967296
      change base.toNat + (4 * values.length + 4) < 4294967296 at hfit
      omega

private theorem readBytes_four_add (mem : Mem) (offset n : Nat) :
    mem.readBytes offset (4 + n) =
      [mem.bytes offset, mem.bytes (offset + 1), mem.bytes (offset + 2),
       mem.bytes (offset + 3)] ++ mem.readBytes (offset + 4) n := by
  unfold Mem.readBytes
  rw [List.range_add]
  simp only [List.map_append, List.range_succ, List.range_zero,
    List.map_cons, List.map_nil, List.nil_append]
  congr 1
  simp [Nat.add_assoc]

/-- Deserializing a byte slice of complete words is the same observation as
the word-array reader used in merge sort's postcondition. -/
theorem deserialize_readBytes (mem : Mem) (base : UInt32) (count : Nat)
    (hfit : base.toNat + 4 * count < UInt32.size) :
    deserialize (mem.readBytes base.toNat (4 * count)) =
      some (readWordArray mem base count) := by
  induction count generalizing base with
  | zero =>
      rfl
  | succ count ih =>
      rw [show 4 * (count + 1) = 4 + 4 * count by omega]
      rw [readBytes_four_add]
      simp only [List.cons_append, List.nil_append, deserialize]
      have hbase : (base + 4).toNat = base.toNat + 4 := by
        simp only [UInt32.toNat_add, UInt32.reduceToNat]
        rw [Nat.mod_eq_of_lt]
        change base.toNat + 4 < 4294967296
        change base.toNat + 4 * (count + 1) < 4294967296 at hfit
        omega
      change (deserialize (mem.readBytes (base.toNat + 4) (4 * count))).map
          (mem.read32 base :: ·) =
        some (mem.read32 base :: readWordArray mem (base + 4) count)
      rw [← hbase, ih]
      · rfl
      · rw [hbase]
        change base.toNat + 4 + 4 * count < 4294967296
        change base.toNat + 4 * (count + 1) < 4294967296 at hfit
        omega

theorem write32_read32 (mem : Mem) (base : UInt32) :
    mem.write32 base (mem.read32 base) = mem := by
  cases mem with
  | mk pages bytes =>
    simp only [Mem.write32, Mem.read32]
    congr
    funext i
    by_cases h0 : i = base.toNat
    · subst i
      simp only [if_pos]
      bv_decide
    by_cases h1 : i = base.toNat + 1
    · subst i
      simp only [if_neg h0, if_pos]
      bv_decide
    by_cases h2 : i = base.toNat + 2
    · subst i
      simp only [if_neg h0, if_neg h1, if_pos]
      bv_decide
    by_cases h3 : i = base.toNat + 3
    · subst i
      simp only [if_neg h0, if_neg h1, if_neg h2, if_pos]
      bv_decide
    simp [h0, h1, h2, h3]

/-- Owning the words currently present in memory can be represented by the
same `writeWordArray` model without changing the concrete memory. -/
theorem writeWordArray_readWordArray (mem : Mem) (base : UInt32)
    (count : Nat) :
    writeWordArray mem base (readWordArray mem base count) = mem := by
  induction count generalizing base with
  | zero => rfl
  | succ count ih =>
      simp only [readWordArray, writeWordArray]
      rw [write32_read32, ih]

theorem quicksort_writeWordArray_eq (mem : Mem) (base : UInt32)
    (values : List UInt32) :
    Quicksort.writeWordArray mem base values = writeWordArray mem base values := by
  induction values generalizing mem base with
  | nil => rfl
  | cons value values ih =>
      simp only [Quicksort.writeWordArray, writeWordArray]
      rw [ih]

theorem quicksort_readWordArray_eq (mem : Mem) (base : UInt32)
    (count : Nat) :
    Quicksort.readWordArray mem base count = readWordArray mem base count := by
  induction count generalizing base with
  | zero => rfl
  | succ count ih =>
      simp only [Quicksort.readWordArray, readWordArray]
      rw [ih]

theorem quicksortHeapAux_addresses_lt
    (σ : WasmHeapMap (Option UInt8)) (base : UInt32)
    (values : List UInt32) (limit : Nat)
    (hσ : ∀ address byte, get? σ address = some byte →
      address.toNat < base.toNat)
    (hfit : base.toNat + 4 * values.length ≤ limit)
    (hlimit : limit < UInt32.size) :
    ∀ address byte,
      get? (Quicksort.quicksortHeapAux σ base values) address = some byte →
      address.toNat < limit := by
  induction values generalizing σ base with
  | nil =>
      intro address byte hget
      exact Nat.lt_of_lt_of_le (hσ address byte hget) (by simpa using hfit)
  | cons value values ih =>
      simp only [Quicksort.quicksortHeapAux, List.length_cons] at *
      have h4 : (base + 4 : UInt32).toNat = base.toNat + 4 :=
        UInt32.add_ofNat_toNat_noWrap base 4 (by decide) (by
          simp only [UInt32.size] at hlimit
          omega)
      have hn1 : (base + 1).toNat = base.toNat + 1 :=
        UInt32.add_ofNat_toNat_noWrap base 1 (by decide) (by
          simp only [UInt32.size] at hlimit
          omega)
      have hn2 : (base + 2).toNat = base.toNat + 2 :=
        UInt32.add_ofNat_toNat_noWrap base 2 (by decide) (by
          simp only [UInt32.size] at hlimit
          omega)
      have hn3 : (base + 3).toNat = base.toNat + 3 :=
        UInt32.add_ofNat_toNat_noWrap base 3 (by decide) (by
          simp only [UInt32.size] at hlimit
          omega)
      apply ih (store32Heap σ base value) (base + 4)
      · intro address byte hget
        rw [h4]
        by_cases h3 : address = base + 3
        · subst h3
          rw [hn3]
          omega
        by_cases h2 : address = base + 2
        · subst h2
          rw [hn2]
          omega
        by_cases h1 : address = base + 1
        · subst h1
          rw [hn1]
          omega
        by_cases h0 : address = base
        · subst h0
          omega
        · simp only [store32Heap,
              get?_insert_ne (Ne.symm h3), get?_insert_ne (Ne.symm h2),
              get?_insert_ne (Ne.symm h1), get?_insert_ne (Ne.symm h0)] at hget
          exact Nat.lt_trans (hσ address byte hget) (by omega)
      · rw [h4]
        omega

/-- The stream-facing wrapper.  Local `0` remembers the byte count returned
by `read`; dividing it by four gives the number of words passed to merge sort.

Unified function indices are: `0 = read`, `1 = write`, `2 = mergeSort`,
`3 = merge`, and `4 = main`. -/
def mainBody : Program :=
  [ .const (UInt32.ofNat bufferBytes), .const source, .call 0, .localSet 0
  -- Probe for one more input byte at the byte immediately after memory.  EOF
  -- is a valid zero-length access there; any remaining byte traps, so a
  -- successful execution cannot have silently truncated its input.
  , .const 1, .const (UInt32.ofNat 65536), .call 0, .localSet 1
  , .const source, .const scratch, .localGet 0, .const 4, .divU, .call 2
  , .localGet 0, .const source, .call 1
  , .ret ]

def mainFunction : Function :=
  { locals := [.i32, .i32]
    body := mainBody }

/-- Merge sort linked against the two-function `StdIO` ABI. -/
def module : Module :=
  { imports := Wasm.StdIO.imports
    funcs := [mergeSortFunction 3, mergeFunction, mainFunction]
    memory := some { pagesMin := 1, pagesMax := some 1 } }

def initialStore (input : List UInt8) : Store Wasm.StdIO.State :=
  { (module.initialStore (α := Wasm.StdIO.State)) with
      host := Wasm.StdIO.State.ofInput input }

def config (input : List UInt8) : Config Wasm.StdIO.State :=
  match SmallStep.initConfig
      { module, host := Wasm.StdIO.env } 4 (initialStore input) [] with
  | .ok result => result
  | .error _ =>
      -- Definitionally unreachable: local function index 4 is `mainFunction`.
      { expr := .trapped (.host "invalid StdIO merge-sort entry")
        store :=
          { runtime := { module, host := Wasm.StdIO.env }
            wasm := initialStore input } }

/-- Execute one exported or imported function with the authoritative
small-step machine, retaining the mutated Wasm/host store for the next phase. -/
def execute (fuel entry : Nat) (store : Store Wasm.StdIO.State)
    (args : List Value) : Option (List Value × Store Wasm.StdIO.State) :=
  match SmallStep.initConfig { module, host := Wasm.StdIO.env } entry store args with
  | .error _ => none
  | .ok phase =>
      match (SmallStep.runSteps fuel phase).result with
      | .success values finalStore => some (values, finalStore.wasm)
      | _ => none

/-- Change only the host-owned component of a Wasm store. This is a
type-changing record update: all core Wasm resources remain identical. -/
def replaceHost (store : Store α) (host : β) : Store β :=
  { store with host := host }

/-- Execute merge sort with an inert host environment, then reattach the
unchanged StdIO buffers. The sort and merge functions have no path to an
import, so this makes their host independence explicit. -/
def executeSort (fuel : Nat) (store : Store Wasm.StdIO.State)
    (args : List Value) : Option (List Value × Store Wasm.StdIO.State) :=
  match SmallStep.initConfig
      { module, host := ({} : HostEnv Unit) } 2 (replaceHost store ()) args with
  | .error _ => none
  | .ok phase =>
      match (SmallStep.runSteps fuel phase).result with
      | .success values finalStore =>
          some (values, replaceHost finalStore.wasm store.host)
      | _ => none

theorem executeSort_host (fuel : Nat) (initial final : Store Wasm.StdIO.State)
    (args : List Value) (values : List Value)
    (hexecute : executeSort fuel initial args = some (values, final)) :
    final.host = initial.host := by
  unfold executeSort at hexecute
  split at hexecute
  · contradiction
  · generalize hresult : (runSteps fuel _).result = result at hexecute
    cases result <;> simp_all [replaceHost]
    case success =>
      have hhost := congrArg (fun concrete : Store Wasm.StdIO.State =>
        concrete.host) hexecute.2
      simpa [replaceHost] using hhost.symm

def writtenStore (store : Store Wasm.StdIO.State) (length : UInt32) :
    Store Wasm.StdIO.State :=
  { store with
    host :=
      { input := store.host.input
        output := store.host.output ++
          store.mem.readBytes source.toNat length.toNat } }

theorem execute_read (store wasm : Store Wasm.StdIO.State)
    (length pointer count : UInt32)
    (hinvoke : Wasm.StdIO.readHost.invoke store
      [.i32 length, .i32 pointer] = .Return [.i32 count] wasm) :
    execute 2 0 store [.i32 pointer, .i32 length] =
      some ([.i32 count], wasm) := by
  let machine : MachineStore Wasm.StdIO.State :=
    { runtime := { module, host := Wasm.StdIO.env }, wasm := store }
  let initial : Config Wasm.StdIO.State :=
    { expr := .running
        ⟨⟨[], [], [.i32 pointer, .i32 length]⟩, [.call 0], 1, [], [], []⟩
      store := machine }
  let middle : Config Wasm.StdIO.State :=
    { expr := .running
        ⟨⟨[], [], [.i32 count]⟩, [], 1, [], [], []⟩
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
    (by simp [machine, module, Wasm.StdIO.imports]) rfl rfl hinvoke
  have hcall : Step initial (.host 0) middle := by
    simpa [initial, middle, machine, module, Wasm.StdIO.imports,
      Wasm.StdIO.env] using hcallRaw
  have hfinish : Step middle (.administrative .finish)
      ⟨.done [.i32 count], { machine with wasm }⟩ := Step.finish
  have hrun := runSteps_eq_success_of_steps
    (Steps.cons hcall (Steps.single hfinish))
  have hinit : SmallStep.initConfig
      { module, host := Wasm.StdIO.env } 0 store
        [.i32 pointer, .i32 length] = .ok initial := by
    rfl
  simp only [execute, hinit]
  rw [show (runSteps 2 initial).result =
      .success [.i32 count] { machine with wasm } by simpa using hrun]

theorem execute_read_trap (store wasm : Store Wasm.StdIO.State)
    (length pointer : UInt32) (message : String)
    (hinvoke : Wasm.StdIO.readHost.invoke store
      [.i32 length, .i32 pointer] = .Trap wasm message) :
    execute 2 0 store [.i32 pointer, .i32 length] = none := by
  let machine : MachineStore Wasm.StdIO.State :=
    { runtime := { module, host := Wasm.StdIO.env }, wasm := store }
  let initial : Config Wasm.StdIO.State :=
    { expr := .running
        ⟨⟨[], [], [.i32 pointer, .i32 length]⟩, [.call 0], 1, [], [], []⟩
      store := machine }
  let trapped : Config Wasm.StdIO.State :=
    { expr := .trapped (.host message)
      store := { machine with wasm } }
  have hcallRaw := Step.callHostTrap
    (store := machine) (functionIndex := 0)
    (imp := Wasm.StdIO.imports[0])
    (hostFunction := Wasm.StdIO.readHost)
    (params := []) (localValues := [])
    (values := [.i32 pointer, .i32 length])
    (wasm := wasm) (message := message)
    (code := []) (arity := 1) (remainder := [])
    (controls := []) (calls := [])
    (by simp [machine, module, Wasm.StdIO.imports]) rfl rfl hinvoke
  have hcall : Step initial (.host 0) trapped := by
    simpa [initial, trapped, machine, module, Wasm.StdIO.imports,
      Wasm.StdIO.env] using hcallRaw
  have hinit : SmallStep.initConfig
      { module, host := Wasm.StdIO.env } 0 store
        [.i32 pointer, .i32 length] = .ok initial := by
    rfl
  simp [execute, hinit, runSteps, stepChecked?_complete hcall, trapped]

theorem execute_write (store wasm : Store Wasm.StdIO.State)
    (length pointer : UInt32)
    (hinvoke : Wasm.StdIO.writeHost.invoke store
      [.i32 length, .i32 pointer] = .Return [] wasm) :
    execute 2 1 store [.i32 pointer, .i32 length] = some ([], wasm) := by
  let machine : MachineStore Wasm.StdIO.State :=
    { runtime := { module, host := Wasm.StdIO.env }, wasm := store }
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
    (values := [.i32 pointer, .i32 length])
    (results := []) (wasm := wasm)
    (code := []) (arity := 0) (remainder := [])
    (controls := []) (calls := [])
    (by simp [machine, module, Wasm.StdIO.imports]) rfl rfl hinvoke
  have hcall : Step initial (.host 1) middle := by
    simpa [initial, middle, machine, module, Wasm.StdIO.imports,
      Wasm.StdIO.env] using hcallRaw
  have hfinish : Step middle (.administrative .finish)
      ⟨.done [], { machine with wasm }⟩ := Step.finish
  have hrun := runSteps_eq_success_of_steps
    (Steps.cons hcall (Steps.single hfinish))
  have hinit : SmallStep.initConfig
      { module, host := Wasm.StdIO.env } 1 store
        [.i32 pointer, .i32 length] = .ok initial := by
    rfl
  simp only [execute, hinit]
  rw [show (runSteps 2 initial).result =
      .success [] { machine with wasm } by simpa using hrun]

theorem execute_write_bytes (store : Store Wasm.StdIO.State) (length : UInt32)
    (hbound : source.toNat + length.toNat ≤ Wasm.StdIO.byteCapacity store) :
    execute 2 1 store [.i32 source, .i32 length] =
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

@[simp] private theorem initialStore_host (input : List UInt8) :
    (initialStore input).host = Wasm.StdIO.State.ofInput input := by
  rfl

set_option maxRecDepth 100000 in
private theorem initial_byteCapacity (input : List UInt8) :
    Wasm.StdIO.byteCapacity (initialStore input) = 65536 := by
  change (module.initialStore (α := Wasm.StdIO.State)).mem.pages * 65536 = 65536
  have hpages : (module.initialStore (α := Wasm.StdIO.State)).mem.pages = 1 := by
    decide
  rw [hpages]

/-- Concrete store after the first read, before the EOF probe. -/
def afterBoundedRead (input : List UInt8) : Store Wasm.StdIO.State :=
  let bytes := input.take bufferBytes
  { initialStore input with
    mem := (initialStore input).mem.writeBytes source.toNat bytes
    host := { input := input.drop bytes.length, output := [] } }

theorem read_bounded (input : List UInt8) :
    execute 2 0 (initialStore input)
      [.i32 source, .i32 (UInt32.ofNat bufferBytes)] =
      some ([.i32 (UInt32.ofNat (input.take bufferBytes).length)],
        afterBoundedRead input) := by
  apply execute_read
  simp only [Wasm.StdIO.readHost, Wasm.StdIO.readResult, initialStore_host,
    Wasm.StdIO.State.ofInput]
  have hbuffer : (UInt32.ofNat bufferBytes).toNat = bufferBytes :=
    UInt32.toNat_ofNat_of_lt' (by decide)
  rw [hbuffer]
  rw [if_pos (by
    simp only [Wasm.StdIO.rangeInBounds, source, initial_byteCapacity]
    apply decide_eq_true
    have htake : (input.take bufferBytes).length ≤ bufferBytes :=
      List.length_take_le bufferBytes input
    simpa only [show (0 : UInt32).toNat = 0 by decide, Nat.zero_add] using
      Nat.le_trans htake (by decide : bufferBytes ≤ 65536))]
  simp [afterBoundedRead, source]

/-- Concrete store after the bounded source read has consumed all serialized
input. -/
def afterRead (input : List UInt32) : Store Wasm.StdIO.State :=
  { initialStore (serialize input) with
    mem := (initialStore (serialize input)).mem.writeBytes
      source.toNat (serialize input)
    host := { input := [], output := [] } }

/-- Exact authoritative configuration used by the merge-sort phase. -/
def sortConfig (input : List UInt32) : Config Unit :=
  { expr := .running
      ⟨sortLocals source scratch input.length 0 0 0 0 [],
        mergeSortBody 3, 0, [], [], []⟩
    store :=
      { runtime := { module, host := {} }
        wasm := replaceHost (afterRead input) () } }

theorem initConfig_sort (input : List UInt32) :
    SmallStep.initConfig { module, host := ({} : HostEnv Unit) } 2
      (replaceHost (afterRead input) ())
      (mergeSortArguments source scratch input.length []) =
      .ok (sortConfig input) := by
  rfl

set_option maxRecDepth 10000 in
theorem read_fits (input : List UInt32)
    (hfit : (serialize input).length ≤ bufferBytes) :
    execute 2 0 (initialStore (serialize input))
      [.i32 source, .i32 (UInt32.ofNat bufferBytes)] =
      some ([.i32 (UInt32.ofNat (serialize input).length)], afterRead input) := by
  apply execute_read
  simp only [Wasm.StdIO.readHost, Wasm.StdIO.readResult]
  simp only [initialStore_host, Wasm.StdIO.State.ofInput]
  have hbuffer : (UInt32.ofNat bufferBytes).toNat = bufferBytes :=
    UInt32.toNat_ofNat_of_lt' (by decide)
  rw [hbuffer]
  rw [take_eq_self_of_length_le _ _ hfit]
  simp only [serialize_length] at hfit
  rw [if_pos (by
    simp only [Wasm.StdIO.rangeInBounds, source, initial_byteCapacity]
    apply decide_eq_true
    simpa only [serialize_length, show (0 : UInt32).toNat = 0 by decide,
      Nat.zero_add] using
      Nat.le_trans hfit (by decide : bufferBytes ≤ 65536))]
  simp [afterRead, source]

private theorem afterRead_byteCapacity (input : List UInt32) :
    Wasm.StdIO.byteCapacity (afterRead input) = 65536 := by
  simpa only [afterRead, Wasm.StdIO.byteCapacity, Mem.writeBytes] using
    initial_byteCapacity (serialize input)

theorem probe_afterRead (input : List UInt32) :
    execute 2 0 (afterRead input)
      [.i32 (UInt32.ofNat 65536), .i32 1] =
      some ([.i32 0], afterRead input) := by
  apply execute_read
  apply Wasm.StdIO.read_empty
  · rfl
  · rw [afterRead_byteCapacity]
    decide

private theorem afterBoundedRead_byteCapacity (input : List UInt8) :
    Wasm.StdIO.byteCapacity (afterBoundedRead input) = 65536 := by
  simpa only [afterBoundedRead, Wasm.StdIO.byteCapacity, Mem.writeBytes] using
    initial_byteCapacity input

theorem probe_traps_of_too_long (input : List UInt8)
    (hlong : bufferBytes < input.length) :
    execute 2 0 (afterBoundedRead input)
      [.i32 (UInt32.ofNat 65536), .i32 1] = none := by
  apply execute_read_trap
  apply Wasm.StdIO.read_one_past_traps
  · simp only [afterBoundedRead]
    intro hempty
    have hlength := congrArg List.length hempty
    simp only [List.length_drop, List.length_nil] at hlength
    rw [List.length_take, Nat.min_eq_left (Nat.le_of_lt hlong)] at hlength
    omega
  · rw [afterBoundedRead_byteCapacity]
    exact UInt32.toNat_ofNat_of_lt' (by decide)

def runAfterRead (fuel : Nat) (byteLength : UInt32)
    (afterRead : Store Wasm.StdIO.State) : Option (List UInt8) := do
  let (probeValues, afterProbe) ← execute 2 0 afterRead
    [.i32 (UInt32.ofNat 65536), .i32 1]
  guard (probeValues = [.i32 0])
  let (_, afterSort) ← executeSort fuel afterProbe
    (mergeSortArguments source scratch (byteLength.toNat / 4) [])
  let (_, afterWrite) ← execute 2 1 afterSort
    [.i32 source, .i32 byteLength]
  pure afterWrite.host.output

/-- Execute the stream program in four explicit phases: read the source
region, prove EOF with the one-past-memory probe, run merge sort, then append
the sorted source region through `write`.  Every phase still executes through
the authoritative Wasm small-step semantics. -/
def run (fuel : Nat) (input : List UInt8) : Option (List UInt8) := do
  let (readValues, afterRead) ← execute 2 0 (initialStore input)
    [.i32 source, .i32 (UInt32.ofNat bufferBytes)]
  let byteLength ← match readValues with
    | [.i32 length] => some length
    | _ => none
  runAfterRead fuel byteLength afterRead

theorem run_none_of_too_long (fuel : Nat) (input : List UInt8)
    (hlong : bufferBytes < input.length) :
    run fuel input = none := by
  have hprobeNone : execute 2 0 (afterBoundedRead input)
      [.i32 (UInt32.ofNat 65536), .i32 1] = none :=
    probe_traps_of_too_long input hlong
  unfold run
  rw [read_bounded]
  change runAfterRead fuel (UInt32.ofNat (input.take bufferBytes).length)
    (afterBoundedRead input) = none
  unfold runAfterRead
  rw [hprobeNone]
  rfl

/-- A clean, host-level execution predicate.  Fuel is hidden existentially
and neither linear memory nor Wasm machine state appears in client specs. -/
def Runs (input output : List UInt8) : Prop :=
  ∃ fuel, run fuel input = some output

/-- Serialize the input, run the byte-stream program, and deserialize its
output.  This is the convenient executable surface for clients. -/
def runValues (fuel : Nat) (input : List UInt32) : Option (List UInt32) :=
  (run fuel (serialize input)).bind deserialize

/-- Fuel-free execution phrased entirely in terms of lists of words. -/
def RunsValues (input output : List UInt32) : Prop :=
  ∃ fuel, runValues fuel input = some output

/-- Pure input-side condition imposed by the fixed one-page Wasm32 layout. -/
def Fits (values : List UInt32) : Prop :=
  (serialize values).length ≤ bufferBytes

/-- Scratch words are whatever is currently present in the reserved second
half of memory. The merge-sort proof only requires scratch storage of the
right length; it does not require a particular initial value. -/
def scratchValues (input : List UInt32) : List UInt32 :=
  readWordArray (afterRead input).mem scratch input.length

/-- Authoritative ghost heap covering both arrays used by merge sort. -/
def sortHeap (input : List UInt32) : WasmHeapMap (Option UInt8) :=
  Quicksort.quicksortHeapAux
    (Quicksort.quicksortHeapAux ∅ source input)
    scratch (scratchValues input)

theorem fits_iff (values : List UInt32) :
    Fits values ↔ 4 * values.length ≤ bufferBytes := by
  simp only [Fits, serialize_length]

theorem encodedLength_toNat (input : List UInt32) (hfit : Fits input) :
    (UInt32.ofNat (serialize input).length).toNat = (serialize input).length := by
  apply UInt32.toNat_ofNat_of_lt'
  rw [fits_iff] at hfit
  change 4 * input.length ≤ 32768 at hfit
  simp only [serialize_length, UInt32.size]
  omega

theorem encodedLength_words (input : List UInt32) (hfit : Fits input) :
    (UInt32.ofNat (serialize input).length).toNat / 4 = input.length := by
  rw [encodedLength_toNat input hfit, serialize_length]
  omega

theorem scratchValues_length (input : List UInt32) :
    (scratchValues input).length = input.length := by
  have aux (mem : Mem) (base : UInt32) (count : Nat) :
      (readWordArray mem base count).length = count := by
    induction count generalizing base with
    | zero => rfl
    | succ count ih =>
        simp only [readWordArray, List.length_cons]
        rw [ih]
  exact aux _ _ _

theorem afterRead_mem_eq (input : List UInt32) (hfit : Fits input) :
    (afterRead input).mem =
      writeWordArray (initialStore (serialize input)).mem source input := by
  unfold afterRead
  simp only
  apply writeBytes_serialize
  simp only [source, UInt32.reduceToNat, Nat.zero_add, UInt32.size]
  rw [fits_iff] at hfit
  change 4 * input.length ≤ 32768 at hfit
  omega

theorem sortHeap_agrees (input : List UInt32) (hfit : Fits input) :
    heapAgreesWithMem (sortHeap input) (afterRead input).mem := by
  let initialMem := (initialStore (serialize input)).mem
  let sourceHeap := Quicksort.quicksortHeapAux ∅ source input
  have hempty : heapAgreesWithMem (∅ : WasmHeapMap (Option UInt8)) initialMem := by
    intro address byte hget
    have hemptyGet : Iris.Std.get? (∅ : WasmHeapMap (Option UInt8)) address = none :=
      Iris.Std.get?_empty address
    rw [hemptyGet] at hget
    contradiction
  have hsource : heapAgreesWithMem sourceHeap (afterRead input).mem := by
    rw [afterRead_mem_eq input hfit]
    simpa only [sourceHeap, initialMem, quicksort_writeWordArray_eq] using
      Quicksort.quicksortHeapAux_agrees ∅ initialMem source input hempty
      (by
        rw [fits_iff] at hfit
        simp only [source, UInt32.reduceToNat, Nat.zero_add, UInt32.size]
        change 4 * input.length ≤ 32768 at hfit
        omega)
  have hscratch := Quicksort.quicksortHeapAux_agrees sourceHeap
    (afterRead input).mem scratch (scratchValues input) hsource
    (by
      rw [scratchValues_length]
      rw [fits_iff] at hfit
      have hscratchNat : scratch.toNat = 32768 := by decide
      rw [hscratchNat]
      simp only [UInt32.size]
      change 4 * input.length ≤ 32768 at hfit
      omega)
  rw [quicksort_writeWordArray_eq] at hscratch
  simpa only [sortHeap, sourceHeap, scratchValues,
    writeWordArray_readWordArray] using hscratch

theorem sortHeap_inBounds (input : List UInt32) (hfit : Fits input) :
    heapAddressesInBounds (sortHeap input) (afterRead input).mem := by
  let initialMem := (initialStore (serialize input)).mem
  let sourceHeap := Quicksort.quicksortHeapAux ∅ source input
  have hempty : heapAddressesInBounds
      (∅ : WasmHeapMap (Option UInt8)) initialMem := by
    intro address byte hget
    have hemptyGet : Iris.Std.get? (∅ : WasmHeapMap (Option UInt8)) address = none :=
      Iris.Std.get?_empty address
    rw [hemptyGet] at hget
    contradiction
  have hsource : heapAddressesInBounds sourceHeap (afterRead input).mem := by
    rw [afterRead_mem_eq input hfit]
    simpa only [sourceHeap, initialMem, quicksort_writeWordArray_eq] using
      Quicksort.quicksortHeapAux_inBounds ∅ initialMem source input hempty
      (by
        rw [fits_iff] at hfit
        simp only [source, UInt32.reduceToNat, Nat.zero_add, UInt32.size]
        change 4 * input.length ≤ 32768 at hfit
        omega)
      (by
        change source.toNat + 4 * input.length ≤
          Wasm.StdIO.byteCapacity (initialStore (serialize input))
        rw [initial_byteCapacity]
        rw [fits_iff] at hfit
        simp only [source, UInt32.reduceToNat, Nat.zero_add]
        change 4 * input.length ≤ 32768 at hfit
        omega)
  have hscratch := Quicksort.quicksortHeapAux_inBounds sourceHeap
    (afterRead input).mem scratch (scratchValues input) hsource
    (by
      rw [scratchValues_length]
      rw [fits_iff] at hfit
      have hscratchNat : scratch.toNat = 32768 := by decide
      rw [hscratchNat]
      simp only [UInt32.size]
      change 4 * input.length ≤ 32768 at hfit
      omega)
    (by
      rw [scratchValues_length]
      change scratch.toNat + 4 * input.length ≤
        Wasm.StdIO.byteCapacity (afterRead input)
      rw [afterRead_byteCapacity]
      rw [fits_iff] at hfit
      have hscratchNat : scratch.toNat = 32768 := by decide
      rw [hscratchNat]
      change 4 * input.length ≤ 32768 at hfit
      omega)
  rw [quicksort_writeWordArray_eq] at hscratch
  simpa only [sortHeap, sourceHeap, scratchValues,
    writeWordArray_readWordArray] using hscratch

theorem sortHeap_pointsTo [WasmHeapGS]
    (input : List UInt32) (hfit : Fits input) :
    ([∗map] address ↦ value ∈ sortHeap input,
      pointsTo (GF := WasmHeapGF) (H := WasmHeapMap)
        address (DFrac.own 1) value) ⊢
      arrayAt source input ∗ arrayAt scratch (scratchValues input) := by
  let sourceHeap := Quicksort.quicksortHeapAux ∅ source input
  have hempty : ∀ address byte,
      get? (∅ : WasmHeapMap (Option UInt8)) address = some byte →
      address.toNat < source.toNat := by
    intro address byte hget
    have hemptyGet : get? (∅ : WasmHeapMap (Option UInt8)) address = none :=
      get?_empty address
    rw [hemptyGet] at hget
    contradiction
  have hsourceFit : source.toNat + 4 * input.length < UInt32.size := by
    rw [fits_iff] at hfit
    simp only [source, UInt32.reduceToNat, Nat.zero_add, UInt32.size]
    change 4 * input.length ≤ 32768 at hfit
    omega
  have hscratchFit :
      scratch.toNat + 4 * (scratchValues input).length < UInt32.size := by
    rw [scratchValues_length]
    rw [fits_iff] at hfit
    have hscratchNat : scratch.toNat = 32768 := by decide
    rw [hscratchNat]
    simp only [UInt32.size]
    change 4 * input.length ≤ 32768 at hfit
    omega
  have hdisjoint : ∀ address byte, get? sourceHeap address = some byte →
      address.toNat < scratch.toNat := by
    apply quicksortHeapAux_addresses_lt ∅ source input scratch.toNat hempty
    · rw [fits_iff] at hfit
      have hscratchNat : scratch.toNat = 32768 := by decide
      rw [hscratchNat]
      simp only [source, UInt32.reduceToNat, Nat.zero_add]
      change 4 * input.length ≤ 32768 at hfit
      exact hfit
    · have hscratchNat : scratch.toNat = 32768 := by decide
      rw [hscratchNat]
      simp only [UInt32.size]
      omega
  simp only [sortHeap]
  iintro Hheap
  ihave HscratchSplit := Quicksort.quicksortHeapAux_pointsTo
    sourceHeap scratch (scratchValues input) hdisjoint hscratchFit $$ Hheap
  icases HscratchSplit with ⟨Hscratch, HsourceHeap⟩
  ihave HsourceSplit := Quicksort.quicksortHeapAux_pointsTo
    ∅ source input hempty hsourceFit $$ HsourceHeap
  icases HsourceSplit with ⟨Hsource, _Hempty⟩
  isplitl [Hsource]
  · iexact Hsource
  · iexact Hscratch

theorem arrayAt_capacity [WasmSmallStepGS hlc]
    (store : MachineStore α) (steps : Nat)
    (observations : List StepKind) (threads : Nat)
    (base : UInt32) (values : List UInt32)
    (hfit : base.toNat + 4 * values.length < UInt32.size)
    (hbaseBound : base.toNat ≤ store.wasm.mem.pages * 65536) :
    stateInterp (GF := WasmHeapGF) store steps observations threads ∗
      arrayAt base values ==∗
    stateInterp (GF := WasmHeapGF) store steps observations threads ∗
      arrayAt base values ∗
      ⌜base.toNat + 4 * values.length ≤ store.wasm.mem.pages * 65536⌝ := by
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
    let address := base + 4 * UInt32.ofNat k
    have haddress : address.toNat = base.toNat + 4 * k := by
      exact Mem.words32_slotAddr_toNat base k (by
        simp only [UInt32.size] at hfit
        omega)
    have h1 : (address + 1).toNat = address.toNat + 1 :=
      UInt32.add_ofNat_toNat_noWrap address 1 (by decide) (by
        simp only [UInt32.size] at hfit
        rw [haddress]
        omega)
    have h2 : (address + 2).toNat = address.toNat + 2 :=
      UInt32.add_ofNat_toNat_noWrap address 2 (by decide) (by
        simp only [UInt32.size] at hfit
        rw [haddress]
        omega)
    have h3 : (address + 3).toNat = address.toNat + 3 :=
      UInt32.add_ofNat_toNat_noWrap address 3 (by decide) (by
        simp only [UInt32.size] at hfit
        rw [haddress]
        omega)
    iintro ⟨Hstate, Harray⟩
    ihave Hfocus := arrayAt_get base values k hk $$ Harray
    icases Hfocus with ⟨Hword, Hrestore⟩
    imod stateInterp_pointsTo_u32_facts_frame store steps observations threads
      address values[k] h1 h2 h3 $$ [$Hstate $Hword] with
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

theorem validLayout (input : List UInt32) (hfit : Fits input) :
    ValidLayout source scratch input.length := by
  rw [fits_iff] at hfit
  unfold ValidLayout arrayByteRange
  simp only [source, UInt32.reduceToNat, Nat.zero_add]
  have hscratchNat : scratch.toNat = 32768 := by decide
  rw [hscratchNat]
  simp only [UInt32.size]
  change 4 * input.length ≤ 32768 at hfit
  omega

def SortPost (input : List UInt32)
    (_values : List Value) (store : MachineStore α) : Prop :=
  ∃ output, SortedPermutation input output ∧
    readWordArray store.wasm.mem source input.length = output ∧
    4 * input.length ≤ store.wasm.mem.pages * 65536

private theorem mergeSortPost_elim [WasmHeapGS]
    (source scratch : UInt32) (input : List UInt32) :
    mergeSortPost source scratch input ⊢
      (iprop% ∃ output scratchFinal : List UInt32,
        ⌜SortedPermutation input output⌝ ∗
        ⌜scratchFinal.length = input.length⌝ ∗
        arrayAt source output ∗ arrayAt scratch scratchFinal) := by
  unfold mergeSortPost
  iintro Hpost
  iexact Hpost

set_option maxHeartbeats 6000000 in
theorem twp_sort [WasmSmallStepGS hlc]
    (input : List UInt32) (hfit : Fits input) :
    (([∗map] address ↦ value ∈ sortHeap input,
        pointsTo (GF := WasmHeapGF) (H := WasmHeapMap)
          address (DFrac.own 1) value) ∗
      ([∗map] index ↦ value ∈ (∅ : WasmGlobalMap Value),
        globalPointsTo index value) ∗
      runtimeModuleOwn (sortConfig input).store.runtime.module) ⊢
      WP (sortConfig input).expr @ Stuckness.NotStuck; ⊤
        [{ values,
          ∀ (store : MachineStore Unit) (_observations : List StepKind),
            stateInterp (GF := WasmHeapGF) store 0 [] 0 -∗
            ⌜SortPost input values store⌝ }] := by
  iintro ⟨Hheap, _Hglobals, Hruntime⟩
  ihave Harrays := sortHeap_pointsTo input hfit $$ Hheap
  icases Harrays with ⟨Hsource, Hscratch⟩
  simp only [sortConfig]
  iapply twp_mergeSortBody (α := Unit) module 3
    (by decide) (by rfl)
    source scratch input (scratchValues input)
  isplitl [Hruntime]
  · iexact Hruntime
  isplitl [Hsource Hscratch]
  · unfold mergeSortPre
    isplitl [Hsource]
    · iexact Hsource
    isplitl [Hscratch]
    · iexact Hscratch
    isplitr
    · ipureintro
      exact scratchValues_length input
    · ipureintro
      exact validLayout input hfit
  · iintro %width %left %mid %right Hruntime Hpost
    ihave Hpost' := mergeSortPost_elim source scratch input $$ Hpost
    icases Hpost' with ⟨%output, %scratchFinal, %hsorted, %_hscratchLength,
      Hsource, _Hscratch⟩
    iapply Wasm.SmallStep.twp_returnFromFunction
    iapply twp.value rfl
    iintro %store %observations Hstate
    imod Quicksort.arrayAt_readWordArray store 0 [] 0 source output
      (by
        have hlength := hsorted.2.length_eq
        rw [← hlength]
        rw [fits_iff] at hfit
        simp only [source, UInt32.reduceToNat, Nat.zero_add, UInt32.size]
        change 4 * input.length ≤ 32768 at hfit
        omega) $$ [$Hstate $Hsource] with
      ⟨Hstate, Hsource, %hread⟩
    have hread' : readWordArray store.wasm.mem source output.length = output := by
      simpa only [quicksort_readWordArray_eq] using hread
    imod arrayAt_capacity store 0 [] 0 source output
      (by
        have hlength := hsorted.2.length_eq
        rw [← hlength]
        rw [fits_iff] at hfit
        simp only [source, UInt32.reduceToNat, Nat.zero_add, UInt32.size]
        change 4 * input.length ≤ 32768 at hfit
        omega)
      (by simp [source]) $$ [$Hstate $Hsource] with
      ⟨_Hstate, _Hsource, %hcapacity⟩
    ipureintro
    exact ⟨output, hsorted, by
      rw [hsorted.2.length_eq]
      exact hread', by
      rw [hsorted.2.length_eq]
      simpa only [source, UInt32.reduceToNat, Nat.zero_add] using hcapacity⟩

theorem sort_partiallyMeets (input : List UInt32) (hfit : Fits input) :
    SmallStep.PartiallyMeets (sortConfig input) (SortPost input) := by
  apply wasm_smallStep_heap_globals_runtime_store_partiallyMeets.{0}
    (sortConfig input) (sortHeap input) ∅ (SortPost input)
  · exact sortHeap_agrees input hfit
  · exact sortHeap_inBounds input hfit
  · exact globalHeapAgrees_empty _
  · intro _
    iintro Hresources
    iapply twp.to_wp
    iapply twp_sort input hfit
    iexact Hresources

theorem sort_stronglyNormalizing (input : List UInt32) (hfit : Fits input) :
    Iris.ProgramLogic.StronglyNormalizing
      (Iris.ProgramLogic.ExprErasedStep (Expr := Expr Unit)
        (State := MachineStore Unit) (Obs := StepKind))
      ((sortConfig input).expr, (sortConfig input).store) := by
  apply Wasm.SmallStep.wasm_smallStep_heap_globals_runtime_stronglyNormalizing.{0}
    (sortConfig input) (sortHeap input) ∅
    (fun _values => iprop(True))
  · exact sortHeap_agrees input hfit
  · exact sortHeap_inBounds input hfit
  · exact globalHeapAgrees_empty _
  · intro _
    iintro Hresources
    ihave Hsort := twp_sort input hfit $$ Hresources
    iapply twp.mono (fun _values => ?_) $$ Hsort
    iintro _Hpost
    itrivial

theorem sort_terminatesWith (input : List UInt32) (hfit : Fits input) :
    SmallStep.TerminatesWith (sortConfig input) (SortPost input) := by
  apply Wasm.SmallStep.stronglyNormalizing_adequate_terminates
    (sortConfig input) (SortPost input) (sort_stronglyNormalizing input hfit)
  apply wasm_smallStep_heap_globals_runtime_store_adequacy.{0}
    (sortConfig input) (sortHeap input) ∅ (SortPost input)
  · exact sortHeap_agrees input hfit
  · exact sortHeap_inBounds input hfit
  · exact globalHeapAgrees_empty _
  · intro _
    iintro Hresources
    iapply twp.to_wp
    iapply twp_sort input hfit
    iexact Hresources

theorem runSteps_sort_correct (fuel : Nat) (input : List UInt32)
    (hfit : Fits input) (values : List Value)
    (store : MachineStore Unit)
    (hrun : (runSteps fuel (sortConfig input)).result =
      .success values store) :
    SortPost input values store := by
  apply sort_partiallyMeets input hfit
    (runSteps fuel (sortConfig input)).trace values store
  apply runSteps_sound
  simp [hrun, RunnerResult.finalConfig?]

theorem execute_sort_correct (fuel : Nat) (input : List UInt32)
    (hfit : Fits input) (values : List Value)
    (store : Store Wasm.StdIO.State)
    (hexecute : executeSort fuel (afterRead input)
      (mergeSortArguments source scratch input.length []) =
      some (values, store)) :
    SortPost input values
      { runtime := { module, host := Wasm.StdIO.env }, wasm := store } := by
  simp only [executeSort, initConfig_sort] at hexecute
  generalize hresult : (runSteps fuel (sortConfig input)).result = result at hexecute
  cases result with
  | success resultValues resultStore =>
      simp only [Option.some.injEq, Prod.mk.injEq] at hexecute
      rcases hexecute with ⟨hvalues, hstore⟩
      subst values
      have hpost := runSteps_sort_correct fuel input hfit resultValues
        resultStore hresult
      obtain ⟨output, hsorted, hread, hcapacity⟩ := hpost
      have hmem : resultStore.wasm.mem = store.mem := by
        have := congrArg (fun concrete : Store Wasm.StdIO.State => concrete.mem)
          hstore
        simpa [replaceHost] using this
      exact ⟨output, hsorted, by simpa [hmem] using hread,
        by simpa [hmem] using hcapacity⟩
  | trapped reason resultStore => simp at hexecute
  | outOfFuel resultConfig => simp at hexecute
  | internalError error resultConfig => simp at hexecute

theorem execute_sort_complete (input : List UInt32) (hfit : Fits input) :
    ∃ fuel values store,
      executeSort fuel (afterRead input)
        (mergeSortArguments source scratch input.length []) =
          some (values, store) ∧
      SortPost input values
        { runtime := { module, host := Wasm.StdIO.env }, wasm := store } := by
  rcases sort_terminatesWith input hfit with
    ⟨trace, values, finalStore, hsteps, hpost⟩
  let store : Store Wasm.StdIO.State :=
    replaceHost finalStore.wasm (afterRead input).host
  refine ⟨trace.length, values, store, ?_, ?_⟩
  · simp only [executeSort, initConfig_sort]
    rw [runSteps_eq_success_of_steps hsteps]
  · simpa only [SortPost, store, replaceHost] using hpost

set_option maxRecDepth 10000 in
theorem run_fits (fuel : Nat) (input : List UInt32) (hfit : Fits input) :
    run fuel (serialize input) =
      runAfterRead fuel (UInt32.ofNat (serialize input).length) (afterRead input) := by
  unfold run
  rw [read_fits input hfit]
  simp only [Bind.bind, Option.bind]

set_option maxRecDepth 10000 in
theorem run_correct (fuel : Nat) (input : List UInt32) (bytes : List UInt8)
    (hfit : Fits input) (hrun : run fuel (serialize input) = some bytes) :
    ∃ output, SortedPermutation input output ∧
      deserialize bytes = some output := by
  rw [run_fits fuel input hfit] at hrun
  unfold runAfterRead at hrun
  rw [probe_afterRead input] at hrun
  simp only [guard] at hrun
  rw [encodedLength_words input hfit] at hrun
  simp only [Bind.bind, Option.bind] at hrun
  simp only [if_true, Pure.pure] at hrun
  generalize hsortResult : executeSort fuel (afterRead input)
      (mergeSortArguments source scratch input.length []) = sortResult at hrun
  cases sortResult with
  | none => simp at hrun
  | some sortPair =>
      rcases sortPair with ⟨sortValues, afterSort⟩
      have hpost := execute_sort_correct fuel input hfit sortValues afterSort
        hsortResult
      obtain ⟨output, hsorted, hread, hcapacity⟩ := hpost
      have hhost := executeSort_host fuel (afterRead input) afterSort
        (mergeSortArguments source scratch input.length []) sortValues hsortResult
      have hbyteLength :
          (UInt32.ofNat (serialize input).length).toNat = 4 * input.length := by
        rw [encodedLength_toNat input hfit, serialize_length]
      have hwriteBound : source.toNat +
          (UInt32.ofNat (serialize input).length).toNat ≤
          Wasm.StdIO.byteCapacity afterSort := by
        simp only [source, UInt32.reduceToNat, Nat.zero_add,
          Wasm.StdIO.byteCapacity, hbyteLength]
        exact hcapacity
      have hwrite := execute_write_bytes afterSort
        (UInt32.ofNat (serialize input).length) hwriteBound
      simp only [] at hrun
      rw [hwrite] at hrun
      simp only [] at hrun
      have houtput : afterSort.host.output = [] := by
        rw [hhost]
        rfl
      have hbytes : bytes = afterSort.mem.readBytes source.toNat
          (UInt32.ofNat (serialize input).length).toNat := by
        simpa [writtenStore, houtput] using hrun.symm
      refine ⟨output, hsorted, ?_⟩
      rw [hbytes, hbyteLength]
      rw [deserialize_readBytes]
      · exact congrArg some hread
      · rw [fits_iff] at hfit
        simp only [source, UInt32.reduceToNat, Nat.zero_add, UInt32.size]
        change 4 * input.length ≤ 32768 at hfit
        omega

theorem RunsValues.fits {input output : List UInt32}
    (h : RunsValues input output) : Fits input := by
  rcases h with ⟨fuel, hrun⟩
  by_contra hfit
  have hlong : bufferBytes < (serialize input).length := by
    exact Nat.lt_of_not_ge hfit
  simp [runValues, run_none_of_too_long fuel (serialize input) hlong] at hrun

/-- Every value-level result successfully produced by the program is a sorted
permutation of its input.  This safety statement is independent of Wasm's
finite-memory resource limit. -/
def Correct : Prop :=
  ∀ input output,
    RunsValues input output → SortedPermutation input output

theorem correct : Correct := by
  intro input output hruns
  have hfit := RunsValues.fits hruns
  rcases hruns with ⟨fuel, hrunValues⟩
  unfold runValues at hrunValues
  cases hrun : run fuel (serialize input) with
  | none => simp [hrun] at hrunValues
  | some bytes =>
      simp only [hrun, Option.bind_some] at hrunValues
      obtain ⟨sorted, hsorted, hdeserialize⟩ :=
        run_correct fuel input bytes hfit hrun
      rw [hdeserialize] at hrunValues
      simp only [Option.some.injEq] at hrunValues
      subst output
      exact hsorted

/-- Every input that fits the current fixed layout successfully produces an
output.  Keeping resource-bounded termination separate leaves `Correct` clean. -/
def Complete : Prop :=
  ∀ input, Fits input →
    ∃ output, RunsValues input output

theorem complete : Complete := by
  intro input hfit
  rcases execute_sort_complete input hfit with
    ⟨fuel, values, afterSort, hsort, hpost⟩
  obtain ⟨output, hsorted, hread, hcapacity⟩ := hpost
  have hhost := executeSort_host fuel (afterRead input) afterSort
    (mergeSortArguments source scratch input.length []) values hsort
  have hbyteLength :
      (UInt32.ofNat (serialize input).length).toNat = 4 * input.length := by
    rw [encodedLength_toNat input hfit, serialize_length]
  have hwriteBound : source.toNat +
      (UInt32.ofNat (serialize input).length).toNat ≤
      Wasm.StdIO.byteCapacity afterSort := by
    simp only [source, UInt32.reduceToNat, Nat.zero_add,
      Wasm.StdIO.byteCapacity, hbyteLength]
    exact hcapacity
  have hwrite := execute_write_bytes afterSort
    (UInt32.ofNat (serialize input).length) hwriteBound
  have houtput : afterSort.host.output = [] := by
    rw [hhost]
    rfl
  have hrun : run fuel (serialize input) =
      some (afterSort.mem.readBytes source.toNat (4 * input.length)) := by
    rw [run_fits fuel input hfit]
    unfold runAfterRead
    rw [probe_afterRead input]
    simp only [guard]
    rw [encodedLength_words input hfit]
    simp only [Bind.bind, Option.bind]
    simp only [if_true, Pure.pure]
    rw [hsort]
    simp only []
    rw [hwrite]
    simp only []
    simp only [writtenStore, houtput,
      List.nil_append, hbyteLength]
  refine ⟨output, fuel, ?_⟩
  unfold runValues
  rw [hrun]
  simp only [Option.bind_some]
  rw [deserialize_readBytes]
  · exact congrArg some hread
  · rw [fits_iff] at hfit
    simp only [source, UInt32.reduceToNat, Nat.zero_add, UInt32.size]
    change 4 * input.length ≤ 32768 at hfit
    omega

theorem exec_empty : run 100 (serialize []) = some (serialize []) := by
  native_decide

theorem exec_five :
    run 12000 (serialize [5, 1, 4, 2, 3]) =
      some (serialize [1, 2, 3, 4, 5]) := by
  native_decide

theorem exec_duplicates :
    run 15000 (serialize [4, 1, 4, 2, 1, 3]) =
      some (serialize [1, 1, 2, 3, 4, 4]) := by
  native_decide

theorem exec_values_five :
    runValues 12000 [5, 1, 4, 2, 3] = some [1, 2, 3, 4, 5] := by
  native_decide

end Wasm.Examples.MergeSort.StdIO
