import CodeLib.Examples.MergeSort.TotalProof
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

open Wasm SmallStep

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

set_option maxRecDepth 10000 in
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
  let (probeValues, afterProbe) ← execute 2 0 afterRead
    [.i32 (UInt32.ofNat 65536), .i32 1]
  guard (probeValues = [.i32 0])
  let (_, afterSort) ← execute fuel 2 afterProbe
    (mergeSortArguments source scratch (byteLength.toNat / 4) [])
  let (_, afterWrite) ← execute 2 1 afterSort
    [.i32 source, .i32 byteLength]
  pure afterWrite.host.output

theorem run_none_of_too_long (fuel : Nat) (input : List UInt8)
    (hlong : bufferBytes < input.length) :
    run fuel input = none := by
  simp [run, read_bounded]
  intro values store hprobe
  have hprobeNone : execute 2 0 (afterBoundedRead input)
      [.i32 (65536 : UInt32), .i32 1] = none := by
    simpa only [show (65536 : UInt32) = UInt32.ofNat 65536 by decide] using
      probe_traps_of_too_long input hlong
  rw [hprobeNone] at hprobe
  contradiction

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

theorem fits_iff (values : List UInt32) :
    Fits values ↔ 4 * values.length ≤ bufferBytes := by
  simp only [Fits, serialize_length]

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

/-- Every input that fits the current fixed layout successfully produces an
output.  Keeping resource-bounded termination separate leaves `Correct` clean. -/
def Complete : Prop :=
  ∀ input, Fits input →
    ∃ output, RunsValues input output

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
