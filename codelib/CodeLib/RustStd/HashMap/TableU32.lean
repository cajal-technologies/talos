import CodeLib.RustStd.HashMap.TableRefinement
import CodeLib.RustStd.HashMap.SipHash

/-!
# The table model at the types of `rust_hash_map`

The crate `rust_hash_map` uses `HashMap<u32, u32>` with the default
`RandomState`, so it hashes each key with SipHash-1-3 over the four
little-endian bytes of the key.  This file fixes `K = V = UInt32` and the
hash `SipHash.hashU32 k0 k1` in the results of
`CodeLib.RustStd.HashMap.TableRefinement`.  The two seeds stay parameters:
the program derives them from two addresses at run time, and a proof about
one run reads them back from the memory of that run.

The statements have the shapes of the outputs in `Project.RustHashMap.Spec`:
`(HashMap.insert (HashMap.ofEntries es) k v).1` and `.2`,
`(HashMap.remove (HashMap.ofEntries es) k).1` and `.2`, `HashMap.get m k` for
a map `m` without repeated keys, `HashMap.containsKey`, `HashMap.len`, and
`sortByKey` of the table.  The one bound is `es.length <= 2 ^ 30`, which
keeps the bucket count below `2 ^ 32`.  The contracts in `Spec` assume
`entries.length < 2 ^ 32`.  This gap does not block the composition: one
wire entry is 8 bytes, and the memory of wasm32 holds at most 4 GiB, so the
program cannot read an input with more than `2 ^ 29` entries, and the
out-of-memory branch of `WritesOrOOM` covers those inputs.

The theorems at the end are kernel checks of the model on the inputs of
interpreter runs of the `rust_hash_map` module.  The seeds are the values
that the program computed in those runs.  The control bytes are the bytes
that the model computes, and the same bytes were found in the linear memory
of the module after each run.  That comparison with memory was made outside
this file.  Here the kernel evaluates SipHash-1-3 and the table operations
and confirms the recorded bytes.  No proof in this file uses `native_decide`.
-/

namespace Wasm.RustStd.HashMap

/-- The displaced value of `insert` is the old value of the key. -/
theorem insert_fst {K V : Type} [BEq K] (m : Map K V) (key : K) (value : V) :
    (HashMap.insert m key value).1 = HashMap.get m key := by
  unfold HashMap.insert HashMap.get
  cases m.find? (fun entry => entry.1 == key) <;> rfl

namespace Table

/-! ### The exports at `UInt32` -/

theorem wf_ofEntries_u32 (k0 k1 : UInt64) (es : Map UInt32 UInt32)
    (hn : es.length ≤ 2 ^ 30) :
    WF (SipHash.hashU32 k0 k1) (ofEntries (SipHash.hashU32 k0 k1) es) ∧
      Clean (ofEntries (SipHash.hashU32 k0 k1) es) ∧
      (ofEntries (SipHash.hashU32 k0 k1) es).buckets < 2 ^ 32 ∧
      (toList (ofEntries (SipHash.hashU32 k0 k1) es)).Perm (HashMap.ofEntries es) :=
  wf_ofEntries _ es hn

theorem sortByKey_ofEntries_u32 (k0 k1 : UInt64) (es : Map UInt32 UInt32)
    (hn : es.length ≤ 2 ^ 30) :
    sortByKey (toList (ofEntries (SipHash.hashU32 k0 k1) es)) =
      sortByKey (HashMap.ofEntries es) :=
  sortByKey_ofEntries (fun _ _ _ => UInt32.le_trans) UInt32.le_total
    (fun _ _ => UInt32.le_antisymm) _ es hn

theorem get_ofEntries_u32 (k0 k1 : UInt64) (es : Map UInt32 UInt32)
    (hn : es.length ≤ 2 ^ 30) (key : UInt32) :
    Table.get (SipHash.hashU32 k0 k1) (ofEntries (SipHash.hashU32 k0 k1) es) key =
      HashMap.get (HashMap.ofEntries es) key :=
  get_ofEntries _ es hn key

/-- The shape of `get_on_hashMap`: the input is a map without repeated keys. -/
theorem get_ofNodup_u32 (k0 k1 : UInt64) (m : Map UInt32 UInt32) (hnd : NodupKeys m)
    (hn : m.length ≤ 2 ^ 30) (key : UInt32) :
    Table.get (SipHash.hashU32 k0 k1) (ofEntries (SipHash.hashU32 k0 k1) m) key =
      HashMap.get m key := by
  rw [get_ofEntries _ m hn, ofEntries_eq_self_of_nodup hnd]

theorem containsKey_ofEntries_u32 (k0 k1 : UInt64) (es : Map UInt32 UInt32)
    (hn : es.length ≤ 2 ^ 30) (key : UInt32) :
    Table.containsKey (SipHash.hashU32 k0 k1) (ofEntries (SipHash.hashU32 k0 k1) es) key =
      HashMap.containsKey (HashMap.ofEntries es) key :=
  containsKey_ofEntries _ es hn key

theorem len_ofEntries_u32 (k0 k1 : UInt64) (es : Map UInt32 UInt32)
    (hn : es.length ≤ 2 ^ 30) :
    len (ofEntries (SipHash.hashU32 k0 k1) es) = HashMap.len (HashMap.ofEntries es) :=
  len_ofEntries _ es hn

/-- The shape of `insert_on_serialized`: the displaced value and the updated
map, the second up to the sort of the output. -/
theorem insert_ofEntries_u32 (k0 k1 : UInt64) (es : Map UInt32 UInt32)
    (hn : es.length ≤ 2 ^ 30) (key value : UInt32) :
    (Table.insert (SipHash.hashU32 k0 k1) (ofEntries (SipHash.hashU32 k0 k1) es) key value).1 =
        (HashMap.insert (HashMap.ofEntries es) key value).1 ∧
      sortByKey (toList (Table.insert (SipHash.hashU32 k0 k1)
          (ofEntries (SipHash.hashU32 k0 k1) es) key value).2) =
        sortByKey (HashMap.insert (HashMap.ofEntries es) key value).2 := by
  have h := insert_ofEntries (fun _ _ _ => UInt32.le_trans) UInt32.le_total
    (fun _ _ => UInt32.le_antisymm) (SipHash.hashU32 k0 k1) es hn key value
  exact ⟨by rw [h.1, insert_fst], h.2⟩

/-- The shape of `remove_on_serialized`. -/
theorem remove_ofEntries_u32 (k0 k1 : UInt64) (es : Map UInt32 UInt32)
    (hn : es.length ≤ 2 ^ 30) (key : UInt32) :
    (Table.remove (SipHash.hashU32 k0 k1) (ofEntries (SipHash.hashU32 k0 k1) es) key).1 =
        (HashMap.remove (HashMap.ofEntries es) key).1 ∧
      sortByKey (toList (Table.remove (SipHash.hashU32 k0 k1)
          (ofEntries (SipHash.hashU32 k0 k1) es) key).2) =
        sortByKey (HashMap.remove (HashMap.ofEntries es) key).2 :=
  remove_ofEntries (fun _ _ _ => UInt32.le_trans) UInt32.le_total
    (fun _ _ => UInt32.le_antisymm) _ es hn key

/-! ### Kernel checks on the inputs of interpreter runs

Each run of an export computes its seeds from two addresses.  In the runs
below `k0` is `1048143` for `map_insert` and `1048191` for `map_remove`;
`k1` depends on the size of the input.  The model gets the seeds of the run
and reproduces the control bytes that the run left in memory. -/

/-- The first seed of the `map_insert` runs. -/
def insertK0 : UInt64 := 1048143

/-- The first seed of the `map_remove` runs. -/
def removeK0 : UInt64 := 1048191

/-- Three entries, as `map_insert` builds them from the wire. -/
def threeU32 : Table UInt32 UInt32 :=
  ofEntries (SipHash.hashU32 insertK0 1049712) [(1, 10), (2, 20), (3, 30)]

theorem threeU32_ctrl :
    threeU32.buckets = 4 ∧ threeU32.items = 3 ∧ threeU32.growthLeft = 0 ∧
    threeU32.ctrl = [255, 112, 69, 52, 255, 255, 255, 255, 255, 112, 69, 52] := by
  decide +kernel

/-- A fourth key resizes to eight buckets. -/
theorem threeU32_insert :
    let r := Table.insert (SipHash.hashU32 insertK0 1049712) threeU32 4 40
    r.1 = none ∧ r.2.buckets = 8 ∧ r.2.items = 4 ∧ r.2.growthLeft = 3 ∧
    r.2.ctrl = [29, 255, 69, 255, 255, 112, 52, 255, 29, 255, 69, 255, 255, 112, 52, 255] := by
  decide +kernel

/-- A present key with no growth left still resizes and keeps `items`. -/
theorem threeU32_insert_present :
    let r := Table.insert (SipHash.hashU32 insertK0 1049712) threeU32 2 21
    r.1 = some 20 ∧ r.2.buckets = 8 ∧ r.2.items = 3 ∧ r.2.growthLeft = 4 ∧
    r.2.ctrl = [255, 255, 69, 255, 255, 112, 52, 255, 255, 255, 69, 255, 255, 112, 52, 255] := by
  decide +kernel

/-- Fourteen entries fill a sixteen-bucket table. -/
def fourteenU32 : Table UInt32 UInt32 :=
  ofEntries (SipHash.hashU32 insertK0 1049928)
    [(1, 0), (8, 1), (15, 2), (22, 3), (29, 4), (36, 5), (43, 6), (50, 7), (57, 8),
      (64, 9), (71, 10), (78, 11), (85, 12), (92, 13)]

theorem fourteenU32_ctrl :
    fourteenU32.buckets = 16 ∧ fourteenU32.items = 14 ∧ fourteenU32.growthLeft = 0 ∧
    fourteenU32.ctrl = [21, 255, 17, 106, 32, 29, 79, 70, 255, 84, 16, 1, 79, 81, 13, 3,
      21, 255, 17, 106, 32, 29, 79, 70] := by
  decide +kernel

/-- The fifteenth key resizes to thirty-two buckets. -/
theorem fourteenU32_insert :
    let r := Table.insert (SipHash.hashU32 insertK0 1049928) fourteenU32 100 1000
    r.1 = none ∧ r.2.buckets = 32 ∧ r.2.items = 15 ∧ r.2.growthLeft = 13 ∧
    r.2.ctrl = [255, 255, 255, 255, 32, 255, 255, 255, 255, 21, 13, 255, 255, 255, 255, 255,
      255, 82, 17, 106, 255, 29, 79, 70, 255, 84, 16, 1, 79, 81, 3, 255,
      255, 255, 255, 255, 32, 255, 255, 255] := by
  decide +kernel

/-- Eight keys that fill the first window of a sixteen-bucket table. -/
def windowU32 : Table UInt32 UInt32 :=
  ofEntries (SipHash.hashU32 insertK0 1049880)
    [(1, 1), (1005, 1005), (2000, 2000), (3031, 3031), (4001, 4001), (5043, 5043),
      (6001, 6001), (7016, 7016)]

/-- A ninth key that starts in the full window lands in the second window. -/
theorem windowU32_insert :
    let r := Table.insert (SipHash.hashU32 insertK0 1049880) windowU32 5011 7
    windowU32.ctrl = [107, 29, 13, 2, 118, 18, 42, 101, 255, 255, 255, 255, 255, 255, 255, 255,
      107, 29, 13, 2, 118, 18, 42, 101] ∧
    r.1 = none ∧ r.2.items = 9 ∧ r.2.growthLeft = 5 ∧
    r.2.ctrl = [107, 29, 13, 2, 118, 18, 42, 101, 51, 255, 255, 255, 255, 255, 255, 255,
      107, 29, 13, 2, 118, 18, 42, 101] := by
  decide +kernel

/-- Eight keys in one window of a sixteen-bucket table, for `map_remove`. -/
def runU32 : Table UInt32 UInt32 :=
  ofEntries (SipHash.hashU32 removeK0 1049880)
    [(7, 7), (1003, 1003), (2015, 2015), (3026, 3026), (4017, 4017), (5005, 5005),
      (6014, 6014), (7005, 7005)]

/-- Erase inside a run of eight full bytes leaves a tombstone. -/
theorem runU32_remove :
    let r := Table.remove (SipHash.hashU32 removeK0 1049880) runU32 3026
    runU32.ctrl = [121, 52, 120, 38, 123, 21, 64, 4, 255, 255, 255, 255, 255, 255, 255, 255,
      121, 52, 120, 38, 123, 21, 64, 4] ∧
    r.1 = some 3026 ∧ r.2.items = 7 ∧ r.2.growthLeft = 6 ∧ r.2.ctrlAt 3 = DELETED ∧
    r.2.ctrl = [121, 52, 120, 128, 123, 21, 64, 4, 255, 255, 255, 255, 255, 255, 255, 255,
      121, 52, 120, 128, 123, 21, 64, 4] := by
  decide +kernel

/-- Seven keys in an eight-bucket table, for `map_remove`. -/
def sevenU32 : Table UInt32 UInt32 :=
  ofEntries (SipHash.hashU32 removeK0 1049744)
    [(3, 3), (1011, 1011), (2016, 2016), (3004, 3004), (4008, 4008), (5040, 5040),
      (6013, 6013)]

/-- The run is seven, so erase leaves `EMPTY` and returns the growth. -/
theorem sevenU32_remove :
    let r := Table.remove (SipHash.hashU32 removeK0 1049744) sevenU32 3004
    sevenU32.ctrl = [50, 78, 47, 27, 42, 101, 54, 255, 50, 78, 47, 27, 42, 101, 54, 255] ∧
    r.1 = some 3004 ∧ r.2.items = 6 ∧ r.2.growthLeft = 1 ∧ r.2.ctrlAt 3 = EMPTY ∧
    r.2.ctrl = [50, 78, 47, 255, 42, 101, 54, 255, 50, 78, 47, 255, 42, 101, 54, 255] := by
  decide +kernel

end Table

end Wasm.RustStd.HashMap
