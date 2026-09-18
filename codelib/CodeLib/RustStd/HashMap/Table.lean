import CodeLib.RustStd.HashMap.Basic

/-!
# A pure model of the `hashbrown` table under `std::collections::HashMap`

`CodeLib.RustStd.HashMap.Basic` models a map as an association list, which is
the observable content of the map.  This file models the data structure that
the compiled program keeps in memory: the SwissTable of `hashbrown` 0.16.1,
which Rust 1.95.0 vendors as the implementation of `HashMap`.  The model is
the bridge between the two.  A later memory-level proof states that a region
of wasm memory holds a `Table`, and `CodeLib.RustStd.HashMap.TableRefinement`
states that `toList` of that table is the association list the contract
speaks about.

The model follows `src/raw/mod.rs`, `src/control/tag.rs` and
`src/control/group/generic.rs` of `hashbrown` 0.16.1 at the level of control
bytes and slots, with the wasm32 parameters:

* a group is eight bytes (`Group::WIDTH`), the generic `u64` group;
* `h1` is the hash truncated to 32 bits, masked to a bucket index;
* `h2`, the tag of a full slot, is bits 25 to 31 of the hash;
* a slot of `(u32, u32)` has size 8, so the small-table minimum capacity is 3.

The representation is physical.  `ctrl` has `buckets + 8` bytes: the bytes
of the buckets, then one trailing group that mirrors the first group, exactly
as `set_ctrl` writes them.  A table with fewer than eight buckets keeps the
bytes between `buckets` and `8` at `EMPTY`.  Every group read is a window of
eight consecutive physical bytes.  `slots` has one entry per bucket and is
`some` only where the control byte is full.  The two counters `items` and
`growthLeft` are the two words of `RawTableInner`.

Every loop takes a fuel argument and is structurally recursive, so each
operation runs under `#eval`, `decide +kernel` and `cbv`.  The fuel of a
probe loop is `buckets / 8 + 1` windows; the refinement proves that a
well-formed table stops the loop inside that fuel.

Two places differ from the Rust code on purpose:

* The group predicates are exact per byte.  The generic `match_tag` of
  `hashbrown` is a SWAR trick that can also report a full byte equal to the
  tag with bit 0 flipped, when that byte follows a matching byte.  Such a
  false positive only adds one key comparison on a slot whose tag differs, so
  the slot found and the final table are the same.  `match_empty` and
  `match_empty_or_deleted` are exact in Rust as well, because a control byte
  is `0xFF`, `0x80` or below `0x80`.
* `rehashInPlace` is modelled in full, but no export of `rust_hash_map` can
  reach it: it runs only when `growth_left` is zero and the live items fit in
  half the capacity, which needs at least half the capacity in tombstones, and
  each export removes at most one key.

The hash function is a parameter `hash : K -> UInt64` of every operation
that needs it.  `CodeLib.RustStd.HashMap.SipHash.hashU32` is the function the
program uses, under keys that only a run of the program fixes.

The theorems at the end of the file are kernel-checked examples under a
test hash that puts key `k` at bucket `k` with tag `k`.  Each one pins one
rule of the table against a state computed by hand from the Rust code.
-/

namespace Wasm.RustStd.HashMap

/-! ## The table -/

/-- The state of one `RawTable<(K, V)>`. -/
structure Table (K V : Type) where
  /-- `bucket_mask + 1`.  One for the empty singleton, else a power of two
  that is at least four. -/
  buckets : Nat
  /-- The `buckets + 8` control bytes, with the trailing mirror group. -/
  ctrl : List UInt8
  /-- One entry per bucket, `some` exactly at the full buckets. -/
  slots : List (Option (K × V))
  /-- `items`: the number of full buckets. -/
  items : Nat
  /-- `growth_left`: inserts into `EMPTY` bytes left before a rehash. -/
  growthLeft : Nat
  deriving Repr

variable {K V : Type}

namespace Table

/-! ## Tags and hash parts -/

/-- `Tag::EMPTY`. -/
def EMPTY : UInt8 := 0xFF

/-- `Tag::DELETED`, a tombstone. -/
def DELETED : UInt8 := 0x80

/-- `Tag::is_full`: the top bit is clear. -/
def isFull (c : UInt8) : Bool := c < 0x80

/-- `Tag::is_special`: the top bit is set, so `EMPTY` or `DELETED`. -/
def isSpecial (c : UInt8) : Bool := 0x80 ≤ c

/-- The byte is `EMPTY`.  On a special byte this is `Tag::special_is_empty`. -/
def isEmpty (c : UInt8) : Bool := c == EMPTY

/-- `h1`: the hash as a `usize`, which is 32 bits on wasm32. -/
def h1 (hash : UInt64) : Nat := hash.toNat % 2 ^ 32

/-- `Tag::full(hash)`, also called `h2`: bits 25 to 31 of the hash. -/
def h2 (hash : UInt64) : UInt8 := ((hash >>> 25) &&& 0x7f).toUInt8

/-- `(a - b) mod n` for `n` a divisor of `2 ^ 32` and `b <= 2 ^ 32`: the
`wrapping_sub` then `& bucket_mask` idiom of the Rust code. -/
def wrapSub (a b n : Nat) : Nat := (a + 2 ^ 32 - b) % n



/-- The control byte of bucket `i`; `EMPTY` out of range. -/
def ctrlAt (t : Table K V) (i : Nat) : UInt8 := t.ctrl.getD i EMPTY

/-- The slot of bucket `i`; `none` out of range. -/
def slotAt (t : Table K V) (i : Nat) : Option (K × V) := t.slots.getD i none

/-- Does bucket `i` hold the key `k`?  The `eq` closure of the Rust code. -/
def keyIs [BEq K] (t : Table K V) (i : Nat) (k : K) : Bool :=
  match t.slotAt i with
  | some (k', _) => k' == k
  | none => false

/-- The second position that `set_ctrl` writes: the mirror of `i` in the
trailing group, or `i` itself once `i` is at least eight. -/
def index2 (buckets i : Nat) : Nat := wrapSub i 8 buckets + 8

/-- `set_ctrl`: write the byte at `i` and at its mirror. -/
def setCtrl (t : Table K V) (i : Nat) (c : UInt8) : Table K V :=
  { t with ctrl := (t.ctrl.set i c).set (index2 t.buckets i) c }

/-! ## Groups -/

/-- `Group::load(self.ctrl(pos))`: the eight physical bytes from `pos`. -/
def groupAt (t : Table K V) (pos : Nat) : List UInt8 :=
  (List.range 8).map fun j => t.ctrlAt (pos + j)

/-- `match_empty().any_bit_set()`. -/
def matchEmpty (g : List UInt8) : Bool := g.any isEmpty

/-- `match_empty_or_deleted().lowest_set_bit()`. -/
def lowestSpecial (g : List UInt8) : Option Nat := g.findIdx? isSpecial

/-- The bit offsets of `match_tag(tag)`, in ascending order. -/
def matchTag (tag : UInt8) (g : List UInt8) : List Nat :=
  (List.range g.length).filter fun j => g.getD j EMPTY == tag

/-- `match_empty().leading_zeros()` in bytes: the run of bytes that are not
`EMPTY` at the end of the group. -/
def leadNonEmpty (g : List UInt8) : Nat :=
  (g.reverse.takeWhile fun c => !isEmpty c).length

/-- `match_empty().trailing_zeros()` in bytes: the run of bytes that are not
`EMPTY` at the start of the group. -/
def trailNonEmpty (g : List UInt8) : Nat :=
  (g.takeWhile fun c => !isEmpty c).length

/-! ## Probing -/

/-- `ProbeSeq`: the current window start and the triangular stride. -/
structure ProbeSeq where
  pos : Nat
  stride : Nat
  deriving Repr

/-- `probe_seq(hash)`: start at `h1` masked to the table. -/
def probeStart (t : Table K V) (hash : UInt64) : ProbeSeq :=
  { pos := h1 hash % t.buckets, stride := 0 }

/-- `ProbeSeq::move_next`: grow the stride by one group, then advance. -/
def ProbeSeq.next (t : Table K V) (p : ProbeSeq) : ProbeSeq :=
  let stride := p.stride + 8
  { pos := (p.pos + stride) % t.buckets, stride }

/-- Windows to visit before a probe loop gives up.  Enough to see every
group once. -/
def probeFuel (t : Table K V) : Nat := t.buckets / 8 + 1

/-- `fix_insert_index`: in a table with fewer than eight buckets the window
can name a full bucket through the padding; then take the first special byte
of the aligned first group instead. -/
def fixInsertIndex (t : Table K V) (i : Nat) : Nat :=
  if isFull (t.ctrlAt i) then (lowestSpecial (groupAt t 0)).getD i else i

/-- The loop of `find_insert_index`. -/
def findInsertIndexLoop (t : Table K V) : Nat → ProbeSeq → Option Nat
  | 0, _ => none
  | fuel + 1, p =>
    match lowestSpecial (groupAt t p.pos) with
    | some j => some (fixInsertIndex t ((p.pos + j) % t.buckets))
    | none => findInsertIndexLoop t fuel (p.next t)

/-- `find_insert_index`: the first special bucket along the probe sequence. -/
def findInsertIndex (t : Table K V) (hash : UInt64) : Nat :=
  (findInsertIndexLoop t (probeFuel t) (probeStart t hash)).getD 0

/-- The loop of `find_inner`. -/
def findLoop [BEq K] (t : Table K V) (tag : UInt8) (k : K) :
    Nat → ProbeSeq → Option Nat
  | 0, _ => none
  | fuel + 1, p =>
    let g := groupAt t p.pos
    match (matchTag tag g).find? (fun j => t.keyIs ((p.pos + j) % t.buckets) k) with
    | some j => some ((p.pos + j) % t.buckets)
    | none => if matchEmpty g then none else findLoop t tag k fuel (p.next t)

/-- `find_inner`: the bucket that holds `k`, if any. -/
def find [BEq K] (t : Table K V) (hash : UInt64) (k : K) : Option Nat :=
  findLoop t (h2 hash) k (probeFuel t) (probeStart t hash)

/-- The result of `find_or_find_insert_index`: `Ok(index)` or `Err(index)`. -/
inductive Lookup where
  | found (i : Nat)
  | insertAt (i : Nat)
  deriving Repr, DecidableEq

/-- The loop of `find_or_find_insert_index_inner`.  The candidate is the first
special bucket seen so far; it is fixed up only when the loop returns it. -/
def findOrFindInsertLoop [BEq K] (t : Table K V) (tag : UInt8) (k : K) :
    Nat → ProbeSeq → Option Nat → Lookup
  | 0, _, cand => .insertAt (fixInsertIndex t (cand.getD 0))
  | fuel + 1, p, cand =>
    let g := groupAt t p.pos
    match (matchTag tag g).find? (fun j => t.keyIs ((p.pos + j) % t.buckets) k) with
    | some j => .found ((p.pos + j) % t.buckets)
    | none =>
      let cand := match cand with
        | some c => some c
        | none => (lowestSpecial g).map fun j => (p.pos + j) % t.buckets
      if matchEmpty g then .insertAt (fixInsertIndex t (cand.getD 0))
      else findOrFindInsertLoop t tag k fuel (p.next t) cand

/-- `find_or_find_insert_index_inner`. -/
def findOrFindInsertIndex [BEq K] (t : Table K V) (hash : UInt64) (k : K) : Lookup :=
  findOrFindInsertLoop t (h2 hash) k (probeFuel t) (probeStart t hash) none

/-! ## Sizing -/

/-- The least power of two that is at least `n`, for `n < 2 ^ 32`.
`usize::next_power_of_two` on wasm32. -/
def nextPow2 (n : Nat) : Nat := go 32 1
where
  go : Nat → Nat → Nat
  | 0, p => p
  | f + 1, p => if n ≤ p then p else go f (p * 2)

/-- `capacity_to_buckets` for a slot of size 8 and a group of width 8. -/
def capacityToBuckets (cap : Nat) : Nat :=
  if cap < 15 then
    let c := max 3 cap
    if c < 4 then 4 else if c < 8 then 8 else 16
  else nextPow2 (cap * 8 / 7)

/-- `bucket_mask_to_capacity`. -/
def bucketMaskToCapacity (mask : Nat) : Nat :=
  if mask < 8 then mask else (mask + 1) / 8 * 7

/-- `RawTable::new()`: the empty singleton with `bucket_mask = 0`. -/
def empty : Table K V :=
  { buckets := 1, ctrl := List.replicate 9 EMPTY, slots := [none],
    items := 0, growthLeft := 0 }

/-- `new_uninitialized` then `fill_empty`, for `buckets` buckets. -/
def newEmpty (buckets : Nat) : Table K V :=
  { buckets, ctrl := List.replicate (buckets + 8) EMPTY,
    slots := List.replicate buckets none,
    items := 0, growthLeft := bucketMaskToCapacity (buckets - 1) }

/-- `with_capacity`. -/
def withCapacity (cap : Nat) : Table K V :=
  if cap = 0 then empty else newEmpty (capacityToBuckets cap)

/-! ## Writes -/

/-- `insert_at_index`: `record_item_insert_at` then the slot write.
`growth_left` drops only when the byte was `EMPTY`. -/
def insertAt (t : Table K V) (i : Nat) (tag : UInt8) (kv : K × V) : Table K V :=
  let old := t.ctrlAt i
  let t := t.setCtrl i tag
  { t with slots := t.slots.set i (some kv), items := t.items + 1,
           growthLeft := t.growthLeft - (if isEmpty old then 1 else 0) }

/-- The full buckets in ascending order: `full_buckets_indices`. -/
def fullIndices (t : Table K V) : List Nat :=
  (List.range t.buckets).filter fun i => isFull (t.ctrlAt i)

/-- `resize_inner`: a fresh table for `cap` items, each full bucket placed by
`find_insert_index` in ascending old order, then the counters. -/
def resize (hash : K → UInt64) (t : Table K V) (cap : Nat) : Table K V :=
  let fresh : Table K V := withCapacity cap
  let moved := (fullIndices t).foldl (fun n i =>
      match t.slotAt i with
      | some (k, v) =>
        let h := hash k
        let j := findInsertIndex n h
        let n := n.setCtrl j (h2 h)
        { n with slots := n.slots.set j (some (k, v)) }
      | none => n) fresh
  { moved with items := t.items, growthLeft := moved.growthLeft - t.items }

/-- `prepare_rehash_in_place`: every special byte becomes `EMPTY`, every full
byte becomes `DELETED`, and the trailing group is rebuilt. -/
def prepareRehash (t : Table K V) : Table K V :=
  let body := (List.range t.buckets).map fun i =>
    if isSpecial (t.ctrlAt i) then EMPTY else DELETED
  let ctrl :=
    if t.buckets < 8 then body ++ List.replicate (8 - t.buckets) EMPTY ++ body
    else body ++ body.take 8
  { t with ctrl }

/-- `is_in_same_group`: both buckets lie in the same window of the probe
sequence that starts at `h1`. -/
def isInSameGroup (t : Table K V) (i newI : Nat) (hash : UInt64) : Bool :=
  let start := h1 hash % t.buckets
  wrapSub i start t.buckets / 8 == wrapSub newI start t.buckets / 8

/-- The inner loop of `rehash_in_place` for the tombstone at `i`.  Each turn
either settles the item at `i` or swaps it with another tombstone. -/
def rehashOne (hash : K → UInt64) (t : Table K V) (i : Nat) : Nat → Table K V
  | 0 => t
  | fuel + 1 =>
    match t.slotAt i with
    | none => t
    | some (k, v) =>
      let h := hash k
      let newI := findInsertIndex t h
      if isInSameGroup t i newI h then t.setCtrl i (h2 h)
      else
        let prev := t.ctrlAt newI
        let t := t.setCtrl newI (h2 h)
        if isEmpty prev then
          let t := t.setCtrl i EMPTY
          { t with slots := (t.slots.set newI (some (k, v))).set i none }
        else
          let other := t.slotAt newI
          let t := { t with slots := (t.slots.set newI (some (k, v))).set i other }
          rehashOne hash t i fuel

/-- `rehash_in_place`.  Not reachable from the `rust_hash_map` exports; see
the file comment. -/
def rehashInPlace (hash : K → UInt64) (t : Table K V) : Table K V :=
  let t := prepareRehash t
  let t := (List.range t.buckets).foldl (fun t i =>
    if t.ctrlAt i == DELETED then rehashOne hash t i t.buckets else t) t
  { t with growthLeft := bucketMaskToCapacity (t.buckets - 1) - t.items }

/-- `reserve`, with the `reserve_rehash_inner` decision. -/
def reserve (hash : K → UInt64) (t : Table K V) (additional : Nat) : Table K V :=
  if additional ≤ t.growthLeft then t
  else
    let newItems := t.items + additional
    let fullCap := bucketMaskToCapacity (t.buckets - 1)
    if newItems ≤ fullCap / 2 then rehashInPlace hash t
    else resize hash t (max newItems (fullCap + 1))

/-! ## The map operations -/

/-- `HashMap::insert`: `reserve(1)` first, then the lookup.  A present key
keeps its stored key object and takes the new value. -/
def insert [BEq K] (hash : K → UInt64) (t : Table K V) (k : K) (v : V) :
    Option V × Table K V :=
  let t := reserve hash t 1
  let h := hash k
  match findOrFindInsertIndex t h k with
  | .found i =>
    match t.slotAt i with
    | some (k', v') => (some v', { t with slots := t.slots.set i (some (k', v)) })
    | none => (none, t)
  | .insertAt i => (none, insertAt t i (h2 h) (k, v))

/-- `erase`: the byte becomes `DELETED` when the eight-byte windows around
`i` show a run of at least eight bytes that are not `EMPTY`, else `EMPTY`. -/
def erase (t : Table K V) (i : Nat) : Table K V :=
  let before := wrapSub i 8 t.buckets
  let lead := leadNonEmpty (groupAt t before)
  let trail := trailNonEmpty (groupAt t i)
  let tomb := 8 ≤ lead + trail
  let t := t.setCtrl i (if tomb then DELETED else EMPTY)
  { t with slots := t.slots.set i none, items := t.items - 1,
           growthLeft := if tomb then t.growthLeft else t.growthLeft + 1 }

/-- `HashMap::remove`. -/
def remove [BEq K] (hash : K → UInt64) (t : Table K V) (k : K) :
    Option V × Table K V :=
  match find t (hash k) k with
  | some i => ((t.slotAt i).map Prod.snd, erase t i)
  | none => (none, t)

/-- `HashMap::get`. -/
def get [BEq K] (hash : K → UInt64) (t : Table K V) (k : K) : Option V :=
  (find t (hash k) k).bind fun i => (t.slotAt i).map Prod.snd

/-- `HashMap::contains_key`. -/
def containsKey [BEq K] (hash : K → UInt64) (t : Table K V) (k : K) : Bool :=
  (find t (hash k) k).isSome

/-- `HashMap::len`. -/
def len (t : Table K V) : Nat := t.items

/-- The entries in bucket order, which is the order of `RawIter`. -/
def toList (t : Table K V) : List (K × V) :=
  (List.range t.buckets).filterMap t.slotAt

/-- `Extend::extend`: reserve the size hint, or half of it on a table that
already has items, then insert each entry. -/
def extend [BEq K] (hash : K → UInt64) (t : Table K V) (es : List (K × V)) :
    Table K V :=
  let hint := es.length
  let t := reserve hash t (if t.items = 0 then hint else (hint + 1) / 2)
  es.foldl (fun t kv => (Table.insert hash t kv.1 kv.2).2) t

/-- `FromIterator::from_iter` of `std`: an empty map, then `extend` with the
exact length of the `Vec` as the size hint. -/
def ofEntries [BEq K] (hash : K → UInt64) (es : List (K × V)) : Table K V :=
  extend hash empty es

/-! ## Kernel-checked examples

`toyHash k` has `h1 = k` and `h2 = k` for `k < 128`, so key `k` starts at
bucket `k mod buckets` with tag `k`. -/

/-- A test hash with bucket `k` and tag `k` for small `k`. -/
def toyHash (k : Nat) : UInt64 := UInt64.ofNat k ||| (UInt64.ofNat k <<< 25)

/-- Sizing, from the Rust code by hand. -/
theorem capacityToBuckets_examples :
    [1, 3, 4, 7, 8, 14, 15, 28, 29].map capacityToBuckets
      = [4, 4, 8, 8, 16, 16, 32, 32, 64] := by decide +kernel

theorem bucketMaskToCapacity_examples :
    [0, 3, 7, 15, 31].map bucketMaskToCapacity = [0, 3, 7, 14, 28] := by decide +kernel

/-- Three entries: four buckets, capacity three, no growth left. -/
def three : Table Nat Nat := Table.ofEntries toyHash [(1, 10), (2, 20), (3, 30)]

theorem three_ctrl :
    three.ctrl = [0xFF, 1, 2, 3, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 1, 2, 3] ∧
    three.buckets = 4 ∧ three.items = 3 ∧ three.growthLeft = 0 := by decide +kernel

/-- A fourth key resizes to eight buckets before the lookup. -/
theorem three_insert_resizes :
    let r := Table.insert toyHash three 4 40
    r.1 = none ∧ r.2.buckets = 8 ∧ r.2.items = 4 ∧ r.2.growthLeft = 3 ∧
    r.2.ctrl = [0xFF, 1, 2, 3, 4, 0xFF, 0xFF, 0xFF, 0xFF, 1, 2, 3, 4, 0xFF, 0xFF, 0xFF] ∧
    Table.toList r.2 = [(1, 10), (2, 20), (3, 30), (4, 40)] := by decide +kernel

/-- A present key with no growth left still resizes, and keeps `items`. -/
theorem three_insert_present_resizes :
    let r := Table.insert toyHash three 2 21
    r.1 = some 20 ∧ r.2.buckets = 8 ∧ r.2.items = 3 ∧
    Table.toList r.2 = [(1, 10), (2, 21), (3, 30)] := by decide +kernel

/-- Erase in a four-bucket table always leaves `EMPTY`. -/
theorem three_remove :
    let r := Table.remove toyHash three 2
    r.1 = some 20 ∧ r.2.items = 2 ∧ r.2.growthLeft = 1 ∧
    r.2.ctrl = [0xFF, 1, 0xFF, 3, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 1, 0xFF, 3] := by
  decide +kernel

/-- Eight consecutive keys in a sixteen-bucket table. -/
def eight : Table Nat Nat := Table.ofEntries toyHash ((List.range 8).map fun k => (k, k))

/-- Erase inside a run of eight full bytes leaves a tombstone. -/
theorem eight_remove_tombstone :
    let r := Table.remove toyHash eight 3
    eight.buckets = 16 ∧ eight.growthLeft = 6 ∧
    r.1 = some 3 ∧ r.2.items = 7 ∧ r.2.growthLeft = 6 ∧ r.2.ctrlAt 3 = DELETED := by
  decide +kernel

/-- Seven keys in an eight-bucket table: the run is seven, so `EMPTY`. -/
theorem seven_remove_empty :
    let t : Table Nat Nat := Table.ofEntries toyHash ((List.range 7).map fun k => (k, k))
    let r := Table.remove toyHash t 3
    t.buckets = 8 ∧ r.2.ctrlAt 3 = EMPTY ∧ r.2.growthLeft = 1 := by decide +kernel

/-- Key 16 collides with bucket 0, whose window is full, and lands in the
second window at bucket 8.  A lookup follows the same path. -/
theorem eight_second_window :
    let r := Table.insert toyHash eight 16 160
    r.2.ctrlAt 8 = 16 ∧ Table.get toyHash r.2 16 = some 160 ∧ Table.get toyHash r.2 24 = none ∧
    Table.containsKey toyHash r.2 7 = true := by decide +kernel

/-- `fix_insert_index`: in a four-bucket table the window at bucket 3 names
bucket 0 through the padding, bucket 0 is full, so the aligned first group
gives bucket 1. -/
theorem fix_insert_index_example :
    let t : Table Nat Nat := Table.ofEntries toyHash [(0, 0), (3, 3)]
    let r := Table.insert toyHash t 7 70
    Table.toList r.2 = [(0, 0), (7, 70), (3, 3)] ∧ r.2.buckets = 4 := by decide +kernel

/-- A repeated key keeps its last value and costs no growth. -/
theorem duplicate_key :
    let t : Table Nat Nat := Table.ofEntries toyHash [(1, 10), (1, 11)]
    Table.toList t = [(1, 11)] ∧ t.items = 1 ∧ t.growthLeft = 2 := by decide +kernel

/-- The singleton grows to four buckets on the first insert. -/
theorem empty_insert :
    let t : Table Nat Nat := Table.ofEntries toyHash []
    let r := Table.insert toyHash t 5 50
    t.buckets = 1 ∧ r.2.buckets = 4 ∧ Table.toList r.2 = [(5, 50)] := by decide +kernel

/-- Fourteen keys fill a sixteen-bucket table; eight removes leave eight
tombstones; the next insert rehashes in place, with the six live keys back
at their buckets and no tombstone left. -/
theorem rehash_in_place_example :
    let t : Table Nat Nat := Table.ofEntries toyHash ((List.range 14).map fun k => (k, k))
    let t := (List.range 8).foldl (fun t k => (Table.remove toyHash t k).2) t
    let r := Table.insert toyHash t 20 200
    t.growthLeft = 0 ∧ t.items = 6 ∧
    r.2.buckets = 16 ∧ r.2.items = 7 ∧ r.2.growthLeft = 7 ∧
    Table.toList r.2 = [(20, 200), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13)] ∧
    (List.range 16).all (fun i => r.2.ctrlAt i != DELETED) = true := by decide +kernel

end Table

end Wasm.RustStd.HashMap
