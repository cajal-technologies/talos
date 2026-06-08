import Interpreter.Wasm
import Interpreter.Wasm.Spec.Termination

/-!
# NEAR host state (`α := NearState`)

The interpreter threads an opaque `host : α` slot through `Store α`; host
imports are the only code that inspects it. This module instantiates that
slot for the **NEAR Protocol** smart-contract host environment.

`NearState` is the part of the NEAR runtime a single contract call can
observe and mutate:

* `storage`   — the contract's storage trie, modelled as a *pure function*
  `key → Option value` (mirroring `Mem.bytes : Nat → UInt8`). This is the
  "projection of NEAR state" specs reason about before/after a call; the
  function model supports `∀ key` (frame) reasoning directly, and NEAR's
  storage-iterator host functions are deprecated so contracts can't
  enumerate keys anyway — only ghost specs do, via quantifiers.
* `registers` — the NEAR register ABI scratch buffers (`id → bytes`). Host
  functions that "return" variable-length data write it to a register; the
  contract then copies it into linear memory via `read_register`.
* `context`   — immutable call context (account ids, input bytes, deposit).
* `returnData` / `logs` — outputs produced via `value_return` / logging.

Promises / cross-contract calls are deliberately out of scope for now.

The host-function semantics live in `CodeLib/Near/Env.lean`; this file is
just the state shape plus the pure helpers those functions are built from.
-/

namespace Wasm

/-- `2^64 - 1`, the NEAR register/length sentinel. Used by host functions
that read an argument through `getMemOrReg`: a length field equal to this
value means "the pointer is a register id, take the bytes already in that
register" rather than "read this many bytes of linear memory". When used
as an output `register_id`, the same value means "discard the output". -/
def u64Max : UInt64 := 0xFFFFFFFFFFFFFFFF

/-- Read `len` consecutive bytes of linear memory starting at byte offset
`off`. Total (out-of-range addresses read whatever `bytes` returns there);
callers bounds-check first. The `List.range`-map shape is the canonical
"easy to `simp`/compute through" form, matching `Mem.fill`/`Mem.copy`. -/
def Mem.readBytes (m : Mem) (off len : Nat) : List UInt8 :=
  (List.range len).map (fun i => m.bytes (off + i))

/-- Immutable per-call NEAR context. Account ids and `input` are raw byte
strings (NEAR account ids are UTF-8; contract input is opaque bytes,
conventionally JSON or Borsh). `attachedDeposit` is a yoctoNEAR `u128`,
written to memory as 16 little-endian bytes by `attached_deposit`. -/
structure NearContext where
  currentAccountId     : List UInt8 := []
  predecessorAccountId : List UInt8 := []
  signerAccountId      : List UInt8 := []
  /-- Raw call input (method arguments). Read into a register by `input`. -/
  input                : List UInt8 := []
  /-- Attached deposit in yoctoNEAR (`u128`). -/
  attachedDeposit      : Nat := 0
deriving Inhabited

/-- The NEAR host state threaded as `Store.host`. -/
structure NearState where
  /-- Storage trie projection: `key ↦ value`, `none` when absent. -/
  storage    : List UInt8 → Option (List UInt8) := fun _ => none
  /-- Register ABI scratch buffers: `id ↦ bytes`, `none` when unset. -/
  registers  : Nat → Option (List UInt8) := fun _ => none
  context    : NearContext := {}
  /-- Value set by `value_return` (the call's result), if any. -/
  returnData : Option (List UInt8) := none
  /-- Log lines emitted during the call, newest last. -/
  logs       : List (List UInt8) := []
deriving Inhabited

namespace NearState

/-- Set register `id` to `data` (creating or overwriting). -/
def setRegister (ns : NearState) (id : Nat) (data : List UInt8) : NearState :=
  { ns with registers := fun i => if i = id then some data else ns.registers i }

/-- Set register `id` unless NEAR's output-register discard sentinel was
passed. Output `register_id = u64::MAX` means "do not copy the output". -/
def setRegisterIf (ns : NearState) (id : UInt64) (data : List UInt8) : NearState :=
  if id = u64Max then ns else ns.setRegister id.toNat data

/-- Insert/overwrite `key ↦ val` in storage. -/
def setStorage (ns : NearState) (key val : List UInt8) : NearState :=
  { ns with storage := fun k => if k = key then some val else ns.storage k }

/-- Remove `key` from storage. -/
def removeStorage (ns : NearState) (key : List UInt8) : NearState :=
  { ns with storage := fun k => if k = key then none else ns.storage k }

end NearState

/-- The NEAR `get_memory_or_register` input convention. For an input
`(ptr, len)` pair: when `len = u64Max`, `ptr` is a *register id* and the
bytes are taken from that register (`none` if the register is unset, which
the caller turns into a trap); otherwise it reads `len` bytes of linear
memory starting at `ptr`, returning `none` when the range exceeds guest
memory. Used uniformly by `storage_*` (keys/values) and `value_return`. -/
def getMemOrReg (st : Store NearState) (ptr len : UInt64) : Option (List UInt8) :=
  if len = u64Max then st.host.registers ptr.toNat
  else if ptr.toNat + len.toNat > st.mem.pages * 65536 then none
  else some (st.mem.readBytes ptr.toNat len.toNat)

end Wasm
