import CodeLib.Near.Env

/-!
# Proof-facing NEAR helpers

This module keeps relational proof APIs separate from the executable NEAR
host semantics in `Env.lean`. The contracts here are intentionally
definitionally tied to the reference `HostFn`s for now: they give Wasm proofs
a `HostSpec` surface and a satisfaction theorem, while finer relational
contracts can replace individual entries as proofs need more abstraction.
-/

namespace Wasm
namespace Near

/-! ## Host contracts -/

/-- Exact contract for a concrete host function. This is the conservative
starting point for proof-facing NEAR specs: it exposes a `HostSpec` interface
without weakening or rephrasing the executable semantics. -/
def exactHostContract (hf : HostFn NearState) : HostContract NearState :=
  fun st args res => res = hf.invoke st args

def inputContract : HostContract NearState := exactHostContract inputFn
def readRegisterContract : HostContract NearState := exactHostContract readRegisterFn
def registerLenContract : HostContract NearState := exactHostContract registerLenFn
def writeRegisterContract : HostContract NearState := exactHostContract writeRegisterFn
def valueReturnContract : HostContract NearState := exactHostContract valueReturnFn
def storageWriteContract : HostContract NearState := exactHostContract storageWriteFn
def storageReadContract : HostContract NearState := exactHostContract storageReadFn
def storageRemoveContract : HostContract NearState := exactHostContract storageRemoveFn
def storageHasKeyContract : HostContract NearState := exactHostContract storageHasKeyFn

/-! ## Relational host contracts

These contracts expose the proof-relevant pre/post relation for the NEAR
host categories currently exercised by examples. Trap messages stay
abstract, but successful calls specify the host and memory effects directly.
-/

def trapResult (st : Store NearState) (res : HostResult NearState) : Prop :=
  ∃ msg, res = .Trap st msg

def inputRelContract : HostContract NearState := fun st args res =>
  match args with
  | [.i64 regId] =>
    match checkedSetRegister? st regId st.host.context.input with
    | some st' => res = .Return [] st'
    | none     => trapResult st res
  | _ => trapResult st res

def readRegisterRelContract : HostContract NearState := fun st args res =>
  match args with
  | [.i64 regId, .i64 ptr] =>
    match st.host.registers regId.toNat with
    | none => trapResult st res
    | some data =>
      if ptr.toNat + data.length > memBytes st then
        trapResult st res
      else
        res = .Return [] { st with mem := st.mem.writeBytes ptr.toNat data }
  | _ => trapResult st res

def registerLenRelContract : HostContract NearState := fun st args res =>
  match args with
  | [.i64 regId] =>
    match st.host.registers regId.toNat with
    | none      => res = .Return [.i64 u64Max] st
    | some data => res = .Return [.i64 (UInt64.ofNat data.length)] st
  | _ => trapResult st res

def writeRegisterRelContract : HostContract NearState := fun st args res =>
  match args with
  | [.i64 regId, .i64 dataLen, .i64 dataPtr] =>
    if dataPtr.toNat + dataLen.toNat > memBytes st then
      trapResult st res
    else
      let data := st.mem.readBytes dataPtr.toNat dataLen.toNat
      res = writeRegisterResult "write_register" st regId data
  | _ => trapResult st res

def valueReturnRelContract : HostContract NearState := fun st args res =>
  match args with
  | [.i64 valLen, .i64 valPtr] =>
    match getMemOrReg st valPtr valLen with
    | some v =>
      if withinLimit st.host.config.maxReturnLen v.length then
        res = .Return [] { st with host := { st.host with returnData := some v } }
      else
        trapResult st res
    | none => trapResult st res
  | _ => trapResult st res

def contextRegisterRelContract (select : NearContext → List UInt8) :
    HostContract NearState := fun st args res =>
  match args with
  | [.i64 regId] =>
    match checkedSetRegister? st regId (select st.host.context) with
    | some st' => res = .Return [] st'
    | none     => trapResult st res
  | _ => trapResult st res

def accountIdRegisterRelContract (prohibitView : Bool)
    (select : NearContext → List UInt8) : HostContract NearState := fun st args res =>
  if prohibitView && st.host.context.isView then
    trapResult st res
  else
    match args with
    | [.i64 regId] =>
      let accountId := select st.host.context
      if st.host.config.validAccountId accountId then
        match checkedSetRegister? st regId accountId with
        | some st' => res = .Return [] st'
        | none     => trapResult st res
      else
        trapResult st res
    | _ => trapResult st res

def publicKeyRegisterRelContract (prohibitView : Bool)
    (select : NearContext → List UInt8) : HostContract NearState := fun st args res =>
  if prohibitView && st.host.context.isView then
    trapResult st res
  else
    match args with
    | [.i64 regId] =>
      let publicKey := select st.host.context
      if st.host.config.validPublicKey publicKey then
        match checkedSetRegister? st regId publicKey with
        | some st' => res = .Return [] st'
        | none     => trapResult st res
      else
        trapResult st res
    | _ => trapResult st res

def contextU64RelContract (prohibitView : Bool) (select : NearContext → UInt64) :
    HostContract NearState := fun st args res =>
  if prohibitView && st.host.context.isView then
    trapResult st res
  else
    match args with
    | [] => res = .Return [.i64 (select st.host.context)] st
    | _  => trapResult st res

def contextU128MemRelContract (prohibitView : Bool) (select : NearContext → Nat) :
    HostContract NearState := fun st args res =>
  if prohibitView && st.host.context.isView then
    trapResult st res
  else
    match args with
    | [.i64 ptr] =>
      if ptr.toNat + 16 > memBytes st then
        trapResult st res
      else
        res = .Return [] { st with mem := st.mem.writeBytes ptr.toNat (leU128Bytes (select st.host.context)) }
    | _ => trapResult st res

def digestRelContract (hash : NearState → List UInt8 → List UInt8) :
    HostContract NearState := fun st args res =>
  match args with
  | [.i64 valueLen, .i64 valuePtr, .i64 regId] =>
    match getMemOrReg st valuePtr valueLen with
    | some value =>
      match checkedSetRegister? st regId (hash st.host value) with
      | some st' => res = .Return [] st'
      | none     => trapResult st res
    | none => trapResult st res
  | _ => trapResult st res

def logRelContract : HostContract NearState := fun st args res =>
  match args with
  | [.i64 len, .i64 ptr] =>
    match getMemOrReg st ptr len with
    | some msg =>
      if withinLimit st.host.config.maxLogLen msg.length then
        if withinLimit st.host.config.maxNumberLogs (st.host.logs.length + 1) then
          res = .Return [] { st with host := { st.host with logs := st.host.logs ++ [msg] } }
        else
          trapResult st res
      else
        trapResult st res
    | none => trapResult st res
  | _ => trapResult st res

def storageWriteRelContract : HostContract NearState := fun st args res =>
  if st.host.context.isView then
    trapResult st res
  else
    match args with
    | [.i64 keyLen, .i64 keyPtr, .i64 valLen, .i64 valPtr, .i64 regId] =>
      match getMemOrReg st keyPtr keyLen, getMemOrReg st valPtr valLen with
      | some key, some val =>
        if withinLimit st.host.config.maxStorageKeyLen key.length then
          if withinLimit st.host.config.maxStorageValueLen val.length then
            match st.host.storage key with
            | some old =>
              match checkedSetRegister? st regId old with
              | some st' =>
                res = .Return [.i64 1]
                  { st' with host := (st'.host.setStorage key val).invalidateIterators }
              | none => trapResult st res
            | none =>
              res = .Return [.i64 0]
                { st with host := (st.host.setStorage key val).invalidateIterators }
          else
            trapResult st res
        else
          trapResult st res
      | _, _ => trapResult st res
    | _ => trapResult st res

def storageReadRelContract : HostContract NearState := fun st args res =>
  match args with
  | [.i64 keyLen, .i64 keyPtr, .i64 regId] =>
    match getMemOrReg st keyPtr keyLen with
    | some key =>
      if withinLimit st.host.config.maxStorageKeyLen key.length then
        match st.host.storage key with
        | some v =>
          match checkedSetRegister? st regId v with
          | some st' => res = .Return [.i64 1] st'
          | none     => trapResult st res
        | none => res = .Return [.i64 0] st
      else
        trapResult st res
    | none => trapResult st res
  | _ => trapResult st res

def storageRemoveRelContract : HostContract NearState := fun st args res =>
  if st.host.context.isView then
    trapResult st res
  else
    match args with
    | [.i64 keyLen, .i64 keyPtr, .i64 regId] =>
      match getMemOrReg st keyPtr keyLen with
      | some key =>
        if withinLimit st.host.config.maxStorageKeyLen key.length then
          match st.host.storage key with
          | some v =>
            match checkedSetRegister? st regId v with
            | some st' =>
              res = .Return [.i64 1]
                { st' with host := (st'.host.removeStorage key).invalidateIterators }
            | none => trapResult st res
          | none => res = .Return [.i64 0] st
        else
          trapResult st res
      | none => trapResult st res
    | _ => trapResult st res

def storageHasKeyRelContract : HostContract NearState := fun st args res =>
  match args with
  | [.i64 keyLen, .i64 keyPtr] =>
    match getMemOrReg st keyPtr keyLen with
    | some key =>
      if withinLimit st.host.config.maxStorageKeyLen key.length then
        res = .Return [.i64 (if (st.host.storage key).isSome then 1 else 0)] st
      else
        trapResult st res
    | none => trapResult st res
  | _ => trapResult st res

def promiseResultRelContract : HostContract NearState := fun st args res =>
  if st.host.context.isView then
    trapResult st res
  else
    match args with
    | [.i64 resultIdx, .i64 regId] =>
      match getPromiseResult? st.host.promiseResults resultIdx.toNat with
      | none => trapResult st res
      | some .notReady => res = .Return [.i64 0] st
      | some (.successful data) =>
        match checkedSetRegister? st regId data with
        | some st' => res = .Return [.i64 1] st'
        | none     => trapResult st res
      | some .failed => res = .Return [.i64 2] st
    | _ => trapResult st res

/-! ## Concrete host-function satisfaction theorems -/

theorem inputFn_satisfies_rel :
    ∀ st args, inputRelContract st args (inputFn.invoke st args) := by
  intro st args
  unfold inputRelContract inputFn writeRegisterResult trapResult
  repeat split
  all_goals simp_all

theorem readRegisterFn_satisfies_rel :
    ∀ st args, readRegisterRelContract st args (readRegisterFn.invoke st args) := by
  intro st args
  unfold readRegisterRelContract readRegisterFn trapResult
  repeat split
  all_goals simp_all

theorem registerLenFn_satisfies_rel :
    ∀ st args, registerLenRelContract st args (registerLenFn.invoke st args) := by
  intro st args
  unfold registerLenRelContract registerLenFn trapResult
  repeat split
  all_goals simp_all

theorem writeRegisterFn_satisfies_rel :
    ∀ st args, writeRegisterRelContract st args (writeRegisterFn.invoke st args) := by
  intro st args
  unfold writeRegisterRelContract writeRegisterFn trapResult
  repeat split
  all_goals simp_all [writeRegisterResult]

theorem valueReturnFn_satisfies_rel :
    ∀ st args, valueReturnRelContract st args (valueReturnFn.invoke st args) := by
  intro st args
  unfold valueReturnRelContract valueReturnFn checkDataLimit trapResult
  repeat split
  all_goals simp_all

theorem contextRegisterFn_satisfies_rel (name : String)
    (select : NearContext → List UInt8) :
    ∀ st args,
      contextRegisterRelContract select st args
        ((contextRegisterFn name select).invoke st args) := by
  intro st args
  unfold contextRegisterRelContract contextRegisterFn writeRegisterResult trapResult
  repeat split
  all_goals simp_all

theorem accountIdRegisterFn_satisfies_rel (name : String)
    (select : NearContext → List UInt8) :
    ∀ st args,
      accountIdRegisterRelContract false select st args
        ((accountIdRegisterFn name select).invoke st args) := by
  intro st args
  simp [accountIdRegisterRelContract, accountIdRegisterFn, checkAccountId,
    writeRegisterResult, trapResult]
  repeat split
  all_goals simp_all

theorem accountIdRegisterFn_satisfies_view_rel (name : String)
    (select : NearContext → List UInt8) :
    ∀ st args,
      accountIdRegisterRelContract true select st args
        ((disallowInView name (accountIdRegisterFn name select)).invoke st args) := by
  intro st args
  by_cases hView : st.host.context.isView
  · simp [accountIdRegisterRelContract, disallowInView, hView, trapResult]
  · simp [accountIdRegisterRelContract, disallowInView, hView]
    unfold accountIdRegisterFn checkAccountId writeRegisterResult trapResult
    repeat split
    all_goals simp_all

theorem publicKeyRegisterFn_satisfies_view_rel (name : String)
    (select : NearContext → List UInt8) :
    ∀ st args,
      publicKeyRegisterRelContract true select st args
        ((disallowInView name (publicKeyRegisterFn name select)).invoke st args) := by
  intro st args
  by_cases hView : st.host.context.isView
  · simp [publicKeyRegisterRelContract, disallowInView, hView, trapResult]
  · simp [publicKeyRegisterRelContract, disallowInView, hView]
    unfold publicKeyRegisterFn checkPublicKey writeRegisterResult trapResult
    repeat split
    all_goals simp_all

theorem contextU64Fn_satisfies_rel (name : String) (select : NearContext → UInt64) :
    ∀ st args,
      contextU64RelContract false select st args
        ((contextU64Fn name select).invoke st args) := by
  intro st args
  simp [contextU64RelContract, contextU64Fn, trapResult]
  repeat split
  all_goals simp_all

theorem contextU64Fn_satisfies_view_rel (name : String) (select : NearContext → UInt64) :
    ∀ st args,
      contextU64RelContract true select st args
        ((disallowInView name (contextU64Fn name select)).invoke st args) := by
  intro st args
  by_cases hView : st.host.context.isView
  · simp [contextU64RelContract, disallowInView, hView, trapResult]
  · simp [contextU64RelContract, disallowInView, hView]
    unfold contextU64Fn trapResult
    repeat split
    all_goals simp_all

@[simp] theorem leU128Bytes_length (n : Nat) :
    (leU128Bytes n).length = 16 := by
  simp [leU128Bytes]

theorem contextU128MemFn_satisfies_rel (name : String) (select : NearContext → Nat) :
    ∀ st args,
      contextU128MemRelContract false select st args
        ((contextU128MemFn name select).invoke st args) := by
  intro st args
  simp [contextU128MemRelContract, contextU128MemFn, writeU128, writeMemBytes, trapResult]
  repeat split
  all_goals simp_all
  all_goals try omega

theorem contextU128MemFn_satisfies_view_rel (name : String) (select : NearContext → Nat) :
    ∀ st args,
      contextU128MemRelContract true select st args
        ((disallowInView name (contextU128MemFn name select)).invoke st args) := by
  intro st args
  by_cases hView : st.host.context.isView
  · simp [contextU128MemRelContract, disallowInView, hView, trapResult]
  · simp [contextU128MemRelContract, disallowInView, hView, contextU128MemFn,
      writeU128, writeMemBytes, trapResult]
    repeat split
    all_goals simp_all
    all_goals try omega

theorem digestFn_satisfies_rel (name : String)
    (hash : NearState → List UInt8 → List UInt8) :
    ∀ st args,
      digestRelContract hash st args
        ((digestFn name hash).invoke st args) := by
  intro st args
  unfold digestRelContract digestFn writeRegisterResult trapResult
  repeat split
  all_goals simp_all

theorem logUtf8Fn_satisfies_rel :
    ∀ st args, logRelContract st args (logUtf8Fn.invoke st args) := by
  intro st args
  unfold logRelContract logUtf8Fn appendLogResult checkDataLimit trapResult
  repeat split
  all_goals simp_all

theorem logUtf16Fn_satisfies_rel :
    ∀ st args, logRelContract st args (logUtf16Fn.invoke st args) := by
  intro st args
  unfold logRelContract logUtf16Fn appendLogResult checkDataLimit trapResult
  repeat split
  all_goals simp_all

theorem storageWriteFn_satisfies_rel :
    ∀ st args, storageWriteRelContract st args (storageWriteFn.invoke st args) := by
  intro st args
  by_cases hView : st.host.context.isView
  · simp [storageWriteRelContract, storageWriteFn, disallowInView, hView, trapResult]
  · simp [storageWriteRelContract, storageWriteFn, disallowInView, hView, checkDataLimit]
    repeat split
    all_goals simp_all [trapResult]

theorem storageReadFn_satisfies_rel :
    ∀ st args, storageReadRelContract st args (storageReadFn.invoke st args) := by
  intro st args
  unfold storageReadRelContract storageReadFn checkDataLimit writeRegisterResult trapResult
  repeat split
  all_goals simp_all

theorem storageRemoveFn_satisfies_rel :
    ∀ st args, storageRemoveRelContract st args (storageRemoveFn.invoke st args) := by
  intro st args
  by_cases hView : st.host.context.isView
  · simp [storageRemoveRelContract, storageRemoveFn, disallowInView, hView, trapResult]
  · simp [storageRemoveRelContract, storageRemoveFn, disallowInView, hView, checkDataLimit]
    repeat split
    all_goals simp_all [trapResult]

theorem storageHasKeyFn_satisfies_rel :
    ∀ st args, storageHasKeyRelContract st args (storageHasKeyFn.invoke st args) := by
  intro st args
  unfold storageHasKeyRelContract storageHasKeyFn checkDataLimit trapResult
  repeat split
  all_goals simp_all

theorem promiseResultFn_satisfies_rel :
    ∀ st args, promiseResultRelContract st args (promiseResultFn.invoke st args) := by
  intro st args
  by_cases hView : st.host.context.isView
  · simp [promiseResultRelContract, promiseResultFn, disallowInView, hView, trapResult]
  · simp [promiseResultRelContract, promiseResultFn, disallowInView, hView,
      writeRegisterResult, trapResult]
    repeat split
    all_goals simp_all
    all_goals split <;> simp_all

/-- Canonical proof spec aligned with `nearImports`/`nearEnv`. -/
def nearSpec : HostSpec NearState :=
  { contracts := nearHostFns.map (fun p => exactHostContract p.snd) }

/-- Resolve one declared NEAR import to the proof contract for the concrete
reference host function selected by `resolveImport?`. -/
def resolveContract? (decl : ImportDecl) : Option (HostContract NearState) :=
  (resolveImport? decl).map exactHostContract

/-- Resolve a module's import subset/order into a proof spec aligned with the
positional host environment returned by `resolveImports?`. -/
def resolveContracts? : List ImportDecl → Option (HostSpec NearState)
  | [] => some { contracts := [] }
  | decl :: rest =>
    match resolveContract? decl, resolveContracts? rest with
    | some c, some spec => some { contracts := c :: spec.contracts }
    | _, _ => none

/-- Resolve a module's imports into a proof spec, returning `none` for unknown
NEAR names or signature mismatches. -/
def resolveSpec? (m : Module) : Option (HostSpec NearState) :=
  resolveContracts? m.imports

/-- The reference NEAR host environment satisfies the canonical proof spec for
any module whose imports are exactly `nearImports`. Hand-built examples can use
this directly; real compiled modules resolved through `resolveEnv?` will need a
subset/order variant. -/
theorem nearEnv_satisfies_canonical (m : Module) (himports : m.imports = nearImports) :
    nearEnv.Satisfies m nearSpec := by
  intro i hi
  have hiFns : i < nearHostFns.length := by
    rw [himports, nearImports] at hi
    simpa using hi
  let p := nearHostFns[i]
  refine ⟨p.snd, exactHostContract p.snd, ?_, ?_, ?_⟩
  · simp [nearEnv, p, hiFns]
  · simp [nearSpec, p, hiFns]
  · intro st args
    rfl

/-! ## Memory framing -/

@[simp] theorem readBytes_length (m : Mem) (off len : Nat) :
    (m.readBytes off len).length = len := by
  simp [Mem.readBytes]

@[simp] theorem writeBytes_pages (m : Mem) (off : Nat) (data : List UInt8) :
    (m.writeBytes off data).pages = m.pages := rfl

@[simp] theorem writeBytes_byte_in (m : Mem) (off i : Nat) (data : List UInt8)
    (h : i < data.length) :
    (m.writeBytes off data).bytes (off + i) = data[i] := by
  simp [Mem.writeBytes, h]

@[simp] theorem writeBytes_byte_before (m : Mem) (off i : Nat) (data : List UInt8)
    (h : i < off) :
    (m.writeBytes off data).bytes i = m.bytes i := by
  simp [Mem.writeBytes]
  omega

@[simp] theorem writeBytes_byte_after (m : Mem) (off i : Nat) (data : List UInt8)
    (h : off + data.length ≤ i) :
    (m.writeBytes off data).bytes i = m.bytes i := by
  simp [Mem.writeBytes]
  omega

@[simp] theorem read32_writeBytes_four (m : Mem) (a : UInt32) (b0 b1 b2 b3 : UInt8) :
    (m.writeBytes a.toNat [b0, b1, b2, b3]).read32 a =
      b0.toUInt32 ||| (b1.toUInt32 <<< 8) ||| (b2.toUInt32 <<< 16) ||| (b3.toUInt32 <<< 24) := by
  simp [Mem.read32, Mem.writeBytes]

theorem readBytes_writeBytes_slice (m : Mem) (off start len : Nat) (data : List UInt8)
    (h : start + len ≤ data.length) :
    (m.writeBytes off data).readBytes (off + start) len = (data.drop start).take len := by
  apply List.ext_getElem
  · simp [Mem.readBytes]
    omega
  · intro i hi1 _hi2
    have hi : i < len := by simpa [Mem.readBytes] using hi1
    have hge : off ≤ off + start + i := by omega
    have hlt : off + start + i < off + data.length := by omega
    have hidx : off + start + i - off = start + i := by omega
    simp [Mem.readBytes, Mem.writeBytes, hge, hlt, hidx]

theorem getMemOrReg_mem (st : Store NearState) (ptr len : UInt64)
    (hLen : len ≠ u64Max) (hBound : ptr.toNat + len.toNat ≤ memBytes st) :
    getMemOrReg st ptr len = some (st.mem.readBytes ptr.toNat len.toNat) := by
  unfold getMemOrReg
  have hNot : ¬ ptr.toNat + len.toNat > st.mem.pages * 65536 := by
    simpa [memBytes, Nat.not_lt] using hBound
  simp [hLen, hNot]

theorem storageWriteFn_invoke_present (st : Store NearState) (key val old : List UInt8)
    (keyLen keyPtr valLen valPtr regId : UInt64) (stReg : Store NearState)
    (hView : st.host.context.isView = false)
    (hKeyGet : getMemOrReg st keyPtr keyLen = some key)
    (hValGet : getMemOrReg st valPtr valLen = some val)
    (hKeyLimit : withinLimit st.host.config.maxStorageKeyLen key.length = true)
    (hValLimit : withinLimit st.host.config.maxStorageValueLen val.length = true)
    (hOld : st.host.storage key = some old)
    (hReg : checkedSetRegister? st regId old = some stReg) :
    storageWriteFn.invoke st [.i64 keyLen, .i64 keyPtr, .i64 valLen, .i64 valPtr, .i64 regId] =
      .Return [.i64 1] { stReg with host := (stReg.host.setStorage key val).invalidateIterators } := by
  simp [storageWriteFn, disallowInView, hView, hKeyGet, hValGet, checkDataLimit,
    hKeyLimit, hValLimit, hOld, hReg]

theorem storageWriteFn_invoke_absent (st : Store NearState) (key val : List UInt8)
    (keyLen keyPtr valLen valPtr regId : UInt64)
    (hView : st.host.context.isView = false)
    (hKeyGet : getMemOrReg st keyPtr keyLen = some key)
    (hValGet : getMemOrReg st valPtr valLen = some val)
    (hKeyLimit : withinLimit st.host.config.maxStorageKeyLen key.length = true)
    (hValLimit : withinLimit st.host.config.maxStorageValueLen val.length = true)
    (hOld : st.host.storage key = none) :
    storageWriteFn.invoke st [.i64 keyLen, .i64 keyPtr, .i64 valLen, .i64 valPtr, .i64 regId] =
      .Return [.i64 0] { st with host := (st.host.setStorage key val).invalidateIterators } := by
  simp [storageWriteFn, disallowInView, hView, hKeyGet, hValGet, checkDataLimit,
    hKeyLimit, hValLimit, hOld]

/-! ## NEAR state projection lemmas -/

@[simp] theorem setStorage_same (ns : NearState) (key val : List UInt8) :
    (ns.setStorage key val).storage key = some val := by
  simp [NearState.setStorage]

@[simp] theorem setStorage_other (ns : NearState) {key other val : List UInt8}
    (h : other ≠ key) :
    (ns.setStorage key val).storage other = ns.storage other := by
  simp [NearState.setStorage, h]

@[simp] theorem removeStorage_same (ns : NearState) (key : List UInt8) :
    (ns.removeStorage key).storage key = none := by
  simp [NearState.removeStorage]

@[simp] theorem removeStorage_other (ns : NearState) {key other : List UInt8}
    (h : other ≠ key) :
    (ns.removeStorage key).storage other = ns.storage other := by
  simp [NearState.removeStorage, h]

end Near
end Wasm
