import CodeLib.Near.State

/-!
# NEAR host-function registry (`nearEnv`)

A `HostEnv NearState` modelling the NEAR Protocol host functions a Wasm
contract imports from module `"env"`. Semantics transcribed from nearcore
(`runtime/near-vm-runner/src/logic/{logic,vmstate}.rs`).

`HostEnv.funcs` is **positional**: index `i` resolves `call i` for
`i < imports.length`. So the env and a module's `imports` must agree on
order. `nearHostFns : List (ImportDecl × HostFn NearState)` is the source
of truth. Hand-built examples can use `nearImports`/`nearEnv` directly;
real compiled modules should call `resolveEnv?` so their declared subset
of imports is resolved by name/signature into the right positional order.

## Incremental strategy

Implemented tiers have real semantics; un-modelled crypto/promise entries
are **trapping stubs** (`unsupported`). A contract that calls an
un-modelled host function therefore *fails to verify loudly* (a trap the
proof can't discharge) rather than silently misbehaving — implement a tier
when a real contract needs it.

Gas is intentionally unmodelled: functional correctness ignores it, and
the interpreter's `fuel` already gives termination. Promises are deferred.
-/

namespace Wasm
namespace Near

/-- Byte capacity of `st`'s linear memory. -/
@[inline] def memBytes (st : Store NearState) : Nat := st.mem.pages * 65536

/-- Little-endian byte encoding of a NEAR `u128` value. Values above
`2^128 - 1` are truncated modulo `2^128`, matching fixed-width writes. -/
def leU128Bytes (n : Nat) : List UInt8 :=
  (List.range 16).map (fun i => UInt8.ofNat (n / 2 ^ (8 * i) % 256))

def leBytesToNat : List UInt8 → Nat
  | [] => 0
  | b :: bs => b.toNat + 256 * leBytesToNat bs

def readMemNat (st : Store NearState) (ptr : UInt64) (len : Nat) : Option Nat :=
  if ptr.toNat + len > memBytes st then
    none
  else
    some (leBytesToNat (st.mem.readBytes ptr.toNat len))

def readU64Mem (st : Store NearState) (ptr : UInt64) : Option Nat :=
  readMemNat st ptr 8

def readU128Mem (st : Store NearState) (ptr : UInt64) : Option Nat :=
  readMemNat st ptr 16

/-- Write bytes into guest memory, trapping when the range is out of bounds. -/
def writeMemBytes (name : String) (st : Store NearState) (ptr : UInt64)
    (data : List UInt8) : HostResult NearState :=
  if ptr.toNat + data.length > memBytes st then
    .Trap st s!"{name}: out of bounds"
  else
    .Return [] { st with mem := st.mem.writeBytes ptr.toNat data }

/-- Write a `u128` into guest memory as 16 little-endian bytes. -/
def writeU128 (name : String) (st : Store NearState) (ptr : UInt64)
    (n : Nat) : HostResult NearState :=
  writeMemBytes name st ptr (leU128Bytes n)

def withinLimit (limit : Option Nat) (n : Nat) : Bool :=
  match limit with
  | none => true
  | some max => decide (n ≤ max)

def checkedSetRegister? (st : Store NearState) (regId : UInt64)
    (data : List UInt8) : Option (Store NearState) :=
  if regId = u64Max then
    some st
  else if withinLimit st.host.config.maxRegisterLen data.length then
    some { st with host := st.host.setRegister regId.toNat data }
  else
    none

def writeRegisterResult (name : String) (st : Store NearState) (regId : UInt64)
    (data : List UInt8) (results : List Value := []) : HostResult NearState :=
  match checkedSetRegister? st regId data with
  | some st' => .Return results st'
  | none     => .Trap st s!"{name}: register size exceeded"

def checkDataLimit (name label : String) (limit : Option Nat) (n : Nat)
    (st : Store NearState) (next : Unit → HostResult NearState) : HostResult NearState :=
  if withinLimit limit n then
    next ()
  else
    .Trap st s!"{name}: {label} size exceeded"

def checkAccountId (name : String) (st : Store NearState) (accountId : List UInt8)
    (next : Unit → HostResult NearState) : HostResult NearState :=
  if st.host.config.validAccountId accountId then
    next ()
  else
    .Trap st s!"{name}: invalid account id"

def checkPublicKey (name : String) (st : Store NearState) (publicKey : List UInt8)
    (next : Unit → HostResult NearState) : HostResult NearState :=
  if st.host.config.validPublicKey publicKey then
    next ()
  else
    .Trap st s!"{name}: invalid public key"

/-- Wrap a host function whose NEAR nearcore semantics return
`ProhibitedInView` during view execution. The wrapped function remains
unchanged for normal calls, keeping direct semantic tests representative of
the registry entry. -/
def disallowInView (name : String) (hf : HostFn NearState) : HostFn NearState :=
  { params := hf.params
    results := hf.results
    invoke := fun st args =>
      if st.host.context.isView then
        .Trap st s!"{name}: ProhibitedInView"
      else
        hf.invoke st args }

/-- Append a log payload. The reference model stores log data as raw bytes:
`log_utf8`/`log_utf16` names describe the guest ABI, but UTF decoding is not
part of functional correctness here. Optional config limits model the
nearcore-style log length/count traps when proofs opt into them. -/
def appendLogResult (name : String) (st : Store NearState)
    (msg : List UInt8) : HostResult NearState :=
  checkDataLimit name "log" st.host.config.maxLogLen msg.length st <| fun _ =>
  checkDataLimit name "log count" st.host.config.maxNumberLogs (st.host.logs.length + 1) st <| fun _ =>
    .Return [] { st with host := { st.host with logs := st.host.logs ++ [msg] } }

def getPromise? : List NearPromise → Nat → Option NearPromise
  | [], _ => none
  | p :: _, 0 => some p
  | _ :: ps, n + 1 => getPromise? ps n

def setPromise? : List NearPromise → Nat → NearPromise → Option (List NearPromise)
  | [], _, _ => none
  | _ :: ps, 0, p => some (p :: ps)
  | q :: ps, n + 1, p => (setPromise? ps n p).map (fun ps' => q :: ps')

def nextPromiseIdx (st : Store NearState) : UInt64 :=
  UInt64.ofNat st.host.promises.length

def appendPromise (st : Store NearState) (p : NearPromise) : Store NearState :=
  { st with host := { st.host with promises := st.host.promises ++ [p] } }

def promiseIndexValid (st : Store NearState) (idx : Nat) : Bool :=
  (getPromise? st.host.promises idx).isSome

def promiseDepsValid (st : Store NearState) (deps : List Nat) : Bool :=
  deps.all (promiseIndexValid st)

def appendPromiseAction? (ps : List NearPromise) (idx : Nat)
    (action : PromiseAction) : Option (List NearPromise) :=
  match getPromise? ps idx with
  | some (.batch accountId actions) =>
    setPromise? ps idx (.batch accountId (actions ++ [action]))
  | some (.callback base accountId actions) =>
    setPromise? ps idx (.callback base accountId (actions ++ [action]))
  | _ => none

def appendPromiseActionResult (name : String) (st : Store NearState)
    (idx : UInt64) (action : PromiseAction) : HostResult NearState :=
  match appendPromiseAction? st.host.promises idx.toNat action with
  | some promises => .Return [] { st with host := { st.host with promises } }
  | none          => .Trap st s!"{name}: invalid promise index"

def promiseYieldDataIdExists (dataId : List UInt8) : List NearPromise → Bool
  | [] => false
  | (.yielded _ _ _ _ existing) :: ps => existing == dataId || promiseYieldDataIdExists dataId ps
  | _ :: ps => promiseYieldDataIdExists dataId ps

def readU64Array (st : Store NearState) (ptr : UInt64) : Nat → Option (List Nat)
  | 0 => some []
  | n + 1 =>
    match readU64Mem st (UInt64.ofNat (ptr.toNat + 8 * n)), readU64Array st ptr n with
    | some x, some xs => some (xs ++ [x])
    | _, _ => none

def createBatchPromiseResult (name : String) (st : Store NearState)
    (accountId : List UInt8) : HostResult NearState :=
  checkAccountId name st accountId <| fun _ =>
    let idx := nextPromiseIdx st
    .Return [.i64 idx] (appendPromise st (.batch accountId []))

def createCallbackPromiseResult (name : String) (st : Store NearState)
    (baseIdx : UInt64) (accountId : List UInt8) : HostResult NearState :=
  if promiseIndexValid st baseIdx.toNat then
    checkAccountId name st accountId <| fun _ =>
      let idx := nextPromiseIdx st
      .Return [.i64 idx] (appendPromise st (.callback baseIdx.toNat accountId []))
  else
    .Trap st s!"{name}: invalid promise index"

def readFunctionCallAction? (st : Store NearState)
    (methodNameLen methodNamePtr argsLen argsPtr amountPtr gas : UInt64) :
    Option PromiseAction := do
  let methodName ← getMemOrReg st methodNamePtr methodNameLen
  let args ← getMemOrReg st argsPtr argsLen
  let amount ← readU128Mem st amountPtr
  some (.functionCall methodName args amount gas)

def promiseCreateFn : HostFn NearState :=
  disallowInView "promise_create" <|
  { params := [.i64, .i64, .i64, .i64, .i64, .i64, .i64, .i64], results := [.i64]
    invoke := fun st args => match args with
      | [.i64 accountIdLen, .i64 accountIdPtr, .i64 methodNameLen, .i64 methodNamePtr,
          .i64 argsLen, .i64 argsPtr, .i64 amountPtr, .i64 gas] =>
        match getMemOrReg st accountIdPtr accountIdLen,
            readFunctionCallAction? st methodNameLen methodNamePtr argsLen argsPtr amountPtr gas with
        | some accountId, some action =>
          checkAccountId "promise_create" st accountId <| fun _ =>
            let idx := nextPromiseIdx st
            .Return [.i64 idx] (appendPromise st (.batch accountId [action]))
        | _, _ => .Trap st "promise_create: invalid input"
      | _ => .Trap st "promise_create: bad args" }

def promiseThenFn : HostFn NearState :=
  disallowInView "promise_then" <|
  { params := [.i64, .i64, .i64, .i64, .i64, .i64, .i64, .i64, .i64], results := [.i64]
    invoke := fun st args => match args with
      | [.i64 baseIdx, .i64 accountIdLen, .i64 accountIdPtr, .i64 methodNameLen, .i64 methodNamePtr,
          .i64 argsLen, .i64 argsPtr, .i64 amountPtr, .i64 gas] =>
        match getMemOrReg st accountIdPtr accountIdLen,
            readFunctionCallAction? st methodNameLen methodNamePtr argsLen argsPtr amountPtr gas with
        | some accountId, some action =>
          if promiseIndexValid st baseIdx.toNat then
            checkAccountId "promise_then" st accountId <| fun _ =>
              let idx := nextPromiseIdx st
              .Return [.i64 idx] (appendPromise st (.callback baseIdx.toNat accountId [action]))
          else
            .Trap st "promise_then: invalid promise index"
        | _, _ => .Trap st "promise_then: invalid input"
      | _ => .Trap st "promise_then: bad args" }

def promiseAndFn : HostFn NearState :=
  disallowInView "promise_and" <|
  { params := [.i64, .i64], results := [.i64]
    invoke := fun st args => match args with
      | [.i64 promiseIdxPtr, .i64 promiseIdxCount] =>
        match readU64Array st promiseIdxPtr promiseIdxCount.toNat with
        | some deps =>
          if promiseDepsValid st deps then
            let idx := nextPromiseIdx st
            .Return [.i64 idx] (appendPromise st (.and deps))
          else
            .Trap st "promise_and: invalid promise index"
        | none => .Trap st "promise_and: invalid memory"
      | _ => .Trap st "promise_and: bad args" }

def promiseBatchCreateFn : HostFn NearState :=
  disallowInView "promise_batch_create" <|
  { params := [.i64, .i64], results := [.i64]
    invoke := fun st args => match args with
      | [.i64 accountIdLen, .i64 accountIdPtr] =>
        match getMemOrReg st accountIdPtr accountIdLen with
        | some accountId => createBatchPromiseResult "promise_batch_create" st accountId
        | none => .Trap st "promise_batch_create: invalid account id"
      | _ => .Trap st "promise_batch_create: bad args" }

def promiseBatchThenFn : HostFn NearState :=
  disallowInView "promise_batch_then" <|
  { params := [.i64, .i64, .i64], results := [.i64]
    invoke := fun st args => match args with
      | [.i64 baseIdx, .i64 accountIdLen, .i64 accountIdPtr] =>
        match getMemOrReg st accountIdPtr accountIdLen with
        | some accountId => createCallbackPromiseResult "promise_batch_then" st baseIdx accountId
        | none => .Trap st "promise_batch_then: invalid account id"
      | _ => .Trap st "promise_batch_then: bad args" }

def promiseBatchActionCreateAccountFn : HostFn NearState :=
  disallowInView "promise_batch_action_create_account" <|
  { params := [.i64], results := []
    invoke := fun st args => match args with
      | [.i64 promiseIdx] =>
        appendPromiseActionResult "promise_batch_action_create_account" st promiseIdx .createAccount
      | _ => .Trap st "promise_batch_action_create_account: bad args" }

def promiseBatchActionDeployContractFn : HostFn NearState :=
  disallowInView "promise_batch_action_deploy_contract" <|
  { params := [.i64, .i64, .i64], results := []
    invoke := fun st args => match args with
      | [.i64 promiseIdx, .i64 codeLen, .i64 codePtr] =>
        match getMemOrReg st codePtr codeLen with
        | some code =>
          appendPromiseActionResult "promise_batch_action_deploy_contract" st promiseIdx (.deployContract code)
        | none => .Trap st "promise_batch_action_deploy_contract: invalid code"
      | _ => .Trap st "promise_batch_action_deploy_contract: bad args" }

def promiseBatchActionFunctionCallFn : HostFn NearState :=
  disallowInView "promise_batch_action_function_call" <|
  { params := [.i64, .i64, .i64, .i64, .i64, .i64, .i64], results := []
    invoke := fun st args => match args with
      | [.i64 promiseIdx, .i64 methodNameLen, .i64 methodNamePtr, .i64 argsLen,
          .i64 argsPtr, .i64 amountPtr, .i64 gas] =>
        match readFunctionCallAction? st methodNameLen methodNamePtr argsLen argsPtr amountPtr gas with
        | some action =>
          appendPromiseActionResult "promise_batch_action_function_call" st promiseIdx action
        | none => .Trap st "promise_batch_action_function_call: invalid input"
      | _ => .Trap st "promise_batch_action_function_call: bad args" }

def promiseBatchActionTransferFn : HostFn NearState :=
  disallowInView "promise_batch_action_transfer" <|
  { params := [.i64, .i64], results := []
    invoke := fun st args => match args with
      | [.i64 promiseIdx, .i64 amountPtr] =>
        match readU128Mem st amountPtr with
        | some amount =>
          appendPromiseActionResult "promise_batch_action_transfer" st promiseIdx (.transfer amount)
        | none => .Trap st "promise_batch_action_transfer: invalid amount"
      | _ => .Trap st "promise_batch_action_transfer: bad args" }

def promiseBatchActionStakeFn : HostFn NearState :=
  disallowInView "promise_batch_action_stake" <|
  { params := [.i64, .i64, .i64, .i64], results := []
    invoke := fun st args => match args with
      | [.i64 promiseIdx, .i64 amountPtr, .i64 pkLen, .i64 pkPtr] =>
        match readU128Mem st amountPtr, getMemOrReg st pkPtr pkLen with
        | some amount, some pk =>
          checkPublicKey "promise_batch_action_stake" st pk <| fun _ =>
            appendPromiseActionResult "promise_batch_action_stake" st promiseIdx (.stake amount pk)
        | _, _ => .Trap st "promise_batch_action_stake: invalid input"
      | _ => .Trap st "promise_batch_action_stake: bad args" }

def promiseBatchActionAddKeyWithFullAccessFn : HostFn NearState :=
  disallowInView "promise_batch_action_add_key_with_full_access" <|
  { params := [.i64, .i64, .i64, .i64], results := []
    invoke := fun st args => match args with
      | [.i64 promiseIdx, .i64 pkLen, .i64 pkPtr, .i64 nonce] =>
        match getMemOrReg st pkPtr pkLen with
        | some pk =>
          checkPublicKey "promise_batch_action_add_key_with_full_access" st pk <| fun _ =>
            appendPromiseActionResult "promise_batch_action_add_key_with_full_access" st promiseIdx
              (.addKey pk nonce .fullAccess)
        | none => .Trap st "promise_batch_action_add_key_with_full_access: invalid public key"
      | _ => .Trap st "promise_batch_action_add_key_with_full_access: bad args" }

def promiseBatchActionAddKeyWithFunctionCallFn : HostFn NearState :=
  disallowInView "promise_batch_action_add_key_with_function_call" <|
  { params := [.i64, .i64, .i64, .i64, .i64, .i64, .i64, .i64, .i64], results := []
    invoke := fun st args => match args with
      | [.i64 promiseIdx, .i64 pkLen, .i64 pkPtr, .i64 nonce, .i64 allowancePtr,
          .i64 receiverLen, .i64 receiverPtr, .i64 methodsLen, .i64 methodsPtr] =>
        match getMemOrReg st pkPtr pkLen, readU128Mem st allowancePtr,
            getMemOrReg st receiverPtr receiverLen, getMemOrReg st methodsPtr methodsLen with
        | some pk, some allowance, some receiverId, some methodNames =>
          checkPublicKey "promise_batch_action_add_key_with_function_call" st pk <| fun _ =>
          checkAccountId "promise_batch_action_add_key_with_function_call" st receiverId <| fun _ =>
            appendPromiseActionResult "promise_batch_action_add_key_with_function_call" st promiseIdx
              (.addKey pk nonce (.functionCall (some allowance) receiverId methodNames))
        | _, _, _, _ => .Trap st "promise_batch_action_add_key_with_function_call: invalid input"
      | _ => .Trap st "promise_batch_action_add_key_with_function_call: bad args" }

def promiseBatchActionDeleteKeyFn : HostFn NearState :=
  disallowInView "promise_batch_action_delete_key" <|
  { params := [.i64, .i64, .i64], results := []
    invoke := fun st args => match args with
      | [.i64 promiseIdx, .i64 pkLen, .i64 pkPtr] =>
        match getMemOrReg st pkPtr pkLen with
        | some pk =>
          checkPublicKey "promise_batch_action_delete_key" st pk <| fun _ =>
            appendPromiseActionResult "promise_batch_action_delete_key" st promiseIdx (.deleteKey pk)
        | none => .Trap st "promise_batch_action_delete_key: invalid public key"
      | _ => .Trap st "promise_batch_action_delete_key: bad args" }

def promiseBatchActionDeleteAccountFn : HostFn NearState :=
  disallowInView "promise_batch_action_delete_account" <|
  { params := [.i64, .i64, .i64], results := []
    invoke := fun st args => match args with
      | [.i64 promiseIdx, .i64 beneficiaryLen, .i64 beneficiaryPtr] =>
        match getMemOrReg st beneficiaryPtr beneficiaryLen with
        | some beneficiaryId =>
          checkAccountId "promise_batch_action_delete_account" st beneficiaryId <| fun _ =>
            appendPromiseActionResult "promise_batch_action_delete_account" st promiseIdx
              (.deleteAccount beneficiaryId)
        | none => .Trap st "promise_batch_action_delete_account: invalid beneficiary"
      | _ => .Trap st "promise_batch_action_delete_account: bad args" }

def promiseYieldCreateFn : HostFn NearState :=
  disallowInView "promise_yield_create" <|
  { params := [.i64, .i64, .i64, .i64, .i64, .i64, .i64], results := [.i64]
    invoke := fun st args => match args with
      | [.i64 methodNameLen, .i64 methodNamePtr, .i64 argsLen, .i64 argsPtr,
          .i64 gas, .i64 weight, .i64 regId] =>
        match getMemOrReg st methodNamePtr methodNameLen, getMemOrReg st argsPtr argsLen with
        | some methodName, some callArgs =>
          let dataId := st.host.yieldCreateToken methodName callArgs gas weight
          match checkedSetRegister? st regId dataId with
          | some st' =>
            let idx := nextPromiseIdx st'
            .Return [.i64 idx] (appendPromise st' (.yielded methodName callArgs gas weight dataId))
          | none => .Trap st "promise_yield_create: register size exceeded"
        | _, _ => .Trap st "promise_yield_create: invalid input"
      | _ => .Trap st "promise_yield_create: bad args" }

def promiseYieldResumeFn : HostFn NearState :=
  disallowInView "promise_yield_resume" <|
  { params := [.i64, .i64, .i64, .i64], results := [.i64]
    invoke := fun st args => match args with
      | [.i64 dataIdLen, .i64 dataIdPtr, .i64 payloadLen, .i64 payloadPtr] =>
        match getMemOrReg st dataIdPtr dataIdLen, getMemOrReg st payloadPtr payloadLen with
        | some dataId, some payload =>
          if promiseYieldDataIdExists dataId st.host.promises then
            .Return [.i64 1]
              { st with host := { st.host with yieldResumes := st.host.yieldResumes ++ [(dataId, payload)] } }
          else
            .Return [.i64 0] st
        | _, _ => .Trap st "promise_yield_resume: invalid input"
      | _ => .Trap st "promise_yield_resume: bad args" }

def contextRegisterFn (name : String) (select : NearContext → List UInt8) : HostFn NearState :=
  { params := [.i64], results := []
    invoke := fun st args => match args with
      | [.i64 regId] =>
        writeRegisterResult name st regId (select st.host.context)
      | _ => .Trap st s!"{name}: bad args" }

def accountIdRegisterFn (name : String) (select : NearContext → List UInt8) : HostFn NearState :=
  { params := [.i64], results := []
    invoke := fun st args => match args with
      | [.i64 regId] =>
        let accountId := select st.host.context
        checkAccountId name st accountId <| fun _ =>
          writeRegisterResult name st regId accountId
      | _ => .Trap st s!"{name}: bad args" }

def publicKeyRegisterFn (name : String) (select : NearContext → List UInt8) : HostFn NearState :=
  { params := [.i64], results := []
    invoke := fun st args => match args with
      | [.i64 regId] =>
        let publicKey := select st.host.context
        checkPublicKey name st publicKey <| fun _ =>
          writeRegisterResult name st regId publicKey
      | _ => .Trap st s!"{name}: bad args" }

def contextU64Fn (name : String) (select : NearContext → UInt64) : HostFn NearState :=
  { params := [], results := [.i64]
    invoke := fun st args => match args with
      | [] => .Return [.i64 (select st.host.context)] st
      | _  => .Trap st s!"{name}: bad args" }

def contextU128MemFn (name : String) (select : NearContext → Nat) : HostFn NearState :=
  { params := [.i64], results := []
    invoke := fun st args => match args with
      | [.i64 ptr] => writeU128 name st ptr (select st.host.context)
      | _          => .Trap st s!"{name}: bad args" }

/-! ## Trapping stub for un-modelled host functions -/

/-- A host function that is declared (so import resolution succeeds) but
not yet modelled: every call traps. Keeps un-modelled functionality from
silently passing verification. -/
def unsupported (name : String) (params results : List ValueType) : HostFn NearState :=
  { params, results, invoke := fun st _ => .Trap st s!"unsupported NEAR host function: {name}" }

/-! ## Tier 0 — registers and I/O -/

/-- `input(register_id)`: write the raw call input into `register_id`. -/
def inputFn : HostFn NearState :=
  { params := [.i64], results := []
    invoke := fun st args => match args with
      | [.i64 regId] =>
        writeRegisterResult "input" st regId st.host.context.input
      | _ => .Trap st "input: bad args" }

/-- `read_register(register_id, ptr)`: copy the whole register into linear
memory at `ptr`. Traps if the register is unset or the write is OOB. -/
def readRegisterFn : HostFn NearState :=
  { params := [.i64, .i64], results := []
    invoke := fun st args => match args with
      | [.i64 regId, .i64 ptr] =>
        match st.host.registers regId.toNat with
        | none => .Trap st "read_register: invalid register"
        | some data =>
          if ptr.toNat + data.length > memBytes st then
            .Trap st "read_register: out of bounds"
          else
            .Return [] { st with mem := st.mem.writeBytes ptr.toNat data }
      | _ => .Trap st "read_register: bad args" }

/-- `register_len(register_id) -> u64`: byte length of the register, or
`u64Max` if the register is unset. -/
def registerLenFn : HostFn NearState :=
  { params := [.i64], results := [.i64]
    invoke := fun st args => match args with
      | [.i64 regId] =>
        match st.host.registers regId.toNat with
        | none      => .Return [.i64 u64Max] st
        | some data => .Return [.i64 (UInt64.ofNat data.length)] st
      | _ => .Trap st "register_len: bad args" }

/-- `write_register(register_id, data_len, data_ptr)`: store
`data_len` bytes of linear memory into `register_id`. Reads memory
directly (no `u64Max` sentinel here). -/
def writeRegisterFn : HostFn NearState :=
  { params := [.i64, .i64, .i64], results := []
    invoke := fun st args => match args with
      | [.i64 regId, .i64 dataLen, .i64 dataPtr] =>
        if dataPtr.toNat + dataLen.toNat > memBytes st then
          .Trap st "write_register: out of bounds"
        else
          let data := st.mem.readBytes dataPtr.toNat dataLen.toNat
          writeRegisterResult "write_register" st regId data
      | _ => .Trap st "write_register: bad args" }

/-- `value_return(value_len, value_ptr)`: set the call's return data, read
through the memory-or-register convention. -/
def valueReturnFn : HostFn NearState :=
  { params := [.i64, .i64], results := []
    invoke := fun st args => match args with
      | [.i64 valLen, .i64 valPtr] =>
        match getMemOrReg st valPtr valLen with
        | none   => .Trap st "value_return: invalid register"
        | some v =>
          checkDataLimit "value_return" "return" st.host.config.maxReturnLen v.length st <|
            fun _ => .Return [] { st with host := { st.host with returnData := some v } }
      | _ => .Trap st "value_return: bad args" }

/-! ## Context and economics -/

def currentAccountIdFn : HostFn NearState :=
  accountIdRegisterFn "current_account_id" (·.currentAccountId)

def predecessorAccountIdFn : HostFn NearState :=
  disallowInView "predecessor_account_id" <|
    accountIdRegisterFn "predecessor_account_id" (·.predecessorAccountId)

def signerAccountIdFn : HostFn NearState :=
  disallowInView "signer_account_id" <|
    accountIdRegisterFn "signer_account_id" (·.signerAccountId)

def signerAccountPkFn : HostFn NearState :=
  disallowInView "signer_account_pk" <|
    publicKeyRegisterFn "signer_account_pk" (·.signerAccountPk)

def blockIndexFn : HostFn NearState :=
  contextU64Fn "block_index" (·.blockIndex)

def blockTimestampFn : HostFn NearState :=
  contextU64Fn "block_timestamp" (·.blockTimestamp)

def epochHeightFn : HostFn NearState :=
  contextU64Fn "epoch_height" (·.epochHeight)

def storageUsageFn : HostFn NearState :=
  contextU64Fn "storage_usage" (·.storageUsage)

def accountBalanceFn : HostFn NearState :=
  contextU128MemFn "account_balance" (·.accountBalance)

def accountLockedBalanceFn : HostFn NearState :=
  contextU128MemFn "account_locked_balance" (·.accountLockedBalance)

def attachedDepositFn : HostFn NearState :=
  disallowInView "attached_deposit" <|
    contextU128MemFn "attached_deposit" (·.attachedDeposit)

def prepaidGasFn : HostFn NearState :=
  disallowInView "prepaid_gas" <|
    contextU64Fn "prepaid_gas" (·.prepaidGas)

def usedGasFn : HostFn NearState :=
  disallowInView "used_gas" <|
    contextU64Fn "used_gas" (·.usedGas)

def validatorStakeFn : HostFn NearState :=
  { params := [.i64, .i64, .i64], results := []
    invoke := fun st args => match args with
      | [.i64 accountIdLen, .i64 accountIdPtr, .i64 stakePtr] =>
        match getMemOrReg st accountIdPtr accountIdLen with
        | none => .Trap st "validator_stake: invalid account id"
        | some accountId =>
          checkAccountId "validator_stake" st accountId <| fun _ =>
            writeU128 "validator_stake" st stakePtr (st.host.context.validatorStake accountId)
      | _ => .Trap st "validator_stake: bad args" }

def validatorTotalStakeFn : HostFn NearState :=
  contextU128MemFn "validator_total_stake" (·.validatorTotalStake)

/-! ## Crypto and math, modelled as pure host-state hooks -/

def digestFn (name : String) (hash : NearState → List UInt8 → List UInt8) : HostFn NearState :=
  { params := [.i64, .i64, .i64], results := []
    invoke := fun st args => match args with
      | [.i64 valueLen, .i64 valuePtr, .i64 regId] =>
        match getMemOrReg st valuePtr valueLen with
        | none => .Trap st s!"{name}: invalid input"
        | some value =>
          writeRegisterResult name st regId (hash st.host value)
      | _ => .Trap st s!"{name}: bad args" }

def sha256Fn : HostFn NearState :=
  digestFn "sha256" (·.sha256)

def keccak256Fn : HostFn NearState :=
  digestFn "keccak256" (·.keccak256)

def keccak512Fn : HostFn NearState :=
  digestFn "keccak512" (·.keccak512)

def ripemd160Fn : HostFn NearState :=
  digestFn "ripemd160" (·.ripemd160)

def randomSeedFn : HostFn NearState :=
  { params := [.i64], results := []
    invoke := fun st args => match args with
      | [.i64 regId] =>
        writeRegisterResult "random_seed" st regId st.host.randomSeed
      | _ => .Trap st "random_seed: bad args" }

def ecrecoverFn : HostFn NearState :=
  { params := [.i64, .i64, .i64, .i64, .i64, .i64], results := [.i64]
    invoke := fun st args => match args with
      | [.i64 hashLen, .i64 hashPtr, .i64 sigLen, .i64 sigPtr, .i64 v, .i64 malleabilityFlag] =>
        match getMemOrReg st hashPtr hashLen, getMemOrReg st sigPtr sigLen with
        | some hash, some sig =>
          match st.host.ecrecover hash sig v (malleabilityFlag != 0) with
          | some pk =>
            checkPublicKey "ecrecover" st pk <| fun _ =>
              writeRegisterResult "ecrecover" st 0 pk [.i64 1]
          | none => .Return [.i64 0] st
        | _, _ => .Trap st "ecrecover: invalid input"
      | _ => .Trap st "ecrecover: bad args" }

def ed25519VerifyFn : HostFn NearState :=
  { params := [.i64, .i64, .i64, .i64, .i64, .i64], results := [.i64]
    invoke := fun st args => match args with
      | [.i64 sigLen, .i64 sigPtr, .i64 msgLen, .i64 msgPtr, .i64 pkLen, .i64 pkPtr] =>
        match getMemOrReg st sigPtr sigLen, getMemOrReg st msgPtr msgLen, getMemOrReg st pkPtr pkLen with
        | some sig, some msg, some pk =>
          checkPublicKey "ed25519_verify" st pk <| fun _ =>
            .Return [.i64 (if st.host.ed25519Verify sig msg pk then 1 else 0)] st
        | _, _, _ => .Trap st "ed25519_verify: invalid input"
      | _ => .Trap st "ed25519_verify: bad args" }

def mathRegisterFn (name : String) (op : NearState → List UInt8 → List UInt8) : HostFn NearState :=
  { params := [.i64, .i64, .i64], results := []
    invoke := fun st args => match args with
      | [.i64 valueLen, .i64 valuePtr, .i64 regId] =>
        match getMemOrReg st valuePtr valueLen with
        | some value => writeRegisterResult name st regId (op st.host value)
        | none => .Trap st s!"{name}: invalid input"
      | _ => .Trap st s!"{name}: bad args" }

def mathStatusRegisterFn (name : String)
    (op : NearState → List UInt8 → UInt64 × List UInt8) : HostFn NearState :=
  { params := [.i64, .i64, .i64], results := [.i64]
    invoke := fun st args => match args with
      | [.i64 valueLen, .i64 valuePtr, .i64 regId] =>
        match getMemOrReg st valuePtr valueLen with
        | some value =>
          let (status, out) := op st.host value
          if status == 0 then
            writeRegisterResult name st regId out [.i64 status]
          else
            .Return [.i64 status] st
        | none => .Trap st s!"{name}: invalid input"
      | _ => .Trap st s!"{name}: bad args" }

def mathStatusFn (name : String) (op : NearState → List UInt8 → UInt64) : HostFn NearState :=
  { params := [.i64, .i64], results := [.i64]
    invoke := fun st args => match args with
      | [.i64 valueLen, .i64 valuePtr] =>
        match getMemOrReg st valuePtr valueLen with
        | some value => .Return [.i64 (op st.host value)] st
        | none => .Trap st s!"{name}: invalid input"
      | _ => .Trap st s!"{name}: bad args" }

def altBn128G1MultiexpFn : HostFn NearState :=
  mathRegisterFn "alt_bn128_g1_multiexp" (·.altBn128G1Multiexp)

def altBn128G1SumFn : HostFn NearState :=
  mathRegisterFn "alt_bn128_g1_sum" (·.altBn128G1Sum)

def altBn128PairingCheckFn : HostFn NearState :=
  mathStatusFn "alt_bn128_pairing_check" (·.altBn128PairingCheck)

def bls12381G1MultiexpFn : HostFn NearState :=
  mathStatusRegisterFn "bls12381_g1_multiexp" (·.bls12381G1Multiexp)

def bls12381G2MultiexpFn : HostFn NearState :=
  mathStatusRegisterFn "bls12381_g2_multiexp" (·.bls12381G2Multiexp)

def bls12381MapFpToG1Fn : HostFn NearState :=
  mathStatusRegisterFn "bls12381_map_fp_to_g1" (·.bls12381MapFpToG1)

def bls12381MapFp2ToG2Fn : HostFn NearState :=
  mathStatusRegisterFn "bls12381_map_fp2_to_g2" (·.bls12381MapFp2ToG2)

def bls12381P1DecompressFn : HostFn NearState :=
  mathStatusRegisterFn "bls12381_p1_decompress" (·.bls12381P1Decompress)

def bls12381P2DecompressFn : HostFn NearState :=
  mathStatusRegisterFn "bls12381_p2_decompress" (·.bls12381P2Decompress)

def bls12381P1SumFn : HostFn NearState :=
  mathStatusRegisterFn "bls12381_p1_sum" (·.bls12381P1Sum)

def bls12381P2SumFn : HostFn NearState :=
  mathStatusRegisterFn "bls12381_p2_sum" (·.bls12381P2Sum)

def bls12381PairingCheckFn : HostFn NearState :=
  mathStatusFn "bls12381_pairing_check" (·.bls12381PairingCheck)

/-! ## Deprecated storage iterators -/

def hasPrefixBytes : List UInt8 → List UInt8 → Bool
  | [], _ => true
  | _, [] => false
  | p :: ps, b :: bs => p == b && hasPrefixBytes ps bs

def bytesLt : List UInt8 → List UInt8 → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs =>
    if a.toNat < b.toNat then
      true
    else if b.toNat < a.toNat then
      false
    else
      bytesLt as bs

def bytesLe (a b : List UInt8) : Bool :=
  a == b || bytesLt a b

def iteratorEntries (st : Store NearState) (keep : List UInt8 → Bool) :
    List (List UInt8 × List UInt8) :=
  st.host.storageKeys.filterMap (fun key =>
    if keep key then
      (st.host.storage key).map (fun value => (key, value))
    else
      none)

def createIteratorResult (st : Store NearState) (entries : List (List UInt8 × List UInt8)) :
    HostResult NearState :=
  let id := st.host.nextIteratorId
  .Return [.i64 (UInt64.ofNat id)]
    { st with host := st.host.setIterator id { entries := entries } }

def storageIterPrefixFn : HostFn NearState :=
  { params := [.i64, .i64], results := [.i64]
    invoke := fun st args => match args with
      | [.i64 prefixLen, .i64 prefixPtr] =>
        match getMemOrReg st prefixPtr prefixLen with
        | some pref =>
          checkDataLimit "storage_iter_prefix" "key" st.host.config.maxStorageKeyLen pref.length st <|
            fun _ => createIteratorResult st (iteratorEntries st (hasPrefixBytes pref))
        | none => .Trap st "storage_iter_prefix: invalid prefix"
      | _ => .Trap st "storage_iter_prefix: bad args" }

def storageIterRangeFn : HostFn NearState :=
  { params := [.i64, .i64, .i64, .i64], results := [.i64]
    invoke := fun st args => match args with
      | [.i64 startLen, .i64 startPtr, .i64 endLen, .i64 endPtr] =>
        match getMemOrReg st startPtr startLen, getMemOrReg st endPtr endLen with
        | some startKey, some endKey =>
          checkDataLimit "storage_iter_range" "start key" st.host.config.maxStorageKeyLen startKey.length st <| fun _ =>
          checkDataLimit "storage_iter_range" "end key" st.host.config.maxStorageKeyLen endKey.length st <| fun _ =>
            if bytesLt startKey endKey then
              createIteratorResult st
                (iteratorEntries st (fun key => bytesLe startKey key && bytesLt key endKey))
            else
              createIteratorResult st []
        | _, _ => .Trap st "storage_iter_range: invalid range"
      | _ => .Trap st "storage_iter_range: bad args" }

def getIteratorEntry? : List (List UInt8 × List UInt8) → Nat → Option (List UInt8 × List UInt8)
  | [], _ => none
  | e :: _, 0 => some e
  | _ :: es, n + 1 => getIteratorEntry? es n

def storageIterNextFn : HostFn NearState :=
  { params := [.i64, .i64, .i64], results := [.i64]
    invoke := fun st args => match args with
      | [.i64 iteratorId, .i64 keyRegId, .i64 valueRegId] =>
        if keyRegId == valueRegId then
          .Trap st "storage_iter_next: duplicate registers"
        else
          match st.host.iterators iteratorId.toNat with
          | none => .Trap st "storage_iter_next: invalid iterator"
          | some it =>
            match getIteratorEntry? it.entries it.pos with
            | none => .Return [.i64 0] st
            | some (key, value) =>
              match checkedSetRegister? st keyRegId key with
              | none => .Trap st "storage_iter_next: key register size exceeded"
              | some stKey =>
                match checkedSetRegister? stKey valueRegId value with
                | none => .Trap st "storage_iter_next: value register size exceeded"
                | some stVal =>
                  .Return [.i64 1]
                    { stVal with host := stVal.host.setIterator iteratorId.toNat { it with pos := it.pos + 1 } }
      | _ => .Trap st "storage_iter_next: bad args" }

/-! ## Tier 1 — storage

Return convention (uniform): `0` = key was absent, `1` = key was present.
On the present case the previous/read value is written to `register_id`
unless `register_id = u64Max`, which discards the output. -/

/-- `storage_write(key_len, key_ptr, value_len, value_ptr, register_id) -> u64`.
Inserts `key ↦ value`. If a value existed it is evicted into
`register_id` and `1` is returned; otherwise `0`. -/
def storageWriteFn : HostFn NearState :=
  disallowInView "storage_write" <|
  { params := [.i64, .i64, .i64, .i64, .i64], results := [.i64]
    invoke := fun st args => match args with
      | [.i64 keyLen, .i64 keyPtr, .i64 valLen, .i64 valPtr, .i64 regId] =>
        match getMemOrReg st keyPtr keyLen, getMemOrReg st valPtr valLen with
        | some key, some val =>
          checkDataLimit "storage_write" "key" st.host.config.maxStorageKeyLen key.length st <| fun _ =>
          checkDataLimit "storage_write" "value" st.host.config.maxStorageValueLen val.length st <| fun _ =>
            match st.host.storage key with
            | some old =>
              match checkedSetRegister? st regId old with
              | some st' =>
                .Return [.i64 1]
                  { st' with host := (st'.host.setStorage key val).invalidateIterators }
              | none     => .Trap st "storage_write: register size exceeded"
            | none =>
              .Return [.i64 0] { st with host := (st.host.setStorage key val).invalidateIterators }
        | _, _ => .Trap st "storage_write: invalid register"
      | _ => .Trap st "storage_write: bad args" }

/-- `storage_read(key_len, key_ptr, register_id) -> u64`. On hit, copies the
value into `register_id` and returns `1`; on miss returns `0` and leaves
the register untouched. -/
def storageReadFn : HostFn NearState :=
  { params := [.i64, .i64, .i64], results := [.i64]
    invoke := fun st args => match args with
      | [.i64 keyLen, .i64 keyPtr, .i64 regId] =>
        match getMemOrReg st keyPtr keyLen with
        | none => .Trap st "storage_read: invalid register"
        | some key =>
          checkDataLimit "storage_read" "key" st.host.config.maxStorageKeyLen key.length st <| fun _ =>
            match st.host.storage key with
            | some v => writeRegisterResult "storage_read" st regId v [.i64 1]
            | none   => .Return [.i64 0] st
      | _ => .Trap st "storage_read: bad args" }

/-- `storage_remove(key_len, key_ptr, register_id) -> u64`. On hit, copies
the removed value into `register_id`, removes the key and returns `1`; on
miss returns `0`. -/
def storageRemoveFn : HostFn NearState :=
  disallowInView "storage_remove" <|
  { params := [.i64, .i64, .i64], results := [.i64]
    invoke := fun st args => match args with
      | [.i64 keyLen, .i64 keyPtr, .i64 regId] =>
        match getMemOrReg st keyPtr keyLen with
        | none => .Trap st "storage_remove: invalid register"
        | some key =>
          checkDataLimit "storage_remove" "key" st.host.config.maxStorageKeyLen key.length st <| fun _ =>
            match st.host.storage key with
            | some v =>
              match checkedSetRegister? st regId v with
              | some st' =>
                .Return [.i64 1] { st' with host := (st'.host.removeStorage key).invalidateIterators }
              | none     => .Trap st "storage_remove: register size exceeded"
            | none => .Return [.i64 0] st
      | _ => .Trap st "storage_remove: bad args" }

/-- `storage_has_key(key_len, key_ptr) -> u64`: `1` if present, else `0`. -/
def storageHasKeyFn : HostFn NearState :=
  { params := [.i64, .i64], results := [.i64]
    invoke := fun st args => match args with
      | [.i64 keyLen, .i64 keyPtr] =>
        match getMemOrReg st keyPtr keyLen with
        | none => .Trap st "storage_has_key: invalid register"
        | some key =>
          checkDataLimit "storage_has_key" "key" st.host.config.maxStorageKeyLen key.length st <|
            fun _ => .Return [.i64 (if (st.host.storage key).isSome then 1 else 0)] st
      | _ => .Trap st "storage_has_key: bad args" }

/-- `panic()`: always traps. -/
def panicFn : HostFn NearState :=
  { invoke := fun st _ => .Trap st "explicit guest panic" }

/-- `panic_utf8(len, ptr)`: always traps (message content not modelled). -/
def panicUtf8Fn : HostFn NearState :=
  { params := [.i64, .i64], results := []
    invoke := fun st _ => .Trap st "guest panic (utf8)" }

def logUtf8Fn : HostFn NearState :=
  { params := [.i64, .i64], results := []
    invoke := fun st args => match args with
      | [.i64 len, .i64 ptr] =>
        match getMemOrReg st ptr len with
        | none => .Trap st "log_utf8: invalid memory"
        | some msg => appendLogResult "log_utf8" st msg
      | _ => .Trap st "log_utf8: bad args" }

def logUtf16Fn : HostFn NearState :=
  { params := [.i64, .i64], results := []
    invoke := fun st args => match args with
      | [.i64 len, .i64 ptr] =>
        match getMemOrReg st ptr len with
        | none => .Trap st "log_utf16: invalid memory"
        | some msg => appendLogResult "log_utf16" st msg
      | _ => .Trap st "log_utf16: bad args" }

def abortFn : HostFn NearState :=
  { params := [.i32, .i32, .i32, .i32], results := []
    invoke := fun st _ => .Trap st "guest abort" }

/-! ## Promises and callback results -/

def getPromiseResult? : List PromiseResult → Nat → Option PromiseResult
  | [], _ => none
  | r :: _, 0 => some r
  | _ :: rs, n + 1 => getPromiseResult? rs n

def promiseResultsCountFn : HostFn NearState :=
  { params := [], results := [.i64]
    invoke := fun st args => match args with
      | [] => .Return [.i64 (UInt64.ofNat st.host.promiseResults.length)] st
      | _  => .Trap st "promise_results_count: bad args" }

def promiseResultFn : HostFn NearState :=
  disallowInView "promise_result" <|
  { params := [.i64, .i64], results := [.i64]
    invoke := fun st args => match args with
      | [.i64 resultIdx, .i64 regId] =>
        match getPromiseResult? st.host.promiseResults resultIdx.toNat with
        | none => .Trap st "promise_result: invalid promise result index"
        | some .notReady => .Return [.i64 0] st
        | some (.successful data) =>
          writeRegisterResult "promise_result" st regId data [.i64 1]
        | some .failed => .Return [.i64 2] st
      | _ => .Trap st "promise_result: bad args" }

def promiseReturnFn : HostFn NearState :=
  disallowInView "promise_return" <|
  { params := [.i64], results := []
    invoke := fun st args => match args with
      | [.i64 promiseIdx] =>
        if promiseIdx.toNat < st.host.promises.length then
          .Return [] { st with host := { st.host with returnedPromise := some promiseIdx.toNat } }
        else
          .Trap st "promise_return: invalid promise index"
      | _ => .Trap st "promise_return: bad args" }

/-! ## The registry — single source of truth -/

private def imp (name : String) (params results : List ValueType) : ImportDecl :=
  { «module» := "env", name, params, results }

/-- Canonical ordered list of NEAR host functions, paired with their import
declarations. Index in this list is the unified function index used by
`call`. Real entries come first; trapping stubs fill out the common
remainder so contracts importing them resolve (and then fail loudly). -/
def nearHostFns : List (ImportDecl × HostFn NearState) :=
  [ (imp "input"                [.i64] [],                          inputFn)          -- 0
  , (imp "read_register"        [.i64, .i64] [],                    readRegisterFn)   -- 1
  , (imp "register_len"         [.i64] [.i64],                      registerLenFn)    -- 2
  , (imp "write_register"       [.i64, .i64, .i64] [],              writeRegisterFn)  -- 3
  , (imp "value_return"         [.i64, .i64] [],                    valueReturnFn)    -- 4
  , (imp "storage_write"        [.i64, .i64, .i64, .i64, .i64] [.i64], storageWriteFn)-- 5
  , (imp "storage_read"         [.i64, .i64, .i64] [.i64],          storageReadFn)    -- 6
  , (imp "storage_remove"       [.i64, .i64, .i64] [.i64],          storageRemoveFn)  -- 7
  , (imp "storage_has_key"      [.i64, .i64] [.i64],                storageHasKeyFn)  -- 8
  , (imp "panic"                [] [],                              panicFn)          -- 9
  , (imp "panic_utf8"           [.i64, .i64] [],                    panicUtf8Fn)      -- 10
  , (imp "current_account_id"     [.i64] [],     currentAccountIdFn)                  -- 11
  , (imp "predecessor_account_id" [.i64] [],     predecessorAccountIdFn)              -- 12
  , (imp "signer_account_id"      [.i64] [],     signerAccountIdFn)                   -- 13
  , (imp "attached_deposit"       [.i64] [],     attachedDepositFn)                   -- 14
  , (imp "log_utf8"               [.i64, .i64] [], logUtf8Fn)                         -- 15
  , (imp "sha256"           [.i64, .i64, .i64] [], sha256Fn)                                     -- 16
  , (imp "keccak256"        [.i64, .i64, .i64] [], keccak256Fn)                                  -- 17
  , (imp "signer_account_pk"      [.i64] [],     signerAccountPkFn)
  , (imp "block_index"            [] [.i64],     blockIndexFn)
  , (imp "block_height"           [] [.i64],     blockIndexFn)
  , (imp "block_timestamp"        [] [.i64],     blockTimestampFn)
  , (imp "epoch_height"           [] [.i64],     epochHeightFn)
  , (imp "storage_usage"          [] [.i64],     storageUsageFn)
  , (imp "account_balance"        [.i64] [],     accountBalanceFn)
  , (imp "account_locked_balance" [.i64] [],     accountLockedBalanceFn)
  , (imp "prepaid_gas"            [] [.i64],     prepaidGasFn)
  , (imp "used_gas"               [] [.i64],     usedGasFn)
  , (imp "validator_stake"        [.i64, .i64, .i64] [], validatorStakeFn)
  , (imp "validator_total_stake"  [.i64] [],     validatorTotalStakeFn)
  , (imp "log_utf16"              [.i64, .i64] [], logUtf16Fn)
  , (imp "abort"                  [.i32, .i32, .i32, .i32] [], abortFn)
  , (imp "storage_iter_prefix"    [.i64, .i64] [.i64], storageIterPrefixFn)
  , (imp "storage_iter_range"     [.i64, .i64, .i64, .i64] [.i64], storageIterRangeFn)
  , (imp "storage_iter_next"      [.i64, .i64, .i64] [.i64], storageIterNextFn)
  , (imp "keccak512"        [.i64, .i64, .i64] [], keccak512Fn)
  , (imp "ripemd160"        [.i64, .i64, .i64] [], ripemd160Fn)
  , (imp "ecrecover"        [.i64, .i64, .i64, .i64, .i64, .i64] [.i64], ecrecoverFn)
  , (imp "ed25519_verify"   [.i64, .i64, .i64, .i64, .i64, .i64] [.i64], ed25519VerifyFn)
  , (imp "random_seed"      [.i64] [], randomSeedFn)
  , (imp "alt_bn128_g1_multiexp" [.i64, .i64, .i64] [], altBn128G1MultiexpFn)
  , (imp "alt_bn128_g1_sum" [.i64, .i64, .i64] [], altBn128G1SumFn)
  , (imp "alt_bn128_pairing_check" [.i64, .i64] [.i64], altBn128PairingCheckFn)
  , (imp "bls12381_g1_multiexp" [.i64, .i64, .i64] [.i64], bls12381G1MultiexpFn)
  , (imp "bls12381_g2_multiexp" [.i64, .i64, .i64] [.i64], bls12381G2MultiexpFn)
  , (imp "bls12381_map_fp_to_g1" [.i64, .i64, .i64] [.i64], bls12381MapFpToG1Fn)
  , (imp "bls12381_map_fp2_to_g2" [.i64, .i64, .i64] [.i64], bls12381MapFp2ToG2Fn)
  , (imp "bls12381_p1_decompress" [.i64, .i64, .i64] [.i64], bls12381P1DecompressFn)
  , (imp "bls12381_p2_decompress" [.i64, .i64, .i64] [.i64], bls12381P2DecompressFn)
  , (imp "bls12381_p1_sum" [.i64, .i64, .i64] [.i64], bls12381P1SumFn)
  , (imp "bls12381_p2_sum" [.i64, .i64, .i64] [.i64], bls12381P2SumFn)
  , (imp "bls12381_pairing_check" [.i64, .i64] [.i64], bls12381PairingCheckFn)
  , (imp "promise_create" [.i64, .i64, .i64, .i64, .i64, .i64, .i64, .i64] [.i64],
      promiseCreateFn)
  , (imp "promise_then" [.i64, .i64, .i64, .i64, .i64, .i64, .i64, .i64, .i64] [.i64],
      promiseThenFn)
  , (imp "promise_and" [.i64, .i64] [.i64], promiseAndFn)
  , (imp "promise_batch_create" [.i64, .i64] [.i64], promiseBatchCreateFn)
  , (imp "promise_batch_then" [.i64, .i64, .i64] [.i64], promiseBatchThenFn)
  , (imp "promise_batch_action_create_account" [.i64] [], promiseBatchActionCreateAccountFn)
  , (imp "promise_batch_action_deploy_contract" [.i64, .i64, .i64] [],
      promiseBatchActionDeployContractFn)
  , (imp "promise_batch_action_function_call" [.i64, .i64, .i64, .i64, .i64, .i64, .i64] [],
      promiseBatchActionFunctionCallFn)
  , (imp "promise_batch_action_transfer" [.i64, .i64] [], promiseBatchActionTransferFn)
  , (imp "promise_batch_action_stake" [.i64, .i64, .i64, .i64] [], promiseBatchActionStakeFn)
  , (imp "promise_batch_action_add_key_with_full_access" [.i64, .i64, .i64, .i64] [],
      promiseBatchActionAddKeyWithFullAccessFn)
  , (imp "promise_batch_action_add_key_with_function_call"
      [.i64, .i64, .i64, .i64, .i64, .i64, .i64, .i64, .i64] [],
      promiseBatchActionAddKeyWithFunctionCallFn)
  , (imp "promise_batch_action_delete_key" [.i64, .i64, .i64] [],
      promiseBatchActionDeleteKeyFn)
  , (imp "promise_batch_action_delete_account" [.i64, .i64, .i64] [],
      promiseBatchActionDeleteAccountFn)
  , (imp "promise_yield_create" [.i64, .i64, .i64, .i64, .i64, .i64, .i64] [.i64],
      promiseYieldCreateFn)
  , (imp "promise_yield_resume" [.i64, .i64, .i64, .i64] [.i64],
      promiseYieldResumeFn)
  , (imp "promise_results_count" [] [.i64], promiseResultsCountFn)
  , (imp "promise_result" [.i64, .i64] [.i64], promiseResultFn)
  , (imp "promise_return" [.i64] [], promiseReturnFn) ]

/-- Import declarations, in canonical order. A NEAR contract module sets
`imports := nearImports`. -/
def nearImports : List ImportDecl := nearHostFns.map Prod.fst

/-- The NEAR host environment. `funcs` aligns positionally with
`nearImports`. -/
def nearEnv : HostEnv NearState := { funcs := nearHostFns.map Prod.snd }

/-- Import declarations match by module, name, params, and results. -/
def importMatches (a b : ImportDecl) : Bool :=
  a.«module» == b.«module» && a.name == b.name &&
    a.params == b.params && a.results == b.results

/-- Resolve one declared import to its NEAR host function. -/
def resolveImport? (decl : ImportDecl) : Option (HostFn NearState) :=
  (nearHostFns.find? (fun p => importMatches p.fst decl)).map Prod.snd

/-- Resolve the exact subset/order of imports declared by a real module into
a positional `HostEnv`. Returns `none` when an import is not a known NEAR
function with the declared signature. -/
def resolveImports? : List ImportDecl → Option (HostEnv NearState)
  | [] => some { funcs := [] }
  | decl :: rest =>
    match resolveImport? decl, resolveImports? rest with
    | some hf, some env => some { funcs := hf :: env.funcs }
    | _, _ => none

/-- Resolve a module's imports into a positional NEAR host environment. -/
def resolveEnv? (m : Module) : Option (HostEnv NearState) :=
  resolveImports? m.imports

/-- Number of host imports; a contract's own functions start at this
unified index. -/
def importCount : Nat := nearImports.length

end Near
end Wasm
