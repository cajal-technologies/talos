# Public-path call-site matrix

Status: **frozen against the exact compiling declarations in
`Contracts.lean`.  Every valid call edge has passed the caller/callee review;
excluded edges remain obligations at their originating guards**.

Absolute Wasm indices include the three imports; `funcN` denotes generated
local function `N` and therefore absolute function `N+3`.  Each row must be
re-audited after the representation and contract corrections below.

| Caller -> callee | Actual operands | Resources/facts prepared by caller | Required continuation result | Current defect/status |
| --- | --- | --- | --- | --- |
| `func10 -> import0` | shim source params `(pointer,length)`; shim-call top-first `[length,pointer]`; direct-import top-first `[pointer,length]`; host `(length,pointer)` | writable owned range of exactly positive `length` bytes; stream state; in-bounds/no-wrap facts | count `min(length,input.length)`; buffer is input prefix followed by untouched old suffix; input drops count | Sharing one operand list between shim and import was rejected by the first proof attempt.  The separated `Import0Spec` and `Func10Spec` now have compiled authoritative proofs. |
| `func11 -> import1` | shim-call top-first `[length,pointer]`; direct-import top-first `[pointer,length]`; host `(length,pointer)` | readable owned range whose byte-list length is exactly positive `length`; stream state | append exactly those bytes; preserve range, input, and OOM marker | The corrected order, exact length/positivity, and preservation post are validated by compiled authoritative proofs; the driver always supplies four. |
| `func6 -> import2` | `[]` | `Streams input output raised`, running-instance/runtime identity, and framed resources | exact host trap `OOM.trapMessage`, `Streams input output true`, no normal return and no `RuntimeContext` | The host trap consumes current-instance ownership.  The corrected terminal continuation is now validated by compiled proofs of both `Import2Spec` and `Func6Spec`; the following `unreachable` is not stepped. |
| `func5/8/9 -> func6` | `[]` on arithmetic/signed-end failure and on `memory.grow=-1` | Streams; unchanged cursor/frontier/metadata; all preexisting live/retired blocks | propagate exact OOM, change only Streams marker, and preserve pre-commit allocator resources | Both logical-OOM and physical-grow-failure subedges pass body/caller review; `Func5Spec`, `Func8Spec`, and `Func9Spec` are frozen. Hard-cap success remains only an optional initial-store strengthening. |
| `func0 -> func8` | `(oldPtr, oldCapacity*elementSize, alignment,newSize)` | result-place ownership; valid live old block; exact/no-wrap old-size product; prefix bound; heap frontier | fresh live block with copied prefix and old block transferred to retired heap, or exact OOM | Frozen `Func8Spec` transfers complete blocks and the exact copied prefix; `GrowSourceOwn`, `growCopied`, and `growHistory` reassemble the frozen `Func0Spec` result. Body proof pending. |
| `func0 -> func4; func5` | marker, then `(newSize,alignment)` when old capacity is zero and size is nonzero | result place and allocator state under separating ownership; valid layout; heap/frontier | marker preserves all state; allocator returns a fresh nonnull live block or exact OOM | Frozen `Func4Spec` and `Func5Spec` provide the exact identity/allocation effects. Frontier authority plus the below-frontier sparse domain proves freshness/disjointness, and reachable arithmetic proves nonnull/alignment. `Func0Spec` is frozen; body proof pending. |
| `func1 -> func43` (addition guard) | `(0,0)` iff `length+additional` wraps | exact unsigned no-wrap fact | edge is false | `Func1Spec` names `initialized.length + current.length < UInt32.size`; derive the branch condition locally in its body proof. |
| `func1 -> func0` | `(sp+4,oldCap,oldPtr,newCap,alignment,elementSize)` | owned 16-byte shadow frame below the 272-byte export frame; result at `sp+4`; Vec live block; geometric lineage | preserved initialized bytes and new `(capacity,pointer,block)`, exact shadow `oldShadow.take 4 ++ serialize [0,newPtr,newCap]`, or exact OOM | `StackReserve_split` gives the exact 4+12 shadow split, `VecStorage_as_growSource` gives the callee source witness, `reserveSuccessShadow` reseals the exact frame, and `GeometricVecFacts.reserveSuccess` proves lineage/history progress and rules out success beyond exponent 29. `Func1Spec` is frozen; body proof pending. |
| `func1 -> func43` (grow tag) | `(result.+4,result.+8)` when tag is one | a valid selected layout proving `func0` cannot normally return a layout error | edge is false | `Func0Spec` has no tag-one normal post under this specialization; prove the edge false at the load/test after the call. |
| `func2 -> func2` (left) | `(source,mid,scratch,mid)` | split left buffers; frame right buffers; numeric lengths equal list lengths | left source is a sorted permutation; left scratch is unchanged for `mid<=1`, otherwise equals left source; resources recombined | Frozen `Func2Spec` plus `SortBuffers_append` packages the independently callable left pair and retains full cross-buffer disjointness for later reassembly. |
| `func2 -> func2` (right) | `(source+4*mid,n-mid,scratch+4*mid,scratchLen-mid)` | split right buffers; frame sorted left buffers; exact nonwrapping suffix addresses | right source is a sorted permutation; right scratch is unchanged for `n-mid<=1`, otherwise equals right source; both halves available to merge | The same frozen contract and reversible packaging close the right call; both strict recursive decreases follow from `n>=2`. |
| `func2 -> func46` | `(0,mid,scratchLen,1049064)` | `scratchLen >= mid` | edge is false | Follows from equal lengths once numeric/list lengths are linked. |
| `func2 -> func49` (four sites) | failing index, logical length, static source location | main invariant `i<mid`, `j<n`, `k=i+(j-mid)<n`; remainder equations `i=mid => k=j` and `j=n => k+(mid-i)=n` | every edge is false | `WordSlice_get`/`WordSlice_set` and `SortBuffers_copyFocus` expose the exact bound premise. The obligation remains at each originating guard in the body proof; no excluded callee spec is used. |
| `func2 -> func55` | `(sourceLen,scratchLen,1049080)` | equal buffer lengths | edge is false | Direct from `SortBuffers`. |
| `func3 -> func10` (loop head/tail) | `(frame+12,256)` | chunk ownership, stream state, frame split | count <= 256; full chunk ownership returned; input strictly shrinks on nonzero count | Read-loop measure is remaining host input length. |
| `func3 -> func46` | `(0,count,256,1049096)` | read result `count <= 256` | edge is false | Direct from read post. |
| `func3 -> func1` | `(frame,vecLength,count,1,1)` | StackPointer, Vec, pure geometric facts, exact `count=min(256,count+remainingAfter.length)`, framed chunk bytes, Streams over `remainingAfter`, and 16-byte reserve below ExportFrame | capacity >= length+count with bytes preserved, exact reserve result bytes, and SP restored; or exact OOM with SP `frame-16` and pre-attempt resources unchanged | The statement passes both directions: pure reserve progress, exact frame reconstruction, and `VecU8_appendFocus` close the caller's copy/length update. Reserve OOM maps exactly to `DriverReserveOOM`; body proof pending. |
| `func3 -> func4; func5` | marker, then `(inputByteLength,4)` | nonzero multiple-of-four length; exact signed-mask equation; valid layout; heap/frontier | arbitrary fresh aligned nonnull values block, or exact OOM | `Func4Spec`/`Func5Spec` return the complete live block. `LiveBlock_as_decodedWordBlock` gives arbitrary fresh bytes a canonical initial word view; the decode invariant `overwritePrefix original initial copied` ends in `original`. Values OOM maps exactly to `DriverValuesOOM`. |
| `func3 -> func43` (values null) | `(4,inputByteLength)` | normal `func5` result is nonnull | edge is false | `LiveBlock` plus `classifyBump_success_reachable` supplies nonnull directly; discharge at WAT line 774. |
| `func3 -> func4; func9` | marker, then `(4*n,4)` | exact `4*n=inputByteLength` without wrap; decoded values live block; heap/frontier | fresh nonnull zeroed scratch block, or exact OOM | `serialize_replicate_zero` and `zeroLiveBlock_as_liveWordBlock` turn the exact zeroed result into the canonical scratch word array without changing ownership. Scratch OOM maps exactly to `DriverScratchOOM`. |
| `func3 -> func43` (scratch null) | `(4,4*n)` | normal `func9` result is nonnull | edge is false | `LiveBlock` plus `classifyBump_success_reachable` supplies nonnull directly; discharge at WAT line 779. |
| `func3 -> func2` | `(valuesPtr,n,scratchPtr,n)` | disjoint equal-length WordSlices and numeric/list-length equations | source contains the sorted result; scratch remains its initial zero list for `n<=1`, otherwise contains the same result | The frozen callee post is exactly what `LiveWordBlocks_sortFocus` reseals. `SortBuffers_empty` covers `n=0`; for nonempty input, allocation tokens and allocator order provide the two word views and disjointness. Both directions pass. |
| `func3 -> func11` (output loop) | `(frame+268,4)` | output slot owns exactly canonical bytes of current word; accumulated output is `serialize (sorted.take emitted)` | append those four bytes and return slot ownership | `ByteSlice_storeWordFocus` converts the arbitrary old four-byte slot to the store cell and reseals it as `serialize [word]`; `Func11Spec` appends those exact bytes and advances the exact `emitted` invariant. |
| `func3 -> func7` (partial-word branch) | `(inputPtr,capacity,1)` | public serialization gives `byteLength % 4 = 0` | edge is false | The proof stops this path at the modulo guard; it does not apply `Func7Spec` or prove the unreachable branch body. |
| `func3 -> func7` (values) | `(valuesPtr,4*n,4)` | resealed values LiveBlock with allocation token | consume token/block and mark entry retired in BumpHeap | `LiveBlock_open` and `BumpHeap_retire` implement the exact lifecycle transition; the authoritative `Func7Spec` proof now compiles. |
| `func3 -> func7` (scratch) | `(scratchPtr,4*n,4)` | resealed scratch LiveBlock with allocation token | consume token/block and mark entry retired in BumpHeap | Same proved representation transition and compiled authoritative `Func7Spec` proof. |
| `func3 -> func7` (input Vec) | `(inputPtr,capacity,1)` | current Vec LiveBlock/token; older realloc blocks already retired | consume current token/block and mark it retired | `ExportFrame_releaseStorage` preserves all 272 stack bytes while exposing the complete `VecStorage`; `BumpHeap_retire` performs the exact transfer, and `StackReserve_combineFrame` restores the final raw entry stack. This is the third valid use of the frozen `Func7Spec`. |

## Contract corrections required by this audit

1. `BumpHeap` owns cursor/frontier authority, allocation-metadata authority,
   and physical bytes of retired blocks.  Physical page count and instantiated
   cap metadata remain under StateInterp.  Exact module identity does not by
   itself fix `memoryCaps`, so grow failure is an in-scope exact-OOM branch.
   `BumpHeap` does **not** own live-block bytes.
2. A live block owns `AllocToken * ByteSlice` for its complete allocation, not
   merely its initialized prefix.  `VecU8` relates its logical prefix to those
   bytes and owns the header and live-block handle.
3. Realloc/dealloc consume the token/live bytes, update authoritative status,
   and transfer old bytes to the retired part of `BumpHeap` exactly once.
4. Allocation returns `exists id bytes, bytes.length = size` plus ownership and
   nonnull/alignment/freshness facts.  Zeroed allocation fixes those bytes to
   zero.  Every Wasm size/alignment argument has an exact logical equation.
5. Every OOM-capable contract threads `Streams`; normal return preserves it and
   exact OOM changes only its marker.  `func1` also owns `StackPointer`; reserve
   OOM returns the pointer exactly at `driverBase-16` and all incoming shadow
   bytes unchanged.
6. Pure `GeometricVecFacts` connects capacities, retained entries, and bump
   frontier strongly enough to prove allocator OOM before RawVec overflow,
   without duplicating `VecU8` or `BumpHeap` ownership.

## Outcome audit implication

The red-team audits rejected the proposed “normal TWP plus separate
relational TrapsWith” architecture: exact trap reasoning would replay caller
control flow and violate the one-analysis rule.  This does not select or
implement an alternative yet.  It records a requirement on all principal
contracts: normal return and exact OOM must be sequenceable through one
continuation-aware interface.  The selected shared outcome-valued Iris
language, exact host-import signature, and adequacy bridge now pass the
miniature acceptance test.  This closes the infrastructure risk only; it does
not freeze a target theorem or its caller-resource contract.
