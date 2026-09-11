import Project.RustHashMap.HostProof

/-!
# Proofs of the import and shim contracts

This file proves the three import contracts of `Project.RustHashMap.Contracts`
from the host bridges in `Project.RustHashMap.HostProof`, and then the three
generated shims that call them.  The shim proofs are the first compiled-body
proofs of the module: each shim body is two or three instructions.

The proofs follow `Project.Mergesort.ContractProofs`.  Byte ownership is
`Wasm.SepLogic.Slices.ByteSlice 0`.
-/

namespace Project.RustHashMap.ImportProofs

open Wasm
open Iris Iris.ProgramLogic Language.Notation Std
open Wasm.SepLogic Wasm.SmallStep
open Project.RustHashMap.Contracts
open scoped Wasm.SmallStep.Outcome

private abbrev readImport : ImportDecl :=
  { «module» := "stdio", name := "read",
    params := [.i32, .i32], results := [.i32] }

private abbrev writeImport : ImportDecl :=
  { «module» := "stdio", name := "write",
    params := [.i32, .i32], results := [] }

private theorem readImport_index :
    Project.RustHashMap.«module».imports[0] = readImport := by rfl

private theorem writeImport_index :
    Project.RustHashMap.«module».imports[1] = writeImport := by rfl

/-- The `stdio.read` import contract. -/
theorem import0_correct [WasmSmallStepGS hlc Universal.State] :
    Import0Spec (hlc := hlc) := by
  unfold Import0Spec Project.RustHashMap.Contracts.readContractAt CallContract
    callExpr
  intro ptr requested buffer input output raised callerLocals stack code arity
    remainder controls calls s E Φ
  dsimp only
  let count := min requested.toNat input.length
  let Cont : HeapIProp := iprop(
    RuntimeContext -∗
    Streams (input.drop count) output raised -∗
    Slices.ByteSlice 0 ptr (input.take count ++ buffer.drop count) -∗
    ⌜count ≤ requested.toNat⌝ -∗
    ResumeWP [.i32 (UInt32.ofNat count)] callerLocals stack code arity
      remainder controls calls s E Φ)
  iintro ⟨Hruntime, ⟨Hstreams, ⟨Hslice, ⟨%hfacts, Hcont⟩⟩⟩⟩
  iopen_map_runtime Hruntime with ⟨Hmodule, Henv⟩
  iintuitionistic Henv
  isimp only [Streams] at Hstreams
  icases Hstreams with ⟨%random, Hhost⟩
  isimp only [Slices.ByteSlice] at Hslice
  icases Hslice with ⟨%hnowrap, Hbytes⟩
  let host : Universal.State :=
    { stdio := { input := input, output := output }
      random := random
      oom := { raised := raised } }
  simp only [List.cons_append, List.nil_append]
  iapply twp_callHost Project.RustHashMap.«module» 0 readImport
      HostProof.readHost (by decide) readImport_index
      (Universal.envFor Project.RustHashMap.«module»)
      HostProof.readHost_resolves
      (iprop(hostStateOwn host ∗ pointsToBytes 0 ptr buffer ∗ Cont))
      (fun results => iprop(
        ⌜results = [.i32 (UInt32.ofNat
          (host.stdio.input.take requested.toNat).length)]⌝ ∗
        hostStateOwn (HostProof.afterRead host
          (host.stdio.input.take requested.toNat).length) ∗
        pointsToBytes 0 ptr
          (host.stdio.input.take requested.toNat ++
            buffer.drop (host.stdio.input.take requested.toNat).length) ∗
        Cont))
      iprop(False) iprop(False) ⟨0⟩
      (fun store ns obs nt hmodule results postWasm hinvoke => by
        have hinvoke' : HostProof.readHost.invoke
            store.wasm [.i32 requested, .i32 ptr] =
              .Return results postWasm := by
          simpa only [List.length_cons, List.length_nil, Nat.reduceAdd,
            List.take_succ_cons, List.take_zero, List.reverse_cons,
            List.reverse_nil, List.cons_append, List.nil_append] using hinvoke
        iintro ⟨⟨Hhost, ⟨Hbytes, Hcont⟩⟩, Hstate⟩
        imod HostProof.readTransfer host ptr requested
            buffer hfacts.1.symm (by omega) hnowrap store ns obs nt
            results postWasm hinvoke' $$ [Hhost Hbytes Hstate] with
            ⟨Hresult, Hstate⟩
        · iframe
        icases Hresult with ⟨Hpure, Hhost, Hbytes⟩
        imodintro
        isplitl [Hpure Hhost Hbytes Hcont]
        · iframe
        · iexact Hstate)
      (fun store ns obs nt _hmodule postWasm msg hinvoke => by
        simp only [List.length_cons, List.length_nil, Nat.reduceAdd,
          List.take_succ_cons, List.take_zero, List.reverse_cons,
          List.reverse_nil, List.cons_append, List.nil_append] at hinvoke
        iintro ⟨⟨Hhost, ⟨Hbytes, _Hcont⟩⟩, Hstate⟩
        ihave %hhostEq : ⌜store.wasm.host = host⌝ $$ [Hstate Hhost]
        · iapply_frame stateInterp_host_agree store ns obs nt host using [Hstate Hhost]
        ihave %hmem :
            ⌜∀ i b, buffer[i]? = some b →
              store.wasm.mem.read8 (ptr + UInt32.ofNat i) = b ∧
              (ptr + UInt32.ofNat i).toNat <
                store.wasm.mem.pages * 65536⌝ $$ [Hstate Hbytes]
        · imod stateInterp_pointsToBytes_agree store ns obs nt ptr buffer
              $$ [$Hstate $Hbytes] with %hmem
          ipureexact hmem
        have hbufferBound : ptr.toNat + buffer.length ≤
            store.wasm.mem.pages * 65536 :=
          pointsToBytes_facts_bound hmem (by omega) hnowrap
        have hincomingBound : ptr.toNat +
            (store.wasm.host.stdio.input.take requested.toNat).length ≤
              store.wasm.mem.pages * 65536 := by
          rw [hhostEq]
          change ptr.toNat + (input.take requested.toNat).length ≤ _
          have := List.length_take_le requested.toNat input
          omega
        have hreturn :=
          HostProof.readHost_invoke_of_bound
            store.wasm requested ptr hincomingBound
        rw [hreturn] at hinvoke; contradiction)
      (fun store ns obs nt _hmodule postWasm tag xs hinvoke => by
        simp only [List.length_cons, List.length_nil, Nat.reduceAdd,
          List.take_succ_cons, List.take_zero, List.reverse_cons,
          List.reverse_nil, List.cons_append, List.nil_append] at hinvoke
        iintro ⟨⟨Hhost, ⟨Hbytes, _Hcont⟩⟩, Hstate⟩
        ihave %hhostEq : ⌜store.wasm.host = host⌝ $$ [Hstate Hhost]
        · iapply_frame stateInterp_host_agree store ns obs nt host using [Hstate Hhost]
        ihave %hmem :
            ⌜∀ i b, buffer[i]? = some b →
              store.wasm.mem.read8 (ptr + UInt32.ofNat i) = b ∧
              (ptr + UInt32.ofNat i).toNat <
                store.wasm.mem.pages * 65536⌝ $$ [Hstate Hbytes]
        · imod stateInterp_pointsToBytes_agree store ns obs nt ptr buffer
              $$ [$Hstate $Hbytes] with %hmem
          ipureexact hmem
        have hbufferBound : ptr.toNat + buffer.length ≤
            store.wasm.mem.pages * 65536 :=
          pointsToBytes_facts_bound hmem (by omega) hnowrap
        have hincomingBound : ptr.toNat +
            (store.wasm.host.stdio.input.take requested.toNat).length ≤
              store.wasm.mem.pages * 65536 := by
          rw [hhostEq]
          change ptr.toNat + (input.take requested.toNat).length ≤ _
          have := List.length_take_le requested.toNat input
          omega
        have hreturn :=
          HostProof.readHost_invoke_of_bound
            store.wasm requested ptr hincomingBound
        rw [hreturn] at hinvoke; contradiction)
      (params := callerLocals.params) (localValues := callerLocals.locals)
      (values := .i32 ptr :: .i32 requested :: stack)
      (code := code) (arity := arity) (remainder := remainder)
      (controls := controls) (calls := calls)
      $$ [$Hhost $Hbytes $Hcont] Hmodule Henv
  · iintro %preWasm %results %postWasm %hinvoke Hresult
    icases Hresult with ⟨⟨%hresults, Hhost, Hbytes, Hcont⟩, Hmodule⟩
    have hcount :
        (host.stdio.input.take requested.toNat).length = count := by
      simp [host, count]
    subst results
    simp only [List.length_cons, List.length_nil, Nat.reduceAdd,
      List.take_succ_cons, List.take_zero, List.drop_succ_cons,
      List.drop_zero]
    rw [hcount]
    have htake : input.take requested.toNat = input.take count := by
      simp [count]
    have hnewLength :
        (input.take count ++ buffer.drop count).length = buffer.length := by
      simp [count, hfacts.1]
    ihave Hstreams : Streams (input.drop count) output raised $$ [Hhost]
    · unfold Streams
      iexists random
      isimp only [HostProof.afterRead, host, hcount]
        at Hhost
      iexact Hhost
    ihave Hslice : Slices.ByteSlice 0 ptr
        (input.take count ++ buffer.drop count) $$ [Hbytes]
    · unfold Slices.ByteSlice
      isplitl_pureexact (by simpa only [hnewLength] using hnowrap)
      rw [← htake, ← hcount]
      isimp only [host] at Hbytes
      iexact Hbytes
    isimp only [Cont, RuntimeContext, ResumeWP, resumeExpr, List.nil_append]
      at Hcont
    iapply Hcont $$ [Hmodule Henv] Hstreams Hslice
    · isplitl_exact Hmodule
      · iexact Henv
    · ipureexact Nat.min_le_left _ _
  · iintro %preWasm %postWasm %msg %hinvoke Hfalse
    iexfalso
    iexact Hfalse
  · iintro %preWasm %postWasm %tag %xs %hinvoke Hfalse
    iexfalso
    iexact Hfalse

/-- The `stdio.write` import contract. -/
theorem import1_correct [WasmSmallStepGS hlc Universal.State] :
    Import1Spec (hlc := hlc) := by
  unfold Import1Spec Project.RustHashMap.Contracts.writeContractAt CallContract
    callExpr
  intro ptr requested bytes input output raised callerLocals stack code arity
    remainder controls calls s E Φ
  let Cont : HeapIProp := iprop(
    RuntimeContext -∗
    Streams input (output ++ bytes) raised -∗
    Slices.ByteSlice 0 ptr bytes -∗
    ResumeWP [] callerLocals stack code arity remainder controls calls s E Φ)
  iintro ⟨Hruntime, ⟨Hstreams, ⟨Hslice, ⟨%hfacts, Hcont⟩⟩⟩⟩
  iopen_map_runtime Hruntime with ⟨Hmodule, Henv⟩
  iintuitionistic Henv
  isimp only [Streams] at Hstreams
  icases Hstreams with ⟨%random, Hhost⟩
  isimp only [Slices.ByteSlice] at Hslice
  icases Hslice with ⟨%hnowrap, Hbytes⟩
  let host : Universal.State :=
    { stdio := { input := input, output := output }
      random := random
      oom := { raised := raised } }
  simp only [List.cons_append, List.nil_append]
  iapply twp_callHost Project.RustHashMap.«module» 1 writeImport
      HostProof.writeHost (by decide) writeImport_index
      (Universal.envFor Project.RustHashMap.«module»)
      HostProof.writeHost_resolves
      (iprop(hostStateOwn host ∗ pointsToBytes 0 ptr bytes ∗ Cont))
      (fun results => iprop(
        ⌜results = []⌝ ∗
        hostStateOwn (HostProof.afterWrite host bytes) ∗
        pointsToBytes 0 ptr bytes ∗ Cont))
      iprop(False) iprop(False) ⟨0⟩
      (fun store ns obs nt hmodule results postWasm hinvoke => by
        have hinvoke' : HostProof.writeHost.invoke
            store.wasm [.i32 requested, .i32 ptr] =
              .Return results postWasm := by
          simpa only [List.length_cons, List.length_nil, Nat.reduceAdd,
            List.take_succ_cons, List.take_zero, List.reverse_cons,
            List.reverse_nil, List.cons_append, List.nil_append] using hinvoke
        iintro ⟨⟨Hhost, ⟨Hbytes, Hcont⟩⟩, Hstate⟩
        imod HostProof.writeTransfer host ptr requested
            bytes hfacts.1 (by omega) hnowrap store ns obs nt results
            postWasm hinvoke' $$ [Hhost Hbytes Hstate] with
            ⟨Hresult, Hstate⟩
        · iframe
        icases Hresult with ⟨Hpure, Hhost, Hbytes⟩
        imodintro
        isplitl [Hpure Hhost Hbytes Hcont]
        · iframe
        · iexact Hstate)
      (fun store ns obs nt _hmodule postWasm msg hinvoke => by
        simp only [List.length_cons, List.length_nil, Nat.reduceAdd,
          List.take_succ_cons, List.take_zero, List.reverse_cons,
          List.reverse_nil, List.cons_append, List.nil_append] at hinvoke
        iintro ⟨⟨_Hhost, ⟨Hbytes, _Hcont⟩⟩, Hstate⟩
        ihave %hmem :
            ⌜∀ i b, bytes[i]? = some b →
              store.wasm.mem.read8 (ptr + UInt32.ofNat i) = b ∧
              (ptr + UInt32.ofNat i).toNat <
                store.wasm.mem.pages * 65536⌝ $$ [Hstate Hbytes]
        · imod stateInterp_pointsToBytes_agree store ns obs nt ptr bytes
              $$ [$Hstate $Hbytes] with %hmem
          ipureexact hmem
        have hbound : ptr.toNat + requested.toNat ≤
            store.wasm.mem.pages * 65536 := by
          rw [hfacts.1]; exact pointsToBytes_facts_bound hmem (by omega) hnowrap
        have hreturn :=
          HostProof.writeHost_invoke_of_bound
            store.wasm requested ptr hbound
        rw [hreturn] at hinvoke; contradiction)
      (fun store ns obs nt _hmodule postWasm tag xs hinvoke => by
        simp only [List.length_cons, List.length_nil, Nat.reduceAdd,
          List.take_succ_cons, List.take_zero, List.reverse_cons,
          List.reverse_nil, List.cons_append, List.nil_append] at hinvoke
        iintro ⟨⟨_Hhost, ⟨Hbytes, _Hcont⟩⟩, Hstate⟩
        ihave %hmem :
            ⌜∀ i b, bytes[i]? = some b →
              store.wasm.mem.read8 (ptr + UInt32.ofNat i) = b ∧
              (ptr + UInt32.ofNat i).toNat <
                store.wasm.mem.pages * 65536⌝ $$ [Hstate Hbytes]
        · imod stateInterp_pointsToBytes_agree store ns obs nt ptr bytes
              $$ [$Hstate $Hbytes] with %hmem
          ipureexact hmem
        have hbound : ptr.toNat + requested.toNat ≤
            store.wasm.mem.pages * 65536 := by
          rw [hfacts.1]; exact pointsToBytes_facts_bound hmem (by omega) hnowrap
        have hreturn :=
          HostProof.writeHost_invoke_of_bound
            store.wasm requested ptr hbound
        rw [hreturn] at hinvoke; contradiction)
      (params := callerLocals.params) (localValues := callerLocals.locals)
      (values := .i32 ptr :: .i32 requested :: stack)
      (code := code) (arity := arity) (remainder := remainder)
      (controls := controls) (calls := calls)
      $$ [$Hhost $Hbytes $Hcont] Hmodule Henv
  · iintro %preWasm %results %postWasm %hinvoke Hresult
    icases Hresult with ⟨⟨%hresults, Hhost, Hbytes, Hcont⟩, Hmodule⟩
    subst results
    simp only [List.length_nil, List.take_zero, List.length_cons,
      Nat.reduceAdd, List.drop_succ_cons, List.drop_zero,
      List.nil_append]
    ihave Hstreams : Streams input (output ++ bytes) raised $$ [Hhost]
    · unfold Streams
      iexists random
      isimp only [HostProof.afterWrite, host] at Hhost
      iexact Hhost
    ihave Hslice : Slices.ByteSlice 0 ptr bytes $$ [Hbytes]
    · unfold Slices.ByteSlice
      isplitl_pureexact hnowrap
      · iexact Hbytes
    isimp only [Cont, RuntimeContext, ResumeWP, resumeExpr, List.nil_append]
      at Hcont
    iapply Hcont $$ [Hmodule Henv] Hstreams Hslice
    · isplitl_exact Hmodule
      · iexact Henv
  · iintro %preWasm %postWasm %msg %hinvoke Hfalse
    iexfalso
    iexact Hfalse
  · iintro %preWasm %postWasm %tag %xs %hinvoke Hfalse
    iexfalso
    iexact Hfalse

/-- The `talos.oom` import contract.  A host trap consumes the running
instance, so the terminal continuation gets the host state but no
`RuntimeContext`. -/
theorem import2_correct [WasmSmallStepGS hlc Universal.State] :
    Import2Spec (hlc := hlc) := by
  unfold Import2Spec CallContract callExpr
  intro input output raised callerLocals stack code arity remainder controls
    calls s E Φ
  iintro ⟨Hruntime, ⟨Hstreams, Hterminal⟩⟩
  iopen_map_runtime Hruntime with ⟨Hmodule, Henv⟩
  isimp only [Streams] at Hstreams
  icases Hstreams with ⟨%random, Hhost⟩
  iapply HostProof.twp_oom_import
      ({ stdio := { input := input, output := output },
         random := random, oom := { raised := raised } } : Universal.State)
  isplitl_exacts [Hhost Hmodule Henv]
  iintro Hhost
  iapply Hterminal
  unfold Streams
  iexists random
  isimp only [HostProof.afterOom] at Hhost
  iexact Hhost

/-- The OOM shim calls import 2 at once.  The import traps, so the
`unreachable` that follows the call is not stepped. -/
theorem func56_correct [WasmSmallStepGS hlc Universal.State] :
    Func56Spec (hlc := hlc) := by
  unfold Func56Spec CallContract callExpr
  intro input output raised callerLocals stack code arity remainder controls
    calls s E Φ
  iintro ⟨Hruntime, ⟨Hstreams, Hterminal⟩⟩
  iopen_map_runtime Hruntime with ⟨Hmodule, Henv⟩
  wasm_twp_bind Wasm.SmallStep.twp_call Project.RustHashMap.«module» 59
      Project.RustHashMap.func56Def (by decide)
      HostProof.func56_index with Hmodule => Hmodule
  simp [Project.RustHashMap.func56Def, Project.RustHashMap.func56,
    Function.toLocals, Function.numParams]
  have Hoom := import2_correct (hlc := hlc)
      (input := input) (output := output) (raised := raised)
      (callerLocals := ({} : Locals)) (stack := [])
      (code := [.unreachable]) (arity := 0) (remainder := [])
      (controls := [])
      (calls :=
        { locals := { callerLocals with values := stack }
          continuation := code
          resultArity := arity
          callerRemainder := remainder
          control := controls
          returningInstance := ⟨0⟩ } :: calls)
      (s := s) (E := E) (Φ := Φ)
  unfold Import2Spec CallContract callExpr at Hoom
  simp only [List.nil_append] at Hoom
  iapply Hoom
  unfold RuntimeContext
  iframe Hmodule Henv Hstreams Hterminal

/-- The read shim changes only the operand order on the machine stack and
delegates to the import-0 contract. -/
theorem func60_correct [WasmSmallStepGS hlc Universal.State] :
    Func60Spec (hlc := hlc) := by
  unfold Func60Spec Project.RustHashMap.Contracts.readContractAt CallContract
    callExpr
  intro ptr requested buffer input output raised callerLocals stack code arity
    remainder controls calls s E Φ
  dsimp only
  iintro ⟨Hruntime, ⟨Hstreams, ⟨Hslice, ⟨%hfacts, Hcont⟩⟩⟩⟩
  iopen_map_runtime Hruntime with ⟨Hmodule, Henv⟩
  iintuitionistic Henv
  simp only [List.cons_append, List.nil_append]
  wasm_twp_bind Wasm.SmallStep.twp_call Project.RustHashMap.«module» 63
      Project.RustHashMap.func60Def (by decide)
      HostProof.func60_index with Hmodule => Hmodule
  simp [Project.RustHashMap.func60Def, Project.RustHashMap.func60,
    Function.toLocals, Function.numParams]
  wasm_twp_pures [twp_localGet twp_localGet]
  let shimLocals : Locals := ⟨[.i32 ptr, .i32 requested], [], []⟩
  let callerFrame : CallFrame :=
    { locals := { callerLocals with values := stack }
      continuation := code
      resultArity := arity
      callerRemainder := remainder
      control := controls
      returningInstance := ⟨0⟩ }
  have Hread := import0_correct (hlc := hlc)
      (ptr := ptr) (requested := requested) (buffer := buffer)
      (input := input) (output := output) (raised := raised)
      (callerLocals := shimLocals) (stack := []) (code := [])
      (arity := 1) (remainder := []) (controls := [])
      (calls := callerFrame :: calls) (s := s) (E := E) (Φ := Φ)
  unfold Import0Spec CallContract callExpr at Hread
  simp only [List.cons_append, List.nil_append] at Hread
  iapply Hread
  isplitl [Hmodule]
  · unfold RuntimeContext
    isplitl_exact Hmodule
    · iexact Henv
  isplitl_exacts [Hstreams Hslice]
  isplitl_pureexact hfacts
  iintro Hruntime Hstreams Hslice %hcount
  iopen_map_runtime Hruntime with ⟨Hmodule, HenvInner⟩
  unfold ResumeWP resumeExpr
  wasm_twp_rebind Wasm.SmallStep.twp_returnFromCallFallthrough with Hmodule
  simp only [List.append_nil, List.take_succ_cons, List.take_zero,
    List.cons_append, List.nil_append]
  isimp only [RuntimeContext, ResumeWP, resumeExpr, List.nil_append] at Hcont
  iapply_frame Hcont $$ [Hmodule HenvInner] Hstreams Hslice
  · itrivial

/-- The write shim changes only the operand order on the machine stack and
delegates to the import-1 contract. -/
theorem func61_correct [WasmSmallStepGS hlc Universal.State] :
    Func61Spec (hlc := hlc) := by
  unfold Func61Spec Project.RustHashMap.Contracts.writeContractAt CallContract
    callExpr
  intro ptr requested bytes input output raised callerLocals stack code arity
    remainder controls calls s E Φ
  iintro ⟨Hruntime, ⟨Hstreams, ⟨Hslice, ⟨%hfacts, Hcont⟩⟩⟩⟩
  iopen_map_runtime Hruntime with ⟨Hmodule, Henv⟩
  iintuitionistic Henv
  simp only [List.cons_append, List.nil_append]
  wasm_twp_bind Wasm.SmallStep.twp_call Project.RustHashMap.«module» 64
      Project.RustHashMap.func61Def (by decide)
      HostProof.func61_index with Hmodule => Hmodule
  simp [Project.RustHashMap.func61Def, Project.RustHashMap.func61,
    Function.toLocals, Function.numParams]
  wasm_twp_pures [twp_localGet twp_localGet]
  let shimLocals : Locals := ⟨[.i32 ptr, .i32 requested], [], []⟩
  let callerFrame : CallFrame :=
    { locals := { callerLocals with values := stack }
      continuation := code
      resultArity := arity
      callerRemainder := remainder
      control := controls
      returningInstance := ⟨0⟩ }
  have Hwrite := import1_correct (hlc := hlc)
      (ptr := ptr) (requested := requested) (bytes := bytes)
      (input := input) (output := output) (raised := raised)
      (callerLocals := shimLocals) (stack := []) (code := [])
      (arity := 0) (remainder := []) (controls := [])
      (calls := callerFrame :: calls) (s := s) (E := E) (Φ := Φ)
  unfold Import1Spec CallContract callExpr at Hwrite
  simp only [List.cons_append, List.nil_append] at Hwrite
  iapply Hwrite
  isplitl [Hmodule]
  · unfold RuntimeContext
    isplitl_exact Hmodule
    · iexact Henv
  isplitl_exacts [Hstreams Hslice]
  isplitl_pureexact hfacts
  iintro Hruntime Hstreams Hslice
  iopen_map_runtime Hruntime with ⟨Hmodule, HenvInner⟩
  unfold ResumeWP resumeExpr
  wasm_twp_rebind Wasm.SmallStep.twp_returnFromCallFallthrough with Hmodule
  simp only [List.take_zero, List.nil_append]
  isimp only [RuntimeContext, ResumeWP, resumeExpr, List.nil_append] at Hcont
  iapply_frame Hcont $$ [Hmodule HenvInner] Hstreams Hslice

end Project.RustHashMap.ImportProofs
