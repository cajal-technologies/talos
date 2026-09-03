import Project.Mergesort.Contracts
import Project.Mergesort.OutcomeInfrastructure
import Project.Mergesort.SortProof

/-!
# Proofs of the authoritative merge-sort contracts

This file proves the reviewed contracts bottom-up.  It deliberately contains
proofs only for imports and generated functions in the valid-input reachable
closure.  Compiler-generated panic, formatting, bounds-error, and generic
allocation-error functions (`func12`--`func55`) have no contracts and no body
proofs; their incoming edges remain obligations at the guards in reachable
callers.
-/

namespace Project.Mergesort.ContractProofs

open Wasm
open Iris Iris.ProgramLogic Language.Notation Std
open Wasm.SepLogic Wasm.SmallStep
open Project.Mergesort.Contracts
open Project.Mergesort.Representations
open scoped Wasm.SmallStep.Outcome

/-- Claim a fresh physical range while taking a generated constant step.
The claim is a ghost-only update, so the Wasm store and the instruction's
ordinary transition are unchanged.  All reachable allocator bodies share
this boundary between page-capacity reasoning and sparse byte ownership. -/
theorem twp_const_alloc_freshRange_owned
    [WasmSmallStepGS hlc Universal.State]
    {params localValues values : List Value}
    {value : UInt32} {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame} {s : Stuckness} {E : CoPset}
    {Φ : ObservableOutcome → HeapIProp}
    {P : HeapIProp}
    (frontier ownedPages : Nat) (base : UInt32) (size : Nat)
    (hbase : frontier ≤ base.toNat)
    (hbound : base.toNat + size ≤ ownedPages * 65536)
    (hnowrap : base.toNat + size < UInt32.size)
    (Hwp : ∀ bytes : List UInt8,
      ⌜bytes.length = size⌝ -∗
      heapFrontierOwn (base.toNat + size) -∗
      memoryPagesOwn ownedPages -∗
      Project.Mergesort.Representations.ByteSlice base bytes -∗
      P -∗
      WP (.running
        ⟨⟨params, localValues, .i32 value :: values⟩,
          code, arity, remainder, controls, calls⟩ : Expr Universal.State)
        @ s; E [{ Φ }]) :
    P -∗
    heapFrontierOwn frontier -∗
    memoryPagesOwn ownedPages -∗
    WP (.running
      ⟨⟨params, localValues, values⟩,
        .const value :: code, arity, remainder, controls, calls⟩ :
          Expr Universal.State)
        @ s; E [{ Φ }] := by
  iintro HP Hfrontier Hpages
  iapply twp_lift_step_no_fork
      (@TerminalView.running_not_val Universal.State ObservableOutcome _ _)
  iintro %store %ns %obs %nt Hσ
  imod stateInterp_alloc_freshRange_owned store ns obs nt
      frontier ownedPages base size hbase hbound hnowrap $$
      [Hσ Hfrontier Hpages] with ⟨Hσ, Hfrontier, Hpages, Hbytes⟩
  · iframe
  let bytes := physicalBytes store.wasm.mem base size
  ihave Hslice : Project.Mergesort.Representations.ByteSlice base bytes $$
      [Hbytes]
  · unfold Project.Mergesort.Representations.ByteSlice
    iframe Hbytes
    ipureintro
    simpa [bytes] using hnowrap
  ihave Hnext := Hwp bytes
  ispecialize Hnext $$ %(by simp [bytes]) Hfrontier Hpages Hslice HP
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro
    cases s <;> simp only [Stuckness.MaybeReducibleNoObs]
    exact ⟨_, store, [], ⟨rfl, _, rfl, Step.const⟩⟩
  iintro %κ %e₂ %store₂ %forks %Hstep
  rcases Hstep with ⟨hforks, kind, hobs, wasmStep⟩
  change forks = [] at hforks
  subst forks
  subst κ
  obtain ⟨rfl, hconfig⟩ := step_deterministic Step.const wasmStep
  have parts := Config.mk.inj hconfig
  have hexpr := parts.1
  have hstore := parts.2
  simp only at hexpr hstore
  subst e₂
  subst store₂
  imod Hclose
  imodintro
  isplit
  · ipureexact rfl
  isplit
  · ipureexact rfl
  isplitl [Hσ]
  · iexact Hσ
  · iexact Hnext

private abbrev readImport : ImportDecl :=
  { module := "stdio", name := "read",
    params := [.i32, .i32], results := [.i32] }

private abbrev writeImport : ImportDecl :=
  { module := "stdio", name := "write",
    params := [.i32, .i32], results := [] }

private theorem readImport_index :
    Project.Mergesort.module.imports[0] = readImport := by
  rfl

private theorem writeImport_index :
    Project.Mergesort.module.imports[1] = writeImport := by
  rfl

/-- The authoritative `stdio.read` import contract. -/
theorem import0_correct [WasmSmallStepGS hlc Universal.State] :
    Import0Spec (hlc := hlc) := by
  unfold Import0Spec Project.Mergesort.Contracts.readContractAt CallContract
    callExpr
  intro ptr requested buffer input output raised callerLocals stack code arity
    remainder controls calls s E Φ
  dsimp only
  let count := min requested.toNat input.length
  let Cont : HeapIProp := iprop(
    RuntimeContext -∗
    Streams (input.drop count) output raised -∗
    ByteSlice ptr (input.take count ++ buffer.drop count) -∗
    ⌜count ≤ requested.toNat⌝ -∗
    ResumeWP [.i32 (UInt32.ofNat count)] callerLocals stack code arity
      remainder controls calls s E Φ)
  iintro ⟨Hruntime, ⟨Hstreams, ⟨Hslice, ⟨%hfacts, Hcont⟩⟩⟩⟩
  iopen_runtime Hruntime with ⟨Hmodule, Henv⟩
  iintuitionistic Henv
  isimp only [Streams] at Hstreams
  icases Hstreams with ⟨%random, Hhost⟩
  isimp only [Project.Mergesort.Representations.ByteSlice] at Hslice
  icases Hslice with ⟨%hnowrap, Hbytes⟩
  let host : Universal.State :=
    { stdio := { input := input, output := output }
      random := random
      oom := { raised := raised } }
  simp only [List.cons_append, List.nil_append]
  iapply twp_callHost Project.Mergesort.module 0 readImport
      Project.Mergesort.WrapperProof.readHost (by decide) readImport_index
      (Universal.envFor Project.Mergesort.module)
      Project.Mergesort.WrapperProof.readHost_resolves
      (iprop(hostStateOwn host ∗ pointsToBytes 0 ptr buffer ∗ Cont))
      (fun results => iprop(
        ⌜results = [.i32 (UInt32.ofNat
          (host.stdio.input.take requested.toNat).length)]⌝ ∗
        hostStateOwn (Project.Mergesort.WrapperProof.afterRead host
          (host.stdio.input.take requested.toNat).length) ∗
        pointsToBytes 0 ptr
          (host.stdio.input.take requested.toNat ++
            buffer.drop (host.stdio.input.take requested.toNat).length) ∗
        Cont))
      iprop(False) iprop(False) ⟨0⟩
      (fun store ns obs nt hmodule results postWasm hinvoke => by
        have hinvoke' : Project.Mergesort.WrapperProof.readHost.invoke
            store.wasm [.i32 requested, .i32 ptr] =
              .Return results postWasm := by
          simpa only [List.length_cons, List.length_nil, Nat.reduceAdd,
            List.take_succ_cons, List.take_zero, List.reverse_cons,
            List.reverse_nil, List.cons_append, List.nil_append] using hinvoke
        iintro ⟨⟨Hhost, ⟨Hbytes, Hcont⟩⟩, Hstate⟩
        imod Project.Mergesort.WrapperProof.readTransfer host ptr requested
            buffer hfacts.1.symm (by omega) hnowrap store ns obs nt hmodule
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
        · iapply stateInterp_host_agree store ns obs nt host
          iframe Hstate Hhost
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
          Project.Mergesort.WrapperProof.readHost_invoke_of_bound
            store.wasm requested ptr hincomingBound
        rw [hreturn] at hinvoke
        contradiction)
      (fun store ns obs nt _hmodule postWasm tag xs hinvoke => by
        simp only [List.length_cons, List.length_nil, Nat.reduceAdd,
          List.take_succ_cons, List.take_zero, List.reverse_cons,
          List.reverse_nil, List.cons_append, List.nil_append] at hinvoke
        iintro ⟨⟨Hhost, ⟨Hbytes, _Hcont⟩⟩, Hstate⟩
        ihave %hhostEq : ⌜store.wasm.host = host⌝ $$ [Hstate Hhost]
        · iapply stateInterp_host_agree store ns obs nt host
          iframe Hstate Hhost
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
          Project.Mergesort.WrapperProof.readHost_invoke_of_bound
            store.wasm requested ptr hincomingBound
        rw [hreturn] at hinvoke
        contradiction)
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
      isimp only [Project.Mergesort.WrapperProof.afterRead, host, hcount]
        at Hhost
      iexact Hhost
    ihave Hslice : ByteSlice ptr
        (input.take count ++ buffer.drop count) $$ [Hbytes]
    · unfold Project.Mergesort.Representations.ByteSlice
      isplitl []
      · ipureintro
        rw [hnewLength]
        exact hnowrap
      · rw [← htake, ← hcount]
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

/-- The authoritative `stdio.write` import contract. -/
theorem import1_correct [WasmSmallStepGS hlc Universal.State] :
    Import1Spec (hlc := hlc) := by
  unfold Import1Spec Project.Mergesort.Contracts.writeContractAt CallContract
    callExpr
  intro ptr requested bytes input output raised callerLocals stack code arity
    remainder controls calls s E Φ
  let Cont : HeapIProp := iprop(
    RuntimeContext -∗
    Streams input (output ++ bytes) raised -∗
    ByteSlice ptr bytes -∗
    ResumeWP [] callerLocals stack code arity remainder controls calls s E Φ)
  iintro ⟨Hruntime, ⟨Hstreams, ⟨Hslice, ⟨%hfacts, Hcont⟩⟩⟩⟩
  iopen_runtime Hruntime with ⟨Hmodule, Henv⟩
  iintuitionistic Henv
  isimp only [Streams] at Hstreams
  icases Hstreams with ⟨%random, Hhost⟩
  isimp only [Project.Mergesort.Representations.ByteSlice] at Hslice
  icases Hslice with ⟨%hnowrap, Hbytes⟩
  let host : Universal.State :=
    { stdio := { input := input, output := output }
      random := random
      oom := { raised := raised } }
  simp only [List.cons_append, List.nil_append]
  iapply twp_callHost Project.Mergesort.module 1 writeImport
      Project.Mergesort.WrapperProof.writeHost (by decide) writeImport_index
      (Universal.envFor Project.Mergesort.module)
      Project.Mergesort.WrapperProof.writeHost_resolves
      (iprop(hostStateOwn host ∗ pointsToBytes 0 ptr bytes ∗ Cont))
      (fun results => iprop(
        ⌜results = []⌝ ∗
        hostStateOwn (Project.Mergesort.WrapperProof.afterWrite host bytes) ∗
        pointsToBytes 0 ptr bytes ∗ Cont))
      iprop(False) iprop(False) ⟨0⟩
      (fun store ns obs nt hmodule results postWasm hinvoke => by
        have hinvoke' : Project.Mergesort.WrapperProof.writeHost.invoke
            store.wasm [.i32 requested, .i32 ptr] =
              .Return results postWasm := by
          simpa only [List.length_cons, List.length_nil, Nat.reduceAdd,
            List.take_succ_cons, List.take_zero, List.reverse_cons,
            List.reverse_nil, List.cons_append, List.nil_append] using hinvoke
        iintro ⟨⟨Hhost, ⟨Hbytes, Hcont⟩⟩, Hstate⟩
        imod Project.Mergesort.WrapperProof.writeTransfer host ptr requested
            bytes hfacts.1 (by omega) hnowrap store ns obs nt hmodule results
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
          rw [hfacts.1]
          exact pointsToBytes_facts_bound hmem (by omega) hnowrap
        have hreturn :=
          Project.Mergesort.WrapperProof.writeHost_invoke_of_bound
            store.wasm requested ptr hbound
        rw [hreturn] at hinvoke
        contradiction)
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
          rw [hfacts.1]
          exact pointsToBytes_facts_bound hmem (by omega) hnowrap
        have hreturn :=
          Project.Mergesort.WrapperProof.writeHost_invoke_of_bound
            store.wasm requested ptr hbound
        rw [hreturn] at hinvoke
        contradiction)
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
      isimp only [Project.Mergesort.WrapperProof.afterWrite, host] at Hhost
      iexact Hhost
    ihave Hslice : ByteSlice ptr bytes $$ [Hbytes]
    · unfold Project.Mergesort.Representations.ByteSlice
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

/-- The authoritative contract for imported `talos.oom`.  A host trap consumes
the current-running-instance ownership, so the terminal continuation receives
the updated host state but no `RuntimeContext`. -/
theorem import2_correct [WasmSmallStepGS hlc Universal.State] :
    Import2Spec (hlc := hlc) := by
  unfold Import2Spec CallContract callExpr
  intro input output raised callerLocals stack code arity remainder controls
    calls s E Φ
  iintro ⟨Hruntime, ⟨Hstreams, Hterminal⟩⟩
  iopen_runtime Hruntime with ⟨Hmodule, Henv⟩
  isimp only [Streams] at Hstreams
  icases Hstreams with ⟨%random, Hhost⟩
  iapply Project.Mergesort.OutcomeInfrastructure.twp_oom_import
      ({ stdio := { input := input, output := output },
         random := random, oom := { raised := raised } } : Universal.State)
  isplitl_exact Hhost
  isplitl_exact Hmodule
  isplitl_exact Henv
  iintro Hhost
  iapply Hterminal
  unfold Streams
  iexists random
  isimp only [Project.Mergesort.WrapperProof.afterOom] at Hhost
  iexact Hhost

/-- The generated OOM shim immediately calls import 2.  The import traps, so
the syntactically following `unreachable` instruction is not stepped. -/
theorem func6_correct [WasmSmallStepGS hlc Universal.State] :
    Func6Spec (hlc := hlc) := by
  unfold Func6Spec CallContract callExpr
  intro input output raised callerLocals stack code arity remainder controls
    calls s E Φ
  iintro ⟨Hruntime, ⟨Hstreams, Hterminal⟩⟩
  iopen_runtime Hruntime with ⟨Hmodule, Henv⟩
  iapply Wasm.SmallStep.twp_call Project.Mergesort.module 9
      Project.Mergesort.func6Def (by decide)
      Project.Mergesort.WrapperProof.func6_index $$ Hmodule
  iintro Hmodule
  simp [Project.Mergesort.func6Def, Project.Mergesort.func6,
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

/-- The pre-allocation marker is exactly a no-op return. -/
theorem func4_correct [WasmSmallStepGS hlc Universal.State] :
    Func4Spec (hlc := hlc) := by
  unfold Func4Spec CallContract callExpr
  intro callerLocals stack code arity remainder controls calls s E Φ
  iintro ⟨Hruntime, Hcont⟩
  iopen_runtime Hruntime with ⟨Hmodule, Henv⟩
  iapply Wasm.SmallStep.twp_call Project.Mergesort.module 7
      Project.Mergesort.func4Def (by decide)
      Project.Mergesort.WrapperProof.func4_index $$ Hmodule
  iintro Hmodule
  simp [Project.Mergesort.func4Def, Project.Mergesort.func4,
    Function.toLocals, Function.numParams]
  wasm_twp_return_from_call Hmodule
  simp only [List.take_zero, List.nil_append]
  isimp only [RuntimeContext, ResumeWP, resumeExpr, List.nil_append] at Hcont
  iapply Hcont $$ [Hmodule Henv]
  · iframe

/-- The generated physical deallocator is a Wasm no-op; its authoritative
logical effect transfers the complete live block into retired allocator
ownership exactly once. -/
theorem func7_correct [WasmSmallStepGS hlc Universal.State] :
    Func7Spec (hlc := hlc) := by
  unfold Func7Spec CallContract callExpr
  intro ptr size alignment layout heapId allocationId bytes storedCursor
    frontier history callerLocals stack code arity remainder controls calls s
    E Φ
  iintro ⟨Hruntime, ⟨Hbump, ⟨Hblock, ⟨%_hlayout, Hcont⟩⟩⟩⟩
  iopen_runtime Hruntime with ⟨Hmodule, Henv⟩
  imod BumpHeap_retire heapId storedCursor frontier history allocationId ptr
      layout bytes $$ [Hbump Hblock] with Hbump
  · iframe
  iapply Wasm.SmallStep.twp_call Project.Mergesort.module 10
      Project.Mergesort.func7Def (by decide)
      Project.Mergesort.WrapperProof.func7_index $$ Hmodule
  iintro Hmodule
  simp [Project.Mergesort.func7Def, Project.Mergesort.func7,
    Function.toLocals, Function.numParams]
  wasm_twp_rebind Wasm.SmallStep.twp_returnFromCallFallthrough with Hmodule
  simp only [List.take_zero, List.nil_append]
  isimp only [RuntimeContext, ResumeWP, resumeExpr, List.nil_append] at Hcont
  iapply Hcont $$ [Hmodule Henv] Hbump
  · iframe

/-- The generated read shim changes only the machine-stack operand order and
delegates to the authoritative import-0 contract. -/
theorem func10_correct [WasmSmallStepGS hlc Universal.State] :
    Func10Spec (hlc := hlc) := by
  unfold Func10Spec Project.Mergesort.Contracts.readContractAt CallContract
    callExpr
  intro ptr requested buffer input output raised callerLocals stack code arity
    remainder controls calls s E Φ
  dsimp only
  iintro ⟨Hruntime, ⟨Hstreams, ⟨Hslice, ⟨%hfacts, Hcont⟩⟩⟩⟩
  iopen_runtime Hruntime with ⟨Hmodule, Henv⟩
  iintuitionistic Henv
  simp only [List.cons_append, List.nil_append]
  iapply Wasm.SmallStep.twp_call Project.Mergesort.module 13
      Project.Mergesort.func10Def (by decide)
      Project.Mergesort.WrapperProof.func10_index $$ Hmodule
  iintro Hmodule
  simp [Project.Mergesort.func10Def, Project.Mergesort.func10,
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
  isplitl_exact Hstreams
  isplitl_exact Hslice
  isplitl_pureexact hfacts
  iintro Hruntime Hstreams Hslice %hcount
  iopen_runtime Hruntime with ⟨Hmodule, HenvInner⟩
  unfold ResumeWP resumeExpr
  wasm_twp_rebind Wasm.SmallStep.twp_returnFromCallFallthrough with Hmodule
  simp only [List.append_nil, List.take_succ_cons, List.take_zero,
    List.cons_append, List.nil_append]
  isimp only [RuntimeContext, ResumeWP, resumeExpr, List.nil_append] at Hcont
  iapply Hcont $$ [Hmodule HenvInner] Hstreams Hslice
  · iframe
  · itrivial

/-- The generated write shim changes only the machine-stack operand order and
delegates to the authoritative import-1 contract. -/
theorem func11_correct [WasmSmallStepGS hlc Universal.State] :
    Func11Spec (hlc := hlc) := by
  unfold Func11Spec Project.Mergesort.Contracts.writeContractAt CallContract
    callExpr
  intro ptr requested bytes input output raised callerLocals stack code arity
    remainder controls calls s E Φ
  iintro ⟨Hruntime, ⟨Hstreams, ⟨Hslice, ⟨%hfacts, Hcont⟩⟩⟩⟩
  iopen_runtime Hruntime with ⟨Hmodule, Henv⟩
  iintuitionistic Henv
  simp only [List.cons_append, List.nil_append]
  iapply Wasm.SmallStep.twp_call Project.Mergesort.module 14
      Project.Mergesort.func11Def (by decide)
      Project.Mergesort.WrapperProof.func11_index $$ Hmodule
  iintro Hmodule
  simp [Project.Mergesort.func11Def, Project.Mergesort.func11,
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
  isplitl_exact Hstreams
  isplitl_exact Hslice
  isplitl_pureexact hfacts
  iintro Hruntime Hstreams Hslice
  iopen_runtime Hruntime with ⟨Hmodule, HenvInner⟩
  unfold ResumeWP resumeExpr
  wasm_twp_rebind Wasm.SmallStep.twp_returnFromCallFallthrough with Hmodule
  simp only [List.take_zero, List.nil_append]
  isimp only [RuntimeContext, ResumeWP, resumeExpr, List.nil_append] at Hcont
  iapply Hcont $$ [Hmodule HenvInner] Hstreams Hslice
  · iframe

/-- The generated recursive sorter satisfies the authoritative exact buffer
contract.  The adapter exposes the canonical word slices as the `arrayAt`
view used by the generated-body proof and then reconstructs `SortBuffers` with
the exact base/non-base scratch result. -/
theorem func2_correct [WasmSmallStepGS hlc Universal.State] :
    Func2Spec (hlc := hlc) := by
  unfold Func2Spec CallContract callExpr
  intro source n scratch scratchN input scratchInput callerLocals stack code
    arity remainder controls calls s E Φ
  iintro ⟨Hruntime, Hbuffers, %hlengths, Hcont⟩
  iopen_runtime Hruntime with ⟨Hmodule, Henv⟩
  isimp only [SortBuffers] at Hbuffers
  icases Hbuffers with ⟨HsourceWords, HscratchWords, %hbufferFacts⟩
  isimp only [WordSlice, Project.Mergesort.Representations.ByteSlice]
    at HsourceWords
  icases HsourceWords with ⟨%hsourceAlign, %hsourceStrict, HsourceBytes⟩
  isimp only [WordSlice, Project.Mergesort.Representations.ByteSlice]
    at HscratchWords
  icases HscratchWords with
    ⟨%hscratchAlign, %hscratchStrict, HscratchBytes⟩
  have hsourceStrictWords :
      source.toNat + 4 * input.length < UInt32.size := by
    simpa only [serialize_length] using hsourceStrict
  have hscratchStrictWords :
      scratch.toNat + 4 * scratchInput.length < UInt32.size := by
    simpa only [serialize_length] using hscratchStrict
  have hdisjoint := hbufferFacts.2
  unfold MemRegion.Disjoint at hdisjoint
  ihave Hsource : arrayAt 0 source input $$ [HsourceBytes]
  · iapply (arrayAt_eq_wordCells source input).mpr
    iexact HsourceBytes
  ihave Hscratch : arrayAt 0 scratch scratchInput $$ [HscratchBytes]
  · iapply (arrayAt_eq_wordCells scratch scratchInput).mpr
    iexact HscratchBytes
  have hscratchStrictInput :
      scratch.toNat + 4 * input.length < UInt32.size := by
    rw [hbufferFacts.1]
    exact hscratchStrictWords
  have hlayout :
      Wasm.Examples.MergeSort.ValidLayout source scratch input.length := by
    unfold Wasm.Examples.MergeSort.ValidLayout
      Wasm.Examples.MergeSort.arrayByteRange
    dsimp only
    refine ⟨Nat.le_of_lt hsourceStrictWords,
      Nat.le_of_lt hscratchStrictInput, ?_⟩
    simpa only [hbufferFacts.1] using hdisjoint
  have hn : n = UInt32.ofNat input.length := by
    calc
      n = UInt32.ofNat n.toNat := UInt32.ofNat_toNat.symm
      _ = UInt32.ofNat input.length := by rw [hlengths.1]
  have hscratchN : scratchN = UInt32.ofNat input.length := by
    calc
      scratchN = UInt32.ofNat scratchN.toNat := UInt32.ofNat_toNat.symm
      _ = UInt32.ofNat scratchInput.length := by rw [hlengths.2]
      _ = UInt32.ofNat input.length := by rw [← hbufferFacts.1]
  rw [hn, hscratchN]
  simp only [List.cons_append, List.nil_append]
  iapply Project.Mergesort.SortProof.twp_sort source scratch input scratchInput
      hbufferFacts.1.symm hlayout hsourceStrictWords hscratchStrictInput
  isplitl_exact Hmodule
  isplitl_exact Hsource
  isplitl_exact Hscratch
  iintro %sorted %scratchResult %hsorted %hscratchLength
    %hscratchExact Hmodule Hsource Hscratch
  have hsortedLength : sorted.length = input.length :=
    hsorted.2.length_eq.symm
  ihave HsourceBytes : WordCells source sorted $$ [Hsource]
  · iapply (arrayAt_eq_wordCells source sorted).mp
    iexact Hsource
  ihave HscratchBytes : WordCells scratch scratchResult $$ [Hscratch]
  · iapply (arrayAt_eq_wordCells scratch scratchResult).mp
    iexact Hscratch
  ihave HsourceWords : WordSlice source sorted $$ [HsourceBytes]
  · unfold WordSlice Project.Mergesort.Representations.ByteSlice
    isplitl_pureexact hsourceAlign
    isplitl []
    · ipureintro
      simpa only [serialize_length, hsortedLength] using hsourceStrict
    · iexact HsourceBytes
  ihave HscratchWords : WordSlice scratch scratchResult $$ [HscratchBytes]
  · unfold WordSlice Project.Mergesort.Representations.ByteSlice
    isplitl_pureexact hscratchAlign
    isplitl []
    · ipureintro
      simpa only [serialize_length, hscratchLength] using
        hscratchStrictInput
    · iexact HscratchBytes
  have hresultDisjoint : MemRegion.Disjoint
      ⟨source, 4 * sorted.length⟩
      ⟨scratch, 4 * scratchResult.length⟩ := by
    unfold MemRegion.Disjoint
    simpa only [hsortedLength, hscratchLength, hbufferFacts.1] using
      hdisjoint
  ihave HresultBuffers :
      SortBuffers source scratch sorted scratchResult $$
        [HsourceWords HscratchWords]
  · unfold SortBuffers
    iframe HsourceWords HscratchWords
    ipureexact ⟨by omega, hresultDisjoint⟩
  ihave HsortResult :
      SortResultBuffers source scratch input scratchInput sorted $$
        [HresultBuffers]
  · unfold SortResultBuffers
    rw [← hscratchExact]
    isplitl_exact HresultBuffers
    · ipureexact hsorted
  isimp only [RuntimeContext, ResumeWP, resumeExpr, List.nil_append] at Hcont
  iapply Hcont $$ [Hmodule Henv] HsortResult
  · iframe

end Project.Mergesort.ContractProofs
