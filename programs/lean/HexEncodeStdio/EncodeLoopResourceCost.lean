import HexEncodeStdio.EncodeResourceCost

/-! Whole generated hexadecimal loop, with a numerical bound over its actual trace. -/
namespace Project.HexEncodeStdio.EncodeLoopResourceCost

open Wasm Wasm.SmallStep Project.HexStdio
open EncodeResourceCost

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

def memoryStore (store : MachineStore Universal.State) (memory : Mem) : MachineStore Universal.State :=
  {store with wasm := {store.wasm with mem := memory}}

def doneConfig (ctx : Context) (store : MachineStore Universal.State)
    (position destination : UInt32) : Config Universal.State :=
  ⟨.running ⟨encodeLocals ctx.result position sentinel 1048512 1 1 destination ctx.tmp1 ctx.tmp2,
    ctx.afterLoop,ctx.arity,ctx.remainder,ctx.controls,ctx.calls⟩,store⟩

/-- Consume the current high/low digit pair and every remaining source byte.
The cursor distance decreases along actual iterator calls; no future execution
is supplied. The exact work is 156 per additional byte plus 132 for the final pair. -/
theorem pair_loop_cost (ctx : Context) (store : MachineStore Universal.State)
    (p remaining : Nat) (capacity output cursor finish high low width ascii destination : UInt32)
    (hmodule : store.runtime.currentModule=Project.HexStdio.module)
    (fields : Fields store.wasm.mem capacity output (UInt32.ofNat p) low cursor finish)
    (table : AsciiTable store.wasm.mem)
    (hhigh : high<128) (hlow : low<128)
    (hcursor : cursor.toNat+remaining=finish.toNat)
    (hcursorLower : 1048592 ≤ cursor.toNat)
    (hsource : finish.toNat≤store.wasm.mem.pages*65536)
    (hcapacity : p+2*(remaining+1)≤capacity.toNat)
    (houtput : 1048592 ≤ output.toNat)
    (hphysical : output.toNat+(p+2*(remaining+1))≤store.wasm.mem.pages*65536)
    (hnowrap : output.toNat+(p+2*(remaining+1))<UInt32.size) :
    ∃ memory finalDestination trace,
      CostedSteps CostedStdIO.work
        (headConfig ctx store (UInt32.ofNat p) high width ascii destination) trace
        (doneConfig ctx (memoryStore store memory) (UInt32.ofNat (p+2*(remaining+1))) finalDestination)
        (156*remaining+132) ∧
      (∀ kind ∈ trace,HostPrimaryMemoryKind kind) ∧
      Fields memory capacity output (UInt32.ofNat (p+2*(remaining+1))) sentinel finish finish ∧
      Framed store.wasm.mem memory output := by
  induction remaining generalizing store p cursor high low width ascii destination with
  | zero =>
    have hc : cursor=finish := UInt32.toNat_inj.mp (by omega)
    subst cursor
    obtain ⟨a,asteps,aprimary,pairFields,pairFrame⟩ := byte_pair_cost ctx store p capacity output finish finish
      high low width ascii destination hmodule fields hhigh hlow (by omega) houtput (by omega) (by omega)
    let paired := pairStore store output (UInt32.ofNat p) high low
    let final := iteratorResetStore paired 1048528
    obtain ⟨b,bsteps,bprimary⟩ := iterator_end_cost paired
      (encodeLocals ctx.result (UInt32.ofNat (p+2)) low 1048512 1 1 (output+UInt32.ofNat (p+1)) ctx.tmp1 ctx.tmp2)
      [] (loopCallTail.drop 1) ctx.arity ctx.remainder
      (TotalEncodeLoop.encodeLoopFrame ctx.afterLoop::ctx.controls) ctx.calls 1048528 finish hmodule
      pairFields.saved pairFields.cursor pairFields.finish
      (by change 1048528+12≤store.wasm.mem.pages*65536;omega) (by decide)
    obtain ⟨c,csteps,cprimary⟩ := exit_cost final ctx.result (UInt32.ofNat (p+2)) low 1 1
      (output+UInt32.ofNat (p+1)) ctx.tmp1 ctx.tmp2 ctx.arity ctx.remainder ctx.afterLoop ctx.controls ctx.calls
    have full := (asteps.trans bsteps).trans csteps
    refine ⟨final.wasm.mem,output+UInt32.ofNat (p+1),(a++b)++c,?_,?_,?_,?_⟩
    · simpa only [doneConfig,memoryStore,final,paired,pairStore,asciiStore,iteratorResetStore,
        Nat.zero_add,Nat.add_zero,Nat.mul_zero,Nat.mul_one] using full
    · intro kind member
      simp only [List.mem_append] at member
      rcases member with (member|member)|member
      · exact aprimary kind member
      · exact bprimary kind member
      · exact cprimary kind member
    · simpa only [Nat.zero_add,Nat.mul_one] using
        low_fields paired capacity output (UInt32.ofNat (p+2)) sentinel finish finish pairFields
    · exact pairFrame.trans (low_framed paired output)
  | succ remaining ih =>
    obtain ⟨a,asteps,aprimary,pairFields,pairFrame⟩ := byte_pair_cost ctx store p capacity output cursor finish
      high low width ascii destination hmodule fields hhigh hlow (by omega) houtput (by omega) (by omega)
    let paired := pairStore store output (UInt32.ofNat p) high low
    let byte := paired.wasm.mem.read8 cursor
    let lowByte := paired.wasm.mem.read8 (1048576+UInt32.ofNat (byte.toNat%16))
    let highByte := paired.wasm.mem.read8 (1048576+UInt32.ofNat (byte.toNat/16))
    let advanced := iteratorHighStore paired 1048528 cursor lowByte
    have tablePaired := pairFrame.ascii table houtput
    have lowAscii : lowByte.toUInt32<128 := tablePaired _ (Nat.mod_lt _ (by decide))
    have highAscii : highByte.toUInt32<128 := tablePaired _ (by have := byte.toNat_lt;omega)
    have hcne : cursor≠finish := by intro equality;rw [equality] at hcursor;omega
    obtain ⟨b,bsteps,bprimary⟩ := iterator_high_cost paired
      (encodeLocals ctx.result (UInt32.ofNat (p+2)) low 1048512 1 1 (output+UInt32.ofNat (p+1)) ctx.tmp1 ctx.tmp2)
      [] (loopCallTail.drop 1) ctx.arity ctx.remainder
      (TotalEncodeLoop.encodeLoopFrame ctx.afterLoop::ctx.controls) ctx.calls 1048528 cursor finish byte lowByte highByte
      hmodule pairFields.saved pairFields.cursor pairFields.finish pairFields.table rfl rfl rfl hcne
      (by decide) hcursorLower (by change cursor.toNat+1≤store.wasm.mem.pages*65536;omega)
    obtain ⟨c,csteps,cprimary⟩ := continue_cost advanced ctx.result (UInt32.ofNat (p+2)) low highByte.toUInt32
      1 1 (output+UInt32.ofNat (p+1)) ctx.tmp1 ctx.tmp2 ctx.arity ctx.remainder ctx.afterLoop ctx.controls ctx.calls
      (ascii_ne_sentinel highAscii)
    have advancedFields := high_fields paired capacity output (UInt32.ofNat (p+2)) sentinel cursor finish lowByte pairFields
    have advancedFrame := high_framed paired output cursor lowByte
    have cursorNext : (cursor+1).toNat=cursor.toNat+1 := by
      have ht : cursor.toNat+1<UInt32.size := by have := finish.toNat_lt;change cursor.toNat+1<4294967296;omega
      simpa only [show (UInt32.ofNat 1:UInt32)=1 from rfl] using offset_toNat cursor 1 ht
    obtain ⟨memory,last,d,dsteps,dprimary,finalFields,finalFrame⟩ := ih advanced (p+2) (cursor+1)
      highByte.toUInt32 lowByte.toUInt32 1 1 (output+UInt32.ofNat (p+1)) hmodule advancedFields
      (advancedFrame.ascii tablePaired houtput) highAscii lowAscii (by rw [cursorNext];omega)
      (by rw [cursorNext];omega) hsource (by omega)
      (by change output.toNat+(p+2+2*(remaining+1))≤store.wasm.mem.pages*65536;omega) (by omega)
    have full := ((asteps.trans bsteps).trans csteps).trans dsteps
    have endPosition : p+2+2*(remaining+1)=p+2*(remaining+1+1) := by omega
    refine ⟨memory,last,((a++b)++c)++d,?_,?_,?_,?_⟩
    · simpa only [doneConfig,memoryStore,advanced,paired,iteratorHighStore,pairStore,asciiStore,
        iteratorResetStore,Nat.succ_eq_add_one,endPosition,
        show 104+48+4+(156*remaining+132)=156*(remaining+1)+132 by omega] using full
    · intro kind member
      simp only [List.mem_append] at member
      rcases member with ((member|member)|member)|member
      · exact aprimary kind member
      · exact bprimary kind member
      · exact cprimary kind member
      · exact dprimary kind member
    · simpa only [Nat.succ_eq_add_one,endPosition] using finalFields
    · exact (pairFrame.trans advancedFrame).trans finalFrame

end Project.HexEncodeStdio.EncodeLoopResourceCost
