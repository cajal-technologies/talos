import HexDecodeStdio.DecodeLoopMath
import HexDecodeStdio.ReadToEndGrowthFacts

namespace Submission.HexDecodeStdio

open Wasm Project.HexStdio Project.HexStdio.Spec
open Wasm.SmallStep

/-- Semantic state at the head of the decoder's collection loop.  `decoded`
is already stored in the vector, while `pending` is the just-decoded byte that
the next loop iteration appends before asking the pair iterator for another
byte. -/
structure DecodeLoopInv (input consumed remaining decoded : List UInt8)
    (store : MachineStore Universal.State)
    (inputCapacity data inputLen ptr capacity outLen bump : UInt32)
    (pending : UInt8) : Prop where
  input_split : input = consumed ++ remaining
  input_even : input.length % 2 = 0
  consumed_even : consumed.length % 2 = 0
  decoded_consumed : decode consumed = some (decoded ++ [pending])
  input_length : inputLen.toNat = input.length
  remaining_length :
    store.wasm.mem.read32 (loopIterator + 4) =
      UInt32.ofNat remaining.length
  iterator_error :
    store.wasm.mem.read32 (loopIterator + 16) = loopError
  iterator_chunk : store.wasm.mem.read32 (loopIterator + 8) = 2
  iterator_pointer :
    store.wasm.mem.read32 loopIterator =
      data + UInt32.ofNat consumed.length
  iterator_index :
    store.wasm.mem.read32 (loopIterator + 12) =
      UInt32.ofNat (consumed.length / 2)
  error_marker : store.wasm.mem.read32 loopError = 1114114
  input_bytes : store.wasm.mem.readBytes data.toNat input.length = input
  input_capacity : input.length ≤ inputCapacity.toNat
  input_before_output :
    data.toNat + inputCapacity.toNat ≤ ptr.toNat
  data_lower : 1054000 ≤ data.toNat
  vector_capacity : store.wasm.mem.read32 (coreFrame + 60) = capacity
  vector_pointer : store.wasm.mem.read32 (coreFrame + 64) = ptr
  vector_length : store.wasm.mem.read32 (coreFrame + 68) = outLen
  output_bytes : store.wasm.mem.readBytes ptr.toNat decoded.length = decoded
  output_length : outLen.toNat = decoded.length
  output_fits : outLen.toNat ≤ capacity.toNat
  capacity_pos : 0 < capacity.toNat
  capacity_min : 8 ≤ capacity.toNat
  output_end : ptr.toNat + capacity.toNat = bump.toNat
  output_bound : bump.toNat ≤ store.wasm.mem.pages * 65536
  bump_eq : store.wasm.mem.read32 1053960 = bump
  bump_signed : bump.toNat < 2 ^ 31
  runtime_module : store.runtime.currentModule = «module»
  runtime_host : store.runtime.currentHost = Universal.envFor «module»
  memory_cap : store.wasm.memoryCap store.runtime.currentModule 0 = 65536
  pages_lower : 17 ≤ store.wasm.mem.pages
  pages_upper : store.wasm.mem.pages ≤ 65536
  global_eq : globalAt? store 0 = some (.i32 coreFrame)
  status_capacity : store.wasm.mem.read32 decodeStatusVector = 0
  status_pointer : store.wasm.mem.read32 (decodeStatusVector + 4) = 1
  status_length : store.wasm.mem.read32 (decodeStatusVector + 8) = 0
  input_eq : store.wasm.host.stdio.input = []
  output_eq : store.wasm.host.stdio.output = []
  oom_eq : store.wasm.host.oom.raised = false

theorem DecodeLoopInv.remaining_even
    {input consumed remaining decoded : List UInt8}
    {store : MachineStore Universal.State}
    {inputCapacity data inputLen ptr capacity outLen bump : UInt32}
    {pending : UInt8}
    (h : DecodeLoopInv input consumed remaining decoded store inputCapacity
      data inputLen ptr capacity outLen bump pending) :
    remaining.length % 2 = 0 := by
  apply even_tail_of_append_even consumed remaining h.consumed_even
  simpa [h.input_split] using h.input_even

theorem DecodeLoopInv.input_small
    {input consumed remaining decoded : List UInt8}
    {store : MachineStore Universal.State}
    {inputCapacity data inputLen ptr capacity outLen bump : UInt32}
    {pending : UInt8}
    (h : DecodeLoopInv input consumed remaining decoded store inputCapacity
      data inputLen ptr capacity outLen bump pending) :
    input.length < 2 ^ 31 := by
  have hp := h.input_before_output
  have hb := h.bump_signed
  have hc := h.input_capacity
  have he := h.output_end
  omega

theorem DecodeLoopInv.consumed_le_input
    {input consumed remaining decoded : List UInt8}
    {store : MachineStore Universal.State}
    {inputCapacity data inputLen ptr capacity outLen bump : UInt32}
    {pending : UInt8}
    (h : DecodeLoopInv input consumed remaining decoded store inputCapacity
      data inputLen ptr capacity outLen bump pending) :
    consumed.length ≤ input.length := by
  rw [h.input_split]
  simp

theorem DecodeLoopInv.iteratorPointer_toNat
    {input consumed remaining decoded : List UInt8}
    {store : MachineStore Universal.State}
    {inputCapacity data inputLen ptr capacity outLen bump : UInt32}
    {pending : UInt8}
    (h : DecodeLoopInv input consumed remaining decoded store inputCapacity
      data inputLen ptr capacity outLen bump pending) :
    (data + UInt32.ofNat consumed.length).toNat =
      data.toNat + consumed.length := by
  apply Wasm.SepLogic.UInt32.add_ofNat_toNat_noWrap
  · have hs := h.input_small
    have hc := h.consumed_le_input
    norm_num [UInt32.size] at hs ⊢
    omega
  · have hdata : data.toNat + consumed.length ≤ bump.toNat := by
      calc
        data.toNat + consumed.length ≤
            data.toNat + inputCapacity.toNat := by
              have hc := h.input_capacity
              have hci := h.consumed_le_input
              omega
        _ ≤ ptr.toNat := h.input_before_output
        _ ≤ bump.toNat := by
          have he := h.output_end
          omega
    have hb := h.bump_signed
    norm_num [UInt32.size] at hb ⊢
    omega

theorem DecodeLoopInv.remainingWord_toNat
    {input consumed remaining decoded : List UInt8}
    {store : MachineStore Universal.State}
    {inputCapacity data inputLen ptr capacity outLen bump : UInt32}
    {pending : UInt8}
    (h : DecodeLoopInv input consumed remaining decoded store inputCapacity
      data inputLen ptr capacity outLen bump pending) :
    (UInt32.ofNat remaining.length).toNat = remaining.length := by
  apply UInt32.toNat_ofNat_of_lt'
  have hs := h.input_small
  norm_num [UInt32.size] at hs ⊢
  rw [h.input_split, List.length_append] at hs
  omega

theorem DecodeLoopInv.input_read
    {input consumed remaining decoded : List UInt8}
    {store : MachineStore Universal.State}
    {inputCapacity data inputLen ptr capacity outLen bump : UInt32}
    {pending : UInt8}
    (h : DecodeLoopInv input consumed remaining decoded store inputCapacity
      data inputLen ptr capacity outLen bump pending)
    (i : Nat) (hi : i < remaining.length) :
    store.wasm.mem.read8
        (data + UInt32.ofNat (consumed.length + i)) = remaining[i] := by
  have hci : consumed.length + i < input.length := by
    rw [h.input_split, List.length_append]
    omega
  have haddr : (data + UInt32.ofNat (consumed.length + i)).toNat =
      data.toNat + (consumed.length + i) := by
    apply Wasm.SepLogic.UInt32.add_ofNat_toNat_noWrap
    · exact lt_of_lt_of_le hci (by
        have hs := h.input_small
        norm_num [UInt32.size] at hs ⊢
        omega)
    · have hdata : data.toNat + (consumed.length + i) ≤ bump.toNat := by
        calc
          data.toNat + (consumed.length + i) ≤
              data.toNat + input.length := by omega
          _ ≤ data.toNat + inputCapacity.toNat := by
            exact Nat.add_le_add_left h.input_capacity _
          _ ≤ ptr.toNat := h.input_before_output
          _ ≤ bump.toNat := by
            have he := h.output_end
            omega
      have hb := h.bump_signed
      norm_num [UInt32.size] at hb ⊢
      omega
  have hget :
      (store.wasm.mem.readBytes data.toNat input.length)[consumed.length + i]? =
        some remaining[i] := by
    rw [h.input_bytes, h.input_split]
    rw [List.getElem?_append_right (by omega)]
    simp [hi]
  simp only [Mem.readBytes] at hget
  have hm : consumed.length + i <
      (List.map (fun i => store.wasm.mem.bytes (data.toNat + i))
        (List.range input.length)).length := by simp [hci]
  rw [List.getElem?_eq_getElem hm] at hget
  simp only [List.getElem_map, List.getElem_range] at hget
  change store.wasm.mem.bytes
      (data + UInt32.ofNat (consumed.length + i)).toNat = remaining[i]
  rw [haddr]
  exact Option.some.inj hget

theorem DecodeLoopInv.input_pair_reads
    {input consumed rest decoded : List UInt8}
    {store : MachineStore Universal.State}
    {inputCapacity data inputLen ptr capacity outLen bump : UInt32}
    {pending hi lo : UInt8}
    (h : DecodeLoopInv input consumed (hi :: lo :: rest) decoded store
      inputCapacity data inputLen ptr capacity outLen bump pending) :
    store.wasm.mem.read8 (data + UInt32.ofNat consumed.length) = hi ∧
    store.wasm.mem.read8
        ((data + UInt32.ofNat consumed.length) + 1) = lo := by
  constructor
  · convert h.input_read 0 (by simp) using 1 <;> simp
  · have hr := h.input_read 1 (by simp)
    have hadd :
        data + UInt32.ofNat (consumed.length + 1) =
          (data + UInt32.ofNat consumed.length) + 1 := by
      rw [UInt32.ofNat_add]
      simp [UInt32.add_assoc]
    rw [hadd] at hr
    simpa using hr

theorem DecodeLoopInv.append_bound
    {input consumed remaining decoded : List UInt8}
    {store : MachineStore Universal.State}
    {inputCapacity data inputLen ptr capacity outLen bump : UInt32}
    {pending : UInt8}
    (h : DecodeLoopInv input consumed remaining decoded store inputCapacity
      data inputLen ptr capacity outLen bump pending)
    (hspare : outLen ≠ capacity) :
    (ptr + outLen).toNat + 1 ≤ store.wasm.mem.pages * 65536 := by
  have hlt : outLen.toNat < capacity.toNat := by
    have hle := h.output_fits
    apply lt_of_le_of_ne hle
    intro heq
    apply hspare
    exact UInt32.toNat_inj.mp heq
  have hadd : (ptr + outLen).toNat = ptr.toNat + outLen.toNat := by
    rw [UInt32.toNat_add, Nat.mod_eq_of_lt]
    have he := h.output_end
    have hb := h.bump_signed
    norm_num at hb ⊢
    omega
  rw [hadd]
  have he := h.output_end
  have hp := h.output_bound
  norm_num at he ⊢
  omega

theorem DecodeLoopInv.consumed_length
    {input consumed remaining decoded : List UInt8}
    {store : MachineStore Universal.State}
    {inputCapacity data inputLen ptr capacity outLen bump : UInt32}
    {pending : UInt8}
    (h : DecodeLoopInv input consumed remaining decoded store inputCapacity
      data inputLen ptr capacity outLen bump pending) :
    consumed.length = 2 * (decoded.length + 1) := by
  have hlen := decode_some_length consumed (decoded ++ [pending])
    h.decoded_consumed
  simpa using hlen

theorem DecodeLoopInv.capacity_small_when_full
    {input consumed remaining decoded : List UInt8}
    {store : MachineStore Universal.State}
    {inputCapacity data inputLen ptr capacity outLen bump : UInt32}
    {pending : UInt8}
    (h : DecodeLoopInv input consumed remaining decoded store inputCapacity
      data inputLen ptr capacity outLen bump pending)
    (hfull : outLen = capacity) :
    2 * capacity.toNat + 32 < 2 ^ 31 := by
  have hc := h.consumed_length
  have hle := h.consumed_le_input
  have hs := h.input_small
  have hout := h.output_length
  have hinputCapacity := h.input_capacity
  have hbefore := h.input_before_output
  have hdata := h.data_lower
  have hend := h.output_end
  have hbump := h.bump_signed
  rw [hfull] at hout
  omega

theorem DecodeLoopInv.capacity_allocator_small_when_full
    {input consumed remaining decoded : List UInt8}
    {store : MachineStore Universal.State}
    {inputCapacity data inputLen ptr capacity outLen bump : UInt32}
    {pending : UInt8}
    (h : DecodeLoopInv input consumed remaining decoded store inputCapacity
      data inputLen ptr capacity outLen bump pending)
    (hfull : outLen = capacity) :
    2 * capacity.toNat + 65536 < 2 ^ 31 := by
  have hc := h.consumed_length
  have hle := h.consumed_le_input
  have hout := h.output_length
  have hinputCapacity := h.input_capacity
  have hbefore := h.input_before_output
  have hdata := h.data_lower
  have hend := h.output_end
  have hbump := h.bump_signed
  rw [hfull] at hout
  omega

end Submission.HexDecodeStdio
