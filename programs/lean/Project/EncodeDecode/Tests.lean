import Project.EncodeDecode.Spec

/-!
# `encode_decode` — reuse demo: round-trip and concrete frames

This file proves *client-level* facts about the codec **without doing any
interpreter reasoning of its own** — it only plugs the two proven exports
(`encode_correct` / `decode_correct`) into `TerminatesWith.mono`. That is the
whole point of the corpus: once a function is verified, using it costs a couple
of tactic lines.

* `encode_decode_roundtrip` — *for every input buffer*, running `encode` then
  feeding the resulting frame to `decode` reproduces the original payload byte
  for byte. The proof is two `TerminatesWith.mono`s and some address arithmetic;
  the codec's memory reasoning was all discharged once, in `Spec.lean`.
-/

namespace Project.EncodeDecode.Spec

open Wasm

/-- **Round-trip correctness.** `encode` the `len`-byte buffer at `src` into a
frame at `mid`, then `decode` that frame into `dst`: the bytes at `dst` equal the
original bytes at `src`. Buffers live above the 1 MiB scratch region and fit in
memory; `src` and the `mid` frame are disjoint (`encode`'s contract). `dst` may
overlap freely — `decode` is memmove-safe. -/
theorem encode_decode_roundtrip (env : HostEnv Unit) (st : Store Unit)
    (src mid dst len cap : UInt32)
    (hg   : st.globals.globals[0]? = some (.i32 1048576))
    (hpg  : st.mem.pages ≤ 65536)
    (hmB  : mid.toNat + 4 + len.toNat ≤ st.mem.pages * 65536)
    (hsB  : src.toNat + len.toNat ≤ st.mem.pages * 65536)
    (hdB  : dst.toNat + len.toNat ≤ st.mem.pages * 65536)
    (hcap : len.toNat ≤ cap.toNat)
    (hm   : 1048576 ≤ mid.toNat)
    (hs   : 1048576 ≤ src.toNat)
    (hd   : 1048576 ≤ dst.toNat)
    (hsm  : src.toNat + len.toNat ≤ mid.toNat ∨ mid.toNat + 4 + len.toNat ≤ src.toNat) :
    TerminatesWith env «module» 3 st [.i32 mid, .i32 len, .i32 src]
      (fun st1 _ =>
        TerminatesWith env «module» 2 st1 [.i32 cap, .i32 dst, .i32 (4 + len), .i32 mid]
          (fun st2 _ => ∀ k : UInt32, k.toNat < len.toNat →
            st2.mem.read8 (dst + k) = st.mem.read8 (src + k))) := by
  have h4len : (4 + len).toNat = 4 + len.toNat := by
    simp only [UInt32.toNat_add, show (4 : UInt32).toNat = 4 from rfl]; omega
  -- Run `encode`, then consume its post to run `decode` and finish.
  refine TerminatesWith.mono
    (encode_correct env st src len mid hg hpg hmB hsB hm hs hsm) ?_
  intro st1 _ hpost
  have hpre := hpost.2.1
  have hpay1 := hpost.2.2.1
  have hglob1 := hpost.2.2.2.1
  have hpages1 := hpost.2.2.2.2
  have hg1 : st1.globals.globals[0]? = some (.i32 1048576) := by rw [hglob1]; exact hg
  refine TerminatesWith.mono
    (decode_correct env st1 mid (4 + len) dst cap hg1
      (by rw [hpages1]; exact hpg)              -- pages ≤ 65536
      (by rw [h4len]; omega)                    -- 4 ≤ (4+len)
      (by rw [hpre, h4len]; omega)              -- read32 mid + 4 ≤ (4+len)
      (by rw [hpre]; exact hcap)                -- read32 mid ≤ cap
      (by rw [hpages1, h4len]; omega)           -- mid + (4+len) ≤ pages
      (by rw [hpages1, hpre]; omega)            -- dst + read32 mid ≤ pages
      hm hd) ?_
  intro st2 _ hpost2
  have hpay2 := hpost2.2.1
  intro k hk
  rw [hpay2 k (by rw [hpre]; exact hk)]
  exact hpay1 k hk

end Project.EncodeDecode.Spec
