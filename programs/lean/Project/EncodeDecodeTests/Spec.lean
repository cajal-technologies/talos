import Project.EncodeDecodeTests.Program
import Project.EncodeDecode.Spec

/-!
# Specification for `encode_decode_tests` — reuse of the frame codec

Every export here is *client code* that calls the `encode_decode` codec. The
proofs do **no memory reasoning of their own**: each crosses its `call` with the
module-parametric `encodeTerminates` / `decodeTerminates` proved once in
`Project.EncodeDecode.Spec`. Discharging the codec's shape hypotheses is `rfl`
(the codec bodies are linked into this module verbatim; only the callee indices
differ — `decode` = func5 calling `load32` = func3, `encode` = func6 calling
`store32` = func4). That is the whole point of the corpus: verifying a program
that *uses* the codec costs a couple of tactics, not a fresh proof.
-/

namespace Project.EncodeDecodeTests.Spec

open Wasm Wasm.Codec Project.EncodeDecode.Spec

set_option maxRecDepth 1048576
set_option linter.unusedSimpArgs false

/-- The codec bodies linked into this module match the canonical parametric
bodies at their local callee indices. -/
example : func5 = decodeBody 3 := rfl
example : func6 = encodeBody 4 := rfl

/-! ## `decode_frame` — forwards to `decode` -/

@[spec_of "rust-exported" "encode_decode_tests::decode_frame"]
def DecodeFrameSpec : Prop :=
  ∀ (env : HostEnv Unit) (st : Store Unit) (src_ptr src_len dst_ptr dst_cap : UInt32),
    st.globals.globals[0]? = some (.i32 1048576) →
    st.mem.pages ≤ 65536 →
    4 ≤ src_len.toNat →
    (st.mem.read32 src_ptr).toNat + 4 ≤ src_len.toNat →
    (st.mem.read32 src_ptr).toNat ≤ dst_cap.toNat →
    src_ptr.toNat + src_len.toNat ≤ st.mem.pages * 65536 →
    dst_ptr.toNat + (st.mem.read32 src_ptr).toNat ≤ st.mem.pages * 65536 →
    1048576 ≤ src_ptr.toNat →
    1048576 ≤ dst_ptr.toNat →
    TerminatesWith env «module» 0 st [.i32 dst_cap, .i32 dst_ptr, .i32 src_len, .i32 src_ptr]
      (fun st' rs => rs = [.i64 (UInt64.ofNat (st.mem.read32 src_ptr).toNat)]
        ∧ (∀ k : UInt32, k.toNat < (st.mem.read32 src_ptr).toNat →
            st'.mem.read8 (dst_ptr + k) = st.mem.read8 (src_ptr + 4 + k))
        ∧ st'.globals = st.globals
        ∧ st'.mem.pages = st.mem.pages)

@[proves Project.EncodeDecodeTests.Spec.DecodeFrameSpec]
theorem decode_frame_correct : DecodeFrameSpec := by
  intro env st src_ptr src_len dst_ptr dst_cap hg hpg h4 hn hnd hsB hdB hs hd
  refine TerminatesWith.of_returns_wp (f := func0Def)
    (rs := [.i64 (UInt64.ofNat (st.mem.read32 src_ptr).toNat)]) rfl rfl ?_ rfl
  simp only [func0Def]
  unfold func0 Returns
  simp only [wp_simp, wp_entry, wp_reduce]
  refine wp_call_tw (decodeTerminates st src_ptr src_len dst_ptr dst_cap
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl hg hpg h4 hn hnd hsB hdB hs hd) ?_
  rintro st' vs ⟨rfl, hpay, hglob, hpages⟩
  simp only [wp_simp, wp_entry, wp_reduce]
  exact ⟨_, rfl, hpay, hglob, hpages⟩

/-! ## `encode_frame` — forwards to `encode` -/

@[spec_of "rust-exported" "encode_decode_tests::encode_frame"]
def EncodeFrameSpec : Prop :=
  ∀ (env : HostEnv Unit) (st : Store Unit) (src_ptr src_len dst_ptr : UInt32),
    st.globals.globals[0]? = some (.i32 1048576) →
    st.mem.pages ≤ 65536 →
    dst_ptr.toNat + 4 + src_len.toNat ≤ st.mem.pages * 65536 →
    src_ptr.toNat + src_len.toNat ≤ st.mem.pages * 65536 →
    1048576 ≤ dst_ptr.toNat →
    1048576 ≤ src_ptr.toNat →
    (src_ptr.toNat + src_len.toNat ≤ dst_ptr.toNat
      ∨ dst_ptr.toNat + 4 + src_len.toNat ≤ src_ptr.toNat) →
    TerminatesWith env «module» 1 st [.i32 dst_ptr, .i32 src_len, .i32 src_ptr]
      (fun st' rs => rs = [.i32 (4 + src_len)]
        ∧ st'.mem.read32 dst_ptr = src_len
        ∧ (∀ k : UInt32, k.toNat < src_len.toNat →
            st'.mem.read8 (dst_ptr + 4 + k) = st.mem.read8 (src_ptr + k))
        ∧ st'.globals = st.globals
        ∧ st'.mem.pages = st.mem.pages)

@[proves Project.EncodeDecodeTests.Spec.EncodeFrameSpec]
theorem encode_frame_correct : EncodeFrameSpec := by
  intro env st src_ptr src_len dst_ptr hg hpg hdB hsB hd hs hdisj
  refine TerminatesWith.of_returns_wp (f := func1Def) (rs := [.i32 (4 + src_len)]) rfl rfl ?_ rfl
  simp only [func1Def]
  unfold func1 Returns
  simp only [wp_simp, wp_entry, wp_reduce]
  refine wp_call_tw (encodeTerminates st src_ptr src_len dst_ptr
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl hg hpg hdB hsB hd hs hdisj) ?_
  rintro st' vs ⟨rfl, hread, hpay, hglob, hpages⟩
  simp only [wp_simp, wp_entry, wp_reduce]
  exact ⟨_, rfl, hread, hpay, hglob, hpages⟩

end Project.EncodeDecodeTests.Spec
