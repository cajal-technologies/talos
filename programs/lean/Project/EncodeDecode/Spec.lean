import Project.EncodeDecode.Program
import Interpreter.Wasm.Wp.Call

/-!
# Specification for `encode_decode`

A *frame* is a 4-byte little-endian `u32` length followed by that many payload
bytes. `encode` writes a frame; `decode` reads one back. The exports are proved
bottom-up, reusing the `RustStd/Mem.lean` framing trunk (including the new
`memory.copy` read-back lemmas).

`func0`/`func1` are the `load32`/`store32` helpers that opt-0 outlines from
`read_unaligned`/`write_unaligned`; `func3` = `encode`, `func2` = `decode`.
-/

namespace Project.EncodeDecode.Spec

open Wasm Wasm.Codec

/-- The codec bodies emitted for this module are the canonical parametric bodies
from `CodeLib.Codec.Frame` (`load32` = func0, `store32` = func1), so the helpers
and exports below are `rfl`-discharged instantiations of the reusable theorems. -/
example : func2 = decodeBody 0 := rfl
example : func3 = encodeBody 1 := rfl

/-- `func1` — the codec module's own `store32` helper: `store32Terminates` at
`«module»`'s function 1. -/
theorem func1_store (env : HostEnv Unit) (st : Store Unit) (p0 p1 p2 g0 : UInt32)
    (hg   : st.globals.globals[0]? = some (.i32 g0))
    (hg16 : 16 ≤ g0.toNat)
    (hgB  : g0.toNat ≤ st.mem.pages * 65536)
    (hp0  : p0.toNat + 4 ≤ st.mem.pages * 65536) :
    TerminatesWith env «module» 1 st [.i32 p2, .i32 p1, .i32 p0]
      (fun st' rs => rs = []
        ∧ st'.mem = (st.mem.write32 (g0 - 16 + 12) p1).write32 p0 p1
        ∧ st'.globals = st.globals) :=
  store32Terminates st p0 p1 p2 g0 rfl rfl rfl rfl rfl hg hg16 hgB hp0

/-- `func0` — the codec module's own `load32` helper: `load32Terminates` at
`«module»`'s function 0. -/
theorem func0_load (env : HostEnv Unit) (st : Store Unit) (p0 p1 g0 : UInt32)
    (hg   : st.globals.globals[0]? = some (.i32 g0))
    (hg16 : 16 ≤ g0.toNat)
    (hgB  : g0.toNat ≤ st.mem.pages * 65536)
    (hp0  : p0.toNat + 4 ≤ st.mem.pages * 65536) :
    TerminatesWith env «module» 0 st [.i32 p1, .i32 p0]
      (fun st' rs => rs = [.i32 (st.mem.read32 p0)]
        ∧ st'.mem = (st.mem.write32 (g0 - 16 + 8) (st.mem.read32 p0)).write32
            (g0 - 16 + 12) (st.mem.read32 p0)
        ∧ st'.globals = st.globals) :=
  load32Terminates st p0 p1 g0 rfl rfl rfl rfl rfl hg hg16 hgB hp0

/-- **`encode` is correct.** Writes the length prefix (`store32`, via `func1`)
then the payload (`memory.copy`), returning `4 + src_len`.

The `hdisj` precondition says the source and destination frames do not overlap
(`copy_nonoverlapping`'s contract); the addressability + `pages ≤ 65536` bounds
rule out `UInt32` address wraparound; global 0 is the shadow-stack pointer at
its initial value. -/
@[spec_of "rust-exported" "encode_decode::encode"]
def EncodeSpec : Prop :=
  ∀ (env : HostEnv Unit) (st : Store Unit) (src_ptr src_len dst_ptr : UInt32),
    st.globals.globals[0]? = some (.i32 1048576) →
    st.mem.pages ≤ 65536 →
    dst_ptr.toNat + 4 + src_len.toNat ≤ st.mem.pages * 65536 →
    src_ptr.toNat + src_len.toNat ≤ st.mem.pages * 65536 →
    1048576 ≤ dst_ptr.toNat →
    1048576 ≤ src_ptr.toNat →
    (src_ptr.toNat + src_len.toNat ≤ dst_ptr.toNat
      ∨ dst_ptr.toNat + 4 + src_len.toNat ≤ src_ptr.toNat) →
    TerminatesWith env «module» 3 st [.i32 dst_ptr, .i32 src_len, .i32 src_ptr]
      (fun st' rs => rs = [.i32 (4 + src_len)]
        ∧ st'.mem.read32 dst_ptr = src_len
        ∧ (∀ k : UInt32, k.toNat < src_len.toNat →
            st'.mem.read8 (dst_ptr + 4 + k) = st.mem.read8 (src_ptr + k))
        ∧ st'.globals = st.globals
        ∧ st'.mem.pages = st.mem.pages)

@[proves Project.EncodeDecode.Spec.EncodeSpec]
theorem encode_correct : EncodeSpec :=
  fun _ st src_ptr src_len dst_ptr hg hpg hdB hsB hd hs hdisj =>
    encodeTerminates st src_ptr src_len dst_ptr rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
      hg hpg hdB hsB hd hs hdisj

/-- **`decode` is correct.** Reads the length prefix (`load32`, via `func0`),
validates the frame, and copies the payload (`memory.copy`), returning the
payload length. Error branches are dead under the frame-valid preconditions:
`h4`/`hn` say the frame's length prefix is present and consistent, `hnd` that
the destination has capacity, and the addressability bounds keep every access
in range. -/
@[spec_of "rust-exported" "encode_decode::decode"]
def DecodeSpec : Prop :=
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
    TerminatesWith env «module» 2 st [.i32 dst_cap, .i32 dst_ptr, .i32 src_len, .i32 src_ptr]
      (fun st' rs => rs = [.i64 (UInt64.ofNat (st.mem.read32 src_ptr).toNat)]
        ∧ (∀ k : UInt32, k.toNat < (st.mem.read32 src_ptr).toNat →
            st'.mem.read8 (dst_ptr + k) = st.mem.read8 (src_ptr + 4 + k))
        ∧ st'.globals = st.globals
        ∧ st'.mem.pages = st.mem.pages)

@[proves Project.EncodeDecode.Spec.DecodeSpec]
theorem decode_correct : DecodeSpec :=
  fun _ st src_ptr src_len dst_ptr dst_cap hg hpg h4 hn hnd hsB hdB hs hd =>
    decodeTerminates st src_ptr src_len dst_ptr dst_cap rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
      hg hpg h4 hn hnd hsB hdB hs hd

end Project.EncodeDecode.Spec
