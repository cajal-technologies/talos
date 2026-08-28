# Mergesort `func11` (absolute 14, `talos_stdio::write`)

Thin adapter `(pointer,length) -> ()`.  The shim call has top-first
`[length,pointer]`; the body produces direct-import `[pointer,length]`, which
invokes imported `stdio.write` as host `(length,pointer)`.  `func3` calls it
with four encoded bytes at frame
offset 268.  Its main contract appends exactly the represented bytes to
the output stream while preserving buffer ownership, input, and OOM marker.
The requested numeric length must equal the owned byte-list length; otherwise
the contract would not identify what the host reads.  It must also be positive:
an empty `ByteSlice` carries no physical in-bounds witness for an arbitrary
pointer, while the sole reachable call always supplies four.

The only caller writes `(frame+268,4)` once per sorted word after storing that
word into the slot.  The codec bridge must identify the physical four bytes
with the canonical public serialization.  Constant shim overhead plus host
work linear in length.
