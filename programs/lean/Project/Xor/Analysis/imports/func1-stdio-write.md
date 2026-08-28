# Xor imported function 1 (`stdio.write`)

Type `(i32, i32) -> ()`.  Through `func7`, the Universal host reads the
specified source region and appends it exactly to output.  The well-formed path
writes one byte from shadow-stack offset 15: the XOR of the two input bytes.
Complexity is linear in the requested length.
