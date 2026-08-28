# Xor `func7` (absolute function 10, `talos_stdio::write`)

## Role and interface

Standard-output adapter with parameters `(ptr, length)`.  It reverses the
parameters for imported `stdio.write` and returns no value.

## Call sites

`func0` calls it with the one-byte stack-frame region at `sp + 15` after both
input bytes are available.

## Contract ingredients

Its main contract appends exactly the represented region to host output while
preserving buffer ownership and contents.
