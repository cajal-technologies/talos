# Xor `func1` (absolute function 4, exported `xor`)

## Role and behavior

Public export `xor`.  It has no parameters or results and consists solely of a
call to `func0` followed by normal return.

## Contract ingredients

Its principal contract is the public function-level boundary and should be
proved only by applying `func0`'s main contract.  The top-level adequacy lemma
must in turn be derived uniquely from this contract.
