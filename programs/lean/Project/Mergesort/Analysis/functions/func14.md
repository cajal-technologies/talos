# Mergesort `func14` (absolute 17, drop `Option<Vec<u8>>`)

> **Scope:** Documentation only. This body is excluded from the valid-input
> proof closure and receives no WP specification or proof. This card records
> low-level behavior and incoming edges solely as exclusion evidence. Every
> correctness obligation is discharged at the originating reachable caller
> guard.

Parameters identify an optional Vec-like value.  It checks the discriminant;
when storage is present and nonempty, it loads pointer/capacity and calls no-op
`func7`.  It is invoked only by panic machinery (`func22`).

Its sole incoming call is from excluded `func22`.  The effect would retire an
optional block through `func7`, but no representation or WP rule is required
for this unreachable path.  Local time is constant.
