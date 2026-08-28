# Mergesort `func52` (absolute 55, `pad_integral::write_prefix`)

> **Scope:** Documentation only. This body is excluded from the valid-input
> proof closure and receives no WP specification or proof. This card records
> low-level behavior and incoming edges solely as exclusion evidence. Every
> correctness obligation is discharged at the originating reachable caller
> guard.

Five parameters describe Formatter/writer, sign, and optional prefix.  It
conditionally emits a sign character and prefix using indirect writer methods,
propagating the first nonzero status.  `func50` calls it up to three syntactic
times for different padding modes.

Its only incoming calls are from excluded `func50`.  Sign/prefix emission and
status propagation are dispatch evidence; no abstract Writer contract is
introduced.  Work is constant plus emitted output length.
