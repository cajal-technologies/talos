# ByteEcho `func9` (absolute function 12, `default_alloc_error_hook`)

## Role and behavior

Installed default allocation-error handler.  It accepts alignment and size but
does not inspect them.  It stores byte `1` at address `1048584` and returns.

## Call sites

There are no direct calls.  The element segment installs it at table slot 1,
which `func8` may select.

## Contract ingredients

The main contract updates a named allocation-error marker cell predicate from
its old value to one while preserving framed resources.
