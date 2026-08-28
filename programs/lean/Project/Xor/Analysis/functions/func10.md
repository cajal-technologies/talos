# Xor `func10` (absolute function 13, `default_alloc_error_hook`)

## Role and behavior

Installed default allocation-error handler.  It ignores its `(alignment, size)`
parameters, stores byte one at address `1048584`, and returns.

## Call sites and contract

It has no direct call sites; table slot one references it.  Its main contract
updates a named allocation-error marker cell while preserving framed resources.
