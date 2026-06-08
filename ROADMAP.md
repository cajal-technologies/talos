# NEAR Host Environment Roadmap

This document tracks the temporary implementation plan for full NEAR host
environment support. Remove this file after the NEAR host environment is
implemented, covered by examples/proofs, and no longer needs a migration
roadmap.

## Goal

Support running and proving real NEAR smart contracts in the Lean Wasm
interpreter. The host model should be close enough to nearcore that proofs
about compiled contracts do not silently assume behavior that would trap or
diverge from chain execution.

## Current Baseline

- `NearState` models storage, registers, context/economics inputs, return data,
  logs, and symbolic crypto hooks.
- Real semantics exist for registers, basic I/O, return data, panic, and storage
  primitives.
- Name/signature import resolution exists for real modules that import a subset
  of NEAR functions.
- Real semantics exist for common context/economics APIs, logging, and symbolic
  crypto hooks.
- The hand-built `KvSetter` example validates a small register/input/storage
  pipeline plus host-regression checks with concrete `native_decide` checks.

## Work Items

1. Import resolution for real contracts
   - Done: add name/signature based resolution from a module's declared imports to a
     positional `HostEnv NearState`.
   - Keep canonical `nearImports` for hand-built examples, but do not require
     real compiled modules to import every NEAR function in canonical order.

2. Context API
   - Done: implement account id and signer key register outputs.
   - Done: implement block height/index, block timestamp, epoch height, and storage
     usage.
   - Add state fields for view-call mode and enforce `ProhibitedInView` where
     useful for proof fidelity.

3. Economics API
   - Done: implement account balance, locked balance, attached deposit, prepaid gas,
     used gas, validator stake, and total validator stake.
   - Done: model `u128` memory writes as 16 little-endian bytes.

4. Logging and miscellaneous API
   - Done: implement basic `log_utf8`, `log_utf16`, and `abort` semantics.
   - Decide how much UTF validation and NEAR log length checking belongs in the
     reference model versus in optional config checks.

5. Crypto and math API
   - Done: add symbolic hooks for `sha256`, `keccak256`, `keccak512`,
     `ripemd160`, `ecrecover`, `ed25519_verify`, and `random_seed`.
   - Still missing: symbolic support for alt-bn128 and BLS host functions.
   - Prefer opaque, pure function fields in `NearState`/`NearConfig` first, with
     deterministic executable implementations added only when needed.

6. Promises and cross-contract calls
   - Add promise/result/action data structures.
   - Implement `promise_create`, `promise_then`, `promise_and`, batch creation,
     batch actions, result access, `promise_return`, and yield/resume APIs.
   - Model promises as an action trace suitable for proving emitted receipts and
     callbacks.

7. Trie iterators
   - Implement `storage_iter_prefix`, `storage_iter_range`, and
     `storage_iter_next`.
   - Extend the storage model with finite key snapshots or iterator state while
     preserving the current function-style storage projection for frame proofs.

8. Limits and errors
   - Add configurable limits for key/value/return/log/register sizes and account
     id/public key validation.
   - Keep traps loud when behavior is unsupported or outside the modeled NEAR
     semantics.

9. Proof-facing API
   - Add host contracts and simp lemmas for each host category.
   - Prove memory framing lemmas for `readBytes`, `read32`, and `writeBytes`.
   - Turn `KvSetter.SetSpec` from a stated proposition plus concrete checks into
     a general theorem.

10. Real contract pipeline
   - Decode/import a compiled `near-sdk-rs` contract.
   - Resolve its imports through the NEAR resolver.
   - Prove at least one storage or access-control property end to end.
