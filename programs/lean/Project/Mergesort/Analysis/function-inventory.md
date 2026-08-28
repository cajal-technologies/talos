# Function inventory and freshness

The body hash is the first 12 hexadecimal digits of SHA-256 over the canonical
function text printed by `wasm-tools print` from the frozen stripped Wasm.  The
module hash in [target.md](target.md) is authoritative; these short hashes are
impact-audit identifiers, not independent security claims.

| Local | Absolute | Type | Code bytes | Body hash | Role |
| ---: | ---: | --- | ---: | --- | --- |
| 0 | 3 | `6 i32 -> ()` | 182 | `0a3b7bc8b64b` | RawVec finish-grow |
| 1 | 4 | `5 i32 -> ()` | 173 | `4cbfccb2a201` | RawVec reserve |
| 2 | 5 | `4 i32 -> ()` | 567 | `a8d39ea480c7` | recursive merge sort |
| 3 | 6 | `() -> ()` | 788 | `75d35ac9960e` | exported stream driver |
| 4 | 7 | `() -> ()` | 3 | `cb4b279e575d` | allocation marker |
| 5 | 8 | `2 i32 -> i32` | 123 | `0e8f4a489b61` | alloc |
| 6 | 9 | `() -> ()` | 9 | `403954e8a83b` | abort OOM |
| 7 | 10 | `3 i32 -> ()` | 2 | `2a07c26c8c8e` | no-op dealloc |
| 8 | 11 | `4 i32 -> i32` | 157 | `ded834c88f4b` | realloc |
| 9 | 12 | `2 i32 -> i32` | 146 | `74772af42f9f` | alloc-zeroed |
| 10 | 13 | `2 i32 -> i32` | 12 | `60a21918b85e` | read shim |
| 11 | 14 | `2 i32 -> ()` | 12 | `8a08ea5ad33f` | write shim |
| 12 | 15 | `2 i32 -> i32` | 9 | `353fc049c8b9` | start panic |
| 13 | 16 | `5 i32 -> ()` | 173 | `fb5643be0c9e` | String RawVec reserve |
| 14 | 17 | `2 i32 -> ()` | 35 | `1d5f7996701b` | drop Option Vec |
| 15 | 18 | `i32 -> ()` | 32 | `4081938349c6` | drop String |
| 16 | 19 | `i32 -> ()` | 34 | `f2dc85e61b5e` | drop format payload |
| 17 | 20 | `i32 -> ()` | 11 | `ffad4c83e125` | OOM backtrace shim |
| 18 | 21 | `i32 -> ()` | 44 | `506a3b6ba148` | Rust OOM closure |
| 19 | 22 | `i32 -> ()` | 11 | `a32eb9138a6e` | panic backtrace shim |
| 20 | 23 | `i32 -> ()` | 154 | `9141503b8c53` | panic handler closure |
| 21 | 24 | `6 i32 -> ()` | 182 | `83f6107c9ca9` | specialized finish-grow |
| 22 | 25 | `5 i32 -> ()` | 274 | `bd1d844b9c60` | panic with hook |
| 23 | 26 | `2 i32 -> ()` | 13 | `04f1b39b1593` | default allocation hook |
| 24 | 27 | `2 i32 -> ()` | 14 | `a4b201f0330e` | rust panic |
| 25 | 28 | `() -> ()` | 3 | `229620646005` | abort/unreachable |
| 26 | 29 | `i32 -> ()` | 56 | `647a74d52f0b` | begin unwind |
| 27 | 30 | `2 i32 -> ()` | 13 | `9492211a1a11` | alloc-error handler |
| 28 | 31 | `2 i32 -> ()` | 47 | `19e76e55ffa6` | std Rust OOM |
| 29 | 32 | `i32 -> i32` | 94 | `e057412b3beb` | panic-count increase |
| 30 | 33 | `2 i32 -> ()` | 30 | `f6a4d1158f90` | String TypeId |
| 31 | 34 | `2 i32 -> ()` | 30 | `0f6eb5e9c501` | str TypeId |
| 32 | 35 | `2 i32 -> i32` | 72 | `b6d11eba8a06` | format-payload Display |
| 33 | 36 | `2 i32 -> ()` | 20 | `73c04aa0eed8` | static payload get |
| 34 | 37 | `2 i32 -> ()` | 12 | `d15b3074fbf4` | static payload as-str |
| 35 | 38 | `2 i32 -> ()` | 84 | `02dc250058ca` | static payload take-box |
| 36 | 39 | `2 i32 -> i32` | 20 | `e564b0ecad26` | static payload Display |
| 37 | 40 | `2 i32 -> i32` | 297 | `8437894fa3b3` | String write-char |
| 38 | 41 | `3 i32 -> i32` | 94 | `c0969ad53c6b` | String write-str |
| 39 | 42 | `2 i32 -> ()` | 165 | `899564fd67e0` | format-payload get |
| 40 | 43 | `2 i32 -> ()` | 265 | `42c5a862c466` | format-payload take-box |
| 41 | 44 | `2 i32 -> ()` | 9 | `0de440f62793` | format-payload as-str |
| 42 | 45 | `3 i32 -> i32` | 20 | `293a5deaf215` | String write-fmt |
| 43 | 46 | `2 i32 -> ()` | 28 | `cc56e4936b04` | RawVec handle-error |
| 44 | 47 | `2 i32 -> ()` | 13 | `9ab5da0d6efa` | handle alloc error |
| 45 | 48 | `() -> ()` | 23 | `7eff48967159` | capacity overflow |
| 46 | 49 | `4 i32 -> ()` | 333 | `9d7ab61e8cd5` | slice-index fail |
| 47 | 50 | `3 i32 -> ()` | 71 | `14578921679b` | panic-fmt |
| 48 | 51 | `4 i32 -> i32` | 628 | `1b70052b0fb6` | core fmt write |
| 49 | 52 | `3 i32 -> ()` | 95 | `a9f8bd3d6554` | bounds panic |
| 50 | 53 | `6 i32 -> i32` | 796 | `96ce5950c544` | pad-integral |
| 51 | 54 | `2 i32 -> i32` | 875 | `d6fbc502b0f6` | count UTF-8 chars |
| 52 | 55 | `5 i32 -> i32` | 73 | `dcd9ed19e284` | write sign/prefix |
| 53 | 56 | `3 i32 -> i32` | 30 | `a1ea7da7d5cd` | Formatter write-str |
| 54 | 57 | `2 i32 -> i32` | 319 | `ccab85b0dda6` | u32 Display |
| 55 | 58 | `3 i32 -> ()` | 95 | `3153a62b55cb` | slice length mismatch |

Each row links by local index to `functions/funcN.md`.  Exact parameter/local
vectors remain in generated `funcNDef`; the function card gives semantic names
and memory roles.
