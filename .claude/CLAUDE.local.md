\# personal rules (talos)



\## behavior

do not guess silently. state assumptions before acting.

if anything is ambiguous, list interpretations and ask.

if a simpler solution exists, say so before implementing.

before any pattern decision, check if the codebase already does it.

if found, use that. if not, stop and ask.



\## code style

minimum code to solve the problem. no extra features.

no abstractions for one-time use.

no decorative dividers. no emoji. no all-caps.

comments: plain lowercase, a word or two.

match existing style when editing existing code.

no Co-Authored-By trailers in commits.



\## scope

only change what the task requires.

do not refactor unrelated code.

mention unrelated problems separately, do not fix them.

touch as few files as possible.

preserve existing structure.



\## verification

turn requests into success criteria before starting.

run lake build to confirm. loop until it passes.



\## reading code

read surrounding code before editing.

identify local conventions before introducing new patterns.



\## lean 4 task patterns

wp lemma: @\[simp, wp\_simp] theorem wp\_X\_cons, proof is by wp\_atomic.

read execOne in Semantics.lean, mirror it in the wp body.

new instruction: Instruction type + execOne + wp lemma + decoder + emitter.

wp-only task: only touch Wp/Atomic.lean.

do not touch Program.lean files.

do not modify existing proofs.

