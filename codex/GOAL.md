# Codex engagement: goal and protocol

## Goal

Produce complete, self-contained, auditable proofs of the isolated
open cores of the Erdős portfolio (see `FRONTIER.md`). The flagship
target is the full resolution of Erdős #686 (`prompt_686_full_solve.md`);
secondary targets are the #23 connected-case inequality
(`prompt_23_connected_B.md`) and the #730 uniform digit-count lemma
(`prompt_730_uniform_lemma.md`).

These targets differ from a raw open problem in one decisive way: the
surrounding structure is already machine-verified. Every prompt
includes (a) the exact statement that must be proven, in both prose
and Lean; (b) the verified context a proof may rely on; (c) the
falsification record — routes that are dead with exact witnesses.
Do not spend budget rediscovering either.

## Why this precedent matters

The Cycle Double Cover Conjecture fell (OpenAI, GPT 5.6 Sol Ultra) to
exactly this discipline: diverse independent approach families, an
approach registry, adversarial audit of every candidate, refusal to
count theorem-strength missing lemmas as progress, and a no-partial-
return rule. The winning proof was three pages of linear algebra atop
one known theorem — the reframing (a relaxed coloring turning the
conjecture into an F₂ solvability question) was everything. Our
targets have been prepared so that an analogous reframing has maximal
verified scaffolding to land on.

## Intake protocol (non-negotiable)

Any returned proof enters the pipeline as an UNVERIFIED CLAIM and
passes, in order:
1. Adversarial audit against the falsification record (the
   `compute730/audit.md` template: dependency tree, per-node verdict,
   every "essentially X" phrase converted to a quantified bound).
2. Exact-arithmetic reproduction of every computational claim.
3. Lean formalization behind the kernel axiom gate
   (`[propext, Classical.choice, Quot.sound]`; no native_decide).
4. Attestation (`attestations.json`).

A proof that cannot survive step 1 in principle (private lemmas,
unquantified uniformity, circular strength) should not be returned.

## Return discipline (mirrors the CDC prompt)

- Return only a complete proof of the exact stated target, or — after
  exhausting the time budget — the strongest rigorously proved
  derivation with its exact remaining gap stated as a single
  quantified lemma.
- A reduction to a lemma of strength equivalent to the target is not
  progress unless accompanied by a genuinely new proof of that lemma.
- Adversarially audit internally before returning: check every
  boundary case named in the prompt's falsification record.
