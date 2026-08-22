# Lean Correspondence v0 candidate packets

These are two source-bound research fixtures for a possible independent
`lean-correspondence` repository. They do not depend on Vela and do not modify
or interpret any repository authority, Standing, Decision, provider state, or
scientific acceptance surface. Every packet has `authority_effect = "none"`.

The custody shape follows one useful discipline from Vela's merged correction
example: keep a real rooted case separate from synthetic mutation coverage,
freeze exact inputs and outputs, and say what the evidence does not establish.
No Vela object or authority rule is copied here.

## Decision

**GO for an independent public artifact repository; NO-GO for treating either
case as reviewer-study evidence yet.** The two cases are materially different
and strong enough to justify a small public repository:

1. Erdős 730 has an executable Lean term connecting a kernel theorem to the
   proposition written on the affirmative right-hand side of the exact Formal
   Conjectures source, plus the Palomar-shaped challenge and solution adapter.
2. `OeisA303656.conjecture` has a deterministic, byte-for-byte reproduced
   Formal Conjectures-to-LeanEval generation chain across distinct pinned Lean
   and Mathlib environments.

That is enough to study correspondence records. It is not evidence of external
adoption, semantic review benefit, maintainer acceptance, equivalence of the
whole Formal Conjectures theorem wrapper, or scientific correctness. A later
reviewer study should start only after these packets are independently replayed
from publicly reachable source roots and the study protocol is preregistered.

## Verify

The fast gate checks frozen bytes, packet invariants, exact Git objects in the
three local repositories, and fail-closed mutation tests:

```bash
python3 lean-correspondence-v0/verify_packets.py \
  --lean-proofs . \
  --formal-conjectures /Users/williamblair/personal/formal-conjectures \
  --lean-eval /Users/williamblair/personal/lean-eval
python3 -m unittest discover -s lean-correspondence-v0/tests -p 'test_*.py'
```

The Lean witnesses use this repository's pinned environment:

```bash
lake env lean lean-correspondence-v0/cases/erdos-730/Witness.lean
lake env lean lean-correspondence-v0/cases/fc-leaneval-oeis-303656/HistoricalRenameWitness.lean
```

Packet-specific regeneration and target-build commands are in each case
README. Generated benchmark files contain `sorry` by design; successful
elaboration validates the statement environment, not a solution.
