# starfleet — independently verified third-party proofs

Lean 4 proofs from **Star Fleet Math** (Colin Snyder, starfleetmath.com),
hosted here as `formal_proof` targets for Formal Conjectures. Each is a claimed
resolution of an **open** Erdős problem. All 16 are rebuilt on CI against their
pinned Mathlib and read for faithfulness before being added:
123, 130, 254, 267, 336, 394, 450, 489, 521, 522, 538, 662, 769, 796, 959, 1188.

These are **not** this repo's own work. See `proofs.yaml` (`source: starfleetmath`)
for attribution and `NOTICE` for terms; they are hosted here with the author's
permission and remain his copyright.

They pin Lean 4.31 / a different Mathlib than the main library, so each is a
self-contained lake project under `starfleet/erdos-<N>/`, built and axiom-audited
by `.github/workflows/starfleet.yml` (not part of `ErdosProblems`).

`faithfulness.json` is the machine-readable version of the same two gates, one
entry per problem: terminal theorem, which FC theorem it is linked from, and
the faithfulness status (`match`, `match-with-note`, `unchecked`, `blocked`)
with the definitions compared. `VERDICTS.md` records the two gates per problem: proof (build + `#print axioms`
⊆ `[propext, Classical.choice, Quot.sound]`) and faithfulness (statement read
against erdosproblems.com / FC).

| Problem | Answer | Terminal theorem |
|--:|---|---|
| 254 | positive | `Erdos254.erdos_254` |
| 267 | positive | `Research.erdos_problem_267` |
| 489 | positive | `Erdos489.erdos489_statement` (= FC's statement verbatim) |
| 521 | negative | `Erdos521.erdos_521_negative` |
| 538 | order | `Erdos538.erdos538_matching_order` |
| 130 | positive | `Erdos130.erdos130_infinite_chromatic` |
| 394 | positive | `Research.erdos394_first_question_proved` (+ second) |
| 796 | positive | `Erdos796.erdos796_statement` (built from source; PNT substituted) |
