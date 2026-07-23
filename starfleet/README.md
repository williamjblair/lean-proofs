# starfleet — independently verified third-party proofs

Lean 4 proofs from **Star Fleet Math** (Colin Snyder, starfleetmath.com),
hosted here as `formal_proof` targets for Formal Conjectures. Each is a claimed
resolution of an **open** Erdős problem (7 verified: 130 254 267 394 489 521 538); each was rebuilt on CI against its
pinned Mathlib and read for faithfulness before being added.

These are **not** this repo's own work — see `proofs.yaml` (`source: starfleetmath`)
for attribution. They pin Lean 4.31 / a different Mathlib than the main library,
so each is a self-contained lake project under `starfleet/erdos-<N>/`, built and
axiom-audited by `.github/workflows/starfleet.yml` (not part of `ErdosProblems`).

`VERDICTS.md` records the two gates per problem: proof (build + `#print axioms`
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
