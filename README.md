# lean-proofs

A small, self-checking index of formal Lean 4 proofs of solved research problems,
hosted as stable `formal_proof` targets for
[Formal Conjectures](https://github.com/google-deepmind/formal-conjectures).

Every push runs the same gate the proofs are claimed to pass: the whole library
builds against a pinned Mathlib, and a `#print axioms` audit fails the build if
any headline theorem uses `sorry` or any axiom outside the kernel set
`[propext, Classical.choice, Quot.sound]`. A green badge here is a standing,
re-checkable guarantee, not a one-time assertion.

## Layout

```
ErdosProblems/Erdos730*.lean   Erdős #730: infinitely many consecutive central
                               binomial coefficients share prime support (SOLVED)
ErdosProblems/Erdos154*.lean   Erdős #154: Sidon sumset equidistribution (proved)
compute730/                    exact-arithmetic provenance for the #730 proof
Audit.lean                     #print axioms for the proof targets
proofs.yaml                    machine-readable index (consumed by erdos-fc-sync)
scripts/check_axioms.sh        the verification gate
```

This repo hosts only **solved** problems with complete, kernel-clean proofs. The
in-progress campaigns moved to their own homes:

- **Erdős 686** — [erdos-686](https://github.com/williamjblair/erdos-686)
- **Erdős 23, 617, 699, 727** — [erdos-frontier](https://github.com/vela-science/erdos-frontier)

## Verify locally

```bash
lake exe cache get
lake build
bash scripts/check_axioms.sh
```

## Erdős #730 full-density proof

Erdős #730 is unconditionally kernel-proved.  The terminal theorem is
`Erdos730.FullDensityTheorem.pairSet_infinite`: infinitely many consecutive
central binomial coefficients have identical prime support.  The proof
formalizes the explicit positive-density family, Kummer digit criterion,
four-range event ledger, fixed-depth Fourier estimate, uniform depth tail,
Mertens input, fixed-modulus PNT in arithmetic progressions, divisor
switching, exact density budget, and density-to-infinitude bridge.  See
`compute730/full_density/` and
`ErdosProblems/Erdos730FullDensityTheorem.lean`.

The hostile-audit certificate includes 119 passing exact-arithmetic tests and
the strict rational bound

```text
4*S + (2/3) log 2
  < 21498408212212214497 / 22462131847034880000
  < 2393/2500,
```

with positive margin
`2344391769572639 / 22462131847034880000`.  The terminal audit exposes only
`[propext, Classical.choice, Quot.sound]`; no `native_decide` is used.

The fixed-modulus PNT-AP step uses the pinned external
`PrimeNumberTheoremAnd` package.  That package contains two admitted
experimental declarations, `prelim_decay_2` and `prelim_decay_3`, outside the
transitive dependency cone of the theorem used here.  The active PNT-AP route
and the Erdős #730 terminal theorem do not depend on `sorryAx`, so this is a
package-global hygiene qualification rather than a gap in the proof.

## Index

| Problem | Theorem | Statement | FC |
|--------:|---------|-----------|----|
| [154](https://www.erdosproblems.com/154) | `Erdos154.erdos_154_sumset` | For a Sidon set `A` with `\|A\| ~ √N`, the sumset `A+A` is equidistributed over residue classes mod `m`. | [#4340](https://github.com/google-deepmind/formal-conjectures/pull/4340) |
| [730](https://www.erdosproblems.com/730) | `Erdos730.FullDensityTheorem.pairSet_infinite` | Infinitely many consecutive central binomial coefficients have identical prime support. | [target](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/730.lean) |

## Relationship to the rest of the ecosystem

- **erdos-fc-sync** reads `proofs.yaml` as a proof source. When a problem has a
  clean proof here that Formal Conjectures does not yet link, the sync surfaces
  it as a contribution target.
- Proofs that build on existing formalizations carry that lineage in their
  headers and in `proofs.yaml`. The 154 sumset proof builds on the Lindström
  residue-distribution theorem for `A` (formal authors Aristotle and Wouter van
  Doorn, hosted via `plby/lean-proofs`) and transfers it to `A+A` using the
  Sidon property.

## Adding a proof

1. Add `ErdosProblems/Erdos<n>.lean`, building cleanly against the pinned Mathlib.
2. Add its module import and a `#print axioms` line to the manifest-tracked
   section of `Audit.lean`.
3. Add an entry to `proofs.yaml`.
4. `bash scripts/check_axioms.sh && bash scripts/check_manifest.sh` must pass.

## License

Original contributions in this repository are MIT licensed (see `LICENSE`).
Third-party formalizations included as build dependencies retain their original
licenses, noted in their file headers; Mathlib is Apache-2.0.
