# lean-proofs

Formal Lean 4 proofs of solved research problems, hosted as stable `formal_proof`
targets for [Formal Conjectures](https://github.com/google-deepmind/formal-conjectures)
and prepared for registration on [Palomar](https://palomar-registry.org), the registry
of machine-checked Lean results.

Every push runs the gate the proofs are claimed to pass: the whole library builds
against a pinned Mathlib, and a `#print axioms` audit fails the build if any tracked
theorem uses `sorry` or any axiom outside `[propext, Classical.choice, Quot.sound]`.
A green badge is a scoped, re-checkable build and axiom result. It is not scientific
acceptance, a Vela Decision, or Standing in any Repository.

## Results

| Problem | Theorem | Statement | Status |
|--------:|---------|-----------|--------|
| [730](https://www.erdosproblems.com/730) | `Erdos730.FullDensityTheorem.pairSet_infinite` | Infinitely many pairs `n < m` (in fact consecutive pairs) whose central binomial coefficients have identical prime support — the affirmative answer to Erdős #730. | kernel-proved; registry statement in `Palomar/Erdos730/` |
| [154](https://www.erdosproblems.com/154) | `Erdos154.erdos_154_sumset` | For Sidon sets `A` with `\|A\| ~ √N`, the sumset `A + A` is equidistributed over residue classes mod `m`. | kernel-proved; registry statement in `Palomar/Erdos154/`; registration waits on the upstream licence of the Lindström formalisation it builds on (see `NOTICE`) |
| [94](https://www.erdosproblems.com/94) | `Erdos94.variants.sum_multiplicity` | The multiplicities of the distinct distances of a finite planar point set sum to `(\|P\| choose 2)`. | kernel-proved bounded identity; statement in `Palomar/Erdos94/`; below a registry's research-interest floor and not a candidate |
| [399](https://www.erdosproblems.com/399) | `Erdos399.erdos_399.variants.cambie` | Coprime `x, y` with `1 < xy`: no factorial is `x⁴ + y⁴`. | kernel-proved bounded variant |
| [1074](https://www.erdosproblems.com/1074) | `Erdos1074.erdos_1074.variants.EHSNumbers_init` | The first seven EHS numbers are `8, 9, 13, 14, 15, 16, 17`. | kernel-proved finite computation |

`proofs.yaml` is the machine-readable index of every tracked theorem, including the
component lemmas of the #730 development; `Audit.lean` prints the axioms of each.

## Layout

```
Palomar/<Problem>/            registry statements: Challenge.lean (imports Mathlib
                              only), Solution.lean (delegates to the proof here),
                              comparator.json (what Comparator compares)
ErdosProblems/                the proofs
Audit.lean                    #print axioms for every tracked theorem
proofs.yaml                   machine-readable index (consumed by erdos-fc-sync)
formalization.yaml            provenance, sources, automation, review (the
                              mathlib-initiative self-reporting standard; Palomar
                              reads it)
compute730/                   exact-arithmetic provenance for the #730 proof
evidence/                     retained computational certificates
docs/                         plans, and the Vela integration contract
scripts/, tests/              the verification gate and its tests
.vela/, vela.toml             optional Vela integration (docs/vela-integration.md)
NOTICE                        third-party material and its terms
```

In-progress campaigns live in their own repositories:
[erdos-686](https://github.com/williamjblair/erdos-686) and
[erdos-frontier](https://github.com/vela-science/erdos-frontier). The third-party
Star Fleet Math proofs that were hosted under `starfleet/` have moved out as well;
existing commit-pinned links to them remain valid.

## Registry statements

Each `Palomar/<Problem>/` directory is one Comparator comparison in the shape the
[Palomar submission standard](https://github.com/PalomarRegistry/PalomarPolicy/blob/main/CONTRIBUTING.md)
asks for: a `Challenge.lean` that imports only Mathlib and states the result in a
single auditable declaration, a `Solution.lean` that proves the same declaration
from the development in `ErdosProblems/`, and a `comparator.json` permitting only the
three standard axioms. Challenge and Solution declare the same names by design, so
the `Palomar` library builds each module on its own.

To reproduce the registry's mechanical check locally, with
[Comparator](https://github.com/leanprover/comparator) and a `lean4export` built at
this repository's Lean version on `PATH` (on macOS, Comparator's
`scripts/fake-landrun.sh` stands in for the Linux sandbox and is not adversarial):

```bash
lake exe cache get
lake build
lake env comparator Palomar/Erdos730/comparator.json
```

Which statements are candidates for registration, and why, is recorded in
`formalization.yaml` (`status.main_results`). Registration is a deliberate, separate
act: nothing in this repository submits anything.

## Verify locally

```bash
lake exe cache get
lake build
bash scripts/check_axioms.sh
bash scripts/check_manifest.sh
python3 -m unittest discover -s tests -p 'test_*.py'
```

The optional Vela integration checks (`vela integration check . --json`,
`python3 scripts/check_vela_integration.py`) are described in
[docs/vela-integration.md](docs/vela-integration.md).

## Erdős #730 full-density proof


Erdős #730 is unconditionally kernel-proved.  The terminal theorem is
`Erdos730.FullDensityTheorem.pairSet_infinite`: infinitely many consecutive
central binomial coefficients have identical prime support.  The proof
formalizes the explicit positive-density family, Kummer digit criterion,
four-range event ledger, fixed-depth Fourier estimate, uniform depth tail,
Mertens input, fixed-modulus PNT in arithmetic progressions, divisor
switching, exact density budget, and density-to-infinitude bridge.  See
`compute730/full_density/`, `ErdosProblems/Erdos730FullDensityTheorem.lean`, and the
registry statement `Palomar/Erdos730/Challenge.lean`.

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

## Erdős #154 sumset equidistribution

`Erdos154.erdos_154_sumset` proves that along Sidon sets `A k ⊆ [0, N k]` with
`N k → ∞` and `|A k| / √(N k) → 1`, the sumset `A k + A k` is equidistributed modulo
every `m ≥ 2`. It is proved from Lindström's residue-distribution theorem for `A`
itself (J. Number Theory 1998), whose formalisation in `ErdosProblems/Erdos154.lean`
is by Aristotle (Harmonic) and Wouter van Doorn via
[Woett/Lean-files](https://github.com/Woett/Lean-files); see `NOTICE` for its terms.
The statement is the one Formal Conjectures records for the problem
([#4340](https://github.com/google-deepmind/formal-conjectures/pull/4340)).

## Relationship to the rest of the ecosystem

- **erdos-fc-sync** reads `proofs.yaml` as a proof source. When a problem has a
  clean proof here that Formal Conjectures does not yet link, the sync surfaces it
  as a contribution target.
- Proofs that build on existing formalisations carry that lineage in their headers,
  in `proofs.yaml`, and in `formalization.yaml`'s `related_formalizations`.

## Adding a proof


1. Add `ErdosProblems/Erdos<n>.lean`, building cleanly against the pinned Mathlib.
2. Add its module import and a `#print axioms` line to the manifest-tracked
   section of `Audit.lean`.
3. Add an entry to `proofs.yaml`.
4. `bash scripts/check_axioms.sh && bash scripts/check_manifest.sh` must pass.

## License

MIT for the material authored here; see `LICENSE`, and `NOTICE` for the third-party
material this grant does not cover.
