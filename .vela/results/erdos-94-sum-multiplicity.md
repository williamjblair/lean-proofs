# Erdős 94 bounded sum-multiplicity result

## Target and outcome

- Target: `Erdos94.variants.sum_multiplicity` in
  `ErdosProblems/Erdos94SumMultiplicity.lean`.
- Outcome: proved for every finite `P : Finset ℝ²`:
  `∑ u ∈ distanceSet P, distanceMultiplicity P u = P.card.choose 2`.
- Scope: the elementary sum identity only. It does not prove the cubic
  distance-multiplicity theorem, the no-three-on-a-line variant, or the regular
  polygon conjecture grouped under Erdős 94.

## Approach and explored scope

The proof sends ordered distinct pairs to `Sym2 ℝ²`, proves each unordered
distance fiber has exactly the swapped representatives `(a, b)` and `(b, a)`,
uses that equality to justify natural-number division by two, and sums the
unordered fibers. `Sym2.card_image_offDiag` then identifies the total with
`P.card.choose 2`. The review checked the zero-, one-, and two-point boundary
behavior implicit in the finite-set identities, repeated distances, swapped
representatives, non-diagonal membership, and truncating division.

## Assumptions and exact environment

- No geometric-position assumption: neither convex independence nor
  non-collinearity is used.
- Lean `4.29.1`, Mathlib
  `5e932f97dd25535344f80f9dd8da3aab83df0fe6`.
- Kernel dependency set: `propext`, `Classical.choice`, `Quot.sound`.
- No `sorry`, `admit`, `unsafe`, `native_decide`, or new axiom appears in the
  proof source.

## Exact artifacts and evidence

- Source commit: `423344341fbfdf4f8f684a302c5d05379125e7dc`.
- Source tree: `eae3c8d1941c997f1055f5ea561cb719088b9202`.
- Source Git blob: `020a4d72cc7bb1706efac07fc1bcef70d3adf838`.
- Source SHA-256: `sha256:412975add8b6963bb44378f5d8ef41fd1f860b9ec06495432ab97e8ca60ffbe0`.
- Exact external target: `williamjblair/formal-conjectures` commit
  `94a278e06a8bcbc2e4f2935e491c0c115ec832e0`, path
  `FormalConjectures/ErdosProblems/94.lean`, selector
  `Erdos94.erdos_94.variants.sum_multiplicity`, file SHA-256
  `sha256:ba09a21af6257987afed3733e9edc737bfe4d1f132f1cb07ca6f5fe216337d3b`.
- Historical integration commit retained for evidence:
  `c23bda1584fa496363f93b4ee783f3e0d1ee116e`. Its source integration packet is
  superseded by the current `main` integration; its campaign/session context is
  not merged.
- Current Method chain: `vela.toml` → formal-proof/lean-project Profiles →
  Bindings → `lean-build`, `axiom-audit`, and `integration-validator` Methods.
  All are authority-neutral.

The exact source commit is preserved as a parent in canonical Git history, so
the accepted external Claim need not be rewritten merely to follow a
cherry-picked proof with a different commit identity.

## Budget and provenance

The original producer report records 1,444 seconds on `darwin-arm64`; network
was used to materialize pinned dependencies. The performer was an OpenAI Codex
agent, with the exact model version unavailable from that harness. Performer
kind is provenance, not a quality score. The present repository review reruns
the proof, axiom, hostile-integration, portability, and cold-consumer gates;
generic turns and checkpoints remain in source-owned activity tooling rather
than being copied into this repository or Vela.

## Compatibility and retry condition

The Formal Conjectures target uses the same `distanceSet` and
`distanceMultiplicity` definitions. A clean public checkout at the exact target
commit was built with Lean `4.27.0` and Mathlib
`a3a10db0e9d66acbebf76c5e6a135066525ac900`. The transplant required the
mechanical `Sym2.mk.uncurry` to `Sym2.mk` spelling adaptation and recreating the
source file's `noncomputable` and `Finset` scope context. The selected theorem
then elaborated with axioms exactly `propext`, `Classical.choice`, and
`Quot.sound`; the only `sorry` warnings came from the three excluded Erdős 94
declarations. These are file/toolchain compatibility details, not mathematical
assumptions.

Retry or revise this bounded result only if the target definitions, selected
declaration, pinned dependency graph, or exact source bytes change. Work on the
cubic Erdős 94 theorem is a separate scientific target and must not be reported
as a retry or failure of this completed identity.

## External mechanical-check readiness

`external/palomar/erdos94-sum-multiplicity/` freezes a minimal trusted
`Challenge.lean`, proved `Solution.lean`, exact Comparator configuration,
bundle-local `formalization.yaml`, toolchain and dependency lock, and SHA-256
inventory. Both Lean files elaborate locally in the pinned repository
environment; the challenge's single `sorry` is the intentional Comparator
hole. A real Comparator replay with a Linux `landrun` sandbox is not available
on this Darwin host and remains an external gate.

This preparation is not a Palomar submission or registration, and no status
URL, credential, or external communication is retained. A future registration
requires explicit authorization at action time and would be external evidence
only—not organizational independence, peer review, novelty, importance, or a
Vela Decision, Event, or Standing change.
