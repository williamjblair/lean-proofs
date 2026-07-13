# Erdős 730 Full-Density Formalization Implementation Plan

> **For Claude:** REQUIRED SUB-SKILL: Use superpowers:executing-plans to implement this plan task-by-task.

**Goal:** Intake the new positive-density proof of Erdős #730, reproduce every finite claim, formalize the strongest kernel-clean theorem surface, and identify any remaining kernel gap as one quantified analytic lemma.

**Architecture:** Freeze the supplied proof as an untrusted source and audit it in four layers: exact family arithmetic, obstruction and digit-count combinatorics, asymptotic analytic estimates, and final density transfer.  Reuse the existing #730 branch algebra and falsification corpus, add an independent exact verifier, then expose the full family and Formal Conjectures target in Lean.  The headline theorem is unconditional only if the required Mertens and fixed-modulus prime-number-theorem inputs can be supplied without `sorry` or new axioms; otherwise the repository records one explicit analytic closure hypothesis and proves all downstream consequences from it.

**Tech Stack:** Lean 4.29.1 with pinned Mathlib, Python standard-library exact arithmetic, pytest, shell axiom/manifest gates.

## Implemented outcome

Tasks 1-3 and 5 are complete.  Task 4 is kernel-banked through the full
consecutive-transition criterion, pointwise event coverage, p-adic counting,
generic higher-power dominated convergence, the exact numerical budget, and
the density-to-upstream reduction.  The pinned library audit found no
kernel-clean reciprocal-prime Mertens asymptotic or fixed-modulus PNT in
arithmetic progressions.  Accordingly, the unconditional headline remains
outside the manifest, and the exact residual theorem is
`Erdos730.FullDensityReduction.CandidatePositiveDensityClaim`.  Task 6 records
the final gate results in the repository status and attestation artifacts.

---

### Task 1: Freeze and adversarially audit the candidate

**Files:**
- Create: `compute730/full_density/audit.md`
- Create: `compute730/full_density/dependency_tree.md`

**Step 1:** Record the candidate source hash and exact claimed density theorem.

**Step 2:** Build a dependency tree from the Kummer transition criterion through the four range estimates and final density transfer.

**Step 3:** Instantiate every boundary from the existing falsification record, especially `p=5,r=432,s=176,a=688`, and explain why the fixed-depth order of limits does or does not evade it.

**Step 4:** Convert every asymptotic phrase into a quantified limit or an explicit imported theorem surface.

### Task 2: Reproduce the finite and rational certificates

**Files:**
- Create: `compute730/full_density/verify.py`
- Create: `compute730/full_density/test_verify.py`

**Step 1:** Recompute `T`, all four slopes, six linear identities, common quadratic coefficient, and exceptional-prime factors.

**Step 2:** Exhaust the top-range residue tables and CRT class counts for the `P` and `R` branches.

**Step 3:** Recompute the six logarithm bounds, infinite-tail majorant, final rational upper bound, and positive margin.

**Step 4:** Re-run the legacy counterexample suites together with the new exact tests.

### Task 3: Formalize the exact family and finite core

**Files:**
- Create: `ErdosProblems/Erdos730FullDensityCore.lean`
- Create: `ErdosProblems/Erdos730FullDensityCoreAudit.lean`

**Step 1:** Define the family `P,Q,R,S,n`, its good-parameter predicate, and the exact upstream pair set.

**Step 2:** Kernel-prove the family identities, strict growth, exceptional-prime arithmetic, and the top-range residue-class certificates.

**Step 3:** Kernel-prove the rational logarithm/series certificate giving
`4 * S + (2/3) * log 2 < 2393/2500`.

**Step 4:** Add independent axiom prints and require exactly `[propext, Classical.choice, Quot.sound]` or a smaller set.

### Task 4: Formalize the analytic reduction

**Files:**
- Create: `ErdosProblems/Erdos730FullDensity.lean`
- Create: `ErdosProblems/Erdos730FullDensityAudit.lean`

**Step 1:** State each event count and the exhaustive bridge `Bad(X) ≤ E(X)`.

**Step 2:** Formalize the higher-power dominated-convergence reduction and the fixed-depth/r-tail split.

**Step 3:** Formalize the transition estimate and divisor-switching reduction.

**Step 4:** Search the pinned dependency graph for kernel-clean Mertens and fixed-modulus PNT-in-AP theorems.  If absent, package precisely those missing standard analytic inputs into one quantified `AnalyticClosure` proposition; do not introduce an axiom or mark the unconditional target proved.

**Step 5:** Prove the positive-density and `Set.Infinite` conclusions from the analytic closure surface.

### Task 5: Integrate the audited status

**Files:**
- Modify: `FRONTIER.md`
- Modify: `codex/prompt_730_uniform_lemma.md`
- Modify: `README.md`
- Modify: `Audit.lean`
- Modify: `proofs.yaml`
- Modify: `attestations.json`

**Step 1:** Replace the stale open-route description with the audited fixed-depth proof status, explicitly separating paper proof from kernel closure.

**Step 2:** Register only theorem surfaces that pass the axiom gate; do not register a conditional theorem as the solved Formal Conjectures target.

**Step 3:** Regenerate attestations and run the full repository gates.

### Task 6: Verify the complete intake

**Step 1:** Run the new exact pytest scope and all legacy #730 falsification tests.

**Step 2:** Run both new Lean audit modules directly.

**Step 3:** Run `lake build`, `bash scripts/check_axioms.sh`, and `bash scripts/check_manifest.sh`.

**Step 4:** Return either the unconditional kernel-clean theorem or the strongest proved conditional derivation with the exact remaining quantified analytic lemma.
