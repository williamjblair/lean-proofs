# Erdős 730 First-Power Routes Hostile Audit Implementation Plan

> **For Claude:** REQUIRED SUB-SKILL: Use superpowers:executing-plans to implement this plan task-by-task.

**Goal:** Build an immutable, independent audit package for the frozen `Erdos730FirstPowerRoutes` partial-proof artifact.

**Architecture:** Pin every producer artifact by SHA-256, then rederive the numerical certificates and hostile witnesses in a verifier that does not import the producer module.  Add a separate Lean audit module that independently reproves the kernel-level algebra and exact arithmetic.  Finish with a hostile report that distinguishes kernel theorems, paper/exact aggregation, finite diagnostics, and the still-open exhaustive coverage bridge plus `1779/2500` residual.

**Tech Stack:** Lean 4/mathlib, Python standard-library exact integers and `Fraction`, bounded NumPy integer scans, pytest, SHA-256.

---

### Task 1: Pin the producer boundary

**Files:**
- Create: `compute730/campaign_uniform/repair/far/first_power_routes_hostile_verify.py`
- Create: `compute730/campaign_uniform/repair/far/test_first_power_routes_hostile_verify.py`

**Step 1:** Add the five expected producer hashes as immutable constants.

**Step 2:** Write a failing pytest asserting every current SHA-256 digest.

**Step 3:** Implement a repository-relative hash verifier without importing `first_power_routes.py`.

**Step 4:** Run the single test and require `PASS`.

### Task 2: Independently reproduce exact constants and scans

**Files:**
- Modify only the two new Python files from Task 1.

**Step 1:** Reimplement rational atanh logarithm bounds, prime enumeration, branch roots/maps, restricted-digit masks, and periodic maximum-window counts.

**Step 2:** Recompute the `6/5` endpoint implication, prime-series envelope, `<174/625`, and exact `1779/2500` remainder.

**Step 3:** Reproduce the first and worst `2*mean` failures, the `8/3` finite boundary, the `p=19` uninflated failure, and the 328-case inflated Q/S scan.

**Step 4:** Reproduce the Q/S threshold implications and predecessor witnesses using exhaustive integer checks around the split points.

**Step 5:** Reproduce primality, root-class length, exact valuation, digit decompositions, and short/non-top status for the `p=30000001` Q/S witnesses.

**Step 6:** Run the independent pytest file and require all tests to pass.

### Task 3: Add an independent Lean kernel audit

**Files:**
- Create: `ErdosProblems/Erdos730FirstPowerRoutesAudit.lean`

**Step 1:** Reprove the fixed-slope divisibility and cleared `6/5` endpoint inequality without invoking the producer theorems.

**Step 2:** Reprove the Q/S digit inequalities and `c^2<p` threshold implications.

**Step 3:** Kernel-check the exact counterexample ratios, terminal ceilings, predecessor witnesses, and `p=30000001` arithmetic data.

**Step 4:** Print axioms for every audit theorem and require only `[propext, Classical.choice, Quot.sound]`.

**Step 5:** Run `lake env lean ErdosProblems/Erdos730FirstPowerRoutesAudit.lean` and require exit code zero.

### Task 4: Write the adversarial report

**Files:**
- Create: `compute730/campaign_uniform/repair/far/first_power_routes_hostile_audit.md`

**Step 1:** Record producer and auditor hashes, dependency tree, per-node verdicts, and boundary instantiations.

**Step 2:** State that the global `174/625` aggregation is paper/exact rather than kernel-expanded.

**Step 3:** State the exhaustive event-multiplicity coverage bridge and the `1779/2500-delta` residual as open, retaining all short classes and endpoint terms.

**Step 4:** List exact reproduction commands, including the frozen 43-test producer scope and the independent audit suite.

### Task 5: Freeze and verify

**Files:**
- Modify only the four new audit artifacts and this plan.

**Step 1:** Run the producer 43-test scope unchanged.

**Step 2:** Run the independent hostile tests, Lean audit, Python byte compilation, forbidden-token scan, and whitespace check.

**Step 3:** Recheck producer hashes and compute final hashes for every audit artifact.

**Step 4:** Return `PASS` only if all frozen checks reproduce; do not commit or edit producer/shared files.
