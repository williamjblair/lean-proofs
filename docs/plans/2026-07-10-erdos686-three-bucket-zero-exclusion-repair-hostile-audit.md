# Erdős 686 Three-Bucket Zero-Exclusion Repair Hostile Audit Implementation Plan

> **For Claude:** REQUIRED SUB-SKILL: Use superpowers:executing-plans to implement this plan task-by-task.

**Goal:** Independently determine whether the repaired three-bucket zero-exclusion candidate is sound and safe to integrate while preserving the historical `5b802d...` FAIL audit unchanged.

**Architecture:** Freeze the current repaired producer, verifier, tests, findings, and plan by SHA-256.  Build a distinctly named verifier that reconstructs all six target rows and arithmetic without importing the producer verifier, plus a separate Lean module that audits every public theorem without invoking the producer proofs.  Record theorem-surface, falsification, axiom, and integration verdicts in a new repair-only hostile report.

**Tech Stack:** Lean 4/mathlib, exact Python integers and `Fraction`, pytest, SHA-256.

---

### Task 1: Preserve history and freeze the repaired boundary

**Files:**
- Create: `compute/campaign686/three_bucket_zero_exclusion_repair_hostile_verify.py`
- Create: `compute/campaign686/test_three_bucket_zero_exclusion_repair_hostile_verify.py`

**Step 1:** Hash the current repaired producer Lean module, verifier, tests, findings, and producer plan.

**Step 2:** Hash the historical FAIL Lean audit, verifier, tests, report, and plan without modifying them.

**Step 3:** Write a failing test that pins both boundaries and rejects the historical producer SHA as the repaired source.

**Step 4:** Implement repository-relative SHA-256 verification and require all pins to match.

### Task 2: Independently reconstruct all six target rows

**Files:**
- Modify only the two new Python audit files.

**Step 1:** Reimplement the six row parameters and every derived integer without importing `three_bucket_zero_exclusion_verify.py`.

**Step 2:** Recompute the zero equation, positivity hypotheses, divisibility witnesses, quotient bounds, LCM restriction, and the repaired theorem boundary for each row.

**Step 3:** Add explicit hostile mutations at each load-bearing hypothesis and assert that the repaired theorem does not claim those mutated cases.

**Step 4:** Run the independent pytest file and require every exact row and mutation test to pass.

### Task 3: Audit every public theorem in Lean

**Files:**
- Create: `ErdosProblems/Erdos686ThreeBucketZeroExclusionRepairAudit.lean`

**Step 1:** Enumerate every public theorem from the repaired producer module.

**Step 2:** Independently reprove each generic arithmetic theorem without invoking the producer theorem.

**Step 3:** Kernel-check all six concrete rows and their exact hypotheses/conclusions.

**Step 4:** Print axioms for every audit theorem and require only `[propext, Classical.choice, Quot.sound]`.

**Step 5:** Compile both repaired producer and audit modules with exit code zero.

### Task 4: Write the repair-only hostile report

**Files:**
- Create: `compute/campaign686/three_bucket_zero_exclusion_repair_hostile_audit.md`

**Step 1:** State the historical `5b802d...` FAIL verdict unchanged and separately identify the repaired candidate hashes.

**Step 2:** Give a dependency tree and per-theorem verdict for the entire public surface.

**Step 3:** Give all six exact rows, every boundary hypothesis, hostile mutations, and the precise strength of the repaired result.

**Step 4:** State PASS/FAIL and whether the module is safe to integrate, without claiming the full Erdős 686 target.

### Task 5: Freeze the repair audit

**Files:**
- Modify only the four new repair-audit artifacts and this plan.

**Step 1:** Run repaired producer tests, independent repair-hostile tests, and any directly related historical tests without changing historical artifacts.

**Step 2:** Run Lean compilation, `#print axioms`, forbidden-token, `native_decide`, `sorry`, custom-axiom, Python byte-compilation, and whitespace gates.

**Step 3:** Recheck producer and historical hashes, then compute final hashes for the five new repair-audit artifacts.

**Step 4:** Return exact PASS/FAIL, integration safety, and frozen hashes; do not modify imports, manifests, documentation indexes, or git state.
