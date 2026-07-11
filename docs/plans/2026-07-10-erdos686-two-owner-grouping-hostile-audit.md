# Erdős 686 Two-Owner Grouping Hostile Audit Implementation Plan

> **For Claude:** REQUIRED SUB-SKILL: Use superpowers:executing-plans to implement this plan task-by-task.

**Goal:** Independently determine whether the frozen finite grouping module closes the bookkeeping gap from per-prime concentration witnesses to the exact two-owner aggregate predicate.

**Architecture:** Freeze and inspect the candidate theorem surface, then rederive all arithmetic in a verifier that does not import producer code. Add a separate Lean audit module for boundary instances and quantified corollaries, run fresh compilation and axiom scans for every public theorem, and record a per-node hostile verdict with the exact surviving Erdős 686 gap.

**Tech Stack:** Lean 4.29.1, mathlib, Lake, Python 3 exact integers, pytest, SHA-256.

---

### Task 1: Freeze the candidate and dependencies

**Files:**
- Read: `ErdosProblems/Erdos686TwoOwnerGrouping.lean`
- Read: `ErdosProblems/Erdos686TwoOwnerAggregate.lean`
- Read: `ErdosProblems/Erdos686GlobalResidualConcentration.lean`
- Create: `docs/plans/2026-07-10-erdos686-two-owner-grouping-hostile-audit.md`

**Steps:**
1. Verify the candidate SHA-256 exactly.
2. Enumerate all 13 public theorems and their explicit hypotheses and conclusions.
3. Trace every nonlocal theorem used by the chooser and cutoff wrapper.
4. Record the exact producer artifact hashes without modifying them.

### Task 2: Write an independent exact-arithmetic verifier

**Files:**
- Create: `compute/campaign686/two_owner_grouping_hostile_verify.py`
- Create: `compute/campaign686/test_two_owner_grouping_hostile_verify.py`

**Steps:**
1. Reimplement primality, factorization, factorial valuations, cleaned exponents, loss products, and owner buckets without importing the producer verifier.
2. Exhaust all gaps in a fixed finite range and all owner maps into three values, including nontrivial owners outside a proposed two-cover.
3. Exercise `p=2`, `p=3`, `p>=k`, zero-clean powers, empty support, one-prime support, coincident owners, and both unit buckets.
4. Recompute every row loss and verify exact `d=g*P*Q`, `g|G_k`, `g<=G_k`, `gcd(P,Q)=1`, and pairwise product divisibilities.
5. Scan executable source independently for forbidden declarations and private-lemma leakage.

### Task 3: Add a kernel-side hostile audit module

**Files:**
- Create: `ErdosProblems/Erdos686TwoOwnerGroupingAudit.lean`

**Steps:**
1. Import only the frozen grouping candidate.
2. Prove explicit empty-support, one-prime, zero-clean, and coincident-owner evaluations.
3. Derive a quantified corollary spelling out that `exists_globalResidualOwnerAssignment_not_two_cover` returns one certified assignment not coverable by any two indices.
4. Confirm the theorem does not imply three distinct prime divisors and does not assert all possible assignments are non-coverable.
5. Compile to fresh temporary objects.

### Task 4: Run kernel, theorem-surface, and adversarial gates

**Files:**
- Inspect: `ErdosProblems/Erdos686TwoOwnerGrouping.lean`
- Inspect: `ErdosProblems/Erdos686TwoOwnerGroupingAudit.lean`

**Steps:**
1. Run `#check` and `#print` for every public theorem.
2. Run `#print axioms` for every public theorem and enforce the allowed kernel set.
3. Build the candidate and audit targets through Lake.
4. Run the focused hostile tests plus the producer tests for comparison.
5. Recheck the frozen candidate hash after all audit work.

### Task 5: Publish an exact hostile verdict

**Files:**
- Create: `compute/campaign686/two_owner_grouping_hostile_audit.md`

**Steps:**
1. Give a dependency tree with a PASS or FAIL verdict at every node.
2. Convert all informal range language into explicit quantifiers.
3. State whether the finite grouping gap is closed.
4. State the exact next Erdős 686 gap without promoting a conditional theorem to an unconditional solution.
5. Freeze all audit artifact SHA-256 values; do not edit shared imports, manifests, registries, or campaign prose.
