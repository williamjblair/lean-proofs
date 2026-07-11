# Erdős 730 Unit-Range Block Implementation Plan

> **For Claude:** REQUIRED SUB-SKILL: Use superpowers:executing-plans to implement this plan task-by-task.

**Goal:** Obtain an exact counterexample or a proper payable restriction for the corrected incomplete-block range `s>=r`, equivalently `a<=r`.

**Architecture:** Freeze the audited payment for `s<r` and work only with the exact quadratic branch map modulo `p^(2r)`.  First scan genuinely new critical cases using the `p^r` block decomposition.  Then prove the exact identity `G(u+p^r v)=G(u)+p^r v G'(u) mod p^(2r)` and use the low-word permutation to derive an explicit aligned-block error term; assess that term in the first-moment normalization without claiming unpaid uniformity.

**Tech Stack:** Python 3 exact integers and `Fraction`, NumPy only for bounded `int64` hostile scans, pytest, Lean 4 with mathlib.

---

### Task 1: Extend the exact hostile grid

**Files:**
- Create: `compute730/campaign_uniform/repair/far/test_unit_range_block.py`
- Create: `compute730/campaign_uniform/repair/far/unit_range_block.py`

**Step 1:** Write failing tests for the block identity, low-word permutation count, and selected new critical scans at `p=5,r=5` and `p=7,r=4`.

**Step 2:** Implement exact block histograms without floating verdicts.

**Step 3:** Compare maximum translated critical counts against the rational main term and certified logarithmic allowance.

### Task 2: Prove the block algebra

**Files:**
- Create: `ErdosProblems/Erdos730UnitRangeBlock.lean`

**Step 1:** Prove the generic quadratic block congruence modulo `p^(2r)`.

**Step 2:** Prove the exact interval decomposition inequality from aligned `p^r` blocks and at most two boundary blocks.

**Step 3:** Compile and inspect the kernel axiom surface; forbid `native_decide` and theorem-strength assumptions.

### Task 3: Quantify the remaining error

**Files:**
- Create: `compute730/campaign_uniform/repair/far/unit_range_block_findings.md`

**Step 1:** State the exact per-block count and resulting error term.

**Step 2:** Convert the error into the family first-moment normalization where justified; if it is not payable, state the exact missing sum as one quantified lemma.

**Step 3:** Record all new hostile cases, boundary `a=r`, `a=1`, and primes `5,7,11` without extrapolating finite scans.
