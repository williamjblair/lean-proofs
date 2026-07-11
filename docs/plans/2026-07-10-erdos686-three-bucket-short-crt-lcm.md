# Erdős 686 Three-Bucket Short-CRT LCM Implementation Plan

> **For Claude:** REQUIRED SUB-SKILL: Use superpowers:executing-plans to implement this plan task-by-task.

**Goal:** Prove and audit a proper target-size restriction for exactly three cleaned residual buckets by excluding every vanishing second obstruction and quantifying the resulting lower bound on `abc`.

**Architecture:** Treat the audited second- and third-order three-bucket consequences as frozen inputs.  If one second obstruction vanishes, the other two components divide fixed coefficient multiples of `g^2`, while the vanishing owner's third lift makes its component divide a fixed coefficient multiple of `g^3`; pairwise coprimality packs all three divisors into one LCM, giving `d | L*g^4`.  An independent exact verifier enumerates every row/triple/owner coefficient, proves the resulting bound is below `10^120`, and then computes the exact row-wise lower bound on `abc` when all second obstructions are nonzero.

**Tech Stack:** Lean 4 with mathlib kernel proofs; Python 3 standard-library exact integers and `fractions.Fraction`; pytest.

---

### Task 1: Freeze the exact finite certificate

**Files:**
- Create: `compute/campaign686/test_three_bucket_short_crt_lcm_verify.py`
- Create: `compute/campaign686/three_bucket_short_crt_lcm_verify.py`

**Step 1:** Write tests for the six row case counts, row LCM maxima, cutoff inequalities, and exact `abc` thresholds.

**Step 2:** Run the focused test and confirm it fails because the verifier module does not yet exist.

**Step 3:** Implement Taylor coefficients, obstruction slopes, positive-zero enumeration, LCM packing constants, and monotone exact threshold search without importing the producer verifier.

**Step 4:** Run the focused test and the verifier's JSON report; expect all six zero-branch bounds below `10^120`.

### Task 2: Kernel-bank the LCM packing node

**Files:**
- Create: `ErdosProblems/Erdos686ThreeBucketShortCrtLcm.lean`

**Step 1:** State the generic square-divisibility cancellation theorem for the vanishing owner's third lift.

**Step 2:** Prove that three pairwise-coprime divisors of one common multiple have product dividing that multiple.

**Step 3:** Compose both facts into `three_bucket_zero_owner_gap_dvd_lcm_power`, proving `d | L*g^4` from the two second-owner divisibilities and the vanishing owner's third-square divisibility.

**Step 4:** Compile with `lake env lean` and inspect `#print axioms`; expect only `[propext, Classical.choice, Quot.sound]` or a subset.

### Task 3: State the audited restriction honestly

**Files:**
- Create: `compute/campaign686/three_bucket_short_crt_lcm_findings.md`

**Step 1:** Record the dependency tree and per-node verdict.

**Step 2:** Record every exact row maximum, the `L*g^4` bound, and the exact lower bound on `abc` after zero exclusion.

**Step 3:** State the remaining gap as one quantified lemma with all second obstructions explicitly nonzero and `abc` above its row threshold.

**Step 4:** Re-run Lean, pytest, the JSON verifier, forbidden-token scan, and `git diff --check`; do not edit or commit shared integration files.
