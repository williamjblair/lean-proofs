# Erdős 686 Three-Bucket Zero-Exclusion Hostile Audit Implementation Plan

> **For Claude:** REQUIRED SUB-SKILL: Use superpowers:executing-plans to implement this plan task-by-task.

**Goal:** Independently decide whether the frozen target-row wrapper proves the advertised conditional exclusion of every zero second obstruction above `10^120`, with exact finite and kernel evidence and no claim of closing the nonzero branch or Erdős #686.

**Architecture:** Keep every audit artifact separate from the frozen producer. Reconstruct the local coefficients by direct elementary-symmetric sums, exhaust all ordered target triples, replay the algebra and cyclic owner permutations, and exercise the named boundary fixtures. Import the producer only in a new Lean audit module that proves anonymous conversion identities and prints the axioms of every public declaration.

**Tech Stack:** Lean 4.29.1 with mathlib, Python 3 exact integers, `pytest`, SHA-256, POSIX shell.

---

### Task 1: Freeze the producer and specify the hostile tests

**Files:**
- Create: `compute/campaign686/test_three_bucket_zero_exclusion_hostile_verify.py`
- Read only: `ErdosProblems/Erdos686ThreeBucketZeroExclusion.lean`
- Read only: `compute/campaign686/three_bucket_zero_exclusion_verify.py`
- Read only: `compute/campaign686/test_three_bucket_zero_exclusion_verify.py`
- Read only: `compute/campaign686/three_bucket_zero_exclusion_findings.md`
- Read only: `docs/plans/2026-07-10-erdos686-three-bucket-zero-exclusion.md`

1. Assert the five supplied SHA-256 hashes exactly.
2. Specify the six row counts, the total `6,210`, the exact coefficient maxima and maximizing ordered cases, the rounded majorant, and floor margin `7`.
3. Specify exhaustive cross-identity, third-conversion, and cyclic-permutation counts.
4. Specify small-prime/shared-`g`, unit, `g^4`-sharpness, both `d=1` telescopes, and the 121-digit CRT pseudo-witness outcomes.
5. Run the focused test and require the expected initial import failure before implementing the verifier.

### Task 2: Implement the independent exact verifier

**Files:**
- Create: `compute/campaign686/three_bucket_zero_exclusion_hostile_verify.py`
- Test: `compute/campaign686/test_three_bucket_zero_exclusion_hostile_verify.py`

1. Compute `C`, `D`, and `E` directly as products with zero, one, or two omitted offsets; do not import any producer or earlier audit module.
2. Enumerate `permutations(range(1,k+1),3)` in every row and reject any zero cross or third coefficient.
3. Check the denominator-free identity
   `C_zero*O_owner-C_owner*O_zero=A*g^2`
   and the third identity
   `F_zero+3*O_zero=K*g^2*d`
   on every ordered triple.
4. Numerically replay all three cyclic designated-zero calls for every ordered triple, including left/right swaps and component-order products.
5. Recompute the rounded cutoff with exact integers.
6. Rebuild boundary fixtures, including an independent CRT construction of the 121-digit pseudo-witness, and explicitly confirm that it has all three obstructions nonzero while failing the short window and equation.
7. Run `python3 -m pytest compute/campaign686/test_three_bucket_zero_exclusion_hostile_verify.py -q` and require all tests to pass.

### Task 3: Rebuild and inspect the kernel surface

**Files:**
- Create: `ErdosProblems/Erdos686ThreeBucketZeroExclusionAudit.lean`

1. Import only `ErdosProblems.Erdos686ThreeBucketZeroExclusion`.
2. Prove anonymous generalized cross and third-conversion identities by unfolding and ring normalization, without calling the producer composition theorems.
3. Print axioms for the coefficient certificate, numeric cutoff, generic specialization, both swap lemmas, the designated-zero theorem, and the cyclic all-nonzero theorem.
4. Also print the key generic packing dependency and the banked equation gap theorem used only for scope comparison.
5. Run `lake env lean ErdosProblems/Erdos686ThreeBucketZeroExclusionAudit.lean`; require every assumption set to be a subset of `[propext, Classical.choice, Quot.sound]`.
6. Run a forbidden-construct scan and reject executable `sorry`, `admit`, `axiom`, `native_decide`, `of_decide`, `unsafe`, `implemented_by`, or `extern` declarations.

### Task 4: Write the hostile verdict and reproduce every gate

**Files:**
- Create: `compute/campaign686/three_bucket_zero_exclusion_hostile_audit.md`

1. Give per-node PASS/FAIL verdicts for coefficient coverage, cross elimination, signed-to-natural conversion, third reduction, coprime packing, numeric cutoff, and all three cyclic calls.
2. State the theorem's exact conditional quantifier scope: it assumes, rather than derives, the three-owner factorization and six divisibilities.
3. Record every frozen and audit hash, exact counts/maxima, kernel assumptions, and boundary outcomes.
4. State that the 121-digit pseudo-witness survives precisely in the all-nonzero branch and that the two `d=1` equation telescopes are outside `d>=10^120`.
5. End with the exact remaining nonzero short-CRT/window lemma and explicitly deny closure of the exactly-three-owner slice and full Erdős #686.
6. Re-run producer plus hostile tests, Python byte-compilation, both Lean builds, hash checks, `git diff --check`, and a final status review restricted to the five new audit files.
