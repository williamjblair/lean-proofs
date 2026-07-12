# Erdős 686 Large-Odd Two-Prime Pell Implementation Plan

> **For Claude:** REQUIRED SUB-SKILL: Use superpowers:executing-plans to implement this plan task-by-task.

**Goal:** Instantiate the existing two-large-prime Pell reduction uniformly for every odd row `k>=17`, using the new `18/13` window to obtain the explicit coefficient bound `A=3k+2`, and expose its exact second-order obstruction divisibilities.

**Architecture:** Reuse `two_large_prime_support_bounded_pell` rather than re-proving localization or Pell algebra.  Derive `n+1<k*d` from `18(n+1)<13kd`, observe `3k+2<k^2`, then package the resulting distinct-owner certificate in a new structure.  Compose the existing generic second-order local lift twice so the package includes both fixed obstruction divisibilities; do not attempt finite congruence closure.

**Tech Stack:** Lean 4/mathlib, exact Python integers and fractions, pytest.

---

### Task 1: Exact threshold and novelty audit

**Files:**
- Create: `compute/campaign686/agent_t2_large_odd_two_prime_pell/large_odd_pell_verify.py`
- Create: `compute/campaign686/agent_t2_large_odd_two_prime_pell/test_large_odd_pell_verify.py`

**Steps:**
1. Verify `18x<13kd -> x<kd` for positive `k,d` over exact integer boundary cases.
2. Verify `3k+2<k^2` for every `k>=4`; record the live odd threshold `k=17` from the large-row window.
3. Reconstruct `C_i,D_i` and verify the two obstruction identities symbolically on exact synthetic Pell tuples.
4. Enumerate determinant-zero owner pairs through a substantial finite range and confirm they are reflected; retain them as an explicit surviving branch.
5. Run focused pytest only; do not run Lean.

### Task 2: Draft the uniform Lean wrapper

**Files:**
- Create: `ErdosProblems/Erdos686LargeOddTwoPrimePell.lean`

**Steps:**
1. Define `LargeOddTwoPrimePellCertificate` with distinct owners, positive coefficients, residual squares, ratio bounds, `ab<(3k+2)^2`, exact Pell subtraction, two second-obstruction divisibilities, and center bounds.
2. Prove `n+1<k*d` from the imported `18/13` theorem.
3. Prove `3k+2<k^2` at `k=2r+1`, `r>=8`.
4. Invoke `two_large_prime_support_bounded_pell` with `C=k`, `A=3k+2`.
5. Recover the two lower-factor divisibilities naturally from the residual equations and cancel the factor three using `p,q>=k>=17`.
6. Apply `second_order_local_lift` twice and `second_obstruction_divisibilities` once.
7. Add `#print axioms` gates but do not invoke Lean until released.

### Task 3: Findings and hostile audit

**Files:**
- Create: `compute/campaign686/agent_t2_large_odd_two_prime_pell/findings.md`
- Create: `compute/campaign686/agent_t2_large_odd_two_prime_pell/hostile_audit.md`

**Steps:**
1. State the exact quantified restriction and dependency tree.
2. Audit `k=17`, exponent one, `p=k`, center owners, strict coefficient endpoints, and reflected determinant degeneracy.
3. Explain why the package is nonduplicative and why it does not claim a second-lift closure.
4. Scan source for prohibited tokens and whitespace without invoking Lean.
5. Freeze source and verifier hashes with kernel status `DRAFT / NOT BUILT`.
