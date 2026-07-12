# Erdős 686 All-Owner Resultant Attack Implementation Plan

> **For Claude:** REQUIRED SUB-SKILL: Use superpowers:executing-plans to implement this plan task-by-task.

**Goal:** Determine whether simultaneous nonzero full-owner square divisibilities admit a global Vandermonde/resultant bound below `10^120`, and bank only a genuinely stronger restriction or a hostile exact negative result.

**Architecture:** Reconstruct the all-owner obstruction polynomials independently from the coefficient definitions and exact residual window. Eliminate the common cofactor product from subsets of at least four owner equations, enumerate every subset in all six rows, and compare the resulting determinant/modulus scale with the existing residual square bound. If the determinant route fails, search for an exact target-scale window-compatible algebraic fixture; otherwise state the precise quantified obstruction and freeze the negative audit without modifying shared registries.

**Tech Stack:** Python 3 exact integers and `fractions.Fraction`, SymPy only for symbolic cross-checks, pytest, Lean 4/mathlib only if a proper theorem emerges.

---

### Task 1: Reconstruct the simultaneous system

**Files:**
- Create: `compute/campaign686/agent_t1_all_owner_resultant/all_owner_resultant_verify.py`
- Create: `compute/campaign686/agent_t1_all_owner_resultant/test_all_owner_resultant_verify.py`

**Steps:**
1. Reconstruct `C_i,D_i,E_i`, signed Vandermonde factors, and row window constants from elementary products rather than importing verifier output.
2. Encode `F_i=-9C_i A+g^2 R_i(12D_i+20E_i d)` and the exact divisibility `P_i^2|F_i`.
3. Cross-check every coefficient against the Lean tables for all 60 target owner rows.
4. Add exact symbolic tests for eliminating the common variable `A` from two or more rows.

### Task 2: Enumerate all owner subsets

**Files:**
- Modify: `compute/campaign686/agent_t1_all_owner_resultant/all_owner_resultant_verify.py`
- Modify: `compute/campaign686/agent_t1_all_owner_resultant/test_all_owner_resultant_verify.py`

**Steps:**
1. Enumerate every subset of size `4..k` for `k in {5,7,9,11,13,15}`.
2. Compute primitive minors/resultants after eliminating `A`, including all endpoint, center, reflected, and mixed subsets.
3. Factor every determinant into its Vandermonde part and remaining coefficient part when possible.
4. Record zero ranks, repeated rows, sign cells, coefficient degrees in `d`, and exact maximum/minimum nonzero determinants.
5. Compare every modulus-to-size implication at `d=10^120` with the existing `P_i^2<U_k d` bound before claiming progress.

### Task 3: Search for a window-compatible algebraic fixture

**Files:**
- Modify: `compute/campaign686/agent_t1_all_owner_resultant/all_owner_resultant_verify.py`

**Steps:**
1. Search exact step-three residual progressions inside each row's rational window.
2. Factor residuals into square buckets and cofactors, enforcing pairwise-coprime buckets, bounded loss, and exact gap reconstruction.
3. Check every second/third obstruction divisibility and nonvanishing condition.
4. If no full fixture is found, freeze the strongest exact partial fixture and state exactly which equation/certificate field fails.

### Task 4: Formalize or audit

**Files:**
- Create if justified: `ErdosProblems/Erdos686AllOwnerResultant.lean`
- Create: `compute/campaign686/agent_t1_all_owner_resultant/findings.md`
- Create: `compute/campaign686/agent_t1_all_owner_resultant/hostile_audit.md`

**Steps:**
1. Formalize only a restriction strictly weaker than Target 1 and not already implied by the certificate.
2. Otherwise write a hostile negative audit with the exact failed determinant inequality and all subset counts.
3. Replay `k=9,15,d=1`, the 121-digit Hensel fixture, unit buckets, bases `2,3`, centers, endpoints, and every target row.
4. Run focused pytest, exact report generation, forbidden-token scan, direct Lean compilation if applicable, and `git diff --check`.
5. Freeze SHA-256 hashes and report the exact remaining quantified obstruction.
