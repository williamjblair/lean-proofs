# Erdős 686 Large-Prime Same-Owner Implementation Plan

> **For Claude:** REQUIRED SUB-SKILL: Use superpowers:executing-plans to implement this plan task-by-task.

**Goal:** Add the missing large-row dominance consequence for an already-aggregated residual owner bucket, and derive an all-parity `k>=16` two-large-prime whole-gap owner-separation theorem without duplicating the existing aggregation machinery.

**Architecture:** Reuse `globalResidualGroupedLeft_square_dvd_residual` for arbitrary pairwise-coprime same-owner aggregation; do not re-prove its finite-product theorem.  Combine that square divisor with the exact `18/13` ratio ceiling from `Erdos686LargePrimeGapComponent`, then instantiate the same inequality directly for two full large-prime components whose gap is their product.  Keep all new files isolated and defer every Lean invocation until the parent releases the build embargo.

**Tech Stack:** Lean 4/mathlib, exact Python integer arithmetic, pytest.

---

### Task 1: Audit subsumption and freeze the exact inequality

**Files:**
- Create: `compute/campaign686/agent_t2_large_prime_same_owner/same_owner_verify.py`
- Create: `compute/campaign686/agent_t2_large_prime_same_owner/test_same_owner_verify.py`
- Create: `compute/campaign686/agent_t2_large_prime_same_owner/findings.md`

**Steps:**
1. Record that `Erdos686TwoOwnerGrouping.globalResidualGroupedLeft_square_dvd_residual` already proves the pairwise-coprime product-square divisibility.
2. Verify symbolically that `h^2 | X_i`, `X_i>0`, and the exact ratio ceiling imply `6h^2 < (13k-6)d+18(k-1)`.
3. Verify that `d=p^e q^f`, `p,q>=k>=16`, and positive exponents imply `(13k-6)d+18(k-1)<=6d^2`.
4. Add boundary tests at `k=16`, `p=17`, `q=19`, `e=f=1`, plus monotonic sweeps over exact integers.
5. Do not run Lean.

### Task 2: Draft the nonduplicative Lean aggregate

**Files:**
- Create: `ErdosProblems/Erdos686LargePrimeSameOwner.lean`

**Steps:**
1. Prove the generic square-divisor strict upper bound for `localResidual` from the existing `18/13` ratio theorem.
2. Apply the existing grouped-owner square theorem to obtain a strict upper bound for every certified owner bucket.
3. State the explicit dominance no-solution theorem for a grouped owner bucket.
4. Derive the arithmetic dominance inequality for a whole two-large-prime gap.
5. Derive an all-parity `k>=16` theorem giving distinct unique localization owners for the two full prime-power components.
6. Add `#print axioms` commands, but do not invoke Lean until released.

### Task 3: Hostile audit

**Files:**
- Create: `compute/campaign686/agent_t2_large_prime_same_owner/hostile_audit.md`

**Steps:**
1. State the exact dependency tree and distinguish reused aggregation from new dominance.
2. Audit `k=16`, exponent-one components, the strict inequality boundary, primes below `k`, extra gap factors, and distinct-owner survivors.
3. Explain why the result is a genuine mixed-gap subclass rather than a target-strength premise.
4. Scan the draft for `native_decide`, `sorry`, `admit`, and new axioms without running Lean.
5. Record source hashes and mark kernel status as `DRAFT/NOT BUILT` until the embargo is lifted.
