# Erdős 686 Any-Position Prime-Power Obstruction Implementation Plan

> **For Claude:** REQUIRED SUB-SKILL: Use superpowers:executing-plans to implement this plan task-by-task.

**Goal:** Prove the strongest valid any-position prime-power obstruction, record exact internal-position counterfixtures to the all-prime claim, and expose a target-facing theorem for every prime base larger than the block length.

**Architecture:** First freeze the exact split-factorial valuation model at an internal owner and test the proposed universal claim adversarially. Then add a reusable Lean core whose explicit hypotheses place the upper block in `(p^A,2p^A)` and assume `p>k`, so valuation concentration loses no factorial power. Derive the `k>=16,d>=k` equation-facing corollary from the banked `9d<n` bound, retain the all-prime endpoint theorem, and update the hostile audit without editing shared registries.

**Tech Stack:** Lean 4/mathlib exact factorization, Python 3 integer valuation checks, pytest.

---

### Task 1: Freeze internal-position counterfixtures

**Files:**
- Modify: `compute/campaign686/agent_t2_small_prime_band/small_prime_band_verify.py`
- Modify: `compute/campaign686/agent_t2_small_prime_band/test_small_prime_band_verify.py`

**Steps:**
1. Implement the exact split valuation `A+v_p((i-1)!)+v_p((k-i)!)` for a lower owner `n+i=p^A`.
2. Compute the upper valuation as the exact shifted factorial quotient.
3. Add fixtures where the discrepancy is exactly `2` for `p=2` and `0` for odd `p`, under `k>=16`, `k<=d`, and `9d<n`.
4. Run the focused tests and require the fixtures to falsify only the proposed valuation contradiction, not the full product equation.

### Task 2: Prove the explicit interval core

**Files:**
- Modify: `ErdosProblems/Erdos686SmallPrimeBand.lean`

**Steps:**
1. State a theorem for prime `p`, owner `i in Icc 1 k`, `n+i=p^A`, `k<p`, and explicit inequalities `p^A<n+d+1` and `n+d+k<2p^A`.
2. Show `p^A` divides the lower block and hence its valuation is at least `A`.
3. Apply valuation concentration to the upper block and prove `v_p((k-1)!)=0` from `p>k`.
4. Bound the concentrated owner valuation by `A-1` because it lies strictly in `(p^A,2p^A)`.
5. Factor the quotient-four equation at `p` and derive the contradiction.

### Task 3: Derive the target-facing any-position theorem

**Files:**
- Modify: `ErdosProblems/Erdos686SmallPrimeBand.lean`

**Steps:**
1. Assume `k>=16`, `k<=d`, `p>k`, `i in Icc 1 k`, and `n+i=p^A`.
2. Under a hypothetical equation, invoke `nine_mul_gap_lt_n_of_four_solution`.
3. Derive the two explicit interval inequalities using `i<=k<=d` and `k<=d<n/9`.
4. Apply the interval core.
5. Print axioms for the new theorem surfaces.

### Task 4: Audit and freeze

**Files:**
- Modify: `compute/campaign686/agent_t2_small_prime_band/findings.md`
- Modify: `compute/campaign686/agent_t2_small_prime_band/hostile_audit.md`

**Steps:**
1. Audit `p=2`, odd `p`, `i=1`, `i=k`, small `A`, and both named row-prefix fixtures.
2. State explicitly that arbitrary internal positions at `p<=k` remain open and give the exact split-factorial correction.
3. Run direct Lean compilation, focused pytest, forbidden-token scan, and `git diff --check`.
4. Freeze SHA-256 hashes and report theorem names without touching aggregate manifests or registries.
