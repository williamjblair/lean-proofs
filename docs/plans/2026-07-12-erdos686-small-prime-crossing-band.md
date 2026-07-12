# Erdős 686 Small-Prime Crossing-Band Implementation Plan

> **For Claude:** REQUIRED SUB-SKILL: Use superpowers:executing-plans to implement this plan task-by-task.

**Goal:** Determine whether exact valuations at primes `p<=k`, together with the exact quotient-four crossing band, exclude a rigorously unbounded subset of Target 2.

**Architecture:** Add an isolated exact-arithmetic scanner. For each `(k,d)`, binary-search the two integer power inequalities defining the full necessary `n`-band, evaluate block valuation differences through Legendre floor sums, and retain only points with discrepancy `2` at `p=2` and `0` at every odd prime `p<=k`. Analyze survivor periodicity and carries; formalize only a structural family that is genuinely unbounded and whose proof does not depend on a finite cutoff.

**Tech Stack:** Python 3 exact integers, `pytest`, Lean 4/mathlib if an unbounded theorem emerges.

---

### Task 1: Exact crossing-band scanner

**Files:**
- Create: `compute/campaign686/agent_t2_small_prime_band/small_prime_band_verify.py`
- Create: `compute/campaign686/agent_t2_small_prime_band/test_small_prime_band_verify.py`

**Steps:**
1. Implement exact monotone binary searches for the least `n` satisfying `(n+d+k)^k<=4(n+k)^k` and the greatest `n` satisfying `4(n+1)^k<=(n+d+1)^k`.
2. Prove in code assertions that every returned endpoint is maximal/minimal and replay direct products for small cases.
3. Implement prime generation and exact Legendre/block valuation differences.
4. Retain only the quotient-four valuation vector.

### Task 2: Fixture and scale audit

**Files:**
- Modify: `compute/campaign686/agent_t2_small_prime_band/small_prime_band_verify.py`

**Steps:**
1. Replay `(984,3177026,4480)` and `(244,48502,277)` exactly.
2. Replay the `n=48502` row-prefix claim and all named large-`k` crossing inequalities.
3. Scan structured grids in `k`, `d/k`, prime and composite `d`, and large decimal scales.
4. Record all survivor counts, first failing primes, and normalized residues.

### Task 3: Structural carry analysis

**Files:**
- Create: `compute/campaign686/agent_t2_small_prime_band/findings.md`

**Steps:**
1. Express each discrepancy as an exact sum of four floor terms for powers `p^a`.
2. Test congruence classes of `k` and `d` suggested by the scan across escalating scales.
3. Attempt a carry-count proof for one unbounded family.
4. Falsify every proposed family beyond the discovery range before formalization.

### Task 4: Formalize or state the obstruction

**Files:**
- Create if justified: `ErdosProblems/Erdos686SmallPrimeBand.lean`
- Create: `compute/campaign686/agent_t2_small_prime_band/hostile_audit.md`

**Steps:**
1. If a structural family survives adversarial search, prove its floor/carry lemma and equation-facing no-solution theorem in Lean.
2. Otherwise bank the exact scanner and state one quantified obstruction explaining why the valuation system alone remains non-closing.
3. Run tests, forbidden-token scans, exact fixture reproduction, and `git diff --check`.
