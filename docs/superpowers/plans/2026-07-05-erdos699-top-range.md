# Erdős 699 Top-Range Lemma Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Prove the Tier A top-range lemma: a prime in the interval `(n - i, n]` gives a relevant common prime divisor for rows `i` and `j` when `i < j` and `2 * j <= n`.

**Architecture:** Reuse the existing `digit`, `dominated`, Lucas bridge, and `commonPrimeDivisor` definitions in `lean/Erdos699/Proved/Basic.lean`. Add a small digit helper showing `¬ dominated k n p` when the units digit of `n` is below `k < p`, then derive divisibility of `Nat.choose n k` through the existing Lucas bridge.

**Tech Stack:** Lean 4.29.1, Mathlib 4.29.1, exact Python criterion tests, repository shell gates.

---

### Task 1: Add The Failing Lean Check

**Files:**
- Create: `lean/Erdos699/WIP/TopRangeTest.lean`

- [x] **Step 1: Write the failing check**

```lean
import Erdos699.Proved.Basic

#check Erdos699.commonPrimeDivisor_of_prime_in_top_interval
```

- [x] **Step 2: Run the check and verify it fails**

Run: `lake env lean lean/Erdos699/WIP/TopRangeTest.lean`

Expected: FAIL with an unknown constant error for
`Erdos699.commonPrimeDivisor_of_prime_in_top_interval`.

### Task 2: Prove Top-Range Divisibility

**Files:**
- Modify: `lean/Erdos699/Proved/Basic.lean`
- Delete: `lean/Erdos699/WIP/TopRangeTest.lean`

- [x] **Step 1: Add the helper statements**

Add the following declarations after `lucas_nonzero_mod_prime_iff_dominated`:

```lean
theorem prime_dvd_choose_of_not_dominated {n k p : ℕ} (hp : p.Prime)
    (hnd : ¬ dominated k n p) :
    p ∣ Nat.choose n k := by
  ...

theorem not_dominated_of_units_digit_lt {n k p : ℕ} (hp : p.Prime)
    (hpn : p ≤ n) (hn2p : n < 2 * p) (hlow : n - p < k) (hhigh : k < p) :
    ¬ dominated k n p := by
  ...

theorem prime_dvd_choose_of_units_digit_lt {n k p : ℕ} (hp : p.Prime)
    (hpn : p ≤ n) (hn2p : n < 2 * p) (hlow : n - p < k) (hhigh : k < p) :
    p ∣ Nat.choose n k := by
  ...
```

- [x] **Step 2: Add the Tier A top-range theorem**

Add this theorem before `t1_i_eq_one`:

```lean
theorem commonPrimeDivisor_of_prime_in_top_interval {n i j p : ℕ}
    (hp : p.Prime) (hij : i < j) (hjn : 2 * j ≤ n) (hleft : n - i < p)
    (hright : p ≤ n) :
    commonPrimeDivisor n i j p := by
  ...
```

- [x] **Step 3: Run the targeted Lean check**

Run: `lake env lean lean/Erdos699/Proved/Basic.lean`

Expected: PASS.

### Task 3: Update Notes And Gates

**Files:**
- Modify: `notes/PROGRESS.md`

- [x] **Step 1: Mark only the proved theorem as `[R]`**

Replace the final open line with:

```markdown
- [R] Proved the top-range lemma
  `Erdos699.commonPrimeDivisor_of_prime_in_top_interval`: if
  `p` is prime, `n - i < p ≤ n`, `i < j`, and `2 * j ≤ n`, then `p`
  is a relevant common prime divisor of `C(n,i)` and `C(n,j)`.
- [OPEN] T2, full T3 confinement beyond the top-range lemma, and all later
  rungs remain unclaimed in this branch.
```

- [x] **Step 2: Run repository gates**

Run:

```bash
python3 -m pytest compute/tests/test_criterion.py -q
lake build
bash scripts/check_axioms.sh
bash scripts/check_manifest.sh
git diff --check
```

Expected: all commands pass.

- [x] **Step 3: Commit the milestone**

Run:

```bash
git add docs/superpowers/plans/2026-07-05-erdos699-top-range.md \
  lean/Erdos699/Proved/Basic.lean notes/PROGRESS.md
git commit -m "feat: prove erdos699 top-range lemma"
```
