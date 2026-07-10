# Erdős 699 T2 Collapse Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Prove the `i = 2` collapse sublemma: if there is no relevant common prime divisor for `C(n,2)` and `C(n,j)`, with `2 < j` and `2 * j <= n`, then `n = 2 * j` and `j` is odd.

**Architecture:** Add small reusable divisibility helpers in `lean/Erdos699/Proved/Basic.lean`: the binomial identity `n | j * C(n,j)`, Lucas-based proof that prime divisors of the relevant part of `n` divide `C(n,2)`, and a coprimality wrapper from the no-common-prime assumption. Use these to eliminate `n` odd and `4 | n`, then show the half of `n` divides `j` and hence equals `j`.

**Tech Stack:** Lean 4.29.1, Mathlib 4.29.1, exact Python criterion tests, repository shell gates.

---

### Task 1: Add The Failing Lean Check

**Files:**
- Create: `lean/Erdos699/WIP/T2CollapseTest.lean`

- [x] **Step 1: Write the failing check**

```lean
import Erdos699.Proved.Basic

#check Erdos699.t2_collapse_of_no_common
```

- [x] **Step 2: Run the check and verify it fails**

Run: `lake env lean lean/Erdos699/WIP/T2CollapseTest.lean`

Expected: FAIL with an unknown identifier error for
`Erdos699.t2_collapse_of_no_common`.

### Task 2: Prove The Collapse

**Files:**
- Modify: `lean/Erdos699/Proved/Basic.lean`
- Delete: `lean/Erdos699/WIP/T2CollapseTest.lean`

- [x] **Step 1: Add helper lemmas**

Add helper lemmas before `t1_i_eq_one`:

```lean
theorem n_dvd_mul_choose_self {n j : ℕ} (hn : 0 < n) (hj : 0 < j) :
    n ∣ j * Nat.choose n j := by
  ...

theorem prime_dvd_choose_two_of_odd_prime_dvd {n p : ℕ} (hp : p.Prime)
    (hp_ne_two : p ≠ 2) (hpn : p ∣ n) :
    p ∣ Nat.choose n 2 := by
  ...

theorem two_dvd_choose_two_of_four_dvd {n : ℕ} (h4 : 4 ∣ n) :
    2 ∣ Nat.choose n 2 := by
  ...
```

- [x] **Step 2: Add the collapse theorem**

Add after the helpers:

```lean
theorem t2_collapse_of_no_common {n j : ℕ}
    (hnone : ∀ p : ℕ, ¬ commonPrimeDivisor n 2 j p)
    (hj : 2 < j) (hjn : 2 * j ≤ n) :
    n = 2 * j ∧ Odd j := by
  ...
```

- [x] **Step 3: Run the targeted Lean file**

Run: `lake env lean lean/Erdos699/Proved/Basic.lean`

Expected: PASS.

- [x] **Step 4: Rebuild and rerun the WIP check**

Run:

```bash
lake build Erdos699
lake env lean lean/Erdos699/WIP/T2CollapseTest.lean
```

Expected: PASS and print the theorem declaration.

### Task 3: Update Notes And Gates

**Files:**
- Modify: `notes/PROGRESS.md`

- [x] **Step 1: Mark only the collapse as `[R]`**

Add:

```markdown
- [R] Proved `Erdos699.t2_collapse_of_no_common`: under the no-common-prime
  assumption for row `i = 2`, `2 < j`, and `2 * j <= n`, the obstruction
  collapses to `n = 2 * j` with `j` odd. The final T2 forced-digit kill is
  still open.
```

- [x] **Step 2: Run repository gates**

Run:

```bash
python3 -m pytest compute/tests/test_criterion.py -q
lake build
bash scripts/check_axioms.sh
bash scripts/check_manifest.sh
lake env lean --stdin <<'EOF'
import Erdos699.Proved.Basic
#print axioms Erdos699.t2_collapse_of_no_common
EOF
git diff --check
```

Expected: all commands pass; the direct axiom report is only
`[propext, Classical.choice, Quot.sound]`.

- [x] **Step 3: Commit the milestone**

Run:

```bash
git add docs/superpowers/plans/2026-07-05-erdos699-t2-collapse.md \
  lean/Erdos699/Proved/Basic.lean notes/PROGRESS.md
git commit -m "feat: prove erdos699 t2 collapse"
```
