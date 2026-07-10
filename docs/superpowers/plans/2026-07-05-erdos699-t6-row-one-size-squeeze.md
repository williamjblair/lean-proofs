# Erdos699 T6 Row One Size Squeeze Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Prove the Lean-friendly T6 row-one size squeeze `4 * (n - 1) ≤ X * X` from the existing normalized divisor `n - 1 ∣ t * (X - t)`.

**Architecture:** Add a small exact quadratic inequality for `t * (X - t)`, a divisor-to-size wrapper, a generic factorization theorem, and the row-3 Case-I instantiation. Keep the statement in integer form rather than square-root form; full T6/T7 remain open.

**Tech Stack:** Lean 4, Mathlib arithmetic tactics, existing `Erdos699.Proved.Basic`, exact Python criterion tests.

---

### Task 1: Red WIP API Check

**Files:**
- Create: `lean/Erdos699/WIP/T6RowOneSizeSqueezeTest.lean`

- [x] **Step 1: Write the failing API check**

```lean
import Erdos699.Proved.Basic

#check Erdos699.four_mul_t_mul_X_sub_t_le_sq
#check Erdos699.four_mul_d_le_sq_of_dvd_t_mul_X_sub_t
#check Erdos699.four_mul_sub_one_le_sq_of_factor_dvd_mul_sub_one
#check Erdos699.i_three_caseI_row_one_four_mul_sub_one_le_X_sq
```

- [x] **Step 2: Run Lean and confirm expected failure**

```bash
lake env lean lean/Erdos699/WIP/T6RowOneSizeSqueezeTest.lean
```

Expected: unknown constants for the four new theorem names.

### Task 2: Add the Quadratic Bound

**Files:**
- Modify: `lean/Erdos699/Proved/Basic.lean`

- [x] **Step 1: Add `four_mul_t_mul_X_sub_t_le_sq` after the row-one normalized divisor theorem**

```lean
theorem four_mul_t_mul_X_sub_t_le_sq {X t : ℕ} (h2tX : 2 * t ≤ X) :
    4 * (t * (X - t)) ≤ X * X := by
  have htX : t ≤ X := by omega
  have hcast_sub : ((X - t : ℕ) : ℤ) = (X : ℤ) - (t : ℤ) := Nat.cast_sub htX
  have hcalc : (4 : ℤ) * ((t : ℤ) * ((X : ℤ) - (t : ℤ))) ≤
      (X : ℤ) * (X : ℤ) := by
    nlinarith [sq_nonneg ((X : ℤ) - 2 * (t : ℤ))]
  have h_int : ((4 * (t * (X - t)) : ℕ) : ℤ) ≤ ((X * X : ℕ) : ℤ) := by
    simpa [hcast_sub] using hcalc
  exact_mod_cast h_int
```

### Task 3: Add Divisor-to-Size Wrappers

**Files:**
- Modify: `lean/Erdos699/Proved/Basic.lean`

- [x] **Step 1: Add `four_mul_d_le_sq_of_dvd_t_mul_X_sub_t`**

```lean
theorem four_mul_d_le_sq_of_dvd_t_mul_X_sub_t {d X t : ℕ}
    (ht_pos : 0 < t) (h2tX : 2 * t ≤ X) (hdvd : d ∣ t * (X - t)) :
    4 * d ≤ X * X := by
  have htX : t ≤ X := by omega
  have hXt_pos : 0 < X - t := by omega
  have hprod_pos : 0 < t * (X - t) := Nat.mul_pos ht_pos hXt_pos
  have hd_le : d ≤ t * (X - t) := Nat.le_of_dvd hprod_pos hdvd
  exact (Nat.mul_le_mul_left 4 hd_le).trans (four_mul_t_mul_X_sub_t_le_sq h2tX)
```

- [x] **Step 2: Add `four_mul_sub_one_le_sq_of_factor_dvd_mul_sub_one`**

```lean
theorem four_mul_sub_one_le_sq_of_factor_dvd_mul_sub_one {n F X j t : ℕ}
    (hn : n = F * X) (hj : j = F * t) (hn_gt : 2 < n) (hj_pos : 0 < j)
    (h2tX : 2 * t ≤ X) (hdvd : n - 1 ∣ j * (j - 1)) :
    4 * (n - 1) ≤ X * X := by
  have ht_pos : 0 < t := by
    by_cases ht0 : t = 0
    · subst t
      simp at hj
      omega
    · exact Nat.pos_of_ne_zero ht0
  exact four_mul_d_le_sq_of_dvd_t_mul_X_sub_t ht_pos h2tX
    (sub_one_dvd_t_mul_X_sub_t_of_factor_dvd_mul_sub_one
      hn hj hn_gt hj_pos (by omega : t ≤ X) hdvd)
```

### Task 4: Add Row-3 Case-I Instantiation

**Files:**
- Modify: `lean/Erdos699/Proved/Basic.lean`

- [x] **Step 1: Add `i_three_caseI_row_one_four_mul_sub_one_le_X_sq`**

```lean
theorem i_three_caseI_row_one_four_mul_sub_one_le_X_sq {n F X j t : ℕ}
    (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor n 3 j q)
    (hn : n = F * X) (hj : j = F * t) (hn_gt : 2 < n) (hj_pos : 0 < j)
    (h2n : 2 ∣ n) (h3n : 3 ∣ n) (h2tX : 2 * t ≤ X) :
    4 * (n - 1) ≤ X * X :=
  four_mul_sub_one_le_sq_of_factor_dvd_mul_sub_one hn hj hn_gt hj_pos h2tX
    (i_three_window_one_sub_one_dvd_mul_sub_one_of_even_three_dvd
      hnone (by omega : 1 < n) h2n h3n)
```

### Task 5: Verification, Progress, and Commit

**Files:**
- Modify: `notes/PROGRESS.md`
- Delete: `lean/Erdos699/WIP/T6RowOneSizeSqueezeTest.lean`

- [x] **Step 1: Run WIP API check green and remove the WIP file**

```bash
lake build Erdos699.Proved.Basic
lake env lean lean/Erdos699/WIP/T6RowOneSizeSqueezeTest.lean
```

Expected: Lean prints all four theorem signatures. Then delete the WIP API file.

- [x] **Step 2: Add the `[R]` progress entry**

```md
- [R] Proved the T6 row-one size squeeze:
  `Erdos699.i_three_caseI_row_one_four_mul_sub_one_le_X_sq` turns the
  normalized case-I divisor into `4 * (n - 1) ≤ X * X` under `2 * t ≤ X`.
  This is the exact-integer version of the `n - 1 ≤ X^2/4` bound. Full T6/T7
  remain open.
```

- [x] **Step 3: Run verification gates**

```bash
lake env lean lean/Erdos699/Proved/Basic.lean
python3 -m pytest compute/tests/test_criterion.py -q
rg -n "\bsorry\b|\badmit\b" lean/Erdos699/Proved || true
git diff --check
lake build
bash scripts/check_axioms.sh
bash scripts/check_manifest.sh
lake env lean --stdin <<'EOF'
import Erdos699.Proved.Basic
#print axioms Erdos699.i_three_caseI_row_one_four_mul_sub_one_le_X_sq
EOF
```

- [x] **Step 4: Commit the milestone**

```bash
git add docs/superpowers/plans/2026-07-05-erdos699-t6-row-one-size-squeeze.md lean/Erdos699/Proved/Basic.lean notes/PROGRESS.md
git commit -m "feat: prove erdos699 t6 row one size squeeze"
```
