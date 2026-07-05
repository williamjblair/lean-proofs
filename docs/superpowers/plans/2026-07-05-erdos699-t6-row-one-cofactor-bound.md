# Erdos699 T6 Row One Cofactor Bound Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Prove the Lean-friendly T6 cofactor squeeze `4 * F ≤ X` from the row-one size bound `4 * (n - 1) ≤ X * X` when `n = F * X`, `X` is even, and `4 ≤ X`.

**Architecture:** Add one generic arithmetic theorem converting the square bound into a cofactor bound, then instantiate it with the existing row-3 Case-I size squeeze. The theorem is explicitly conditional on `2 ∣ X`; this matches the even Case-I block and avoids a false generic statement for odd or tiny `X`.

**Tech Stack:** Lean 4, Mathlib arithmetic tactics, existing `Erdos699.Proved.Basic`, exact Python criterion tests.

---

### Task 1: Red WIP API Check

**Files:**
- Create: `lean/Erdos699/WIP/T6RowOneCofactorBoundTest.lean`

- [x] **Step 1: Write the failing API check**

```lean
import Erdos699.Proved.Basic

#check Erdos699.four_mul_factor_le_of_even_four_le_of_four_mul_sub_one_le_sq
#check Erdos699.i_three_caseI_row_one_four_mul_factor_le_X
```

- [x] **Step 2: Run Lean and confirm expected failure**

```bash
lake env lean lean/Erdos699/WIP/T6RowOneCofactorBoundTest.lean
```

Expected: unknown constants for the two new theorem names.

### Task 2: Add Generic Cofactor Bound

**Files:**
- Modify: `lean/Erdos699/Proved/Basic.lean`

- [x] **Step 1: Add `four_mul_factor_le_of_even_four_le_of_four_mul_sub_one_le_sq` after the row-one size squeeze**

```lean
theorem four_mul_factor_le_of_even_four_le_of_four_mul_sub_one_le_sq {n F X : ℕ}
    (hn : n = F * X) (hX_even : 2 ∣ X) (hX_four : 4 ≤ X)
    (hsize : 4 * (n - 1) ≤ X * X) :
    4 * F ≤ X := by
  by_contra hnot
  have hlt : X < 4 * F := Nat.lt_of_not_ge hnot
  have hn_pos : 0 < n := by
    subst n
    have hF_pos : 0 < F := by omega
    have hX_pos : 0 < X := by omega
    exact Nat.mul_pos hF_pos hX_pos
  have hcast_sub : ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 :=
    Nat.cast_sub (by omega : 1 ≤ n)
  have hsize_int : (4 : ℤ) * ((n : ℤ) - 1) ≤ (X : ℤ) * (X : ℤ) := by
    have h := hsize
    have hcast : ((4 * (n - 1) : ℕ) : ℤ) = (4 : ℤ) * ((n : ℤ) - 1) := by
      rw [Nat.cast_mul, hcast_sub]
      norm_num
    have hcast_right : ((X * X : ℕ) : ℤ) = (X : ℤ) * (X : ℤ) := by norm_num
    exact hcast ▸ hcast_right ▸ (by exact_mod_cast h)
  have hn_int : (n : ℤ) = (F : ℤ) * (X : ℤ) := by exact_mod_cast hn
  have hdiff_ge_two_nat : 2 ≤ 4 * F - X := by
    rcases hX_even with ⟨a, ha⟩
    subst X
    have hdiff_pos : 0 < 4 * F - 2 * a := by omega
    have hdiff_even : 2 ∣ 4 * F - 2 * a := by
      refine ⟨2 * F - a, ?_⟩
      omega
    rcases hdiff_even with ⟨b, hb⟩
    have hb_pos : 0 < b := by omega
    omega
  have hcast_diff : ((4 * F - X : ℕ) : ℤ) = (4 : ℤ) * (F : ℤ) - (X : ℤ) :=
    Nat.cast_sub hlt.le
  have hdiff_ge_two : (2 : ℤ) ≤ (4 : ℤ) * (F : ℤ) - (X : ℤ) := by
    have h : (2 : ℤ) ≤ ((4 * F - X : ℕ) : ℤ) := by exact_mod_cast hdiff_ge_two_nat
    simpa [hcast_diff] using h
  have hX_four_int : (4 : ℤ) ≤ X := by exact_mod_cast hX_four
  nlinarith
```

### Task 3: Add Row-3 Case-I Instantiation

**Files:**
- Modify: `lean/Erdos699/Proved/Basic.lean`

- [x] **Step 1: Add `i_three_caseI_row_one_four_mul_factor_le_X`**

```lean
theorem i_three_caseI_row_one_four_mul_factor_le_X {n F X j t : ℕ}
    (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor n 3 j q)
    (hn : n = F * X) (hj : j = F * t) (hn_gt : 2 < n) (hj_pos : 0 < j)
    (h2n : 2 ∣ n) (h3n : 3 ∣ n) (hX_even : 2 ∣ X) (hX_four : 4 ≤ X)
    (h2tX : 2 * t ≤ X) :
    4 * F ≤ X :=
  four_mul_factor_le_of_even_four_le_of_four_mul_sub_one_le_sq hn hX_even hX_four
    (i_three_caseI_row_one_four_mul_sub_one_le_X_sq
      hnone hn hj hn_gt hj_pos h2n h3n h2tX)
```

### Task 4: Verification, Progress, and Commit

**Files:**
- Modify: `notes/PROGRESS.md`
- Delete: `lean/Erdos699/WIP/T6RowOneCofactorBoundTest.lean`

- [x] **Step 1: Run WIP API check green and remove the WIP file**

```bash
lake build Erdos699.Proved.Basic
lake env lean lean/Erdos699/WIP/T6RowOneCofactorBoundTest.lean
```

Expected: Lean prints both theorem signatures. Then delete the WIP API file.

- [x] **Step 2: Add the `[R]` progress entry**

```md
- [R] Proved the T6 row-one cofactor squeeze:
  `Erdos699.i_three_caseI_row_one_four_mul_factor_le_X` turns the row-one
  square bound into `4 * F ≤ X` when `n = F * X`, `2 ∣ X`, and `4 ≤ X`.
  This is the exact cofactor form of the first-row thin-family constraint.
  Full T6/T7 remain open.
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
#print axioms Erdos699.i_three_caseI_row_one_four_mul_factor_le_X
EOF
```

- [x] **Step 4: Commit the milestone**

```bash
git add docs/superpowers/plans/2026-07-05-erdos699-t6-row-one-cofactor-bound.md lean/Erdos699/Proved/Basic.lean notes/PROGRESS.md
git commit -m "feat: prove erdos699 t6 row one cofactor bound"
```
