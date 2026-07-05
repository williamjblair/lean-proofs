# Erdős 699 T7 Odd-Factor Parity Wrapper Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Remove explicit `X` parity hypotheses from Case-I row-one and factor-square wrappers when the normalized cofactor `F` is odd and `4 | n`.

**Architecture:** Prove the arithmetic bridge `4 | F * X` and `Odd F` imply `4 | X`. Then use it to supply the existing `2 | X` and `4 ≤ X` inputs for row-one cofactor squeeze, and the existing `2 | X` input for the `4 | n` factor-square squeeze.

**Tech Stack:** Lean 4, Mathlib, existing `lean/Erdos699/Proved/Basic.lean`.

---

### Task 1: Add Red Lean Checks

**Files:**
- Create: `lean/Erdos699/WIP/OddFactorParityCheck.lean`

- [x] **Step 1: Add planned theorem checks**

```lean
import Erdos699.Proved.Basic

namespace Erdos699

#check four_dvd_right_factor_of_four_dvd_mul_odd
#check i_three_caseI_row_one_four_mul_factor_le_X_of_four_dvd_odd_factor_from_row_bound
#check i_three_caseI_factor_sq_squeeze_of_four_dvd_odd_factor_from_row_bound

end Erdos699
```

- [x] **Step 2: Run and verify RED**

Run: `lake env lean lean/Erdos699/WIP/OddFactorParityCheck.lean`

Expected: FAIL because the theorem names are not defined yet.

### Task 2: Prove Odd-Factor Parity Bridge and Wrappers

**Files:**
- Modify: `lean/Erdos699/Proved/Basic.lean`

- [x] **Step 1: Add arithmetic parity bridge**

Add before the row-one cofactor wrappers:

```lean
theorem four_dvd_right_factor_of_four_dvd_mul_odd {F X : ℕ}
    (hFodd : Odd F) (h4 : 4 ∣ F * X) :
    4 ∣ X := by
  have h2mul : 2 ∣ F * X := Nat.dvd_trans (by norm_num : 2 ∣ 4) h4
  have h2X : 2 ∣ X := by
    rcases (by decide : Nat.Prime 2).dvd_mul.mp h2mul with h2F | h2X
    · have hnot_odd : ¬ Odd F :=
        Nat.not_odd_iff_even.mpr (even_iff_two_dvd.mpr h2F)
      exact False.elim (hnot_odd hFodd)
    · exact h2X
  rcases h2X with ⟨Y, hX⟩
  subst X
  have h2FY : 2 ∣ F * Y := by
    rcases h4 with ⟨a, ha⟩
    refine ⟨a, ?_⟩
    have hdouble : F * Y * 2 = (2 * a) * 2 := by
      calc
        F * Y * 2 = F * (2 * Y) := by ring
        _ = 4 * a := ha
        _ = (2 * a) * 2 := by ring
    exact Nat.mul_right_cancel (by decide : 0 < 2) hdouble
  have h2Y : 2 ∣ Y := by
    rcases (by decide : Nat.Prime 2).dvd_mul.mp h2FY with h2F | h2Y
    · have hnot_odd : ¬ Odd F :=
        Nat.not_odd_iff_even.mpr (even_iff_two_dvd.mpr h2F)
      exact False.elim (hnot_odd hFodd)
    · exact h2Y
  rcases h2Y with ⟨Z, hY⟩
  refine ⟨Z, ?_⟩
  omega
```

- [x] **Step 2: Add row-one cofactor wrapper**

```lean
theorem i_three_caseI_row_one_four_mul_factor_le_X_of_four_dvd_odd_factor_from_row_bound
    {n F X j t : ℕ}
    (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor n 3 j q)
    (hn : n = F * X) (hj : j = F * t) (hn_gt : 2 < n) (hj_pos : 0 < j)
    (h2n : 2 ∣ n) (h3n : 3 ∣ n) (h4n : 4 ∣ n) (hFodd : Odd F)
    (hjn : 2 * j ≤ n) :
    4 * F ≤ X := by
  have h4X : 4 ∣ X := four_dvd_right_factor_of_four_dvd_mul_odd hFodd (by
    simpa [hn] using h4n)
  have hX_even : 2 ∣ X := Nat.dvd_trans (by norm_num : 2 ∣ 4) h4X
  have hX_pos : 0 < X := by
    by_contra hnot
    have hX0 : X = 0 := Nat.eq_zero_of_not_pos hnot
    subst X
    omega
  have hX_four : 4 ≤ X := Nat.le_of_dvd hX_pos h4X
  exact i_three_caseI_row_one_four_mul_factor_le_X_from_row_bound
    hnone hn hj hn_gt hj_pos h2n h3n hX_even hX_four hjn
```

- [x] **Step 3: Add factor-square wrapper**

```lean
theorem i_three_caseI_factor_sq_squeeze_of_four_dvd_odd_factor_from_row_bound
    {n F X j t : ℕ}
    (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor n 3 j q)
    (hn : n = F * X) (hj : j = F * t) (hn_gt : 2 < n) (hj_pos : 0 < j)
    (hj_two : 2 ≤ j) (h2n : 2 ∣ n) (h3n : 3 ∣ n) (h4n : 4 ∣ n)
    (hFodd : Odd F) (hjn : 2 * j ≤ n) :
    2 * (F * F) ≤ X := by
  have h4X : 4 ∣ X := four_dvd_right_factor_of_four_dvd_mul_odd hFodd (by
    simpa [hn] using h4n)
  have hX_even : 2 ∣ X := Nat.dvd_trans (by norm_num : 2 ∣ 4) h4X
  exact i_three_caseI_factor_sq_squeeze_of_four_dvd_from_row_bound
    hnone hn hj hn_gt hj_pos hj_two h2n h3n h4n hX_even hjn
```

- [x] **Step 4: Run focused Lean check**

Run:

```bash
lake build Erdos699.Proved.Basic
lake env lean lean/Erdos699/WIP/OddFactorParityCheck.lean
```

Expected: PASS.

### Task 3: Document and Verify

**Files:**
- Modify: `notes/PROGRESS.md`

- [x] **Step 1: Update progress log**

Add an `[R]` entry naming:
- `Erdos699.four_dvd_right_factor_of_four_dvd_mul_odd`
- `Erdos699.i_three_caseI_row_one_four_mul_factor_le_X_of_four_dvd_odd_factor_from_row_bound`
- `Erdos699.i_three_caseI_factor_sq_squeeze_of_four_dvd_odd_factor_from_row_bound`

State that this is a normalized odd-cofactor wrapper, not full T7.

- [x] **Step 2: Run final verification and commit**

Run:

```bash
lake env lean lean/Erdos699/WIP/OddFactorParityCheck.lean
lake env lean lean/Erdos699/Proved/Basic.lean
rg -n "sorry|admit" lean/Erdos699/Proved
git diff --check
lake build Erdos699.Proved.Basic
lake build
bash scripts/check_manifest.sh
bash scripts/check_axioms.sh
python3 -m pytest compute/tests/test_criterion.py compute/tests/test_scan.py -q
```

Commit:

```bash
git add lean/Erdos699/Proved/Basic.lean lean/Erdos699/WIP/OddFactorParityCheck.lean \
  notes/PROGRESS.md docs/superpowers/plans/2026-07-05-erdos699-t7-odd-factor-parity.md
git commit -m "feat: prove erdos699 odd-factor parity wrappers"
```
