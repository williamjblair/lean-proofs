# Erdos699 T7 Joint Large-Part Cancellation Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Prove the T7 support cancellation: if `t * (X - t) = g * (n - 1)`, then the row-two large-prime part divides `g * (X - 2 * t)`.

**Architecture:** Add a generic coprime cancellation lemma, an existence wrapper, a proof that `primePowerPartGE 5 (n - 2)` is coprime to `n - 1`, and a row-3 Case-I instantiation using the existing second-row normalized divisor. This is the algebraic cancellation core of the T7 joint-row squeeze, but it still only uses the large-prime part and does not claim full T7.

**Tech Stack:** Lean 4, Mathlib `Nat.Coprime`, existing `Erdos699.Proved.Basic`, exact Python criterion tests.

---

### Task 1: Red WIP API Check

**Files:**
- Create: `lean/Erdos699/WIP/T7JointLargePartCancellationTest.lean`

- [x] **Step 1: Write the failing API check**

```lean
import Erdos699.Proved.Basic

#check Erdos699.dvd_factor_mul_of_eq_mul_and_coprime
#check Erdos699.exists_factor_dvd_factor_mul_of_dvd_and_coprime
#check Erdos699.primePowerPartGE_five_sub_two_coprime_sub_one
#check Erdos699.i_three_caseI_joint_large_part_dvd_factor_mul_X_sub_two_t
```

- [x] **Step 2: Run Lean and confirm expected failure**

```bash
lake env lean lean/Erdos699/WIP/T7JointLargePartCancellationTest.lean
```

Expected: unknown constants for the four new theorem names.

### Task 2: Add Generic Cancellation Lemmas

**Files:**
- Modify: `lean/Erdos699/Proved/Basic.lean`

- [x] **Step 1: Add `dvd_factor_mul_of_eq_mul_and_coprime` before the row-two algebra bridge**

```lean
theorem dvd_factor_mul_of_eq_mul_and_coprime {d e a b g : ℕ}
    (ha : a = g * d) (hcop : e.Coprime d) (hedvd : e ∣ a * b) :
    e ∣ g * b := by
  have hdiv : e ∣ (g * b) * d := by
    simpa [ha, mul_assoc, mul_comm, mul_left_comm] using hedvd
  exact hcop.dvd_of_dvd_mul_right hdiv
```

- [x] **Step 2: Add `exists_factor_dvd_factor_mul_of_dvd_and_coprime`**

```lean
theorem exists_factor_dvd_factor_mul_of_dvd_and_coprime {d e a b : ℕ}
    (hda : d ∣ a) (hcop : e.Coprime d) (hedvd : e ∣ a * b) :
    ∃ g : ℕ, a = g * d ∧ e ∣ g * b := by
  rcases hda with ⟨g, hg⟩
  refine ⟨g, ?_, ?_⟩
  · simpa [mul_comm] using hg
  · exact dvd_factor_mul_of_eq_mul_and_coprime (by simpa [mul_comm] using hg) hcop hedvd
```

### Task 3: Add Consecutive-Row Coprimality

**Files:**
- Modify: `lean/Erdos699/Proved/Basic.lean`

- [x] **Step 1: Add `primePowerPartGE_five_sub_two_coprime_sub_one`**

```lean
theorem primePowerPartGE_five_sub_two_coprime_sub_one {n : ℕ} (hn : 2 < n) :
    (primePowerPartGE 5 (n - 2)).Coprime (n - 1) := by
  have hbase : (n - 2).Coprime (n - 1) := by
    have hsucc : n - 1 = (n - 2) + 1 := by omega
    rw [hsucc]
    exact Nat.coprime_self_add_right.mpr (by simp)
  exact Nat.Coprime.coprime_dvd_left
    (primePowerPartGE_dvd_self (by omega : n - 2 ≠ 0)) hbase
```

### Task 4: Add Row-3 Joint Large-Part Instantiation

**Files:**
- Modify: `lean/Erdos699/Proved/Basic.lean`

- [x] **Step 1: Add `i_three_caseI_joint_large_part_dvd_factor_mul_X_sub_two_t`**

```lean
theorem i_three_caseI_joint_large_part_dvd_factor_mul_X_sub_two_t {n F X j t g : ℕ}
    (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor n 3 j q)
    (hn : n = F * X) (hj : j = F * t) (hn_ge_two : 2 ≤ n) (hn_gt_two : 2 < n)
    (hj_two : 2 ≤ j) (htX : t ≤ X) (h2tX : 2 * t ≤ X)
    (hrow1 : t * (X - t) = g * (n - 1)) :
    primePowerPartGE 5 (n - 2) ∣ g * (X - 2 * t) :=
  dvd_factor_mul_of_eq_mul_and_coprime hrow1
    (primePowerPartGE_five_sub_two_coprime_sub_one hn_gt_two)
    (i_three_caseI_row_two_primePowerPartGE_dvd_t_mul_X_sub_t_mul_X_sub_two_t
      hnone hn hj hn_ge_two hn_gt_two hj_two htX h2tX)
```

### Task 5: Verification, Progress, and Commit

**Files:**
- Modify: `notes/PROGRESS.md`
- Delete: `lean/Erdos699/WIP/T7JointLargePartCancellationTest.lean`

- [x] **Step 1: Run WIP API check green and remove the WIP file**

```bash
lake build Erdos699.Proved.Basic
lake env lean lean/Erdos699/WIP/T7JointLargePartCancellationTest.lean
```

Expected: Lean prints all four theorem signatures. Then delete the WIP API file.

- [x] **Step 2: Add the `[R]` progress entry**

```md
- [R] Proved the T7 joint-row large-part cancellation:
  `Erdos699.i_three_caseI_joint_large_part_dvd_factor_mul_X_sub_two_t` shows
  that if `t * (X - t) = g * (n - 1)`, then the row-two large-prime part
  divides `g * (X - 2 * t)`. This banks the coprime cancellation core of the
  joint-row squeeze; full T7 remains open.
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
#print axioms Erdos699.i_three_caseI_joint_large_part_dvd_factor_mul_X_sub_two_t
EOF
```

- [x] **Step 4: Commit the milestone**

```bash
git add docs/superpowers/plans/2026-07-05-erdos699-t7-joint-large-part-cancellation.md lean/Erdos699/Proved/Basic.lean notes/PROGRESS.md
git commit -m "feat: prove erdos699 t7 joint large part cancellation"
```
