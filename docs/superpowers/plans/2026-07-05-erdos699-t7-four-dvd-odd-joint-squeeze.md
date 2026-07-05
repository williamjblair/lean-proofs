# Erdős 699 T7 Four-Divisibility Odd Joint Squeeze Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Bundle the `4 | n`, odd-cofactor Case-I row-bound consequences into one Lean theorem carrying the joint half-row system plus the two normalized squeeze inequalities.

**Architecture:** Reuse the existing row-bound half-row cube package, the row-one cofactor squeeze, and the factor-square squeeze. The new theorem does not strengthen T7 mathematically; it packages the already proved `4 | n`, `Odd F` branch into the shape needed by downstream kernel work.

**Tech Stack:** Lean 4, Mathlib, existing `lean/Erdos699/Proved/Basic.lean`.

---

### Task 1: Add Red Lean Checks

**Files:**
- Create: `lean/Erdos699/WIP/FourDvdOddJointSqueezeCheck.lean`

- [x] **Step 1: Add planned theorem checks**

```lean
import Erdos699.Proved.Basic

namespace Erdos699

#check i_three_caseI_four_dvd_odd_factor_joint_package_from_row_bound
#check i_three_caseI_four_dvd_odd_factor_joint_squeeze_from_row_bound

end Erdos699
```

- [x] **Step 2: Run and verify RED**

Run: `lake env lean lean/Erdos699/WIP/FourDvdOddJointSqueezeCheck.lean`

Expected: FAIL because the theorem names are not defined yet.

### Task 2: Prove Bundled Joint System and Squeeze Projection

**Files:**
- Modify: `lean/Erdos699/Proved/Basic.lean`

- [x] **Step 1: Add bundled joint theorem**

Add after `i_three_caseI_factor_sq_squeeze_of_four_dvd_odd_factor_from_row_bound`:

```lean
theorem i_three_caseI_four_dvd_odd_factor_joint_package_from_row_bound
    {n F X j t : ℕ}
    (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor n 3 j q)
    (hn : n = F * X) (hj : j = F * t) (hn_gt : 2 < n) (hj_pos : 0 < j)
    (hj_two : 2 ≤ j) (h2n : 2 ∣ n) (h3n : 3 ∣ n) (h4n : 4 ∣ n)
    (hFodd : Odd F) (hjn : 2 * j ≤ n) :
    ∃ g : ℕ,
      t * (X - t) = g * (n - 1) ∧
        n / 2 - 1 ∣ g * (X - 2 * t) ∧
          n / 2 - 1 ≤ g * (X - 2 * t) ∧
            4 * ((n - 1) * (n / 2 - 1)) ≤ X * X * X ∧
              4 * F ≤ X ∧
                2 * (F * F) ≤ X := by
  rcases i_three_caseI_exists_joint_half_sub_one_cube_from_four_dvd_row_bound
      hnone hn hj hn_gt hj_pos hj_two h2n h3n h4n hjn with
    ⟨g, hrow1, hdvd, hle, hcube⟩
  have hrow :
      4 * F ≤ X :=
    i_three_caseI_row_one_four_mul_factor_le_X_of_four_dvd_odd_factor_from_row_bound
      hnone hn hj hn_gt hj_pos h2n h3n h4n hFodd hjn
  have hsq :
      2 * (F * F) ≤ X :=
    i_three_caseI_factor_sq_squeeze_of_four_dvd_odd_factor_from_row_bound
      hnone hn hj hn_gt hj_pos hj_two h2n h3n h4n hFodd hjn
  exact ⟨g, hrow1, hdvd, hle, hcube, hrow, hsq⟩
```

- [x] **Step 2: Add squeeze projection theorem**

```lean
theorem i_three_caseI_four_dvd_odd_factor_joint_squeeze_from_row_bound
    {n F X j t : ℕ}
    (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor n 3 j q)
    (hn : n = F * X) (hj : j = F * t) (hn_gt : 2 < n) (hj_pos : 0 < j)
    (hj_two : 2 ≤ j) (h2n : 2 ∣ n) (h3n : 3 ∣ n) (h4n : 4 ∣ n)
    (hFodd : Odd F) (hjn : 2 * j ≤ n) :
    4 * F ≤ X ∧ 2 * (F * F) ≤ X := by
  rcases
      i_three_caseI_four_dvd_odd_factor_joint_package_from_row_bound
        hnone hn hj hn_gt hj_pos hj_two h2n h3n h4n hFodd hjn with
    ⟨_g, _hrow1, _hdvd, _hle, _hcube, hrow, hsq⟩
  exact ⟨hrow, hsq⟩
```

- [x] **Step 3: Run focused Lean check**

Run:

```bash
lake build Erdos699.Proved.Basic
lake env lean lean/Erdos699/WIP/FourDvdOddJointSqueezeCheck.lean
```

Expected: PASS.

### Task 3: Document and Verify

**Files:**
- Modify: `notes/PROGRESS.md`

- [x] **Step 1: Update progress log**

Add an `[R]` entry naming:
- `Erdos699.i_three_caseI_four_dvd_odd_factor_joint_package_from_row_bound`
- `Erdos699.i_three_caseI_four_dvd_odd_factor_joint_squeeze_from_row_bound`

State that this is a bundled `4 | n`, odd-cofactor Case-I package and not a proof of full T7.

- [x] **Step 2: Run final verification and commit**

Run:

```bash
lake env lean lean/Erdos699/WIP/FourDvdOddJointSqueezeCheck.lean
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
git add lean/Erdos699/Proved/Basic.lean lean/Erdos699/WIP/FourDvdOddJointSqueezeCheck.lean \
  notes/PROGRESS.md docs/superpowers/plans/2026-07-05-erdos699-t7-four-dvd-odd-joint-squeeze.md
git commit -m "feat: bundle erdos699 four-divisibility odd squeeze"
```
