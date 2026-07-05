# Erdős 699 T7 Four-Divisibility Full Half-Row Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Upgrade the `4 | n` Case-I subcase from a large-prime-part half-row theorem to a full `n / 2 - 1` half-row cube package.

**Architecture:** Reuse the existing `half_sub_one_prime_ge_five_of_even_three_dvd_coprime_four` and the recently proved `half_sub_one_coprime_four_of_four_dvd` to show `primePowerPartGE 5 (n / 2 - 1) = n / 2 - 1` when `4 | n`, `3 | n`, and `2 < n`. Then rewrite the existing large-prime-part row-bound package through that equality.

**Tech Stack:** Lean 4, Mathlib, existing `lean/Erdos699/Proved/Basic.lean`.

---

### Task 1: Add Red Lean Checks

**Files:**
- Create: `lean/Erdos699/WIP/FourDvdFullHalfRowCheck.lean`

- [x] **Step 1: Add planned theorem checks**

```lean
import Erdos699.Proved.Basic

namespace Erdos699

#check primePowerPartGE_five_half_sub_one_eq_self_of_four_dvd_three_dvd
#check i_three_caseI_exists_joint_half_sub_one_cube_from_four_dvd_row_bound
#check i_three_caseI_half_sub_one_cube_from_four_dvd_row_bound

end Erdos699
```

- [x] **Step 2: Run and verify RED**

Run: `lake env lean lean/Erdos699/WIP/FourDvdFullHalfRowCheck.lean`

Expected: FAIL because the three theorem names are not defined yet.

### Task 2: Prove Full Half-Row Wrappers

**Files:**
- Modify: `lean/Erdos699/Proved/Basic.lean`

- [x] **Step 1: Add large-part equality**

Add near the existing half-row coprimality lemmas:

```lean
theorem primePowerPartGE_five_half_sub_one_eq_self_of_four_dvd_three_dvd {n : ℕ}
    (h4n : 4 ∣ n) (h3n : 3 ∣ n) (hn : 2 < n) :
    primePowerPartGE 5 (n / 2 - 1) = n / 2 - 1 := by
  have h2n : 2 ∣ n := Nat.dvd_trans (by norm_num : 2 ∣ 4) h4n
  exact primePowerPartGE_eq_self_of_forall_prime_ge
    (half_sub_one_ne_zero_of_even h2n hn)
    (half_sub_one_prime_ge_five_of_even_three_dvd_coprime_four h2n h3n hn
      (half_sub_one_coprime_four_of_four_dvd h4n hn))
```

- [x] **Step 2: Add existential full half-row package**

Add near `i_three_caseI_exists_joint_half_large_part_cube_from_row_bound`:

```lean
theorem i_three_caseI_exists_joint_half_sub_one_cube_from_four_dvd_row_bound
    {n F X j t : ℕ} (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor n 3 j q)
    (hn : n = F * X) (hj : j = F * t) (hn_gt : 2 < n) (hj_pos : 0 < j)
    (hj_two : 2 ≤ j) (h2n : 2 ∣ n) (h3n : 3 ∣ n) (h4n : 4 ∣ n)
    (hjn : 2 * j ≤ n) :
    ∃ g : ℕ,
      t * (X - t) = g * (n - 1) ∧
        n / 2 - 1 ∣ g * (X - 2 * t) ∧
          n / 2 - 1 ≤ g * (X - 2 * t) ∧
            4 * ((n - 1) * (n / 2 - 1)) ≤ X * X * X := by
  have hlarge :=
    i_three_caseI_exists_joint_half_large_part_cube_from_row_bound
      hnone hn hj hn_gt hj_pos hj_two h2n h3n hjn
  simpa [primePowerPartGE_five_half_sub_one_eq_self_of_four_dvd_three_dvd h4n h3n hn_gt]
    using hlarge
```

- [x] **Step 3: Add projected cube inequality**

```lean
theorem i_three_caseI_half_sub_one_cube_from_four_dvd_row_bound {n F X j t : ℕ}
    (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor n 3 j q)
    (hn : n = F * X) (hj : j = F * t) (hn_gt : 2 < n) (hj_pos : 0 < j)
    (hj_two : 2 ≤ j) (h2n : 2 ∣ n) (h3n : 3 ∣ n) (h4n : 4 ∣ n)
    (hjn : 2 * j ≤ n) :
    4 * ((n - 1) * (n / 2 - 1)) ≤ X * X * X := by
  rcases i_three_caseI_exists_joint_half_sub_one_cube_from_four_dvd_row_bound
      hnone hn hj hn_gt hj_pos hj_two h2n h3n h4n hjn with
    ⟨_g, _hrow1, _hdvd, _hle, hcube⟩
  exact hcube
```

- [x] **Step 4: Run focused Lean check**

Run:

```bash
lake build Erdos699.Proved.Basic
lake env lean lean/Erdos699/WIP/FourDvdFullHalfRowCheck.lean
```

Expected: PASS.

### Task 3: Document and Verify

**Files:**
- Modify: `notes/PROGRESS.md`

- [x] **Step 1: Update progress log**

Add an `[R]` entry naming:
- `Erdos699.primePowerPartGE_five_half_sub_one_eq_self_of_four_dvd_three_dvd`
- `Erdos699.i_three_caseI_exists_joint_half_sub_one_cube_from_four_dvd_row_bound`
- `Erdos699.i_three_caseI_half_sub_one_cube_from_four_dvd_row_bound`

State that this closes the missing `2`-adic half-row factor only in the `4 | n` subcase; full T7 remains open.

- [x] **Step 2: Run final verification and commit**

Run:

```bash
lake env lean lean/Erdos699/WIP/FourDvdFullHalfRowCheck.lean
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
git add lean/Erdos699/Proved/Basic.lean lean/Erdos699/WIP/FourDvdFullHalfRowCheck.lean \
  notes/PROGRESS.md docs/superpowers/plans/2026-07-05-erdos699-t7-four-dvd-full-half-row.md
git commit -m "feat: prove erdos699 four-divisibility full half-row package"
```
