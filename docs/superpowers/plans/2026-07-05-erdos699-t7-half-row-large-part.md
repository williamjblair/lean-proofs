# Erdos699 T7 Half-Row Large-Part Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Bank a sorry-free T7 slice showing that the forced large-prime part `primePowerPartGE 5 (n / 2 - 1)` of the half-row divisor passes through row two and the joint-row cancellation.

**Architecture:** Reuse the existing `primePowerPartGE` full-multiplicity machinery instead of defining a new odd-part operation. First prove `primePowerPartGE 5 (n / 2 - 1)` divides the row-two product because it divides `n - 2` and only contains primes `p ≥ 5`. Then reuse the existing congruence bridge and coprime cancellation to obtain divisibility, size, gap, and cube bounds for this 2-adic-free half-row factor. This does not claim full T7 because the missing power of 2 remains intentionally free under the corrected `p ≥ i` rule.

**Tech Stack:** Lean 4, Mathlib, Lake, existing `Erdos699.Proved.Basic` theorem surface.

---

### Task 1: Half-Row Large-Part Divisibility

**Files:**
- Create: `lean/Erdos699/WIP/HalfRowLargePartCheck.lean`
- Modify: `lean/Erdos699/Proved/Basic.lean`
- Modify: `notes/PROGRESS.md`

- [ ] **Step 1: Write the failing WIP API check**

```lean
import Erdos699.Proved.Basic

namespace Erdos699

#check i_three_caseI_half_sub_one_large_part_dvd_row_two_product
#check i_three_caseI_joint_half_sub_one_large_part_dvd_factor_mul_X_sub_two_t
#check i_three_caseI_joint_half_sub_one_large_part_cube_bound

end Erdos699
```

- [ ] **Step 2: Run the WIP check to verify it fails**

Run:

```bash
lake env lean lean/Erdos699/WIP/HalfRowLargePartCheck.lean
```

Expected: failure with unknown identifier errors for the new theorem names.

- [ ] **Step 3: Implement the Lean theorem slice**

Add helper lemmas after the existing half-row coprime lemmas, then add normalized row-two and joint-row wrappers near the existing T7 large-part theorems:

```lean
theorem half_sub_one_ne_zero_of_even {n : ℕ} (h2n : 2 ∣ n) (hn : 2 < n) :
    n / 2 - 1 ≠ 0 := by
  rcases h2n with ⟨m, hm⟩
  subst n
  omega
```

Add these public endpoints with sorry-free proofs:

```lean
theorem i_three_caseI_half_sub_one_large_part_dvd_row_two_product {n j : ℕ}
    (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor n 3 j q)
    (h2n : 2 ∣ n) (hn : 2 < n) :
    primePowerPartGE 5 (n / 2 - 1) ∣ j * (j - 1) * (j - 2)

theorem i_three_caseI_row_two_half_sub_one_large_part_dvd_t_mul_X_sub_t_mul_X_sub_two_t
    {n F X j t : ℕ} (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor n 3 j q)
    (hn : n = F * X) (hj : j = F * t) (hn_gt : 2 < n) (hj_two : 2 ≤ j)
    (h2n : 2 ∣ n) (htX : t ≤ X) (h2tX : 2 * t ≤ X) :
    primePowerPartGE 5 (n / 2 - 1) ∣ t * (X - t) * (X - 2 * t)

theorem i_three_caseI_joint_half_sub_one_large_part_dvd_factor_mul_X_sub_two_t
    {n F X j t g : ℕ} (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor n 3 j q)
    (hn : n = F * X) (hj : j = F * t) (hn_gt : 2 < n) (hj_two : 2 ≤ j)
    (h2n : 2 ∣ n) (htX : t ≤ X) (h2tX : 2 * t ≤ X)
    (hrow1 : t * (X - t) = g * (n - 1)) :
    primePowerPartGE 5 (n / 2 - 1) ∣ g * (X - 2 * t)

theorem i_three_caseI_joint_half_sub_one_large_part_le_factor_mul_X_sub_two_t
    {n F X j t g : ℕ} (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor n 3 j q)
    (hn : n = F * X) (hj : j = F * t) (hn_gt : 2 < n)
    (hj_two : 2 ≤ j) (h2n : 2 ∣ n) (hrow1 : t * (X - t) = g * (n - 1))
    (hbranch : 0 < X - 2 * t) :
    primePowerPartGE 5 (n / 2 - 1) ≤ g * (X - 2 * t)

theorem i_three_caseI_joint_half_sub_one_large_part_gap_bound {n F X j t g : ℕ}
    (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor n 3 j q)
    (hn : n = F * X) (hj : j = F * t) (hn_gt : 2 < n)
    (hj_two : 2 ≤ j) (h2n : 2 ∣ n) (hrow1 : t * (X - t) = g * (n - 1))
    (hbranch : 0 < X - 2 * t) :
    4 * ((n - 1) * primePowerPartGE 5 (n / 2 - 1)) ≤ X * X * (X - 2 * t)

theorem i_three_caseI_joint_half_sub_one_large_part_cube_bound {n F X j t g : ℕ}
    (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor n 3 j q)
    (hn : n = F * X) (hj : j = F * t) (hn_gt : 2 < n)
    (hj_two : 2 ≤ j) (h2n : 2 ∣ n) (hrow1 : t * (X - t) = g * (n - 1))
    (hbranch : 0 < X - 2 * t) :
    4 * ((n - 1) * primePowerPartGE 5 (n / 2 - 1)) ≤ X * X * X
```

- [ ] **Step 4: Update progress log**

Add a `[R]` entry naming the new public endpoints and stating that this is the forced `p ≥ 5` large-prime part of `n / 2 - 1`, not the full half-row divisor.

- [ ] **Step 5: Run verification**

Run:

```bash
lake env lean lean/Erdos699/Proved/Basic.lean
lake build Erdos699.Proved.Basic
lake env lean lean/Erdos699/WIP/HalfRowLargePartCheck.lean
rg -n "sorry|admit" lean/Erdos699/Proved
git diff --check
lake build
```

Expected: Lean commands and builds exit 0; the `rg` command returns no matches; whitespace check exits 0.

- [ ] **Step 6: Commit the milestone**

Run:

```bash
git add docs/superpowers/plans/2026-07-05-erdos699-t7-half-row-large-part.md lean/Erdos699/Proved/Basic.lean lean/Erdos699/WIP/HalfRowLargePartCheck.lean notes/PROGRESS.md
git commit -m "feat: prove erdos699 half-row large-part squeeze"
```
