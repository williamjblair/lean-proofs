# Erdős 699 T6 Row-One Row-Bound Wrapper Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Package the existing row-one case-I constraints under the original row bound `2 * j <= n`.

**Architecture:** Reuse the already proved factor-normalization helper to derive `2 * t <= X`, then expose thin wrappers around the existing row-one divisibility, factor-existence, square-bound, and cofactor-bound theorems. The proof adds no new mathematical hypothesis beyond the existing row-bound front end.

**Tech Stack:** Lean 4, Mathlib, Lake, exact arithmetic only.

---

### Task 1: Add Red API Check

**Files:**
- Create: `lean/Erdos699/WIP/RowOneRowBoundCheck.lean`

- [x] **Step 1: Write the failing API check**

```lean
import Erdos699.Proved.Basic

namespace Erdos699

#check t_le_X_of_factorized_half_bound
#check i_three_caseI_row_one_sub_one_dvd_t_mul_X_sub_t_from_row_bound
#check i_three_caseI_row_one_exists_factor_from_row_bound
#check i_three_caseI_row_one_four_mul_sub_one_le_X_sq_from_row_bound
#check i_three_caseI_row_one_four_mul_factor_le_X_from_row_bound

end Erdos699
```

- [x] **Step 2: Run the check and verify RED**

Run: `lake env lean lean/Erdos699/WIP/RowOneRowBoundCheck.lean`

Expected: FAIL with unknown identifiers for the five names above.

### Task 2: Prove Row-Bound Wrappers

**Files:**
- Modify: `lean/Erdos699/Proved/Basic.lean`

- [x] **Step 1: Add the one-sided helper**

```lean
theorem t_le_X_of_factorized_half_bound {n F X j t : ℕ}
    (hn : n = F * X) (hj : j = F * t) (hj_pos : 0 < j) (hjn : 2 * j ≤ n) :
    t ≤ X := by
  have h2tX := two_mul_t_le_X_of_factorized_half_bound hn hj hj_pos hjn
  omega
```

- [x] **Step 2: Add row-one theorem wrappers**

```lean
theorem i_three_caseI_row_one_sub_one_dvd_t_mul_X_sub_t_from_row_bound {n F X j t : ℕ}
    (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor n 3 j q)
    (hn : n = F * X) (hj : j = F * t) (hn_gt : 2 < n) (hj_pos : 0 < j)
    (h2n : 2 ∣ n) (h3n : 3 ∣ n) (hjn : 2 * j ≤ n) :
    n - 1 ∣ t * (X - t) :=
  i_three_caseI_row_one_sub_one_dvd_t_mul_X_sub_t
    hnone hn hj hn_gt hj_pos h2n h3n
    (t_le_X_of_factorized_half_bound hn hj hj_pos hjn)
```

Add analogous wrappers for `i_three_caseI_row_one_exists_factor`,
`i_three_caseI_row_one_four_mul_sub_one_le_X_sq`, and
`i_three_caseI_row_one_four_mul_factor_le_X`.

- [x] **Step 3: Run the Lean file and API check**

Run:
- `lake env lean lean/Erdos699/Proved/Basic.lean`
- `lake build Erdos699.Proved.Basic`
- `lake env lean lean/Erdos699/WIP/RowOneRowBoundCheck.lean`

Expected: all commands succeed.

### Task 3: Document and Verify

**Files:**
- Modify: `notes/PROGRESS.md`

- [x] **Step 1: Add an [R] progress entry**

Record that these are row-bound front ends for existing row-one T6 constraints, not full T6/T7.

- [x] **Step 2: Run the verification gate**

Run:
- `lake env lean lean/Erdos699/Proved/Basic.lean`
- `lake build Erdos699.Proved.Basic`
- `lake env lean lean/Erdos699/WIP/RowOneRowBoundCheck.lean`
- `python3 -m pytest compute/tests/test_criterion.py -q`
- `rg -n "sorry|admit" lean/Erdos699/Proved`
- `git diff --check`
- `lake build`
- `bash scripts/check_manifest.sh && bash scripts/check_axioms.sh`
- `#print axioms Erdos699.i_three_caseI_row_one_four_mul_factor_le_X_from_row_bound`

- [ ] **Step 3: Commit**

```bash
git add lean/Erdos699/Proved/Basic.lean notes/PROGRESS.md \
  lean/Erdos699/WIP/RowOneRowBoundCheck.lean \
  docs/superpowers/plans/2026-07-05-erdos699-t6-row-one-row-bound.md
git commit -m "feat: prove erdos699 row-one row-bound squeeze"
```
