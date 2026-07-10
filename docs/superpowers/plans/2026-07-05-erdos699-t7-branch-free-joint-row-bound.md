# Erdős 699 T7 Branch-Free Joint Row-Bound Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Package the noncentral joint-row consequences under the original row bound `2 * j <= n` by deriving the noncentral branch from the central-branch contradiction.

**Architecture:** Prove a helper `x_sub_two_t_pos_of_row_bound` from `2 * j <= n`, `n = F * X`, `j = F * t`, and the case-I row-one central contradiction. Then wrap the existing `exists_joint_*` factor, gap, cube, and half-row-large-part cube theorems with this helper.

**Tech Stack:** Lean 4, Mathlib, Lake, exact arithmetic only.

---

### Task 1: Add Red API Check

**Files:**
- Create: `lean/Erdos699/WIP/BranchFreeJointRowBoundCheck.lean`

- [x] **Step 1: Write the failing API check**

```lean
import Erdos699.Proved.Basic

namespace Erdos699

#check x_sub_two_t_pos_of_row_bound
#check i_three_caseI_exists_joint_large_part_factor_le_from_row_bound
#check i_three_caseI_exists_joint_large_part_gap_bound_from_row_bound
#check i_three_caseI_exists_joint_large_part_cube_bound_from_row_bound
#check i_three_caseI_exists_joint_half_large_part_cube_from_row_bound
#check i_three_caseI_half_large_part_cube_from_row_bound

end Erdos699
```

- [x] **Step 2: Run the check and verify RED**

Run: `lake env lean lean/Erdos699/WIP/BranchFreeJointRowBoundCheck.lean`

Expected: FAIL with unknown identifiers for the six names above.

### Task 2: Prove Branch-Free Row-Bound Wrappers

**Files:**
- Modify: `lean/Erdos699/Proved/Basic.lean`

- [x] **Step 1: Add the noncentral-branch helper**

```lean
theorem x_sub_two_t_pos_of_row_bound {n F X j t : ℕ}
    (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor n 3 j q)
    (hn : n = F * X) (hj : j = F * t) (hn_gt : 2 < n) (hj_pos : 0 < j)
    (h2n : 2 ∣ n) (h3n : 3 ∣ n) (hjn : 2 * j ≤ n) :
    0 < X - 2 * t := by
  have h2tX := two_mul_t_le_X_of_factorized_half_bound hn hj hj_pos hjn
  by_cases hcentral : 2 * t = X
  · exact False.elim
      (i_three_caseI_central_branch_false hnone hn hj hn_gt hj_pos h2n h3n hcentral)
  · omega
```

- [x] **Step 2: Add package wrappers**

Add wrappers for:
- `i_three_caseI_exists_joint_large_part_factor_le`
- `i_three_caseI_exists_joint_large_part_gap_bound`
- `i_three_caseI_exists_joint_large_part_cube_bound`
- `i_three_caseI_exists_joint_half_sub_one_large_part_cube_bound`

Each wrapper delegates to the existing theorem with:

```lean
(x_sub_two_t_pos_of_row_bound hnone hn hj hn_gt hj_pos h2n h3n hjn)
```

- [x] **Step 3: Add the projection wrapper**

Add `i_three_caseI_half_large_part_cube_from_row_bound` by projecting the
cube inequality from the half-row-large-part package.

- [x] **Step 4: Run the Lean file and API check**

Run:
- `lake env lean lean/Erdos699/Proved/Basic.lean`
- `lake build Erdos699.Proved.Basic`
- `lake env lean lean/Erdos699/WIP/BranchFreeJointRowBoundCheck.lean`

Expected: all commands succeed.

### Task 3: Document and Verify

**Files:**
- Modify: `notes/PROGRESS.md`

- [x] **Step 1: Add an [R] progress entry**

Record that the new theorems remove the explicit noncentral branch from the
packaged joint-row consequences under the original row bound. Do not claim full
T7 or the half-row lower-bound obstruction is solved.

- [x] **Step 2: Run the verification gate**

Run:
- `lake env lean lean/Erdos699/Proved/Basic.lean`
- `lake build Erdos699.Proved.Basic`
- `lake env lean lean/Erdos699/WIP/BranchFreeJointRowBoundCheck.lean`
- `python3 -m pytest compute/tests/test_criterion.py -q`
- `rg -n "sorry|admit" lean/Erdos699/Proved`
- `git diff --check`
- `lake build`
- `bash scripts/check_manifest.sh && bash scripts/check_axioms.sh`
- `#print axioms Erdos699.i_three_caseI_half_large_part_cube_from_row_bound`

- [ ] **Step 3: Commit**

```bash
git add lean/Erdos699/Proved/Basic.lean notes/PROGRESS.md \
  lean/Erdos699/WIP/BranchFreeJointRowBoundCheck.lean \
  docs/superpowers/plans/2026-07-05-erdos699-t7-branch-free-joint-row-bound.md
git commit -m "feat: prove erdos699 branch-free joint row-bound package"
```
