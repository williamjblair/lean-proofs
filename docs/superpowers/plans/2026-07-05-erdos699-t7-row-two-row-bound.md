# Erdős 699 T7 Row-Two Row-Bound Wrapper Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Package the existing row-two and joint-row cancellation bridges under the original row bound `2 * j <= n`.

**Architecture:** Reuse `t_le_X_of_factorized_half_bound` and `two_mul_t_le_X_of_factorized_half_bound` to discharge normalized `t <= X` and `2 * t <= X` side conditions. Add direct wrappers around the three row-two divisor bridges and the three joint cancellation bridges.

**Tech Stack:** Lean 4, Mathlib, Lake, exact arithmetic only.

---

### Task 1: Add Red API Check

**Files:**
- Create: `lean/Erdos699/WIP/RowTwoRowBoundCheck.lean`

- [x] **Step 1: Write the failing API check**

```lean
import Erdos699.Proved.Basic

namespace Erdos699

#check i_three_caseI_row_two_primePowerPartGE_dvd_t_mul_X_sub_t_mul_X_sub_two_t_from_row_bound
#check i_three_caseI_row_two_half_sub_one_dvd_t_mul_X_sub_t_mul_X_sub_two_t_from_row_bound
#check i_three_caseI_row_two_half_large_part_dvd_triple_from_row_bound
#check i_three_caseI_joint_large_part_dvd_factor_mul_X_sub_two_t_from_row_bound
#check i_three_caseI_joint_half_sub_one_dvd_factor_mul_X_sub_two_t_from_row_bound
#check i_three_caseI_joint_half_sub_one_large_part_dvd_factor_mul_X_sub_two_t_from_row_bound

end Erdos699
```

- [x] **Step 2: Run the check and verify RED**

Run: `lake env lean lean/Erdos699/WIP/RowTwoRowBoundCheck.lean`

Expected: FAIL with unknown identifiers for the six names above.

### Task 2: Prove Row-Bound Wrappers

**Files:**
- Modify: `lean/Erdos699/Proved/Basic.lean`

- [x] **Step 1: Add row-two divisor wrappers**

Add wrappers for:
- `i_three_caseI_row_two_primePowerPartGE_dvd_t_mul_X_sub_t_mul_X_sub_two_t`
- `i_three_caseI_row_two_half_sub_one_dvd_t_mul_X_sub_t_mul_X_sub_two_t`
- `i_three_caseI_row_two_half_sub_one_large_part_dvd_t_mul_X_sub_t_mul_X_sub_two_t`

Each wrapper takes `hj_pos : 0 < j` and `hjn : 2 * j <= n`, then delegates to
the normalized theorem using:

```lean
(t_le_X_of_factorized_half_bound hn hj hj_pos hjn)
(two_mul_t_le_X_of_factorized_half_bound hn hj hj_pos hjn)
```

- [x] **Step 2: Add joint cancellation wrappers**

Add wrappers for:
- `i_three_caseI_joint_large_part_dvd_factor_mul_X_sub_two_t`
- `i_three_caseI_joint_half_sub_one_dvd_factor_mul_X_sub_two_t`
- `i_three_caseI_joint_half_sub_one_large_part_dvd_factor_mul_X_sub_two_t`

Each wrapper keeps the explicit row-one factor hypothesis
`hrow1 : t * (X - t) = g * (n - 1)` and replaces only the normalized side
conditions with the original row bound.

- [x] **Step 3: Run the Lean file and API check**

Run:
- `lake env lean lean/Erdos699/Proved/Basic.lean`
- `lake build Erdos699.Proved.Basic`
- `lake env lean lean/Erdos699/WIP/RowTwoRowBoundCheck.lean`

Expected: all commands succeed.

### Task 3: Document and Verify

**Files:**
- Modify: `notes/PROGRESS.md`

- [x] **Step 1: Add an [R] progress entry**

Record that the row-two and joint cancellation bridges now have original
row-bound front ends. Do not claim full T7.

- [x] **Step 2: Run the verification gate**

Run:
- `lake env lean lean/Erdos699/Proved/Basic.lean`
- `lake build Erdos699.Proved.Basic`
- `lake env lean lean/Erdos699/WIP/RowTwoRowBoundCheck.lean`
- `python3 -m pytest compute/tests/test_criterion.py -q`
- `rg -n "sorry|admit" lean/Erdos699/Proved`
- `git diff --check`
- `lake build`
- `bash scripts/check_manifest.sh && bash scripts/check_axioms.sh`
- `#print axioms Erdos699.i_three_caseI_joint_half_sub_one_large_part_dvd_factor_mul_X_sub_two_t_from_row_bound`

- [ ] **Step 3: Commit**

```bash
git add lean/Erdos699/Proved/Basic.lean notes/PROGRESS.md \
  lean/Erdos699/WIP/RowTwoRowBoundCheck.lean \
  docs/superpowers/plans/2026-07-05-erdos699-t7-row-two-row-bound.md
git commit -m "feat: prove erdos699 row-two row-bound bridges"
```
