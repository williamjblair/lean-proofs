# Erdos699 T7 Packaged Half-Row Large-Part Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Package the half-row large-prime-part cube bound so callers no longer need to supply the row-one factor `g`.

**Architecture:** Reuse `i_three_caseI_row_one_exists_factor` to introduce `g`, then apply the existing `primePowerPartGE 5 (n / 2 - 1)` divisibility, size, and cube-bound lemmas. Add a projection theorem returning only the cube inequality. This is a packaging step for the 2-adic-free half-row factor, not a full T7 proof.

**Tech Stack:** Lean 4, Mathlib, Lake, existing `Erdos699.Proved.Basic` theorem surface.

---

### Task 1: Packaged Half-Row Large-Part Bound

**Files:**
- Create: `lean/Erdos699/WIP/HalfRowLargePartPackageCheck.lean`
- Modify: `lean/Erdos699/Proved/Basic.lean`
- Modify: `notes/PROGRESS.md`

- [ ] **Step 1: Write the failing WIP API check**

```lean
import Erdos699.Proved.Basic

namespace Erdos699

#check i_three_caseI_exists_joint_half_sub_one_large_part_cube_bound
#check i_three_caseI_noncentral_half_sub_one_large_part_cube_bound

end Erdos699
```

- [ ] **Step 2: Run the WIP check to verify it fails**

Run:

```bash
lake env lean lean/Erdos699/WIP/HalfRowLargePartPackageCheck.lean
```

Expected: failure with unknown identifier errors for the two new theorem names.

- [ ] **Step 3: Add the existential theorem**

Insert after `i_three_caseI_joint_half_sub_one_cube_bound`:

```lean
theorem i_three_caseI_exists_joint_half_sub_one_large_part_cube_bound {n F X j t : ℕ}
    (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor n 3 j q)
    (hn : n = F * X) (hj : j = F * t) (hn_gt : 2 < n) (hj_pos : 0 < j)
    (hj_two : 2 ≤ j) (h2n : 2 ∣ n) (h3n : 3 ∣ n) (hbranch : 0 < X - 2 * t) :
    ∃ g : ℕ,
      t * (X - t) = g * (n - 1) ∧
        primePowerPartGE 5 (n / 2 - 1) ∣ g * (X - 2 * t) ∧
          primePowerPartGE 5 (n / 2 - 1) ≤ g * (X - 2 * t) ∧
            4 * ((n - 1) * primePowerPartGE 5 (n / 2 - 1)) ≤ X * X * X := by
  rcases i_three_caseI_row_one_exists_factor
      hnone hn hj hn_gt hj_pos h2n h3n (by omega : t ≤ X) with ⟨g, hrow1⟩
  exact ⟨g, hrow1,
    i_three_caseI_joint_half_sub_one_large_part_dvd_factor_mul_X_sub_two_t
      hnone hn hj hn_gt hj_two h2n (by omega : t ≤ X) (by omega : 2 * t ≤ X)
      hrow1,
    i_three_caseI_joint_half_sub_one_large_part_le_factor_mul_X_sub_two_t
      hnone hn hj hn_gt hj_two h2n hrow1 hbranch,
    i_three_caseI_joint_half_sub_one_large_part_cube_bound
      hnone hn hj hn_gt hj_two h2n hrow1 hbranch⟩
```

- [ ] **Step 4: Add the projection theorem**

Insert after the existential theorem:

```lean
theorem i_three_caseI_noncentral_half_sub_one_large_part_cube_bound {n F X j t : ℕ}
    (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor n 3 j q)
    (hn : n = F * X) (hj : j = F * t) (hn_gt : 2 < n) (hj_pos : 0 < j)
    (hj_two : 2 ≤ j) (h2n : 2 ∣ n) (h3n : 3 ∣ n) (hbranch : 0 < X - 2 * t) :
    4 * ((n - 1) * primePowerPartGE 5 (n / 2 - 1)) ≤ X * X * X := by
  rcases i_three_caseI_exists_joint_half_sub_one_large_part_cube_bound
      hnone hn hj hn_gt hj_pos hj_two h2n h3n hbranch with
    ⟨_g, _hrow1, _hdvd, _hle, hcube⟩
  exact hcube
```

- [ ] **Step 5: Update progress log**

Add a `[R]` entry naming both packaged theorem endpoints and explicitly stating that they package only the forced `p ≥ 5` half-row large-prime part.

- [ ] **Step 6: Run verification**

Run:

```bash
lake env lean lean/Erdos699/Proved/Basic.lean
lake build Erdos699.Proved.Basic
lake env lean lean/Erdos699/WIP/HalfRowLargePartPackageCheck.lean
python3 -m pytest compute/tests/test_criterion.py -q
rg -n "sorry|admit" lean/Erdos699/Proved
git diff --check
lake build
bash scripts/check_manifest.sh
bash scripts/check_axioms.sh
lake env lean --stdin <<'EOF'
import Erdos699.Proved.Basic
#print axioms Erdos699.i_three_caseI_noncentral_half_sub_one_large_part_cube_bound
EOF
```

Expected: Lean commands, pytest, scripts, whitespace check, and full build exit 0; the `rg` command returns no matches; the axiom print reports only `[propext, Classical.choice, Quot.sound]`.

- [ ] **Step 7: Commit the milestone**

Run:

```bash
git add docs/superpowers/plans/2026-07-05-erdos699-t7-packaged-half-row-large-part.md lean/Erdos699/Proved/Basic.lean lean/Erdos699/WIP/HalfRowLargePartPackageCheck.lean notes/PROGRESS.md
git commit -m "feat: package erdos699 half-row large-part bound"
```
