# Erdos699 T7 Packaged Half-Row Cube Bound Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Bank a sorry-free packaged half-row cube bound that no longer requires callers to provide the row-one factor `g`.

**Architecture:** Add an existential theorem that combines the existing factor-existence package with the conditional half-row cube squeeze. Add a projection theorem returning only `4 * ((n - 1) * (n / 2 - 1)) ≤ X * X * X`. The lower-bound hypothesis `n / 2 - 1 ≤ primePowerPartGE 5 (n - 2)` remains explicit; this does not close the small-prime analysis or full T7.

**Tech Stack:** Lean 4, Mathlib, Lake, existing `Erdos699.Proved.Basic` theorem surface.

---

### Task 1: Packaged Half-Row Cube Bound

**Files:**
- Create: `lean/Erdos699/WIP/T7PackagedHalfRowCubeBoundTest.lean`
- Modify: `lean/Erdos699/Proved/Basic.lean`
- Modify: `notes/PROGRESS.md`

- [ ] **Step 1: Write the failing WIP API check**

```lean
import Erdos699.Proved.Basic

#check Erdos699.i_three_caseI_exists_joint_half_sub_one_cube_bound
#check Erdos699.i_three_caseI_noncentral_half_sub_one_cube_bound
```

- [ ] **Step 2: Run the WIP check to verify it fails**

Run:

```bash
lake env lean lean/Erdos699/WIP/T7PackagedHalfRowCubeBoundTest.lean
```

Expected: failure with unknown identifier errors for the two new theorem names.

- [ ] **Step 3: Add the packaged existential theorem**

Insert after `i_three_caseI_joint_half_sub_one_cube_bound`:

```lean
theorem i_three_caseI_exists_joint_half_sub_one_cube_bound {n F X j t : ℕ}
    (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor n 3 j q)
    (hn : n = F * X) (hj : j = F * t) (hn_gt : 2 < n) (hj_pos : 0 < j)
    (hj_two : 2 ≤ j) (h2n : 2 ∣ n) (h3n : 3 ∣ n) (hbranch : 0 < X - 2 * t)
    (hhalf : n / 2 - 1 ≤ primePowerPartGE 5 (n - 2)) :
    ∃ g : ℕ,
      t * (X - t) = g * (n - 1) ∧
        primePowerPartGE 5 (n - 2) ∣ g * (X - 2 * t) ∧
          primePowerPartGE 5 (n - 2) ≤ g * (X - 2 * t) ∧
            4 * ((n - 1) * (n / 2 - 1)) ≤ X * X * X := by
  rcases i_three_caseI_exists_joint_large_part_factor_le
      hnone hn hj hn_gt hj_pos hj_two h2n h3n hbranch with
    ⟨g, hrow1, hdvd, hle⟩
  exact ⟨g, hrow1, hdvd, hle,
    i_three_caseI_joint_half_sub_one_cube_bound
      hnone hn hj hn_gt hj_two hrow1 hbranch hhalf⟩
```

- [ ] **Step 4: Add the projection theorem**

Insert after the existential theorem:

```lean
theorem i_three_caseI_noncentral_half_sub_one_cube_bound {n F X j t : ℕ}
    (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor n 3 j q)
    (hn : n = F * X) (hj : j = F * t) (hn_gt : 2 < n) (hj_pos : 0 < j)
    (hj_two : 2 ≤ j) (h2n : 2 ∣ n) (h3n : 3 ∣ n) (hbranch : 0 < X - 2 * t)
    (hhalf : n / 2 - 1 ≤ primePowerPartGE 5 (n - 2)) :
    4 * ((n - 1) * (n / 2 - 1)) ≤ X * X * X := by
  rcases i_three_caseI_exists_joint_half_sub_one_cube_bound
      hnone hn hj hn_gt hj_pos hj_two h2n h3n hbranch hhalf with
    ⟨_g, _hrow1, _hdvd, _hle, hcube⟩
  exact hcube
```

- [ ] **Step 5: Update progress log**

Add a `[R]` entry to `notes/PROGRESS.md` naming both new theorems and stating that the lower-bound hypothesis remains open.

- [ ] **Step 6: Run focused verification**

Run:

```bash
lake env lean lean/Erdos699/Proved/Basic.lean
lake build Erdos699.Proved.Basic
lake env lean lean/Erdos699/WIP/T7PackagedHalfRowCubeBoundTest.lean
```

Expected: all commands exit 0.

- [ ] **Step 7: Remove the WIP check and run full gates**

Delete `lean/Erdos699/WIP/T7PackagedHalfRowCubeBoundTest.lean`, then run:

```bash
python3 -m pytest compute/tests/test_criterion.py -q
rg -n "\bsorry\b|\badmit\b" lean/Erdos699/Proved || true
git diff --check
lake build
bash scripts/check_axioms.sh
bash scripts/check_manifest.sh
lake env lean --stdin <<'EOF'
import Erdos699.Proved.Basic
#print axioms Erdos699.i_three_caseI_noncentral_half_sub_one_cube_bound
EOF
```

Expected: tests pass, no proved-file `sorry` or `admit` hits, build exits 0, scripts exit 0, and the theorem axiom print contains only the standard trusted base already expected in this project.

- [ ] **Step 8: Commit the milestone**

Run:

```bash
git add docs/superpowers/plans/2026-07-05-erdos699-t7-packaged-half-row-cube-bound.md lean/Erdos699/Proved/Basic.lean notes/PROGRESS.md
git commit -m "feat: prove erdos699 t7 packaged half-row bound"
```
