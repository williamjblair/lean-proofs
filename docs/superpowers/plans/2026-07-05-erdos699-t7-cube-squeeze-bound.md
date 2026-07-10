# Erdos699 T7 Cube Squeeze Bound Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Bank a sorry-free non-central T7 `X^3` squeeze that follows from the proved gap product bound, plus a lower-bound specialization for later `n / 2 - 1` instantiation.

**Architecture:** Add fixed-factor and existential cube-bound theorems after the existing T7 gap product bound in `lean/Erdos699/Proved/Basic.lean`. Then add a lower-bound theorem parameterized by `L ≤ primePowerPartGE 5 (n - 2)` and a half-row specialization using `L = n / 2 - 1` as an explicit hypothesis. These statements remain conditional on `0 < X - 2 * t`; the central branch and full T7 stay open.

**Tech Stack:** Lean 4, Mathlib, Lake, existing `Erdos699.Proved.Basic` theorem surface.

---

### Task 1: Noncentral Cube Squeeze API

**Files:**
- Create: `lean/Erdos699/WIP/T7CubeSqueezeBoundTest.lean`
- Modify: `lean/Erdos699/Proved/Basic.lean`
- Modify: `notes/PROGRESS.md`

- [ ] **Step 1: Write the failing WIP API check**

```lean
import Erdos699.Proved.Basic

#check Erdos699.i_three_caseI_joint_large_part_cube_bound
#check Erdos699.i_three_caseI_exists_joint_large_part_cube_bound
#check Erdos699.i_three_caseI_joint_lower_part_cube_bound
#check Erdos699.i_three_caseI_joint_half_sub_one_cube_bound
```

- [ ] **Step 2: Run the WIP check to verify it fails**

Run:

```bash
lake env lean lean/Erdos699/WIP/T7CubeSqueezeBoundTest.lean
```

Expected: failure with unknown identifier errors for the four new theorem names.

- [ ] **Step 3: Add the fixed-factor cube theorem**

Insert after `i_three_caseI_joint_large_part_gap_bound`:

```lean
theorem i_three_caseI_joint_large_part_cube_bound {n F X j t g : ℕ}
    (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor n 3 j q)
    (hn : n = F * X) (hj : j = F * t) (hn_gt : 2 < n)
    (hj_two : 2 ≤ j) (hrow1 : t * (X - t) = g * (n - 1))
    (hbranch : 0 < X - 2 * t) :
    4 * ((n - 1) * primePowerPartGE 5 (n - 2)) ≤ X * X * X := by
  have hgap :=
    i_three_caseI_joint_large_part_gap_bound hnone hn hj hn_gt hj_two hrow1 hbranch
  have hgap_le : X - 2 * t ≤ X := Nat.sub_le X (2 * t)
  exact hgap.trans (by
    simpa [mul_assoc] using Nat.mul_le_mul_left (X * X) hgap_le)
```

- [ ] **Step 4: Add the existential cube theorem**

Insert after `i_three_caseI_exists_joint_large_part_gap_bound`:

```lean
theorem i_three_caseI_exists_joint_large_part_cube_bound {n F X j t : ℕ}
    (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor n 3 j q)
    (hn : n = F * X) (hj : j = F * t) (hn_gt : 2 < n) (hj_pos : 0 < j)
    (hj_two : 2 ≤ j) (h2n : 2 ∣ n) (h3n : 3 ∣ n) (hbranch : 0 < X - 2 * t) :
    ∃ g : ℕ,
      t * (X - t) = g * (n - 1) ∧
        primePowerPartGE 5 (n - 2) ∣ g * (X - 2 * t) ∧
          primePowerPartGE 5 (n - 2) ≤ g * (X - 2 * t) ∧
            4 * ((n - 1) * primePowerPartGE 5 (n - 2)) ≤ X * X * X := by
  rcases i_three_caseI_exists_joint_large_part_gap_bound
      hnone hn hj hn_gt hj_pos hj_two h2n h3n hbranch with
    ⟨g, hrow1, hdvd, hle, _hgap⟩
  exact ⟨g, hrow1, hdvd, hle,
    i_three_caseI_joint_large_part_cube_bound hnone hn hj hn_gt hj_two hrow1 hbranch⟩
```

- [ ] **Step 5: Add lower-bound and half-row specializations**

Insert after the existential cube theorem:

```lean
theorem i_three_caseI_joint_lower_part_cube_bound {n F X j t g L : ℕ}
    (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor n 3 j q)
    (hn : n = F * X) (hj : j = F * t) (hn_gt : 2 < n)
    (hj_two : 2 ≤ j) (hrow1 : t * (X - t) = g * (n - 1))
    (hbranch : 0 < X - 2 * t) (hL : L ≤ primePowerPartGE 5 (n - 2)) :
    4 * ((n - 1) * L) ≤ X * X * X := by
  have hcube :=
    i_three_caseI_joint_large_part_cube_bound hnone hn hj hn_gt hj_two hrow1 hbranch
  exact (Nat.mul_le_mul_left 4 (Nat.mul_le_mul_left (n - 1) hL)).trans hcube

theorem i_three_caseI_joint_half_sub_one_cube_bound {n F X j t g : ℕ}
    (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor n 3 j q)
    (hn : n = F * X) (hj : j = F * t) (hn_gt : 2 < n)
    (hj_two : 2 ≤ j) (hrow1 : t * (X - t) = g * (n - 1))
    (hbranch : 0 < X - 2 * t)
    (hhalf : n / 2 - 1 ≤ primePowerPartGE 5 (n - 2)) :
    4 * ((n - 1) * (n / 2 - 1)) ≤ X * X * X :=
  i_three_caseI_joint_lower_part_cube_bound hnone hn hj hn_gt hj_two hrow1 hbranch hhalf
```

- [ ] **Step 6: Update progress log**

Add a `[R]` entry to `notes/PROGRESS.md` naming all four new theorems and stating that this is the non-central cube squeeze, with the half-row result conditional on the explicit lower-bound hypothesis; full T7 remains open.

- [ ] **Step 7: Run focused verification**

Run:

```bash
lake env lean lean/Erdos699/Proved/Basic.lean
lake build Erdos699.Proved.Basic
lake env lean lean/Erdos699/WIP/T7CubeSqueezeBoundTest.lean
```

Expected: all commands exit 0.

- [ ] **Step 8: Remove the WIP check and run full gates**

Delete `lean/Erdos699/WIP/T7CubeSqueezeBoundTest.lean`, then run:

```bash
python3 -m pytest compute/tests/test_criterion.py -q
rg -n "\bsorry\b|\badmit\b" lean/Erdos699/Proved || true
git diff --check
lake build
bash scripts/check_axioms.sh
bash scripts/check_manifest.sh
lake env lean --stdin <<'EOF'
import Erdos699.Proved.Basic
#print axioms Erdos699.i_three_caseI_joint_half_sub_one_cube_bound
EOF
```

Expected: tests pass, no proved-file `sorry` or `admit` hits, build exits 0, scripts exit 0, and the theorem axiom print contains only the standard trusted base already expected in this project.

- [ ] **Step 9: Commit the milestone**

Run:

```bash
git add docs/superpowers/plans/2026-07-05-erdos699-t7-cube-squeeze-bound.md lean/Erdos699/Proved/Basic.lean notes/PROGRESS.md
git commit -m "feat: prove erdos699 t7 cube squeeze bound"
```
