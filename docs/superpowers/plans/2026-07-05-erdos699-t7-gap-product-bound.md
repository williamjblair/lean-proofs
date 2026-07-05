# Erdos699 T7 Gap Product Bound Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Bank a sorry-free non-central T7 product inequality combining the row-one parabola bound with the row-two large-prime-part size bound.

**Architecture:** Add a fixed-factor theorem proving `4 * ((n - 1) * primePowerPartGE 5 (n - 2)) ≤ X * X * (X - 2 * t)` under the explicit non-central branch and row-one factor equation. Add an existential wrapper that packages the row-one factor, divisibility, size bound, and product gap inequality for later kernel arguments.

**Tech Stack:** Lean 4, Mathlib, Lake, existing `Erdos699.Proved.Basic` theorem surface.

---

### Task 1: Noncentral Gap Product Bound

**Files:**
- Create: `lean/Erdos699/WIP/T7GapProductBoundTest.lean`
- Modify: `lean/Erdos699/Proved/Basic.lean`
- Modify: `notes/PROGRESS.md`

- [ ] **Step 1: Write the failing WIP API check**

```lean
import Erdos699.Proved.Basic

#check Erdos699.i_three_caseI_joint_large_part_gap_bound
#check Erdos699.i_three_caseI_exists_joint_large_part_gap_bound
```

- [ ] **Step 2: Run the WIP check to verify it fails**

Run:

```bash
lake env lean lean/Erdos699/WIP/T7GapProductBoundTest.lean
```

Expected: failure with unknown identifier errors for the two new theorem names.

- [ ] **Step 3: Add the fixed-factor gap theorem**

Insert after `i_three_caseI_joint_large_part_le_factor_mul_X_sub_two_t`:

```lean
theorem i_three_caseI_joint_large_part_gap_bound {n F X j t g : ℕ}
    (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor n 3 j q)
    (hn : n = F * X) (hj : j = F * t) (hn_gt : 2 < n)
    (hj_two : 2 ≤ j) (hrow1 : t * (X - t) = g * (n - 1))
    (hbranch : 0 < X - 2 * t) :
    4 * ((n - 1) * primePowerPartGE 5 (n - 2)) ≤ X * X * (X - 2 * t) := by
  have hlarge :
      primePowerPartGE 5 (n - 2) ≤ g * (X - 2 * t) :=
    i_three_caseI_joint_large_part_le_factor_mul_X_sub_two_t
      hnone hn hj hn_gt hj_two hrow1 hbranch
  have hrow_bound : 4 * (g * (n - 1)) ≤ X * X := by
    simpa [hrow1] using four_mul_t_mul_X_sub_t_le_sq (by omega : 2 * t ≤ X)
  calc
    4 * ((n - 1) * primePowerPartGE 5 (n - 2))
        ≤ 4 * ((n - 1) * (g * (X - 2 * t))) := by
          exact Nat.mul_le_mul_left 4 (Nat.mul_le_mul_left (n - 1) hlarge)
    _ = (4 * (g * (n - 1))) * (X - 2 * t) := by ring
    _ ≤ (X * X) * (X - 2 * t) := by
          exact Nat.mul_le_mul_right (X - 2 * t) hrow_bound
    _ = X * X * (X - 2 * t) := by ring
```

- [ ] **Step 4: Add the existential packaged gap theorem**

Insert after `i_three_caseI_exists_joint_large_part_factor_le`:

```lean
theorem i_three_caseI_exists_joint_large_part_gap_bound {n F X j t : ℕ}
    (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor n 3 j q)
    (hn : n = F * X) (hj : j = F * t) (hn_gt : 2 < n) (hj_pos : 0 < j)
    (hj_two : 2 ≤ j) (h2n : 2 ∣ n) (h3n : 3 ∣ n) (hbranch : 0 < X - 2 * t) :
    ∃ g : ℕ,
      t * (X - t) = g * (n - 1) ∧
        primePowerPartGE 5 (n - 2) ∣ g * (X - 2 * t) ∧
          primePowerPartGE 5 (n - 2) ≤ g * (X - 2 * t) ∧
            4 * ((n - 1) * primePowerPartGE 5 (n - 2)) ≤
              X * X * (X - 2 * t) := by
  rcases i_three_caseI_exists_joint_large_part_factor_le
      hnone hn hj hn_gt hj_pos hj_two h2n h3n hbranch with
    ⟨g, hrow1, hdvd, hle⟩
  exact ⟨g, hrow1, hdvd, hle,
    i_three_caseI_joint_large_part_gap_bound hnone hn hj hn_gt hj_two hrow1 hbranch⟩
```

- [ ] **Step 5: Update progress log**

Add a `[R]` entry to `notes/PROGRESS.md` naming both new theorems and stating that this is still conditional on the non-central branch; full T7 remains open.

- [ ] **Step 6: Run focused verification**

Run:

```bash
lake env lean lean/Erdos699/Proved/Basic.lean
lake build Erdos699.Proved.Basic
lake env lean lean/Erdos699/WIP/T7GapProductBoundTest.lean
```

Expected: all commands exit 0.

- [ ] **Step 7: Remove the WIP check and run full gates**

Delete `lean/Erdos699/WIP/T7GapProductBoundTest.lean`, then run:

```bash
python3 -m pytest compute/tests/test_criterion.py -q
rg -n "\bsorry\b|\badmit\b" lean/Erdos699/Proved || true
git diff --check
lake build
bash scripts/check_axioms.sh
bash scripts/check_manifest.sh
lake env lean --stdin <<'EOF'
import Erdos699.Proved.Basic
#print axioms Erdos699.i_three_caseI_exists_joint_large_part_gap_bound
EOF
```

Expected: tests pass, no proved-file `sorry` or `admit` hits, build exits 0, scripts exit 0, and the theorem axiom print contains only the standard trusted base already expected in this project.

- [ ] **Step 8: Commit the milestone**

Run:

```bash
git add docs/superpowers/plans/2026-07-05-erdos699-t7-gap-product-bound.md lean/Erdos699/Proved/Basic.lean notes/PROGRESS.md
git commit -m "feat: prove erdos699 t7 gap product bound"
```
