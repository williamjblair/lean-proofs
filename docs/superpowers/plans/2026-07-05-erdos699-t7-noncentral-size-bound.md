# Erdos699 T7 Noncentral Size Bound Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Bank a sorry-free conditional T7 size bound on the non-central branch `0 < X - 2 * t`.

**Architecture:** Add a fixed-factor theorem that turns the proved large-prime-part divisibility into an inequality using `Nat.le_of_dvd` once the product is positive. Add an existential theorem that combines the row-one factor-existence wrapper with divisibility and the new inequality. The statements are explicitly conditional and do not claim the central branch or full T7.

**Tech Stack:** Lean 4, Mathlib, Lake, existing `Erdos699.Proved.Basic` theorem surface.

---

### Task 1: Noncentral Large-Part Size Bound

**Files:**
- Create: `lean/Erdos699/WIP/T7NoncentralSizeBoundTest.lean`
- Modify: `lean/Erdos699/Proved/Basic.lean`
- Modify: `notes/PROGRESS.md`

- [ ] **Step 1: Write the failing WIP API check**

```lean
import Erdos699.Proved.Basic

#check Erdos699.i_three_caseI_joint_large_part_le_factor_mul_X_sub_two_t
#check Erdos699.i_three_caseI_exists_joint_large_part_factor_le
```

- [ ] **Step 2: Run the WIP check to verify it fails**

Run:

```bash
lake env lean lean/Erdos699/WIP/T7NoncentralSizeBoundTest.lean
```

Expected: failure with unknown identifier errors for the two new theorem names.

- [ ] **Step 3: Add the fixed-factor size theorem**

Insert after `i_three_caseI_joint_large_part_dvd_factor_mul_X_sub_two_t`:

```lean
theorem i_three_caseI_joint_large_part_le_factor_mul_X_sub_two_t {n F X j t g : ℕ}
    (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor n 3 j q)
    (hn : n = F * X) (hj : j = F * t) (hn_gt : 2 < n)
    (hj_two : 2 ≤ j) (hrow1 : t * (X - t) = g * (n - 1))
    (hbranch : 0 < X - 2 * t) :
    primePowerPartGE 5 (n - 2) ≤ g * (X - 2 * t) := by
  have hdvd :
      primePowerPartGE 5 (n - 2) ∣ g * (X - 2 * t) :=
    i_three_caseI_joint_large_part_dvd_factor_mul_X_sub_two_t
      hnone hn hj (by omega : 2 ≤ n) hn_gt hj_two
      (by omega : t ≤ X) (by omega : 2 * t ≤ X) hrow1
  have ht_pos : 0 < t := by
    by_cases ht0 : t = 0
    · subst t
      simp at hj
      omega
    · exact Nat.pos_of_ne_zero ht0
  have hXt_pos : 0 < X - t := by omega
  have hleft_pos : 0 < t * (X - t) := Nat.mul_pos ht_pos hXt_pos
  have hright_pos : 0 < g * (n - 1) := by
    simpa [hrow1] using hleft_pos
  have hg_pos : 0 < g := by
    by_cases hg0 : g = 0
    · subst g
      simp at hright_pos
    · exact Nat.pos_of_ne_zero hg0
  exact Nat.le_of_dvd (Nat.mul_pos hg_pos hbranch) hdvd
```

- [ ] **Step 4: Add the existential packaged size theorem**

Insert after `i_three_caseI_exists_joint_large_part_factor`:

```lean
theorem i_three_caseI_exists_joint_large_part_factor_le {n F X j t : ℕ}
    (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor n 3 j q)
    (hn : n = F * X) (hj : j = F * t) (hn_gt : 2 < n) (hj_pos : 0 < j)
    (hj_two : 2 ≤ j) (h2n : 2 ∣ n) (h3n : 3 ∣ n) (hbranch : 0 < X - 2 * t) :
    ∃ g : ℕ,
      t * (X - t) = g * (n - 1) ∧
        primePowerPartGE 5 (n - 2) ∣ g * (X - 2 * t) ∧
          primePowerPartGE 5 (n - 2) ≤ g * (X - 2 * t) := by
  rcases i_three_caseI_exists_joint_large_part_factor
      hnone hn hj hn_gt hj_pos hj_two h2n h3n (by omega : 2 * t ≤ X) with
    ⟨g, hrow1, hdvd⟩
  exact ⟨g, hrow1, hdvd,
    i_three_caseI_joint_large_part_le_factor_mul_X_sub_two_t
      hnone hn hj hn_gt hj_two hrow1 hbranch⟩
```

- [ ] **Step 5: Update progress log**

Add a `[R]` entry to `notes/PROGRESS.md` naming both new theorems and stating that this only covers the non-central branch under `0 < X - 2 * t`; full T7 remains open.

- [ ] **Step 6: Run focused verification**

Run:

```bash
lake env lean lean/Erdos699/Proved/Basic.lean
lake build Erdos699.Proved.Basic
lake env lean lean/Erdos699/WIP/T7NoncentralSizeBoundTest.lean
```

Expected: all commands exit 0.

- [ ] **Step 7: Remove the WIP check and run full gates**

Delete `lean/Erdos699/WIP/T7NoncentralSizeBoundTest.lean`, then run:

```bash
python3 -m pytest compute/tests/test_criterion.py -q
rg -n "\bsorry\b|\badmit\b" lean/Erdos699/Proved || true
git diff --check
lake build
bash scripts/check_axioms.sh
bash scripts/check_manifest.sh
lake env lean --stdin <<'EOF'
import Erdos699.Proved.Basic
#print axioms Erdos699.i_three_caseI_exists_joint_large_part_factor_le
EOF
```

Expected: tests pass, no proved-file `sorry` or `admit` hits, build exits 0, scripts exit 0, and the theorem axiom print contains only the standard trusted base already expected in this project.

- [ ] **Step 8: Commit the milestone**

Run:

```bash
git add docs/superpowers/plans/2026-07-05-erdos699-t7-noncentral-size-bound.md lean/Erdos699/Proved/Basic.lean notes/PROGRESS.md
git commit -m "feat: prove erdos699 t7 noncentral size bound"
```
