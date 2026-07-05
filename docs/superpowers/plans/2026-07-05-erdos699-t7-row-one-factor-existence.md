# Erdos699 T7 Row-One Factor Existence Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Bank a sorry-free T7 bridge that packages the row-one divisor as an explicit factor and immediately combines it with the proved joint large-part cancellation.

**Architecture:** Add two theorems to `lean/Erdos699/Proved/Basic.lean` near the existing row-one and T7 cancellation lemmas. The first theorem turns `n - 1 ∣ t * (X - t)` into an existential factor. The second theorem returns the same factor together with the row-two large-prime-part divisibility, preserving explicit hypotheses and avoiding any claim that full T7 is closed.

**Tech Stack:** Lean 4, Mathlib, Lake, existing `Erdos699.Proved.Basic` theorem surface.

---

### Task 1: Row-One Factor Existence API

**Files:**
- Create: `lean/Erdos699/WIP/T7RowOneFactorExistenceTest.lean`
- Modify: `lean/Erdos699/Proved/Basic.lean`
- Modify: `notes/PROGRESS.md`

- [ ] **Step 1: Write the failing WIP API check**

```lean
import Erdos699.Proved.Basic

#check Erdos699.i_three_caseI_row_one_exists_factor
#check Erdos699.i_three_caseI_exists_joint_large_part_factor
```

- [ ] **Step 2: Run the WIP check to verify it fails**

Run:

```bash
lake env lean lean/Erdos699/WIP/T7RowOneFactorExistenceTest.lean
```

Expected: failure with unknown identifier errors for the two new theorem names.

- [ ] **Step 3: Add the row-one factor theorem**

Insert after `i_three_caseI_row_one_sub_one_dvd_t_mul_X_sub_t`:

```lean
theorem i_three_caseI_row_one_exists_factor {n F X j t : ℕ}
    (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor n 3 j q)
    (hn : n = F * X) (hj : j = F * t) (hn_gt : 2 < n) (hj_pos : 0 < j)
    (h2n : 2 ∣ n) (h3n : 3 ∣ n) (htX : t ≤ X) :
    ∃ g : ℕ, t * (X - t) = g * (n - 1) := by
  rcases i_three_caseI_row_one_sub_one_dvd_t_mul_X_sub_t
      hnone hn hj hn_gt hj_pos h2n h3n htX with ⟨g, hg⟩
  exact ⟨g, by simpa [mul_comm] using hg⟩
```

- [ ] **Step 4: Add the combined joint-factor theorem**

Insert after `i_three_caseI_joint_large_part_dvd_factor_mul_X_sub_two_t`:

```lean
theorem i_three_caseI_exists_joint_large_part_factor {n F X j t : ℕ}
    (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor n 3 j q)
    (hn : n = F * X) (hj : j = F * t) (hn_gt : 2 < n) (hj_pos : 0 < j)
    (hj_two : 2 ≤ j) (h2n : 2 ∣ n) (h3n : 3 ∣ n) (h2tX : 2 * t ≤ X) :
    ∃ g : ℕ,
      t * (X - t) = g * (n - 1) ∧
        primePowerPartGE 5 (n - 2) ∣ g * (X - 2 * t) := by
  rcases i_three_caseI_row_one_exists_factor
      hnone hn hj hn_gt hj_pos h2n h3n (by omega : t ≤ X) with ⟨g, hg⟩
  exact ⟨g, hg,
    i_three_caseI_joint_large_part_dvd_factor_mul_X_sub_two_t
      hnone hn hj (by omega : 2 ≤ n) hn_gt hj_two (by omega : t ≤ X) h2tX hg⟩
```

- [ ] **Step 5: Update progress log**

Add a `[R]` entry to `notes/PROGRESS.md` naming both new theorems and stating that full T7 remains open.

- [ ] **Step 6: Run focused verification**

Run:

```bash
lake env lean lean/Erdos699/Proved/Basic.lean
lake build Erdos699.Proved.Basic
lake env lean lean/Erdos699/WIP/T7RowOneFactorExistenceTest.lean
```

Expected: all commands exit 0.

- [ ] **Step 7: Remove the WIP check and run full gates**

Delete `lean/Erdos699/WIP/T7RowOneFactorExistenceTest.lean`, then run:

```bash
python3 -m pytest compute/tests/test_criterion.py -q
rg -n "\bsorry\b|\badmit\b" lean/Erdos699/Proved || true
git diff --check
lake build
bash scripts/check_axioms.sh
bash scripts/check_manifest.sh
lake env lean --stdin <<'EOF'
import Erdos699.Proved.Basic
#print axioms Erdos699.i_three_caseI_exists_joint_large_part_factor
EOF
```

Expected: tests pass, no proved-file `sorry` or `admit` hits, build exits 0, scripts exit 0, and the theorem axiom print contains no unexpected noncomputable or native-decide audit footprint beyond Lean's standard trusted base.

- [ ] **Step 8: Commit the milestone**

Run:

```bash
git add docs/superpowers/plans/2026-07-05-erdos699-t7-row-one-factor-existence.md lean/Erdos699/Proved/Basic.lean notes/PROGRESS.md
git commit -m "feat: prove erdos699 t7 factor existence"
```
