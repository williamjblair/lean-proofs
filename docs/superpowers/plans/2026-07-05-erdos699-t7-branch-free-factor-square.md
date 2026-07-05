# Erdos699 T7 Branch-Free Factor-Square Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Remove the explicit non-central branch hypothesis from the T7 factor-square squeeze wrappers by combining them with the central branch contradiction.

**Architecture:** Add two wrapper theorems. Each assumes the natural side condition `2 * t ≤ X`; if `2 * t = X`, invoke `i_three_caseI_central_branch_false`; otherwise `omega` gives `0 < X - 2 * t`, and the existing noncentral factor-square theorem applies. This is a packaging theorem only; it does not close the half-row lower-bound or free 2-adic obstruction.

**Tech Stack:** Lean 4, Mathlib, Lake, existing `Erdos699.Proved.Basic` theorem surface.

---

### Task 1: Branch-Free Factor-Square Wrappers

**Files:**
- Create: `lean/Erdos699/WIP/BranchFreeFactorSquareCheck.lean`
- Modify: `lean/Erdos699/Proved/Basic.lean`
- Modify: `notes/PROGRESS.md`

- [ ] **Step 1: Write the failing WIP API check**

```lean
import Erdos699.Proved.Basic

namespace Erdos699

#check i_three_caseI_factor_sq_squeeze_of_half_bound
#check i_three_caseI_factor_sq_squeeze_of_half_coprime_four

end Erdos699
```

- [ ] **Step 2: Run the WIP check to verify it fails**

Run:

```bash
lake env lean lean/Erdos699/WIP/BranchFreeFactorSquareCheck.lean
```

Expected: failure with unknown identifier errors for both theorem names.

- [ ] **Step 3: Add the half-bound branch-free theorem**

Insert after `i_three_caseI_noncentral_factor_sq_squeeze`:

```lean
theorem i_three_caseI_factor_sq_squeeze_of_half_bound {n F X j t : ℕ}
    (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor n 3 j q)
    (hn : n = F * X) (hj : j = F * t) (hn_gt : 2 < n) (hj_pos : 0 < j)
    (hj_two : 2 ≤ j) (h2n : 2 ∣ n) (h3n : 3 ∣ n) (hX_even : 2 ∣ X)
    (h2tX : 2 * t ≤ X) (hhalf : n / 2 - 1 ≤ primePowerPartGE 5 (n - 2)) :
    2 * (F * F) ≤ X := by
  by_cases hcentral : 2 * t = X
  · exact False.elim
      (i_three_caseI_central_branch_false hnone hn hj hn_gt hj_pos h2n h3n hcentral)
  · have hbranch : 0 < X - 2 * t := by omega
    exact i_three_caseI_noncentral_factor_sq_squeeze
      hnone hn hj hn_gt hj_pos hj_two h2n h3n hX_even hbranch hhalf
```

- [ ] **Step 4: Add the coprime-to-4 branch-free theorem**

Insert after `i_three_caseI_noncentral_factor_sq_squeeze_of_half_coprime_four`:

```lean
theorem i_three_caseI_factor_sq_squeeze_of_half_coprime_four {n F X j t : ℕ}
    (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor n 3 j q)
    (hn : n = F * X) (hj : j = F * t) (hn_gt : 2 < n) (hj_pos : 0 < j)
    (hj_two : 2 ≤ j) (h2n : 2 ∣ n) (h3n : 3 ∣ n) (hX_even : 2 ∣ X)
    (h2tX : 2 * t ≤ X) (hcop4 : (n / 2 - 1).Coprime 4) :
    2 * (F * F) ≤ X := by
  by_cases hcentral : 2 * t = X
  · exact False.elim
      (i_three_caseI_central_branch_false hnone hn hj hn_gt hj_pos h2n h3n hcentral)
  · have hbranch : 0 < X - 2 * t := by omega
    exact i_three_caseI_noncentral_factor_sq_squeeze_of_half_coprime_four
      hnone hn hj hn_gt hj_pos hj_two h2n h3n hX_even hbranch hcop4
```

- [ ] **Step 5: Update progress log**

Add a `[R]` entry naming both wrappers and stating they eliminate the explicit noncentral branch only under the stated `2 * t ≤ X` side condition.

- [ ] **Step 6: Run verification**

Run:

```bash
lake env lean lean/Erdos699/Proved/Basic.lean
lake build Erdos699.Proved.Basic
lake env lean lean/Erdos699/WIP/BranchFreeFactorSquareCheck.lean
python3 -m pytest compute/tests/test_criterion.py -q
rg -n "sorry|admit" lean/Erdos699/Proved
git diff --check
lake build
bash scripts/check_manifest.sh
bash scripts/check_axioms.sh
lake env lean --stdin <<'EOF'
import Erdos699.Proved.Basic
#print axioms Erdos699.i_three_caseI_factor_sq_squeeze_of_half_coprime_four
EOF
```

Expected: Lean commands, pytest, scripts, whitespace check, and full build exit 0; the `rg` command returns no matches; the axiom print reports only `[propext, Classical.choice, Quot.sound]`.

- [ ] **Step 7: Commit the milestone**

Run:

```bash
git add docs/superpowers/plans/2026-07-05-erdos699-t7-branch-free-factor-square.md lean/Erdos699/Proved/Basic.lean lean/Erdos699/WIP/BranchFreeFactorSquareCheck.lean notes/PROGRESS.md
git commit -m "feat: prove erdos699 branch-free factor squeeze"
```
