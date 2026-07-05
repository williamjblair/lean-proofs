# Erdos699 T7 Factor Square Squeeze Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Bank a sorry-free exact cofactor squeeze from the half-row cube inequality: `2 * (F * F) ≤ X`.

**Architecture:** Add a pure arithmetic lemma converting `n = F * X`, even `X`, and `4 * ((n - 1) * (n / 2 - 1)) ≤ X^3` into `2 * (F * F) ≤ X`. Then add the T7 wrapper that invokes `i_three_caseI_noncentral_half_sub_one_cube_bound` under the existing explicit non-central and half-row lower-bound hypotheses. This advances the `odd(n) ≤ sqrt(X/2)` lane but still does not close the lower-bound input, central branch, or full T7.

**Tech Stack:** Lean 4, Mathlib, Lake, existing `Erdos699.Proved.Basic` theorem surface.

---

### Task 1: Exact Factor Square Squeeze

**Files:**
- Create: `lean/Erdos699/WIP/T7FactorSquareSqueezeTest.lean`
- Modify: `lean/Erdos699/Proved/Basic.lean`
- Modify: `notes/PROGRESS.md`

- [ ] **Step 1: Write the failing WIP API check**

```lean
import Erdos699.Proved.Basic

#check Erdos699.two_mul_factor_sq_le_of_even_half_cube_bound
#check Erdos699.i_three_caseI_noncentral_factor_sq_squeeze
```

- [ ] **Step 2: Run the WIP check to verify it fails**

Run:

```bash
lake env lean lean/Erdos699/WIP/T7FactorSquareSqueezeTest.lean
```

Expected: failure with unknown identifier errors for the two new theorem names.

- [ ] **Step 3: Add the pure arithmetic lemma**

Insert after `i_three_caseI_noncentral_half_sub_one_cube_bound`:

```lean
theorem two_mul_factor_sq_le_of_even_half_cube_bound {n F X : ℕ}
    (hn : n = F * X) (hn_gt : 2 < n) (hX_even : 2 ∣ X)
    (hbound : 4 * ((n - 1) * (n / 2 - 1)) ≤ X * X * X) :
    2 * (F * F) ≤ X := by
  rcases hX_even with ⟨a, ha⟩
  subst X
  subst n
  have hdouble : F * (2 * a) = 2 * (F * a) := by ring
  have hFa_gt_one : 1 < F * a := by
    have hlt_double : 2 * 1 < 2 * (F * a) := by
      simpa [hdouble] using hn_gt
    exact Nat.lt_of_mul_lt_mul_left hlt_double
  by_contra hnot
  have hlt2 : 2 * a < 2 * (F * F) := Nat.lt_of_not_ge hnot
  have hlt : a < F * F := Nat.lt_of_mul_lt_mul_left hlt2
  have ha_pos : 0 < a := by
    by_contra hapos
    have ha0 : a = 0 := Nat.eq_zero_of_not_pos hapos
    subst a
    simp at hFa_gt_one
  have hF_ge_two : 2 ≤ F := by
    by_contra hFnot
    have hFlt2 : F < 2 := Nat.lt_of_not_ge hFnot
    interval_cases F <;> omega
  let k : ℕ := F * F - a
  have hk_pos : 0 < k := by dsimp [k]; omega
  have hsum_int : (a : ℤ) + (k : ℤ) = (F : ℤ) * (F : ℤ) := by
    dsimp [k]
    rw [Nat.cast_sub (by omega : a ≤ F * F), Nat.cast_mul]
    ring
  have ha_int : (1 : ℤ) ≤ a := by exact_mod_cast ha_pos
  have hk_int : (1 : ℤ) ≤ k := by exact_mod_cast hk_pos
  have hprod_lower_int : (F : ℤ) * (F : ℤ) - 1 ≤ (a : ℤ) * (k : ℤ) := by
    have hnonneg : (0 : ℤ) ≤ ((a : ℤ) - 1) * ((k : ℤ) - 1) :=
      mul_nonneg (by omega) (by omega)
    nlinarith
  have htwo_lower_int : (3 : ℤ) * (F : ℤ) ≤ 2 * ((F : ℤ) * (F : ℤ) - 1) := by
    have hF_int : (2 : ℤ) ≤ F := by exact_mod_cast hF_ge_two
    nlinarith
  have hkey_int : (3 : ℤ) * (F : ℤ) ≤ 2 * ((a : ℤ) * (k : ℤ)) := by nlinarith
  have hk_eq_int : ((k : ℕ) : ℤ) = (F : ℤ) * (F : ℤ) - (a : ℤ) := by
    dsimp [k]
    rw [Nat.cast_sub (by omega : a ≤ F * F), Nat.cast_mul]
  have hF2a_ge_one : 1 ≤ F * (2 * a) := by omega
  have hcast1 : ((F * (2 * a) - 1 : ℕ) : ℤ) = (F : ℤ) * (2 * (a : ℤ)) - 1 := by
    rw [Nat.cast_sub hF2a_ge_one, Nat.cast_mul, Nat.cast_mul]
    norm_num
  have hcast2 : ((F * (2 * a) / 2 - 1 : ℕ) : ℤ) = (F : ℤ) * (a : ℤ) - 1 := by
    have hdiv : F * (2 * a) / 2 = F * a := by omega
    rw [hdiv, Nat.cast_sub (Nat.le_of_lt hFa_gt_one), Nat.cast_mul]
    norm_num
  have hbound_int :
      (4 : ℤ) * (((F : ℤ) * (2 * (a : ℤ)) - 1) * ((F : ℤ) * (a : ℤ) - 1)) ≤
        (2 * (a : ℤ)) * (2 * (a : ℤ)) * (2 * (a : ℤ)) := by
    have h := hbound
    have hleft :
        ((4 * (((F * (2 * a) - 1) * (F * (2 * a) / 2 - 1))) : ℕ) : ℤ) =
          (4 : ℤ) * (((F : ℤ) * (2 * (a : ℤ)) - 1) *
            ((F : ℤ) * (a : ℤ) - 1)) := by
      rw [Nat.cast_mul, Nat.cast_mul, hcast1, hcast2]
      norm_num
    have hright : (((2 * a) * (2 * a) * (2 * a) : ℕ) : ℤ) =
        (2 * (a : ℤ)) * (2 * (a : ℤ)) * (2 * (a : ℤ)) := by norm_num
    exact hleft ▸ hright ▸ (by exact_mod_cast h)
  have hmain_pos :
      (0 : ℤ) <
        (4 : ℤ) * (((F : ℤ) * (2 * (a : ℤ)) - 1) * ((F : ℤ) * (a : ℤ) - 1)) -
          (2 * (a : ℤ)) * (2 * (a : ℤ)) * (2 * (a : ℤ)) := by
    rw [hk_eq_int] at hkey_int
    nlinarith
  nlinarith
```

- [ ] **Step 4: Add the T7 wrapper**

Insert after the arithmetic lemma:

```lean
theorem i_three_caseI_noncentral_factor_sq_squeeze {n F X j t : ℕ}
    (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor n 3 j q)
    (hn : n = F * X) (hj : j = F * t) (hn_gt : 2 < n) (hj_pos : 0 < j)
    (hj_two : 2 ≤ j) (h2n : 2 ∣ n) (h3n : 3 ∣ n) (hX_even : 2 ∣ X)
    (hbranch : 0 < X - 2 * t)
    (hhalf : n / 2 - 1 ≤ primePowerPartGE 5 (n - 2)) :
    2 * (F * F) ≤ X :=
  two_mul_factor_sq_le_of_even_half_cube_bound hn hn_gt hX_even
    (i_three_caseI_noncentral_half_sub_one_cube_bound
      hnone hn hj hn_gt hj_pos hj_two h2n h3n hbranch hhalf)
```

- [ ] **Step 5: Update progress log**

Add a `[R]` entry to `notes/PROGRESS.md` naming both new theorems and stating that this is the exact non-central cofactor squeeze under the still-open half-row lower-bound hypothesis.

- [ ] **Step 6: Run focused verification**

Run:

```bash
lake env lean lean/Erdos699/Proved/Basic.lean
lake build Erdos699.Proved.Basic
lake env lean lean/Erdos699/WIP/T7FactorSquareSqueezeTest.lean
```

Expected: all commands exit 0.

- [ ] **Step 7: Remove the WIP check and run full gates**

Delete `lean/Erdos699/WIP/T7FactorSquareSqueezeTest.lean`, then run:

```bash
python3 -m pytest compute/tests/test_criterion.py -q
rg -n "\bsorry\b|\badmit\b" lean/Erdos699/Proved || true
git diff --check
lake build
bash scripts/check_axioms.sh
bash scripts/check_manifest.sh
lake env lean --stdin <<'EOF'
import Erdos699.Proved.Basic
#print axioms Erdos699.i_three_caseI_noncentral_factor_sq_squeeze
EOF
```

Expected: tests pass, no proved-file `sorry` or `admit` hits, build exits 0, scripts exit 0, and the theorem axiom print contains only the standard trusted base already expected in this project.

- [ ] **Step 8: Commit the milestone**

Run:

```bash
git add docs/superpowers/plans/2026-07-05-erdos699-t7-factor-square-squeeze.md lean/Erdos699/Proved/Basic.lean notes/PROGRESS.md
git commit -m "feat: prove erdos699 t7 factor square squeeze"
```
