# Erdos699 T6 Algebra Bridge Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Prove the T6 row-one algebra bridge from `n - 1 ∣ j * (j - 1)` to `n - 1 ∣ t * (X - t)` under a factorization `n = F * X`, `j = F * t`, and `t ≤ X`.

**Architecture:** Add one generic integer-congruence bridge theorem to `lean/Erdos699/Proved/Basic.lean`, then instantiate it with the existing case-I row-one divisor theorem `i_three_window_one_sub_one_dvd_mul_sub_one_of_even_three_dvd`. Keep this as T6 structure support only; it does not prove full T6/T7 or the kernel.

**Tech Stack:** Lean 4, Mathlib `Nat.ModEq`/`Int.ModEq`, existing `Erdos699.Proved.Basic`, exact Python criterion tests.

---

### Task 1: Red WIP API Check

**Files:**
- Create: `lean/Erdos699/WIP/T6AlgebraBridgeTest.lean`

- [x] **Step 1: Write the failing API check**

```lean
import Erdos699.Proved.Basic

#check Erdos699.sub_one_dvd_t_mul_X_sub_t_of_factor_dvd_mul_sub_one
#check Erdos699.i_three_caseI_row_one_sub_one_dvd_t_mul_X_sub_t
```

- [x] **Step 2: Run Lean and confirm expected failure**

```bash
lake env lean lean/Erdos699/WIP/T6AlgebraBridgeTest.lean
```

Expected: unknown constants for the two new theorem names.

### Task 2: Add the Generic Algebra Bridge

**Files:**
- Modify: `lean/Erdos699/Proved/Basic.lean`
- Delete: `lean/Erdos699/WIP/T6AlgebraBridgeScratch.lean`

- [x] **Step 1: Add `sub_one_dvd_t_mul_X_sub_t_of_factor_dvd_mul_sub_one` after the case-I row-one bridge**

```lean
theorem sub_one_dvd_t_mul_X_sub_t_of_factor_dvd_mul_sub_one {n F X j t : ℕ}
    (hn : n = F * X) (hj : j = F * t) (hn_gt : 2 < n) (hj_pos : 0 < j)
    (htX : t ≤ X) (hdvd : n - 1 ∣ j * (j - 1)) :
    n - 1 ∣ t * (X - t) := by
  let d := n - 1
  have hd_gt_one : 1 < d := by
    dsimp [d]
    omega
  have hn_mod_nat : n ≡ 1 [MOD d] := by
    have hn_eq : n = d * 1 + 1 := by
      dsimp [d]
      omega
    rw [hn_eq, Nat.ModEq]
    simp [Nat.mod_eq_of_lt hd_gt_one]
  have hFX_nat : F * X ≡ 1 [MOD d] := by
    simpa [d, hn] using hn_mod_nat
  have hFX_int : (F : ℤ) * (X : ℤ) ≡ 1 [ZMOD (d : ℤ)] := by
    exact_mod_cast hFX_nat
  have hzero_nat : j * (j - 1) ≡ 0 [MOD d] :=
    Nat.modEq_zero_iff_dvd.mpr (by simpa [d] using hdvd)
  have hzero_int : (j : ℤ) * ((j : ℤ) - 1) ≡ 0 [ZMOD (d : ℤ)] := by
    have hcast :
        ((j * (j - 1) : ℕ) : ℤ) = (j : ℤ) * ((j : ℤ) - 1) := by
      rw [Nat.cast_mul, Nat.cast_sub (Nat.succ_le_of_lt hj_pos)]
      norm_num
    simpa [hcast] using (Int.natCast_modEq_iff.mpr hzero_nat)
  have hj_int : (j : ℤ) = (F : ℤ) * (t : ℤ) := by
    exact_mod_cast hj
  have hzero_Ft : ((F : ℤ) * (t : ℤ)) * (((F : ℤ) * (t : ℤ)) - 1) ≡
      0 [ZMOD (d : ℤ)] := by
    simpa [hj_int] using hzero_int
  have hfirst : (X : ℤ) * ((F : ℤ) * (t : ℤ)) ≡ (t : ℤ) [ZMOD (d : ℤ)] := by
    have h := hFX_int.mul_right (t : ℤ)
    simpa [mul_assoc, mul_comm, mul_left_comm] using h
  have hsecond : (X : ℤ) * (((F : ℤ) * (t : ℤ)) - 1) ≡
      (t : ℤ) - (X : ℤ) [ZMOD (d : ℤ)] := by
    have h := hfirst.sub (Int.ModEq.refl (a := (X : ℤ)) (n := (d : ℤ)))
    simpa [mul_sub] using h
  have hprod : ((X : ℤ) ^ 2) *
        (((F : ℤ) * (t : ℤ)) * (((F : ℤ) * (t : ℤ)) - 1)) ≡
      (t : ℤ) * ((t : ℤ) - (X : ℤ)) [ZMOD (d : ℤ)] := by
    have h := hfirst.mul hsecond
    simpa [pow_two, mul_assoc, mul_comm, mul_left_comm] using h
  have hscaled_zero : ((X : ℤ) ^ 2) *
        (((F : ℤ) * (t : ℤ)) * (((F : ℤ) * (t : ℤ)) - 1)) ≡
      0 [ZMOD (d : ℤ)] := by
    simpa using hzero_Ft.mul_left ((X : ℤ) ^ 2)
  have htx_zero : (t : ℤ) * ((t : ℤ) - (X : ℤ)) ≡ 0 [ZMOD (d : ℤ)] :=
    hprod.symm.trans hscaled_zero
  have htarget_int : ((t * (X - t) : ℕ) : ℤ) ≡ 0 [ZMOD (d : ℤ)] := by
    have hcast_sub : ((X - t : ℕ) : ℤ) = (X : ℤ) - (t : ℤ) :=
      Nat.cast_sub htX
    have hcast :
        ((t * (X - t) : ℕ) : ℤ) =
          -((t : ℤ) * ((t : ℤ) - (X : ℤ))) := by
      rw [Nat.cast_mul, hcast_sub]
      ring
    simpa [hcast] using htx_zero.neg
  have hdvd_int : (d : ℤ) ∣ ((t * (X - t) : ℕ) : ℤ) :=
    Int.modEq_zero_iff_dvd.mp htarget_int
  exact Int.natCast_dvd_natCast.mp hdvd_int
```

- [x] **Step 2: Delete the scratch file**

```bash
rm lean/Erdos699/WIP/T6AlgebraBridgeScratch.lean
```

Use `apply_patch` deletion rather than shell deletion.

### Task 3: Add the Row-3 Case-I Instantiation

**Files:**
- Modify: `lean/Erdos699/Proved/Basic.lean`

- [x] **Step 1: Add `i_three_caseI_row_one_sub_one_dvd_t_mul_X_sub_t` after the generic bridge**

```lean
theorem i_three_caseI_row_one_sub_one_dvd_t_mul_X_sub_t {n F X j t : ℕ}
    (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor n 3 j q)
    (hn : n = F * X) (hj : j = F * t) (hn_gt : 2 < n) (hj_pos : 0 < j)
    (h2n : 2 ∣ n) (h3n : 3 ∣ n) (htX : t ≤ X) :
    n - 1 ∣ t * (X - t) :=
  sub_one_dvd_t_mul_X_sub_t_of_factor_dvd_mul_sub_one hn hj hn_gt hj_pos htX
    (i_three_window_one_sub_one_dvd_mul_sub_one_of_even_three_dvd
      hnone (by omega : 1 < n) h2n h3n)
```

### Task 4: Verification, Progress, and Commit

**Files:**
- Modify: `notes/PROGRESS.md`
- Delete: `lean/Erdos699/WIP/T6AlgebraBridgeTest.lean`

- [x] **Step 1: Run WIP API check green and remove the WIP test file**

```bash
lake build Erdos699.Proved.Basic
lake env lean lean/Erdos699/WIP/T6AlgebraBridgeTest.lean
```

Expected: Lean prints both theorem signatures. Then delete the WIP API file.

- [x] **Step 2: Add the `[R]` progress entry**

```md
- [R] Proved the T6 row-one algebra bridge:
  `Erdos699.i_three_caseI_row_one_sub_one_dvd_t_mul_X_sub_t` turns the
  case-I divisor `n - 1 ∣ j * (j - 1)` into the normalized form
  `n - 1 ∣ t * (X - t)` whenever `n = F * X`, `j = F * t`, and `t ≤ X`.
  Full T6/T7 remain open.
```

- [x] **Step 3: Run verification gates**

```bash
lake env lean lean/Erdos699/Proved/Basic.lean
python3 -m pytest compute/tests/test_criterion.py -q
rg -n "\bsorry\b|\badmit\b" lean/Erdos699/Proved || true
git diff --check
lake build
bash scripts/check_axioms.sh
bash scripts/check_manifest.sh
lake env lean --stdin <<'EOF'
import Erdos699.Proved.Basic
#print axioms Erdos699.i_three_caseI_row_one_sub_one_dvd_t_mul_X_sub_t
EOF
```

- [x] **Step 4: Commit the milestone**

```bash
git add docs/superpowers/plans/2026-07-05-erdos699-t6-algebra-bridge.md lean/Erdos699/Proved/Basic.lean notes/PROGRESS.md
git commit -m "feat: prove erdos699 t6 algebra bridge"
```
