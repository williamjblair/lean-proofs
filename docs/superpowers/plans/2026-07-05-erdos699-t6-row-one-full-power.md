# Erdos699 T6 Row One Full Power Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Prove the first full-power T6 forcing theorem: for row `i = 3`, if `p^e ∣ n - 1`, then the no-common-prime hypothesis forces `p^e ∣ j * (j - 1)`.

**Architecture:** Reuse the prior T6 digit-layer lemmas. First prove general digit-to-prime-power divisibility lemmas by induction on `e`; then instantiate them with the row-3 digit constraints from `p^e ∣ n - 1`.

**Tech Stack:** Lean 4, Mathlib `Nat`, existing `Erdos699.Proved.Basic`, exact pytest criterion tests.

---

### Task 1: Red WIP API Check

**Files:**
- Create: `lean/Erdos699/WIP/T6RowOneFullPowerTest.lean`

- [x] **Step 1: Write the failing API check**

```lean
import Erdos699.Proved.Basic

#check Erdos699.pow_dvd_of_forall_digit_eq_zero
#check Erdos699.pow_dvd_sub_one_of_unit_digit_one_high_zero
#check Erdos699.pow_dvd_mul_sub_one_of_digit_le_one_high_zero
#check Erdos699.i_three_window_one_prime_pow_dvd_mul_sub_one
```

- [x] **Step 2: Run Lean and confirm expected failure**

```bash
lake env lean lean/Erdos699/WIP/T6RowOneFullPowerTest.lean
```

Expected: unknown constants for the four new theorem names.

### Task 2: Add General Digit-To-Full-Power Lemmas

**Files:**
- Modify: `lean/Erdos699/Proved/Basic.lean`

- [x] **Step 1: Add `pow_dvd_of_forall_digit_eq_zero`**

```lean
theorem pow_dvd_of_forall_digit_eq_zero {j p e : ℕ}
    (hp_pos : 0 < p) (hzero : ∀ r : ℕ, r < e → digit j p r = 0) :
    p ^ e ∣ j := by
  induction e with
  | zero =>
      simp
  | succ e ih =>
      have hlow : p ^ e ∣ j :=
        ih fun r hr => hzero r (Nat.lt_trans hr (Nat.lt_succ_self e))
      rcases hlow with ⟨a, ha⟩
      have hpow_pos : 0 < p ^ e := pow_pos hp_pos e
      have hdiv : j / p ^ e = a := by
        rw [ha]
        exact Nat.mul_div_cancel_left a hpow_pos
      have hdigit : digit j p e = 0 := hzero e (Nat.lt_succ_self e)
      have hpa : p ∣ a := by
        rw [digit, hdiv] at hdigit
        exact Nat.dvd_iff_mod_eq_zero.mpr hdigit
      rcases hpa with ⟨b, hb⟩
      refine ⟨b, ?_⟩
      rw [ha, hb, pow_succ']
      ac_rfl
```

- [x] **Step 2: Add `pow_dvd_sub_one_of_unit_digit_one_high_zero`**

```lean
theorem pow_dvd_sub_one_of_unit_digit_one_high_zero {j p e : ℕ}
    (hp : p.Prime) (hunit : digit j p 0 = 1)
    (hzero : ∀ r : ℕ, 1 ≤ r → r < e → digit j p r = 0) :
    p ^ e ∣ j - 1 := by
  induction e with
  | zero =>
      simp
  | succ e ih =>
      by_cases he0 : e = 0
      · subst e
        have hjmod : j % p = 1 := by
          simpa [digit] using hunit
        refine ⟨j / p, ?_⟩
        have hj_eq : j = p * (j / p) + 1 := by
          have h := Nat.div_add_mod j p
          rw [hjmod] at h
          omega
        have htarget : j - 1 = p * (j / p) := by omega
        simpa using htarget
      · have he_pos : 0 < e := Nat.pos_of_ne_zero he0
        have hlow : p ^ e ∣ j - 1 :=
          ih fun r hrpos hrlt => hzero r hrpos (Nat.lt_trans hrlt (Nat.lt_succ_self e))
        rcases hlow with ⟨a, ha⟩
        have hj_pos : 0 < j := by
          by_contra hj_not
          have hj0 : j = 0 := Nat.eq_zero_of_not_pos hj_not
          have hunit0 : digit j p 0 = 0 := by simp [digit, hj0]
          omega
        have hj_eq : j = p ^ e * a + 1 := by omega
        have hpow_pos : 0 < p ^ e := pow_pos hp.pos e
        have hrem_lt : 1 < p ^ e := Nat.one_lt_pow (Nat.ne_of_gt he_pos) hp.one_lt
        have hdiv : j / p ^ e = a := by
          rw [hj_eq, Nat.add_comm]
          rw [Nat.add_mul_div_left _ _ hpow_pos, Nat.div_eq_of_lt hrem_lt]
          simp
        have hdigit : digit j p e = 0 :=
          hzero e (by omega) (Nat.lt_succ_self e)
        have hpa : p ∣ a := by
          rw [digit, hdiv] at hdigit
          exact Nat.dvd_iff_mod_eq_zero.mpr hdigit
        rcases hpa with ⟨b, hb⟩
        refine ⟨b, ?_⟩
        rw [ha, hb, pow_succ']
        ac_rfl
```

- [x] **Step 3: Add `pow_dvd_mul_sub_one_of_digit_le_one_high_zero`**

```lean
theorem pow_dvd_mul_sub_one_of_digit_le_one_high_zero {j p e : ℕ}
    (hp : p.Prime) (hunit_le : digit j p 0 ≤ 1)
    (hzero : ∀ r : ℕ, 1 ≤ r → r < e → digit j p r = 0) :
    p ^ e ∣ j * (j - 1) := by
  by_cases he0 : e = 0
  · subst e
    simp
  · have hunit_cases : digit j p 0 = 0 ∨ digit j p 0 = 1 := by omega
    rcases hunit_cases with hunit0 | hunit1
    · have hall_zero : ∀ r : ℕ, r < e → digit j p r = 0 := by
        intro r hr
        by_cases hr0 : r = 0
        · simpa [hr0] using hunit0
        · exact hzero r (Nat.succ_le_of_lt (Nat.pos_of_ne_zero hr0)) hr
      have hpow : p ^ e ∣ j := pow_dvd_of_forall_digit_eq_zero hp.pos hall_zero
      exact dvd_mul_of_dvd_left hpow (j - 1)
    · have hpow : p ^ e ∣ j - 1 :=
        pow_dvd_sub_one_of_unit_digit_one_high_zero hp hunit1 hzero
      exact dvd_mul_of_dvd_right hpow j
```

### Task 3: Add Row-3 Full-Power Forcing

**Files:**
- Modify: `lean/Erdos699/Proved/Basic.lean`

- [x] **Step 1: Add `i_three_window_one_prime_pow_dvd_mul_sub_one`**

```lean
theorem i_three_window_one_prime_pow_dvd_mul_sub_one {n j p e : ℕ}
    (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor n 3 j q)
    (hp : p.Prime) (hp5 : 5 ≤ p) (hn : 1 < n) (hpdvd : p ^ e ∣ n - 1) :
    p ^ e ∣ j * (j - 1) := by
  by_cases he0 : e = 0
  · subst e
    simp
  have hunit_le : digit j p 0 ≤ 1 := by
    exact i_three_window_one_units_digit_le_one_of_prime_pow_dvd_sub_one
      hnone hp hp5 hn (Nat.pos_of_ne_zero he0) hpdvd
  have hzero : ∀ r : ℕ, 1 ≤ r → r < e → digit j p r = 0 := by
    intro r hrpos hrlt
    exact i_three_window_one_high_digit_zero_of_prime_pow_dvd_sub_one
      hnone hp hp5 hn hrpos hrlt hpdvd
  exact pow_dvd_mul_sub_one_of_digit_le_one_high_zero hp hunit_le hzero
```

### Task 4: Verification, Cleanup, and Commit

**Files:**
- Modify: `notes/PROGRESS.md`
- Delete: `lean/Erdos699/WIP/T6RowOneFullPowerTest.lean`
- Delete: `lean/Erdos699/WIP/T6PowForcingScratch.lean`

- [x] **Step 1: Run WIP API check green and remove WIP files**

```bash
lake build Erdos699.Proved.Basic
lake env lean lean/Erdos699/WIP/T6RowOneFullPowerTest.lean
```

Expected: Lean prints all four theorem signatures. Then delete both WIP files.

- [x] **Step 2: Add the `[R]` progress entry**

```md
- [R] Proved first T6 full-power forcing for the `n - 1` row:
  `Erdos699.i_three_window_one_prime_pow_dvd_mul_sub_one` shows that under
  row-3 no-common-prime hypotheses, every prime power `p^e ∣ n - 1` with
  `p ≥ 5` divides `j * (j - 1)`. Full T6 remains open.
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
#print axioms Erdos699.i_three_window_one_prime_pow_dvd_mul_sub_one
EOF
```

- [x] **Step 4: Commit the milestone**

```bash
git add docs/superpowers/plans/2026-07-05-erdos699-t6-row-one-full-power.md lean/Erdos699/Proved/Basic.lean notes/PROGRESS.md
git commit -m "feat: prove erdos699 t6 row one full power"
```
