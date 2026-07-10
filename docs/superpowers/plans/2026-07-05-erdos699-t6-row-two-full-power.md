# Erdos699 T6 Row Two Full Power Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Prove the analogous T6 full-power forcing theorem for the `n - 2` row: if `p^e ∣ n - 2`, then the row-3 no-common-prime hypothesis forces `p^e ∣ j * (j - 1) * (j - 2)`.

**Architecture:** Mirror the already verified `n - 1` row machinery. Add `n - 2` digit-layer lemmas, row-3 Lucas transfer lemmas, a generic unit-digit-`≤ 2` full-power product lemma, and the final row-two full-power theorem.

**Tech Stack:** Lean 4, Mathlib `Nat`, existing `Erdos699.Proved.Basic`, exact pytest criterion tests.

---

### Task 1: Red WIP API Check

**Files:**
- Create: `lean/Erdos699/WIP/T6RowTwoFullPowerTest.lean`

- [x] **Step 1: Write the failing API check**

```lean
import Erdos699.Proved.Basic

#check Erdos699.digit_zero_eq_two_of_pow_dvd_sub_two
#check Erdos699.digit_eq_zero_of_pow_dvd_sub_two
#check Erdos699.i_three_window_two_units_digit_le_two_of_prime_pow_dvd_sub_two
#check Erdos699.i_three_window_two_high_digit_zero_of_prime_pow_dvd_sub_two
#check Erdos699.pow_dvd_sub_two_of_unit_digit_two_high_zero
#check Erdos699.pow_dvd_mul_sub_one_sub_two_of_digit_le_two_high_zero
#check Erdos699.i_three_window_two_prime_pow_dvd_mul_sub_one_sub_two
```

- [x] **Step 2: Run Lean and confirm expected failure**

```bash
lake env lean lean/Erdos699/WIP/T6RowTwoFullPowerTest.lean
```

Expected: unknown constants for the seven new theorem names.

### Task 2: Add `n - 2` Digit-Layer Lemmas

**Files:**
- Modify: `lean/Erdos699/Proved/Basic.lean`

- [x] **Step 1: Add `digit_zero_eq_two_of_pow_dvd_sub_two`**

```lean
theorem digit_zero_eq_two_of_pow_dvd_sub_two {n p e : ℕ}
    (hp5 : 5 ≤ p) (h2n : 2 ≤ n) (he_pos : 0 < e) (hpdvd : p ^ e ∣ n - 2) :
    digit n p 0 = 2 := by
  rcases hpdvd with ⟨a, ha⟩
  have hn_eq : n = p ^ e * a + 2 := by omega
  have hp_dvd_pow : p ∣ p ^ e := prime_dvd_of_pow_dvd he_pos dvd_rfl
  have hp_dvd_left : p ∣ p ^ e * a := dvd_mul_of_dvd_left hp_dvd_pow a
  have hmod_left : p ^ e * a % p = 0 := Nat.dvd_iff_mod_eq_zero.mp hp_dvd_left
  rw [digit, hn_eq]
  simp [Nat.add_mod, hmod_left, Nat.mod_eq_of_lt (by omega : 2 < p)]
```

- [x] **Step 2: Add `digit_eq_zero_of_pow_dvd_sub_two`**

```lean
theorem digit_eq_zero_of_pow_dvd_sub_two {n p e r : ℕ}
    (hp5 : 5 ≤ p) (h2n : 2 ≤ n) (hr_pos : 1 ≤ r) (hr_lt : r < e)
    (hpdvd : p ^ e ∣ n - 2) :
    digit n p r = 0 := by
  rcases hpdvd with ⟨a, ha⟩
  have hn_eq : n = p ^ e * a + 2 := by omega
  have hre : r ≤ e := Nat.le_of_lt hr_lt
  have hpow_split : p ^ e = p ^ r * p ^ (e - r) := by
    rw [← pow_add, Nat.add_sub_of_le hre]
  have hdiv :
      (p ^ e * a + 2) / p ^ r = p ^ (e - r) * a := by
    rw [hpow_split]
    have hpow_pos : 0 < p ^ r := pow_pos (by omega : 0 < p) r
    have hp_le_pow : p ≤ p ^ r :=
      Nat.le_self_pow (by omega : r ≠ 0) p
    have hrem_lt : 2 < p ^ r := by omega
    rw [mul_assoc]
    have hbase : (p ^ r * (p ^ (e - r) * a) + 2) / p ^ r =
        p ^ (e - r) * a := by
      rw [Nat.add_comm]
      rw [Nat.add_mul_div_left _ _ hpow_pos, Nat.div_eq_of_lt hrem_lt]
      simp
    exact hbase
  have hfactor : p ∣ p ^ (e - r) * a := by
    have hexp_pos : 0 < e - r := Nat.sub_pos_of_lt hr_lt
    rcases Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hexp_pos) with ⟨c, hc⟩
    rw [hc, pow_succ']
    exact dvd_mul_of_dvd_left (dvd_mul_right p (p ^ c)) a
  rw [digit, hn_eq, hdiv]
  exact Nat.dvd_iff_mod_eq_zero.mp hfactor
```

### Task 3: Add Row-Two Lucas Transfer

**Files:**
- Modify: `lean/Erdos699/Proved/Basic.lean`

- [x] **Step 1: Add domination transfer**

```lean
theorem i_three_window_two_dominated_of_prime_pow_dvd_sub_two {n j p e : ℕ}
    (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor n 3 j q)
    (hp : p.Prime) (hp5 : 5 ≤ p) (hn : 2 < n) (he_pos : 0 < e)
    (hpdvd : p ^ e ∣ n - 2) :
    dominated j n p := by
  have hchoose3 : p ∣ Nat.choose n 3 := by
    apply prime_dvd_choose_of_not_dominated hp
    intro hdom
    have hdigits := (dominated_iff_forall_digits hp.two_le).mp hdom 0
    have hn_mod : n % p = 2 := by
      simpa [digit] using
        digit_zero_eq_two_of_pow_dvd_sub_two hp5 (by omega : 2 ≤ n) he_pos hpdvd
    have h3mod : 3 % p = 3 := Nat.mod_eq_of_lt (by omega : 3 < p)
    simp [digit, hn_mod, h3mod] at hdigits
  have hnot_choose_j : ¬ p ∣ Nat.choose n j := by
    intro hpj
    exact hnone p ⟨hp, by omega, hchoose3, hpj⟩
  have hnonzero : Nat.choose n j % p ≠ 0 := by
    intro hzero
    exact hnot_choose_j (Nat.dvd_iff_mod_eq_zero.mpr hzero)
  exact (lucas_nonzero_mod_prime_iff_dominated hp).mp hnonzero
```

- [x] **Step 2: Add units and high-digit transfers**

```lean
theorem i_three_window_two_units_digit_le_two_of_prime_pow_dvd_sub_two {n j p e : ℕ}
    (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor n 3 j q)
    (hp : p.Prime) (hp5 : 5 ≤ p) (hn : 2 < n) (he_pos : 0 < e)
    (hpdvd : p ^ e ∣ n - 2) :
    digit j p 0 ≤ 2 := by
  have hdom : dominated j n p :=
    i_three_window_two_dominated_of_prime_pow_dvd_sub_two
      hnone hp hp5 hn he_pos hpdvd
  have hdigitsj := (dominated_iff_forall_digits hp.two_le).mp hdom 0
  have hn_digit : digit n p 0 = 2 :=
    digit_zero_eq_two_of_pow_dvd_sub_two hp5 (by omega : 2 ≤ n) he_pos hpdvd
  simpa [hn_digit] using hdigitsj

theorem i_three_window_two_high_digit_zero_of_prime_pow_dvd_sub_two {n j p e r : ℕ}
    (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor n 3 j q)
    (hp : p.Prime) (hp5 : 5 ≤ p) (hn : 2 < n)
    (hr_pos : 1 ≤ r) (hr_lt : r < e) (hpdvd : p ^ e ∣ n - 2) :
    digit j p r = 0 := by
  have hdom : dominated j n p :=
    i_three_window_two_dominated_of_prime_pow_dvd_sub_two hnone hp hp5 hn
      (by omega : 0 < e) hpdvd
  have hdigitsj := (dominated_iff_forall_digits hp.two_le).mp hdom r
  have hn_digit : digit n p r = 0 :=
    digit_eq_zero_of_pow_dvd_sub_two hp5 (by omega : 2 ≤ n) hr_pos hr_lt hpdvd
  have hle : digit j p r ≤ 0 := by simpa [hn_digit] using hdigitsj
  omega
```

### Task 4: Add Triple-Product Full-Power Forcing

**Files:**
- Modify: `lean/Erdos699/Proved/Basic.lean`

- [x] **Step 1: Add generic `j - 2` full-power lemma**

```lean
theorem pow_dvd_sub_two_of_unit_digit_two_high_zero {j p e : ℕ}
    (hp5 : 5 ≤ p) (hunit : digit j p 0 = 2)
    (hzero : ∀ r : ℕ, 1 ≤ r → r < e → digit j p r = 0) :
    p ^ e ∣ j - 2 := by
  induction e with
  | zero =>
      simp
  | succ e ih =>
      by_cases he0 : e = 0
      · subst e
        have hjmod : j % p = 2 := by
          simpa [digit] using hunit
        refine ⟨j / p, ?_⟩
        have hj_eq : j = p * (j / p) + 2 := by
          have h := Nat.div_add_mod j p
          rw [hjmod] at h
          omega
        have htarget : j - 2 = p * (j / p) := by omega
        simpa using htarget
      · have he_pos : 0 < e := Nat.pos_of_ne_zero he0
        have hlow : p ^ e ∣ j - 2 :=
          ih fun r hrpos hrlt => hzero r hrpos (Nat.lt_trans hrlt (Nat.lt_succ_self e))
        rcases hlow with ⟨a, ha⟩
        have hj_ge_two : 2 ≤ j := by
          by_contra hj_not
          have hj_lt : j < 2 := Nat.lt_of_not_ge hj_not
          have hj_cases : j = 0 ∨ j = 1 := by omega
          rcases hj_cases with hj0 | hj1
          · have hunit0 : digit j p 0 = 0 := by simp [digit, hj0]
            omega
          · have hunit1 : digit j p 0 = 1 := by
              simp [digit, hj1, Nat.mod_eq_of_lt (by omega : 1 < p)]
            omega
        have hj_eq : j = p ^ e * a + 2 := by omega
        have hpow_pos : 0 < p ^ e := pow_pos (by omega : 0 < p) e
        have hp_le_pow : p ≤ p ^ e :=
          Nat.le_self_pow (Nat.ne_of_gt he_pos) p
        have hrem_lt : 2 < p ^ e := by omega
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

- [x] **Step 2: Add generic triple-product lemma and row theorem**

```lean
theorem pow_dvd_mul_sub_one_sub_two_of_digit_le_two_high_zero {j p e : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hunit_le : digit j p 0 ≤ 2)
    (hzero : ∀ r : ℕ, 1 ≤ r → r < e → digit j p r = 0) :
    p ^ e ∣ j * (j - 1) * (j - 2) := by
  by_cases he0 : e = 0
  · subst e
    simp
  · have hunit_cases : digit j p 0 = 0 ∨ digit j p 0 = 1 ∨ digit j p 0 = 2 := by omega
    rcases hunit_cases with hunit0 | hunit1 | hunit2
    · have hall_zero : ∀ r : ℕ, r < e → digit j p r = 0 := by
        intro r hr
        by_cases hr0 : r = 0
        · simpa [hr0] using hunit0
        · exact hzero r (Nat.succ_le_of_lt (Nat.pos_of_ne_zero hr0)) hr
      have hpow : p ^ e ∣ j := pow_dvd_of_forall_digit_eq_zero hp.pos hall_zero
      exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left hpow (j - 1)) (j - 2)
    · have hpow : p ^ e ∣ j - 1 :=
        pow_dvd_sub_one_of_unit_digit_one_high_zero hp hunit1 hzero
      have hprod : p ^ e ∣ j * (j - 1) := dvd_mul_of_dvd_right hpow j
      exact dvd_mul_of_dvd_left hprod (j - 2)
    · have hpow : p ^ e ∣ j - 2 :=
        pow_dvd_sub_two_of_unit_digit_two_high_zero hp5 hunit2 hzero
      exact dvd_mul_of_dvd_right hpow (j * (j - 1))

theorem i_three_window_two_prime_pow_dvd_mul_sub_one_sub_two {n j p e : ℕ}
    (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor n 3 j q)
    (hp : p.Prime) (hp5 : 5 ≤ p) (hn : 2 < n) (hpdvd : p ^ e ∣ n - 2) :
    p ^ e ∣ j * (j - 1) * (j - 2) := by
  by_cases he0 : e = 0
  · subst e
    simp
  have hunit_le : digit j p 0 ≤ 2 := by
    exact i_three_window_two_units_digit_le_two_of_prime_pow_dvd_sub_two
      hnone hp hp5 hn (Nat.pos_of_ne_zero he0) hpdvd
  have hzero : ∀ r : ℕ, 1 ≤ r → r < e → digit j p r = 0 := by
    intro r hrpos hrlt
    exact i_three_window_two_high_digit_zero_of_prime_pow_dvd_sub_two
      hnone hp hp5 hn hrpos hrlt hpdvd
  exact pow_dvd_mul_sub_one_sub_two_of_digit_le_two_high_zero hp hp5 hunit_le hzero
```

### Task 5: Verification, Cleanup, and Commit

**Files:**
- Modify: `notes/PROGRESS.md`
- Delete: `lean/Erdos699/WIP/T6RowTwoFullPowerTest.lean`
- Delete: `lean/Erdos699/WIP/T6RowTwoFullPowerScratch.lean`

- [x] **Step 1: Run WIP API check green and remove WIP files**

```bash
lake build Erdos699.Proved.Basic
lake env lean lean/Erdos699/WIP/T6RowTwoFullPowerTest.lean
```

Expected: Lean prints all seven theorem signatures. Then delete both WIP files.

- [x] **Step 2: Add the `[R]` progress entry**

```md
- [R] Proved T6 full-power forcing for the `n - 2` row:
  `Erdos699.i_three_window_two_prime_pow_dvd_mul_sub_one_sub_two` shows that
  under row-3 no-common-prime hypotheses, every prime power `p^e ∣ n - 2`
  with `p ≥ 5` divides `j * (j - 1) * (j - 2)`. Full T6 remains open.
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
#print axioms Erdos699.i_three_window_two_prime_pow_dvd_mul_sub_one_sub_two
EOF
```

- [x] **Step 4: Commit the milestone**

```bash
git add docs/superpowers/plans/2026-07-05-erdos699-t6-row-two-full-power.md lean/Erdos699/Proved/Basic.lean notes/PROGRESS.md
git commit -m "feat: prove erdos699 t6 row two full power"
```
