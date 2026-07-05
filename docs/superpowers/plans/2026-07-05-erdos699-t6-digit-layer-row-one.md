# Erdos699 T6 Digit Layer Row One Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Bank the first T6 digit-layer facts for the `n - 1` window row: if `p^e ∣ n - 1`, then `n` has units digit `1` and zero base-`p` digits at levels `1..e-1`, and row-3 no-common hypotheses transfer those digit constraints to `j`.

**Architecture:** Add small arithmetic digit lemmas to `lean/Erdos699/Proved/Basic.lean`, then add row-3 no-common consequences using the existing Lucas bridge. Keep this as support infrastructure only; do not claim the full T6 divisibility theorem yet.

**Tech Stack:** Lean 4, Mathlib `Nat` digit lemmas, existing `Erdos699.Proved.Basic`, exact pytest criterion tests.

---

### Task 1: Red WIP API Check

**Files:**
- Create: `lean/Erdos699/WIP/T6DigitLayerRowOneTest.lean`

- [x] **Step 1: Write the failing API check**

```lean
import Erdos699.Proved.Basic

#check Erdos699.digit_zero_eq_one_of_pow_dvd_sub_one
#check Erdos699.digit_eq_zero_of_pow_dvd_sub_one
#check Erdos699.i_three_window_one_dominated_of_prime_pow_dvd_sub_one
#check Erdos699.i_three_window_one_units_digit_le_one_of_prime_pow_dvd_sub_one
#check Erdos699.i_three_window_one_high_digit_zero_of_prime_pow_dvd_sub_one
```

- [x] **Step 2: Run Lean and confirm expected failure**

```bash
lake env lean lean/Erdos699/WIP/T6DigitLayerRowOneTest.lean
```

Expected: unknown constants for the five new theorem names.

### Task 2: Add Arithmetic Digit Lemmas

**Files:**
- Modify: `lean/Erdos699/Proved/Basic.lean`

- [x] **Step 1: Add `prime_dvd_of_pow_dvd`**

Insert near the digit/product helper lemmas:

```lean
theorem prime_dvd_of_pow_dvd {p e m : ℕ} (he : 0 < e) (h : p ^ e ∣ m) :
    p ∣ m := by
  rcases h with ⟨a, ha⟩
  rcases Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt he) with ⟨c, hc⟩
  refine ⟨p ^ c * a, ?_⟩
  rw [ha, hc, pow_succ']
  omega
```

- [x] **Step 2: Add the units digit lemma**

```lean
theorem digit_zero_eq_one_of_pow_dvd_sub_one {n p e : ℕ}
    (hp : p.Prime) (hn_pos : 0 < n) (he_pos : 0 < e) (hpdvd : p ^ e ∣ n - 1) :
    digit n p 0 = 1 := by
  rcases hpdvd with ⟨a, ha⟩
  have hn_eq : n = p ^ e * a + 1 := by omega
  have hp_dvd_pow : p ∣ p ^ e := prime_dvd_of_pow_dvd he_pos dvd_rfl
  have hp_dvd_left : p ∣ p ^ e * a := dvd_mul_of_dvd_left hp_dvd_pow a
  have hmod_left : p ^ e * a % p = 0 := Nat.dvd_iff_mod_eq_zero.mp hp_dvd_left
  rw [digit, hn_eq]
  simp [Nat.add_mod, hmod_left, Nat.mod_eq_of_lt hp.one_lt]
```

- [x] **Step 3: Add the high digit zero lemma**

```lean
theorem digit_eq_zero_of_pow_dvd_sub_one {n p e r : ℕ}
    (hp : p.Prime) (hn_pos : 0 < n) (hr_pos : 1 ≤ r) (hr_lt : r < e)
    (hpdvd : p ^ e ∣ n - 1) :
    digit n p r = 0 := by
  rcases hpdvd with ⟨a, ha⟩
  have hn_eq : n = p ^ e * a + 1 := by omega
  have hre : r ≤ e := Nat.le_of_lt hr_lt
  have hpow_split : p ^ e = p ^ r * p ^ (e - r) := by
    rw [← pow_add, Nat.add_sub_of_le hre]
  have hdiv :
      (p ^ e * a + 1) / p ^ r = p ^ (e - r) * a := by
    rw [hpow_split]
    have hpow_pos : 0 < p ^ r := pow_pos hp.pos r
    have hrem_lt : 1 < p ^ r := Nat.one_lt_pow (by omega : r ≠ 0) hp.one_lt
    rw [mul_assoc]
    have hbase : (p ^ r * (p ^ (e - r) * a) + 1) / p ^ r = p ^ (e - r) * a := by
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

### Task 3: Add Row-3 No-Common Digit-Layer Consequences

**Files:**
- Modify: `lean/Erdos699/Proved/Basic.lean`

- [x] **Step 1: Add the domination transfer theorem**

```lean
theorem i_three_window_one_dominated_of_prime_pow_dvd_sub_one {n j p e : ℕ}
    (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor n 3 j q)
    (hp : p.Prime) (hp5 : 5 ≤ p) (hn : 1 < n) (he_pos : 0 < e)
    (hpdvd : p ^ e ∣ n - 1) :
    dominated j n p := by
  have hp_dvd : p ∣ n - 1 := prime_dvd_of_pow_dvd he_pos hpdvd
  have hchoose3 : p ∣ Nat.choose n 3 := by
    apply prime_dvd_choose_of_not_dominated hp
    intro hdom
    have hdigits := (dominated_iff_forall_digits hp.two_le).mp hdom 0
    have hn_mod : n % p = 1 :=
      digit_zero_eq_one_of_pow_dvd_sub_one hp (by omega : 0 < n) he_pos hpdvd
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

- [x] **Step 2: Add the units digit bound for `j`**

```lean
theorem i_three_window_one_units_digit_le_one_of_prime_pow_dvd_sub_one {n j p e : ℕ}
    (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor n 3 j q)
    (hp : p.Prime) (hp5 : 5 ≤ p) (hn : 1 < n) (he_pos : 0 < e)
    (hpdvd : p ^ e ∣ n - 1) :
    digit j p 0 ≤ 1 := by
  have hdom : dominated j n p :=
    i_three_window_one_dominated_of_prime_pow_dvd_sub_one hnone hp hp5 hn he_pos hpdvd
  have hdigitsj := (dominated_iff_forall_digits hp.two_le).mp hdom 0
  have hn_digit : digit n p 0 = 1 :=
    digit_zero_eq_one_of_pow_dvd_sub_one hp (by omega : 0 < n) he_pos hpdvd
  simpa [hn_digit] using hdigitsj
```

- [x] **Step 3: Add the high-digit zero transfer for `j`**

```lean
theorem i_three_window_one_high_digit_zero_of_prime_pow_dvd_sub_one {n j p e r : ℕ}
    (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor n 3 j q)
    (hp : p.Prime) (hp5 : 5 ≤ p) (hn : 1 < n)
    (hr_pos : 1 ≤ r) (hr_lt : r < e) (hpdvd : p ^ e ∣ n - 1) :
    digit j p r = 0 := by
  have hdom : dominated j n p :=
    i_three_window_one_dominated_of_prime_pow_dvd_sub_one hnone hp hp5 hn
      (by omega : 0 < e) hpdvd
  have hdigitsj := (dominated_iff_forall_digits hp.two_le).mp hdom r
  have hn_digit : digit n p r = 0 :=
    digit_eq_zero_of_pow_dvd_sub_one hp (by omega : 0 < n) hr_pos hr_lt hpdvd
  have hle : digit j p r ≤ 0 := by simpa [hn_digit] using hdigitsj
  omega
```

### Task 4: Verification, Cleanup, and Commit

**Files:**
- Modify: `notes/PROGRESS.md`
- Delete: `lean/Erdos699/WIP/T6DigitLayerRowOneTest.lean`
- Delete: `lean/Erdos699/WIP/T6DigitZeroScratch.lean`

- [x] **Step 1: Run the WIP API check green and remove WIP files**

```bash
lake build Erdos699.Proved.Basic
lake env lean lean/Erdos699/WIP/T6DigitLayerRowOneTest.lean
```

Expected: Lean prints all five theorem signatures. Then delete both WIP files.

- [x] **Step 2: Add the `[R]` progress entry**

```md
- [R] Proved first T6 digit-layer support for the `n - 1` row:
  `Erdos699.digit_zero_eq_one_of_pow_dvd_sub_one`,
  `Erdos699.digit_eq_zero_of_pow_dvd_sub_one`, and row-3 transfer lemmas
  forcing `j`'s units digit to be at most `1` and levels `1..e-1` to vanish
  when `p^e ∣ n - 1`. Full T6 remains open.
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
#print axioms Erdos699.i_three_window_one_high_digit_zero_of_prime_pow_dvd_sub_one
#print axioms Erdos699.i_three_window_one_units_digit_le_one_of_prime_pow_dvd_sub_one
EOF
```

- [x] **Step 4: Commit the milestone**

```bash
git add docs/superpowers/plans/2026-07-05-erdos699-t6-digit-layer-row-one.md lean/Erdos699/Proved/Basic.lean notes/PROGRESS.md
git commit -m "feat: prove erdos699 t6 row one digit layer"
```
