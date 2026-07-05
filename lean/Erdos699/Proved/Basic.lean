/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/

import Mathlib.Data.Nat.Choose.Factorization
import Mathlib.Data.Nat.Choose.Lucas
import Mathlib.Data.Nat.Digits.Lemmas

namespace Erdos699

/-- The base-`p` digit at level `r`, with level zero the units digit. -/
def digit (k p r : ℕ) : ℕ :=
  k / p ^ r % p

/-- Digitwise domination of `k` by `n` in base `p`, checked on a finite safe range. -/
def dominated (k n p : ℕ) : Prop :=
  (Finset.range (max k n + 1)).filter (fun r => digit n p r < digit k p r) = ∅

instance (k n p : ℕ) : Decidable (dominated k n p) :=
  inferInstanceAs
    (Decidable ((Finset.range (max k n + 1)).filter
      (fun r => digit n p r < digit k p r) = ∅))

theorem dominated_iff_forall_mem_range (k n p : ℕ) :
    dominated k n p ↔
      ∀ r ∈ Finset.range (max k n + 1), digit k p r ≤ digit n p r := by
  classical
  unfold dominated
  rw [Finset.filter_eq_empty_iff]
  constructor
  · intro h r hr
    exact Nat.not_lt.mp (h hr)
  · intro h r hr
    exact Nat.not_lt.mpr (h r hr)

theorem dominated_iff_forall_digits {k n p : ℕ} (hp : 2 ≤ p) :
    dominated k n p ↔ ∀ r : ℕ, digit k p r ≤ digit n p r := by
  classical
  constructor
  · intro h r
    by_cases hr : r ∈ Finset.range (max k n + 1)
    · exact (dominated_iff_forall_mem_range k n p).mp h r hr
    · have hle : max k n + 1 ≤ r := by
        exact Nat.le_of_not_gt (by simpa [Finset.mem_range] using hr)
      have hm_lt_r : max k n < r := Nat.lt_of_succ_le hle
      have hp_one : 1 < p := Nat.lt_of_lt_of_le one_lt_two hp
      have hr_lt_pow : r < p ^ r := Nat.lt_pow_self hp_one
      have hk_lt : k < p ^ r := (le_max_left k n).trans_lt (hm_lt_r.trans hr_lt_pow)
      have hn_lt : n < p ^ r := (le_max_right k n).trans_lt (hm_lt_r.trans hr_lt_pow)
      simp [digit, Nat.div_eq_of_lt hk_lt, Nat.div_eq_of_lt hn_lt]
  · intro h
    exact (dominated_iff_forall_mem_range k n p).mpr fun r _ => h r

theorem prime_not_dvd_small_choose_of_le {p a b : ℕ} (hp : p.Prime) (ha : a < p)
    (hb : b ≤ a) :
    ¬ p ∣ Nat.choose a b := by
  have hchoose_ne : Nat.choose a b ≠ 0 := Nat.choose_ne_zero hb
  intro hdiv
  have hfac_pos : 0 < (Nat.choose a b).factorization p :=
    hp.factorization_pos_of_dvd hchoose_ne hdiv
  have hfac_zero : (Nat.choose a b).factorization p = 0 :=
    Nat.factorization_choose_eq_zero_of_lt ha
  omega

theorem prime_not_dvd_finset_prod {α : Type*} {s : Finset α} {f : α → ℕ} {p : ℕ}
    (hp : p.Prime) (h : ∀ a ∈ s, ¬ p ∣ f a) :
    ¬ p ∣ s.prod f := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simpa using hp.not_dvd_one
  | insert a s ha ih =>
      intro hdiv
      rw [Finset.prod_insert ha] at hdiv
      rcases hp.dvd_mul.mp hdiv with hpa | hps
      · exact h a (Finset.mem_insert_self a s) hpa
      · exact ih (fun x hx => h x (Finset.mem_insert_of_mem hx)) hps

theorem lucas_nonzero_mod_prime_iff_dominated {n k p : ℕ} (hp : p.Prime) :
    Nat.choose n k % p ≠ 0 ↔ dominated k n p := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  let a := max k n + 1
  have hp_one : 1 < p := hp.one_lt
  have hn_bound : n < p ^ a := by
    have hn_lt_a : n < a := (le_max_right k n).trans_lt (Nat.lt_succ_self _)
    exact hn_lt_a.trans (Nat.lt_pow_self hp_one)
  have hk_bound : k < p ^ a := by
    have hk_lt_a : k < a := (le_max_left k n).trans_lt (Nat.lt_succ_self _)
    exact hk_lt_a.trans (Nat.lt_pow_self hp_one)
  have hlucas :
      Nat.choose n k ≡
        ∏ i ∈ Finset.range a, Nat.choose (n / p ^ i % p) (k / p ^ i % p) [MOD p] :=
    Choose.lucas_theorem_nat (n := n) (k := k) (p := p) (a := a) hn_bound hk_bound
  constructor
  · intro hnonzero
    by_contra hdom
    rw [dominated_iff_forall_mem_range k n p] at hdom
    push Not at hdom
    obtain ⟨r, hr, hbad⟩ := hdom
    have hfactor_zero : Nat.choose (n / p ^ r % p) (k / p ^ r % p) = 0 :=
      Nat.choose_eq_zero_of_lt hbad
    have hprod_zero :
        (∏ i ∈ Finset.range a, Nat.choose (n / p ^ i % p) (k / p ^ i % p)) = 0 :=
      Finset.prod_eq_zero hr hfactor_zero
    rw [Nat.ModEq] at hlucas
    exact hnonzero (by simpa [hprod_zero] using hlucas)
  · intro hdom
    have hprod_not_dvd :
        ¬ p ∣ (∏ i ∈ Finset.range a, Nat.choose (n / p ^ i % p) (k / p ^ i % p)) := by
      refine prime_not_dvd_finset_prod hp ?_
      intro r hr
      apply prime_not_dvd_small_choose_of_le hp
      · exact Nat.mod_lt _ hp.pos
      · exact (dominated_iff_forall_mem_range k n p).mp hdom r hr
    rw [Nat.ModEq] at hlucas
    intro hzero
    have hprod_zero :
        (∏ i ∈ Finset.range a, Nat.choose (n / p ^ i % p) (k / p ^ i % p)) % p = 0 := by
      simpa [hlucas] using hzero
    exact hprod_not_dvd (Nat.dvd_iff_mod_eq_zero.mpr hprod_zero)

theorem prime_dvd_choose_of_not_dominated {n k p : ℕ} (hp : p.Prime)
    (hnd : ¬ dominated k n p) :
    p ∣ Nat.choose n k := by
  by_contra hnot_dvd
  have hnonzero : Nat.choose n k % p ≠ 0 := by
    intro hzero
    exact hnot_dvd (Nat.dvd_iff_mod_eq_zero.mpr hzero)
  exact hnd ((lucas_nonzero_mod_prime_iff_dominated hp).mp hnonzero)

theorem not_dominated_of_units_digit_lt {n k p : ℕ} (hp : p.Prime)
    (hpn : p ≤ n) (hn2p : n < 2 * p) (hlow : n - p < k) (hhigh : k < p) :
    ¬ dominated k n p := by
  intro hdom
  have hdigits := (dominated_iff_forall_digits hp.two_le).mp hdom 0
  have hn_mod : n % p = n - p := by
    have hsub_lt : n - p < p := by
      rw [Nat.sub_lt_iff_lt_add hpn]
      simpa [two_mul, Nat.add_comm] using hn2p
    rw [Nat.mod_eq_sub_mod hpn]
    exact Nat.mod_eq_of_lt hsub_lt
  have hk_mod : k % p = k := Nat.mod_eq_of_lt hhigh
  have hle : k ≤ n - p := by
    simpa [digit, hn_mod, hk_mod] using hdigits
  omega

theorem prime_dvd_choose_of_units_digit_lt {n k p : ℕ} (hp : p.Prime)
    (hpn : p ≤ n) (hn2p : n < 2 * p) (hlow : n - p < k) (hhigh : k < p) :
    p ∣ Nat.choose n k :=
  prime_dvd_choose_of_not_dominated hp
    (not_dominated_of_units_digit_lt hp hpn hn2p hlow hhigh)

/-- A prime `p` that is large enough for row `i` and divides both binomial coefficients. -/
def commonPrimeDivisor (n i j p : ℕ) : Prop :=
  p.Prime ∧ i ≤ p ∧ p ∣ Nat.choose n i ∧ p ∣ Nat.choose n j

theorem commonPrimeDivisor_of_prime_in_top_interval {n i j p : ℕ}
    (hp : p.Prime) (hij : i < j) (hjn : 2 * j ≤ n) (hleft : n - i < p)
    (hright : p ≤ n) :
    commonPrimeDivisor n i j p := by
  have hi_lt_p : i < p := by omega
  have hj_lt_p : j < p := by omega
  have hn_lt_2p : n < 2 * p := by omega
  have hlow_i : n - p < i := by omega
  have hlow_j : n - p < j := by omega
  exact
    ⟨hp, hi_lt_p.le,
      prime_dvd_choose_of_units_digit_lt hp hright hn_lt_2p hlow_i hi_lt_p,
      prime_dvd_choose_of_units_digit_lt hp hright hn_lt_2p hlow_j hj_lt_p⟩

/-- The numerator window `n(n-1)...(n-i+1)` for `C(n,i)`. -/
def fallingWindowProduct (n i : ℕ) : ℕ :=
  ∏ r ∈ Finset.range i, (n - r)

theorem t3_top_interval_prime_free_of_no_common {n i j p : ℕ}
    (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor n i j q)
    (hij : i < j) (hjn : 2 * j ≤ n) (hp : p.Prime) :
    ¬ (n - i < p ∧ p ≤ n) := by
  intro hinterval
  exact hnone p
    (commonPrimeDivisor_of_prime_in_top_interval hp hij hjn hinterval.1 hinterval.2)

theorem t3_no_large_prime_dvd_fallingWindowProduct_of_no_common {n i j p : ℕ}
    (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor n i j q)
    (hij : i < j) (hjn : 2 * j ≤ n) (hp : p.Prime) (hp_large : n < 2 * p) :
    ¬ p ∣ fallingWindowProduct n i := by
  intro hprod
  have hexists : ∃ r ∈ Finset.range i, p ∣ n - r := by
    by_contra hnone_factor
    rw [not_exists] at hnone_factor
    have hno_factor : ∀ r ∈ Finset.range i, ¬ p ∣ n - r := by
      intro r hr hdiv
      exact hnone_factor r ⟨hr, hdiv⟩
    exact (prime_not_dvd_finset_prod hp hno_factor) hprod
  obtain ⟨r, hr, hpdiv⟩ := hexists
  have hrlt : r < i := by simpa [Finset.mem_range] using hr
  have hrn : r < n := by omega
  have hfactor_ne_zero : n - r ≠ 0 := by omega
  have hfactor_lt : n - r < 2 * p := by omega
  have hfactor_eq : n - r = p := Nat.eq_of_dvd_of_lt_two_mul hfactor_ne_zero hpdiv hfactor_lt
  have hinterval : n - i < p ∧ p ≤ n := by
    constructor <;> omega
  exact (t3_top_interval_prime_free_of_no_common hnone hij hjn hp) hinterval

/-- A natural number that is exactly a power of two. -/
def twoPower (m : ℕ) : Prop :=
  ∃ a : ℕ, m = 2 ^ a

theorem twoPower_eq_one_of_odd {m : ℕ} (hm : twoPower m) (hodd : Odd m) :
    m = 1 := by
  rcases hm with ⟨a, rfl⟩
  by_cases ha : a = 0
  · simp [ha]
  · rcases Nat.exists_eq_succ_of_ne_zero ha with ⟨b, rfl⟩
    have heven : Even (2 ^ (b + 1)) := by
      rw [pow_succ]
      exact even_iff_two_dvd.mpr ⟨2 ^ b, by rw [mul_comm]⟩
    have hnot_odd : ¬ Odd (2 ^ (b + 1)) := Nat.not_odd_iff_even.mpr heven
    exact False.elim (hnot_odd hodd)

theorem eq_three_of_sub_one_sub_two_twoPowers {n : ℕ}
    (h1 : twoPower (n - 1)) (h2 : twoPower (n - 2)) :
    n = 3 := by
  rcases h2 with ⟨b, hb⟩
  by_cases hb0 : b = 0
  · have hn2 : n - 2 = 1 := by simpa [hb0] using hb
    omega
  · have heven_n2 : Even (n - 2) := by
      rcases Nat.exists_eq_succ_of_ne_zero hb0 with ⟨c, rfl⟩
      rw [hb, pow_succ]
      exact even_iff_two_dvd.mpr ⟨2 ^ c, by rw [mul_comm]⟩
    have hmod_n2 : (n - 2) % 2 = 0 := Nat.even_iff.mp heven_n2
    have hsucc : n - 1 = n - 2 + 1 := by
      have hpos : 0 < n - 2 := by
        rw [hb]
        exact pow_pos (by decide : 0 < 2) b
      omega
    have hmod_n1 : (n - 1) % 2 = 1 := by
      rw [hsucc, Nat.add_mod, hmod_n2]
    have hodd_n1 : Odd (n - 1) := Nat.odd_iff.mpr hmod_n1
    have hn1 : n - 1 = 1 := twoPower_eq_one_of_odd h1 hodd_n1
    have hpos : 0 < n - 2 := by
      rw [hb]
      exact pow_pos (by decide : 0 < 2) b
    omega

theorem i_three_window_one_digit_forcing {n j p : ℕ}
    (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor n 3 j q)
    (hp : p.Prime) (hp5 : 5 ≤ p) (hn : 1 < n) (hpdvd : p ∣ n - 1) :
    j % p ≤ 1 := by
  have hn_mod : n % p = 1 := by
    rcases hpdvd with ⟨a, ha⟩
    have hEq : n = p * a + 1 := by omega
    rw [hEq]
    simp [Nat.add_mod, Nat.mod_eq_of_lt hp.one_lt]
  have hchoose3 : p ∣ Nat.choose n 3 := by
    apply prime_dvd_choose_of_not_dominated hp
    intro hdom
    have hdigits := (dominated_iff_forall_digits hp.two_le).mp hdom 0
    have h3mod : 3 % p = 3 := Nat.mod_eq_of_lt (by omega)
    simp [digit, hn_mod, h3mod] at hdigits
  have hnot_choose_j : ¬ p ∣ Nat.choose n j := by
    intro hpj
    exact hnone p ⟨hp, by omega, hchoose3, hpj⟩
  have hnonzero : Nat.choose n j % p ≠ 0 := by
    intro hzero
    exact hnot_choose_j (Nat.dvd_iff_mod_eq_zero.mpr hzero)
  have hdomj : dominated j n p := (lucas_nonzero_mod_prime_iff_dominated hp).mp hnonzero
  have hdigitsj := (dominated_iff_forall_digits hp.two_le).mp hdomj 0
  simpa [digit, hn_mod] using hdigitsj

theorem i_three_window_two_digit_forcing {n j p : ℕ}
    (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor n 3 j q)
    (hp : p.Prime) (hp5 : 5 ≤ p) (hn : 2 < n) (hpdvd : p ∣ n - 2) :
    j % p ≤ 2 := by
  have hn_mod : n % p = 2 := by
    rcases hpdvd with ⟨a, ha⟩
    have hEq : n = p * a + 2 := by omega
    rw [hEq]
    simp [Nat.add_mod, Nat.mod_eq_of_lt (by omega : 2 < p)]
  have hchoose3 : p ∣ Nat.choose n 3 := by
    apply prime_dvd_choose_of_not_dominated hp
    intro hdom
    have hdigits := (dominated_iff_forall_digits hp.two_le).mp hdom 0
    have h3mod : 3 % p = 3 := Nat.mod_eq_of_lt (by omega)
    simp [digit, hn_mod, h3mod] at hdigits
  have hnot_choose_j : ¬ p ∣ Nat.choose n j := by
    intro hpj
    exact hnone p ⟨hp, by omega, hchoose3, hpj⟩
  have hnonzero : Nat.choose n j % p ≠ 0 := by
    intro hzero
    exact hnot_choose_j (Nat.dvd_iff_mod_eq_zero.mpr hzero)
  have hdomj : dominated j n p := (lucas_nonzero_mod_prime_iff_dominated hp).mp hnonzero
  have hdigitsj := (dominated_iff_forall_digits hp.two_le).mp hdomj 0
  simpa [digit, hn_mod] using hdigitsj

private theorem dvd_sub_of_mod_eq {j p r : ℕ} (hmod : j % p = r) : p ∣ j - r := by
  refine ⟨j / p, ?_⟩
  have h := Nat.div_add_mod j p
  rw [hmod] at h
  omega

theorem mod_eq_of_dvd_sub {j p r : ℕ} (hrj : r ≤ j) (hrp : r < p)
    (hpdvd : p ∣ j - r) :
    j % p = r := by
  rcases hpdvd with ⟨a, ha⟩
  have hEq : j = p * a + r := by omega
  rw [hEq]
  simp [Nat.add_mod, Nat.mod_eq_of_lt hrp]

theorem dvd_mul_sub_one_of_mod_le_one {j p : ℕ} (hmod : j % p ≤ 1) :
    p ∣ j * (j - 1) := by
  have hcase : j % p = 0 ∨ j % p = 1 := by omega
  rcases hcase with hzero | hone
  · have hj : p ∣ j := Nat.dvd_iff_mod_eq_zero.mpr hzero
    exact dvd_mul_of_dvd_left hj (j - 1)
  · have hj1 : p ∣ j - 1 := dvd_sub_of_mod_eq hone
    exact dvd_mul_of_dvd_right hj1 j

theorem dvd_mul_sub_one_sub_two_of_mod_le_two {j p : ℕ} (hmod : j % p ≤ 2) :
    p ∣ j * (j - 1) * (j - 2) := by
  have hcase : j % p = 0 ∨ j % p = 1 ∨ j % p = 2 := by omega
  rcases hcase with hzero | hone | htwo
  · have hj : p ∣ j := Nat.dvd_iff_mod_eq_zero.mpr hzero
    exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left hj (j - 1)) (j - 2)
  · have hj1 : p ∣ j - 1 := dvd_sub_of_mod_eq hone
    have hprod : p ∣ j * (j - 1) := dvd_mul_of_dvd_right hj1 j
    exact dvd_mul_of_dvd_left hprod (j - 2)
  · have hj2 : p ∣ j - 2 := dvd_sub_of_mod_eq htwo
    exact dvd_mul_of_dvd_right hj2 (j * (j - 1))

theorem i_three_window_one_product_forcing {n j p : ℕ}
    (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor n 3 j q)
    (hp : p.Prime) (hp5 : 5 ≤ p) (hn : 1 < n) (hpdvd : p ∣ n - 1) :
    p ∣ j * (j - 1) :=
  dvd_mul_sub_one_of_mod_le_one
    (i_three_window_one_digit_forcing hnone hp hp5 hn hpdvd)

theorem i_three_window_two_product_forcing {n j p : ℕ}
    (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor n 3 j q)
    (hp : p.Prime) (hp5 : 5 ≤ p) (hn : 2 < n) (hpdvd : p ∣ n - 2) :
    p ∣ j * (j - 1) * (j - 2) :=
  dvd_mul_sub_one_sub_two_of_mod_le_two
    (i_three_window_two_digit_forcing hnone hp hp5 hn hpdvd)

theorem three_mul_mod_eq_one_of_dvd_pred {j p : ℕ}
    (hp : p.Prime) (hj : 0 < j) (hpdvd : p ∣ 3 * j - 1) :
    (3 * j) % p = 1 := by
  rcases hpdvd with ⟨a, ha⟩
  have hEq : 3 * j = p * a + 1 := by omega
  rw [hEq]
  simp [Nat.add_mod, Nat.mod_eq_of_lt hp.one_lt]

theorem three_mul_mod_eq_two_of_dvd_sub_two {j p : ℕ}
    (hp5 : 5 ≤ p) (hj : 0 < j) (hpdvd : p ∣ 3 * j - 2) :
    (3 * j) % p = 2 := by
  rcases hpdvd with ⟨a, ha⟩
  have hEq : 3 * j = p * a + 2 := by omega
  rw [hEq]
  simp [Nat.add_mod, Nat.mod_eq_of_lt (by omega : 2 < p)]

theorem no_prime_ge_five_dvd_three_mul_sub_one_of_dvd_mul_sub_one {j p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hj : 0 < j) (hlin : p ∣ 3 * j - 1)
    (hprod : p ∣ j * (j - 1)) : False := by
  have hmodlin : (3 * j) % p = 1 := three_mul_mod_eq_one_of_dvd_pred hp hj hlin
  have h3mod : 3 % p = 3 := Nat.mod_eq_of_lt (by omega : 3 < p)
  rcases hp.dvd_mul.mp hprod with hjdvd | hj1dvd
  · have hjmod : j % p = 0 := Nat.dvd_iff_mod_eq_zero.mp hjdvd
    rw [Nat.mul_mod, h3mod, hjmod] at hmodlin
    norm_num at hmodlin
  · have hjmod : j % p = 1 := mod_eq_of_dvd_sub (by omega) (by omega) hj1dvd
    rw [Nat.mul_mod, h3mod, hjmod, Nat.mod_eq_of_lt (by omega : 3 < p)] at hmodlin
    omega

theorem no_prime_ge_five_dvd_three_mul_sub_two_of_dvd_triple {j p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hj : 2 ≤ j) (hlin : p ∣ 3 * j - 2)
    (hprod : p ∣ j * (j - 1) * (j - 2)) : False := by
  have hj_pos : 0 < j := by omega
  have hmodlin : (3 * j) % p = 2 := three_mul_mod_eq_two_of_dvd_sub_two hp5 hj_pos hlin
  have h3mod : 3 % p = 3 := Nat.mod_eq_of_lt (by omega : 3 < p)
  rcases hp.dvd_mul.mp hprod with hleft | hj2dvd
  · rcases hp.dvd_mul.mp hleft with hjdvd | hj1dvd
    · have hjmod : j % p = 0 := Nat.dvd_iff_mod_eq_zero.mp hjdvd
      rw [Nat.mul_mod, h3mod, hjmod] at hmodlin
      norm_num at hmodlin
    · have hjmod : j % p = 1 := mod_eq_of_dvd_sub (by omega) (by omega) hj1dvd
      rw [Nat.mul_mod, h3mod, hjmod, Nat.mod_eq_of_lt (by omega : 3 < p)] at hmodlin
      omega
  · have hjmod : j % p = 2 := mod_eq_of_dvd_sub hj (by omega) hj2dvd
    rw [Nat.mul_mod, h3mod, hjmod] at hmodlin
    by_cases hp_eq_five : p = 5
    · subst p
      norm_num at hmodlin
    · have hp_ne_six : p ≠ 6 := by
        intro hp6
        subst p
        exact (by decide : ¬ Nat.Prime 6) hp
      have h6lt : 6 < p := by omega
      rw [Nat.mod_eq_of_lt h6lt] at hmodlin
      omega

theorem no_prime_ge_five_dvd_sub_one_of_no_common_eq_three_mul {n j p : ℕ}
    (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor n 3 j q) (hn_eq : n = 3 * j)
    (hp : p.Prime) (hp5 : 5 ≤ p) (hj : 0 < j) (hpdvd : p ∣ n - 1) :
    False := by
  have hn_gt : 1 < n := by omega
  have hprod : p ∣ j * (j - 1) :=
    i_three_window_one_product_forcing (n := n) (j := j) (p := p)
      hnone hp hp5 hn_gt hpdvd
  have hlin : p ∣ 3 * j - 1 := by
    simpa [hn_eq] using hpdvd
  exact no_prime_ge_five_dvd_three_mul_sub_one_of_dvd_mul_sub_one hp hp5 hj hlin hprod

theorem no_prime_ge_five_dvd_sub_two_of_no_common_eq_three_mul {n j p : ℕ}
    (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor n 3 j q) (hn_eq : n = 3 * j)
    (hp : p.Prime) (hp5 : 5 ≤ p) (hj : 2 ≤ j) (hpdvd : p ∣ n - 2) :
    False := by
  have hn_gt : 2 < n := by omega
  have hprod : p ∣ j * (j - 1) * (j - 2) :=
    i_three_window_two_product_forcing (n := n) (j := j) (p := p)
      hnone hp hp5 hn_gt hpdvd
  have hlin : p ∣ 3 * j - 2 := by
    simpa [hn_eq] using hpdvd
  exact no_prime_ge_five_dvd_three_mul_sub_two_of_dvd_triple hp hp5 hj hlin hprod

theorem twoPower_of_unique_prime_dvd_two {m : ℕ} (hm0 : m ≠ 0)
    (huniq : ∀ {p : ℕ}, p.Prime → p ∣ m → p = 2) :
    twoPower m := by
  exact ⟨m.primeFactorsList.length, Nat.eq_prime_pow_of_unique_prime_dvd hm0 huniq⟩

theorem twoPower_of_no_prime_ge_five_and_not_three {m : ℕ} (hm0 : m ≠ 0)
    (hno5 : ∀ p : ℕ, p.Prime → 5 ≤ p → ¬ p ∣ m) (hnot3 : ¬ 3 ∣ m) :
    twoPower m := by
  apply twoPower_of_unique_prime_dvd_two hm0
  intro p hp hpm
  by_cases hp2 : p = 2
  · exact hp2
  by_cases hp3 : p = 3
  · exact False.elim (hnot3 (by simpa [hp3] using hpm))
  have hp4 : p ≠ 4 := by
    intro hp_eq
    subst p
    exact (by decide : ¬ Nat.Prime 4) hp
  have hp5 : 5 ≤ p := by
    have hp2le : 2 ≤ p := hp.two_le
    omega
  exact False.elim ((hno5 p hp hp5) hpm)

theorem not_three_dvd_sub_one_of_eq_three_mul {n j : ℕ} (hn_eq : n = 3 * j)
    (hj : 0 < j) :
    ¬ 3 ∣ n - 1 := by
  intro h
  rcases h with ⟨a, ha⟩
  omega

theorem not_three_dvd_sub_two_of_eq_three_mul {n j : ℕ} (hn_eq : n = 3 * j)
    (hj : 0 < j) :
    ¬ 3 ∣ n - 2 := by
  intro h
  rcases h with ⟨a, ha⟩
  omega

theorem twoPower_sub_one_of_no_common_eq_three_mul {n j : ℕ}
    (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor n 3 j q) (hn_eq : n = 3 * j)
    (hj : 0 < j) :
    twoPower (n - 1) := by
  apply twoPower_of_no_prime_ge_five_and_not_three
  · omega
  · intro p hp hp5 hpdvd
    exact no_prime_ge_five_dvd_sub_one_of_no_common_eq_three_mul hnone hn_eq hp hp5 hj hpdvd
  · exact not_three_dvd_sub_one_of_eq_three_mul hn_eq hj

theorem twoPower_sub_two_of_no_common_eq_three_mul {n j : ℕ}
    (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor n 3 j q) (hn_eq : n = 3 * j)
    (hj : 2 ≤ j) :
    twoPower (n - 2) := by
  apply twoPower_of_no_prime_ge_five_and_not_three
  · omega
  · intro p hp hp5 hpdvd
    exact no_prime_ge_five_dvd_sub_two_of_no_common_eq_three_mul hnone hn_eq hp hp5 hj hpdvd
  · exact not_three_dvd_sub_two_of_eq_three_mul hn_eq (by omega)

theorem eq_three_of_no_common_eq_three_mul {n j : ℕ}
    (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor n 3 j q) (hn_eq : n = 3 * j)
    (hj : 2 ≤ j) :
    n = 3 :=
  eq_three_of_sub_one_sub_two_twoPowers
    (twoPower_sub_one_of_no_common_eq_three_mul hnone hn_eq (by omega))
    (twoPower_sub_two_of_no_common_eq_three_mul hnone hn_eq hj)

theorem no_common_eq_three_mul_false_of_two_le {n j : ℕ}
    (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor n 3 j q) (hn_eq : n = 3 * j)
    (hj : 2 ≤ j) :
    False := by
  have hn3 : n = 3 := eq_three_of_no_common_eq_three_mul hnone hn_eq hj
  omega

/-- Product of the prime divisors of `m` that are at least `lo`, without multiplicity. -/
def primeRadicalGE (lo m : ℕ) : ℕ :=
  ∏ p ∈ m.primeFactors.filter (fun p => lo ≤ p), p

theorem prime_coprime_finset_prod_of_not_mem {p : ℕ} (hp : p.Prime) (s : Finset ℕ)
    (hs : ∀ q ∈ s, q.Prime) (hnot : p ∉ s) :
    p.Coprime (∏ q ∈ s, q) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.prod_insert ha]
      have hp_ne_a : p ≠ a := by
        intro hpa
        apply hnot
        rw [hpa]
        exact Finset.mem_insert_self a s
      have hpa_coprime : p.Coprime a :=
        (Nat.coprime_primes hp (hs a (Finset.mem_insert_self a s))).mpr hp_ne_a
      have hp_not_s : p ∉ s := by
        intro hps
        exact hnot (Finset.mem_insert_of_mem hps)
      have hprod : p.Coprime (∏ q ∈ s, q) :=
        ih (fun q hq => hs q (Finset.mem_insert_of_mem hq)) hp_not_s
      exact hpa_coprime.mul_right hprod

theorem finset_prod_primes_dvd_of_forall_dvd {s : Finset ℕ} {x : ℕ}
    (hprime : ∀ p ∈ s, p.Prime) (hdiv : ∀ p ∈ s, p ∣ x) :
    (∏ p ∈ s, p) ∣ x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.prod_insert ha]
      have hacoprime : a.Coprime (∏ p ∈ s, p) :=
        prime_coprime_finset_prod_of_not_mem (hprime a (Finset.mem_insert_self a s)) s
          (fun p hp => hprime p (Finset.mem_insert_of_mem hp)) ha
      exact Nat.Coprime.mul_dvd_of_dvd_of_dvd hacoprime
        (hdiv a (Finset.mem_insert_self a s))
        (ih (fun p hp => hprime p (Finset.mem_insert_of_mem hp))
          (fun p hp => hdiv p (Finset.mem_insert_of_mem hp)))

theorem primeRadicalGE_dvd_of_forall_prime_dvd {lo m x : ℕ}
    (h : ∀ p : ℕ, p.Prime → lo ≤ p → p ∣ m → p ∣ x) :
    primeRadicalGE lo m ∣ x := by
  classical
  unfold primeRadicalGE
  apply finset_prod_primes_dvd_of_forall_dvd
  · intro p hp_mem
    exact (Nat.mem_primeFactors.mp (Finset.mem_filter.mp hp_mem).1).1
  · intro p hp_mem
    rcases Finset.mem_filter.mp hp_mem with ⟨hpm, hlo⟩
    exact h p (Nat.mem_primeFactors.mp hpm).1 hlo (Nat.mem_primeFactors.mp hpm).2.1

theorem i_three_window_one_primeRadicalGE_dvd {n j : ℕ}
    (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor n 3 j q) (hn : 1 < n) :
    primeRadicalGE 5 (n - 1) ∣ j * (j - 1) :=
  primeRadicalGE_dvd_of_forall_prime_dvd fun p hp hp5 hpdvd =>
    i_three_window_one_product_forcing (p := p) hnone hp hp5 hn hpdvd

theorem i_three_window_two_primeRadicalGE_dvd {n j : ℕ}
    (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor n 3 j q) (hn : 2 < n) :
    primeRadicalGE 5 (n - 2) ∣ j * (j - 1) * (j - 2) :=
  primeRadicalGE_dvd_of_forall_prime_dvd fun p hp hp5 hpdvd =>
    i_three_window_two_product_forcing (p := p) hnone hp hp5 hn hpdvd

theorem n_dvd_mul_choose_self {n j : ℕ} (hn : 0 < n) (hj : 0 < j) :
    n ∣ j * Nat.choose n j := by
  have hidentity :
      n * Nat.choose (n - 1) (j - 1) = Nat.choose n j * j := by
    have h := Nat.add_one_mul_choose_eq (n - 1) (j - 1)
    have hn_sub : n - 1 + 1 = n := Nat.sub_add_cancel hn
    have hj_sub : j - 1 + 1 = j := Nat.sub_add_cancel hj
    simpa [hn_sub, hj_sub] using h
  rw [mul_comm j (Nat.choose n j), ← hidentity]
  exact dvd_mul_right n _

theorem prime_dvd_choose_three_of_prime_ge_five_dvd {n p : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) (hpn : p ∣ n) :
    p ∣ Nat.choose n 3 := by
  apply prime_dvd_choose_of_not_dominated hp
  intro hdom
  have hdigits := (dominated_iff_forall_digits hp.two_le).mp hdom 0
  have hn_mod : n % p = 0 := Nat.dvd_iff_mod_eq_zero.mp hpn
  have hthree_mod : 3 % p = 3 := Nat.mod_eq_of_lt (by omega : 3 < p)
  simp [digit, hn_mod, hthree_mod] at hdigits

theorem dvd_j_of_no_common_i_three {d n j : ℕ}
    (hnone : ∀ p : ℕ, ¬ commonPrimeDivisor n 3 j p) (hn : 0 < n) (hj : 0 < j)
    (hdn : d ∣ n) (hrel : ∀ p : ℕ, p.Prime → p ∣ d → 3 ≤ p)
    (hdchoose : ∀ p : ℕ, p.Prime → p ∣ d → p ∣ Nat.choose n 3) :
    d ∣ j := by
  have hcop : d.Coprime (Nat.choose n j) := by
    apply Nat.coprime_of_dvd
    intro p hp hpd hpchoose
    exact hnone p ⟨hp, hrel p hp hpd, hdchoose p hp hpd, hpchoose⟩
  have hn_dvd : n ∣ j * Nat.choose n j := n_dvd_mul_choose_self hn hj
  have hdprod : d ∣ j * Nat.choose n j := Nat.dvd_trans hdn hn_dvd
  exact (hcop.dvd_mul_right).mp hdprod

theorem prime_ge_five_of_dvd_div_three_odd_not_nine {n p : ℕ}
    (hodd : Odd n) (h3n : 3 ∣ n) (hnot9 : ¬ 9 ∣ n) (hp : p.Prime)
    (hpd : p ∣ n / 3) :
    5 ≤ p := by
  have hn_eq : n = 3 * (n / 3) := (Nat.mul_div_cancel' h3n).symm
  have hdn : n / 3 ∣ n := by
    refine ⟨3, ?_⟩
    simpa [mul_comm] using hn_eq
  by_cases hp2 : p = 2
  · subst p
    have h2n : 2 ∣ n := Nat.dvd_trans hpd hdn
    have hn_even : Even n := even_iff_two_dvd.mpr h2n
    exact False.elim ((Nat.not_odd_iff_even.mpr hn_even) hodd)
  by_cases hp3 : p = 3
  · subst p
    rcases hpd with ⟨a, ha⟩
    apply False.elim
    apply hnot9
    refine ⟨a, ?_⟩
    rw [hn_eq, ha]
    omega
  have hp4 : p ≠ 4 := by
    intro hp_eq
    subst p
    exact (by decide : ¬ Nat.Prime 4) hp
  have hp2le : 2 ≤ p := hp.two_le
  omega

theorem t5_collapse_eq_three_mul_of_no_common {n j : ℕ}
    (hnone : ∀ p : ℕ, ¬ commonPrimeDivisor n 3 j p) (hodd : Odd n)
    (h3n : 3 ∣ n) (hnot9 : ¬ 9 ∣ n) (hj : 3 < j) (hjn : 2 * j ≤ n) :
    n = 3 * j := by
  let d := n / 3
  have hj_pos : 0 < j := by omega
  have hn_pos : 0 < n := by omega
  have hn_eq : n = 3 * d := by
    dsimp [d]
    exact (Nat.mul_div_cancel' h3n).symm
  have hdn : d ∣ n := by
    refine ⟨3, ?_⟩
    simpa [mul_comm] using hn_eq
  have hrel : ∀ p : ℕ, p.Prime → p ∣ d → 3 ≤ p := by
    intro p hp hpd
    have hp5 : 5 ≤ p :=
      prime_ge_five_of_dvd_div_three_odd_not_nine hodd h3n hnot9 hp (by simpa [d] using hpd)
    omega
  have hdchoose : ∀ p : ℕ, p.Prime → p ∣ d → p ∣ Nat.choose n 3 := by
    intro p hp hpd
    have hp5 : 5 ≤ p :=
      prime_ge_five_of_dvd_div_three_odd_not_nine hodd h3n hnot9 hp (by simpa [d] using hpd)
    exact prime_dvd_choose_three_of_prime_ge_five_dvd hp hp5 (Nat.dvd_trans hpd hdn)
  have hdj : d ∣ j := dvd_j_of_no_common_i_three hnone hn_pos hj_pos hdn hrel hdchoose
  have hd_pos : 0 < d := by omega
  have hj_lt_two_d : j < 2 * d := by omega
  have hj_eq_d : j = d := Nat.eq_of_dvd_of_lt_two_mul (by omega) hdj hj_lt_two_d
  rw [hn_eq, hj_eq_d]

theorem t5_i_eq_three_odd_three_exactly_once {n j : ℕ} (hodd : Odd n)
    (h3n : 3 ∣ n) (hnot9 : ¬ 9 ∣ n) (hj : 3 < j) (hjn : 2 * j ≤ n) :
    ∃ p : ℕ, commonPrimeDivisor n 3 j p := by
  by_contra hnone_exists
  rw [not_exists] at hnone_exists
  have hn_eq : n = 3 * j :=
    t5_collapse_eq_three_mul_of_no_common hnone_exists hodd h3n hnot9 hj hjn
  exact no_common_eq_three_mul_false_of_two_le hnone_exists hn_eq (by omega)

theorem prime_dvd_choose_two_of_odd_prime_dvd {n p : ℕ} (hp : p.Prime)
    (hp_ne_two : p ≠ 2) (hpn : p ∣ n) :
    p ∣ Nat.choose n 2 := by
  apply prime_dvd_choose_of_not_dominated hp
  intro hdom
  have hdigits := (dominated_iff_forall_digits hp.two_le).mp hdom 0
  have hp_two_le : 2 ≤ p := hp.two_le
  have hp_gt_two : 2 < p := by omega
  have hn_mod : n % p = 0 := Nat.dvd_iff_mod_eq_zero.mp hpn
  have htwo_mod : 2 % p = 2 := Nat.mod_eq_of_lt hp_gt_two
  simp [digit, hn_mod, htwo_mod] at hdigits

theorem two_dvd_choose_two_of_four_dvd {n : ℕ} (h4 : 4 ∣ n) :
    2 ∣ Nat.choose n 2 := by
  apply prime_dvd_choose_of_not_dominated (by decide : Nat.Prime 2)
  intro hdom
  have hdigits := (dominated_iff_forall_digits (by decide : 2 ≤ 2)).mp hdom 1
  rcases h4 with ⟨a, rfl⟩
  have hlevel : (4 * a / 2) % 2 = 0 := by
    have hdiv : 4 * a / 2 = 2 * a := by
      rw [show 4 * a = 2 * (2 * a) by omega]
      exact Nat.mul_div_cancel_left (2 * a) (by decide : 0 < 2)
    rw [hdiv]
    exact Nat.dvd_iff_mod_eq_zero.mp (dvd_mul_right 2 a)
  simp [digit, hlevel] at hdigits

theorem dvd_j_of_no_common_i_two {d n j : ℕ}
    (hnone : ∀ p : ℕ, ¬ commonPrimeDivisor n 2 j p) (hn : 0 < n) (hj : 0 < j)
    (hdn : d ∣ n) (hdchoose : ∀ p : ℕ, p.Prime → p ∣ d → p ∣ Nat.choose n 2) :
    d ∣ j := by
  have hcop : d.Coprime (Nat.choose n j) := by
    apply Nat.coprime_of_dvd
    intro p hp hpd hpchoose
    exact hnone p ⟨hp, hp.two_le, hdchoose p hp hpd, hpchoose⟩
  have hn_dvd : n ∣ j * Nat.choose n j := n_dvd_mul_choose_self hn hj
  have hdprod : d ∣ j * Nat.choose n j := Nat.dvd_trans hdn hn_dvd
  exact (hcop.dvd_mul_right).mp hdprod

theorem t2_collapse_of_no_common {n j : ℕ}
    (hnone : ∀ p : ℕ, ¬ commonPrimeDivisor n 2 j p)
    (hj : 2 < j) (hjn : 2 * j ≤ n) :
    n = 2 * j ∧ Odd j := by
  have hj_pos : 0 < j := by omega
  have hn_pos : 0 < n := by omega
  by_cases hnodd : Odd n
  · have hdchoose : ∀ p : ℕ, p.Prime → p ∣ n → p ∣ Nat.choose n 2 := by
      intro p hp hpn
      have hp_ne_two : p ≠ 2 := by
        intro hp_eq
        subst p
        have hmod0 : n % 2 = 0 := Nat.dvd_iff_mod_eq_zero.mp hpn
        have hmod1 : n % 2 = 1 := Nat.odd_iff.mp hnodd
        omega
      exact prime_dvd_choose_two_of_odd_prime_dvd hp hp_ne_two hpn
    have hn_dvd_j : n ∣ j :=
      dvd_j_of_no_common_i_two hnone hn_pos hj_pos dvd_rfl hdchoose
    have hn_le_j : n ≤ j := Nat.le_of_dvd hj_pos hn_dvd_j
    omega
  · by_cases h4 : 4 ∣ n
    · have hdchoose : ∀ p : ℕ, p.Prime → p ∣ n → p ∣ Nat.choose n 2 := by
        intro p hp hpn
        by_cases hp_eq_two : p = 2
        · subst p
          exact two_dvd_choose_two_of_four_dvd h4
        · exact prime_dvd_choose_two_of_odd_prime_dvd hp hp_eq_two hpn
      have hn_dvd_j : n ∣ j :=
        dvd_j_of_no_common_i_two hnone hn_pos hj_pos dvd_rfl hdchoose
      have hn_le_j : n ≤ j := Nat.le_of_dvd hj_pos hn_dvd_j
      omega
    · let m := n / 2
      have hneven : Even n := Nat.not_odd_iff_even.mp hnodd
      have h2n : 2 ∣ n := even_iff_two_dvd.mp hneven
      have hn_eq_two_m : n = 2 * m := by
        dsimp [m]
        exact (Nat.mul_div_cancel' h2n).symm
      have hmdvdn : m ∣ n := by
        refine ⟨2, ?_⟩
        rw [hn_eq_two_m, mul_comm]
      have hdchoose : ∀ p : ℕ, p.Prime → p ∣ m → p ∣ Nat.choose n 2 := by
        intro p hp hpm
        have hp_ne_two : p ≠ 2 := by
          intro hp_eq
          subst p
          apply h4
          rcases hpm with ⟨a, ha⟩
          refine ⟨a, ?_⟩
          rw [hn_eq_two_m, ha]
          omega
        have hpn : p ∣ n := Nat.dvd_trans hpm hmdvdn
        exact prime_dvd_choose_two_of_odd_prime_dvd hp hp_ne_two hpn
      have hm_dvd_j : m ∣ j :=
        dvd_j_of_no_common_i_two hnone hn_pos hj_pos hmdvdn hdchoose
      have hm_le_j : m ≤ j := Nat.le_of_dvd hj_pos hm_dvd_j
      have hj_le_m : j ≤ m := by
        dsimp [m]
        rw [Nat.le_div_iff_mul_le (by decide : 0 < 2)]
        simpa [mul_comm] using hjn
      have hm_eq_j : m = j := le_antisymm hm_le_j hj_le_m
      have hn_eq : n = 2 * j := by
        rw [hn_eq_two_m, hm_eq_j]
      have hj_odd : Odd j := by
        apply Nat.not_even_iff_odd.mp
        intro hjeven
        apply h4
        have h2j : 2 ∣ j := even_iff_two_dvd.mp hjeven
        rcases h2j with ⟨a, ha⟩
        refine ⟨a, ?_⟩
        rw [hn_eq, ha]
        omega
      exact ⟨hn_eq, hj_odd⟩

theorem two_mul_mod_eq_one_of_dvd_pred {j p : ℕ}
    (hp : p.Prime) (hpdvd : p ∣ 2 * j - 1) (hj : 0 < j) :
    (2 * j) % p = 1 := by
  rcases hpdvd with ⟨a, ha⟩
  have hEq : 2 * j = p * a + 1 := by omega
  rw [hEq]
  simp [Nat.add_mod, Nat.mod_eq_of_lt hp.one_lt]

theorem prime_dvd_choose_two_of_dvd_two_mul_sub_one {j p : ℕ}
    (hp : p.Prime) (hp_ne_two : p ≠ 2) (hpdvd : p ∣ 2 * j - 1) (hj : 0 < j) :
    p ∣ Nat.choose (2 * j) 2 := by
  apply prime_dvd_choose_of_not_dominated hp
  intro hdom
  have hdigits := (dominated_iff_forall_digits hp.two_le).mp hdom 0
  have hp_two_le : 2 ≤ p := hp.two_le
  have hp_gt_two : 2 < p := by omega
  have hn_mod : (2 * j) % p = 1 := two_mul_mod_eq_one_of_dvd_pred hp hpdvd hj
  have htwo_mod : 2 % p = 2 := Nat.mod_eq_of_lt hp_gt_two
  simp [digit, hn_mod, htwo_mod] at hdigits

theorem prime_dvd_central_of_dvd_two_mul_sub_one {j p : ℕ}
    (hp : p.Prime) (hp_ne_two : p ≠ 2) (hpdvd : p ∣ 2 * j - 1) (hj : 0 < j) :
    p ∣ Nat.choose (2 * j) j := by
  apply prime_dvd_choose_of_not_dominated hp
  intro hdom
  have hdigits := (dominated_iff_forall_digits hp.two_le).mp hdom 0
  have hp_two_le : 2 ≤ p := hp.two_le
  have hp_gt_two : 2 < p := by omega
  have hn_mod : (2 * j) % p = 1 := two_mul_mod_eq_one_of_dvd_pred hp hpdvd hj
  have hp_not_dvd_j : ¬ p ∣ j := by
    intro hpj
    have hj_mod0 : j % p = 0 := Nat.dvd_iff_mod_eq_zero.mp hpj
    have htwom0 : (2 * j) % p = 0 := by
      rw [Nat.mul_mod, hj_mod0]
      simp
    omega
  have hle : j % p ≤ 1 := by
    simpa [digit, hn_mod] using hdigits
  have hj_mod_ne_zero : j % p ≠ 0 := by
    intro hj_mod0
    exact hp_not_dvd_j (Nat.dvd_iff_mod_eq_zero.mpr hj_mod0)
  have hj_mod : j % p = 1 := by omega
  have htwom_calc : (2 * j) % p = 2 := by
    rw [Nat.mul_mod, hj_mod, Nat.mod_eq_of_lt hp_gt_two]
    exact Nat.mod_eq_of_lt hp_gt_two
  omega

theorem t2_i_eq_two {n j : ℕ} (hj : 2 < j) (hjn : 2 * j ≤ n) :
    ∃ p : ℕ, commonPrimeDivisor n 2 j p := by
  by_contra hnone_exists
  rw [not_exists] at hnone_exists
  have hj_pos : 0 < j := by omega
  have hcollapse := t2_collapse_of_no_common hnone_exists hj hjn
  rcases hcollapse with ⟨hn_eq, _⟩
  have hpred_ne_one : 2 * j - 1 ≠ 1 := by omega
  obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hpred_ne_one
  have hp_ne_two : p ≠ 2 := by
    intro hp_eq
    subst p
    rcases hpdvd with ⟨a, ha⟩
    omega
  have hp_choose_two : p ∣ Nat.choose (2 * j) 2 :=
    prime_dvd_choose_two_of_dvd_two_mul_sub_one hp hp_ne_two hpdvd hj_pos
  have hp_choose_j : p ∣ Nat.choose (2 * j) j :=
    prime_dvd_central_of_dvd_two_mul_sub_one hp hp_ne_two hpdvd hj_pos
  exact hnone_exists p ⟨hp, hp.two_le, by simpa [hn_eq] using hp_choose_two,
    by simpa [hn_eq] using hp_choose_j⟩

theorem t1_i_eq_one {n j : ℕ} (hj : 2 ≤ j) (hjn : 2 * j ≤ n) :
    ∃ p : ℕ, commonPrimeDivisor n 1 j p := by
  by_contra hnone
  rw [not_exists] at hnone
  have hj_pos : 0 < j := Nat.lt_of_lt_of_le (by decide : 0 < 2) hj
  have hn_pos : 0 < n := (Nat.mul_pos (by decide : 0 < 2) hj_pos).trans_le hjn
  have hcop : n.Coprime (Nat.choose n j) := by
    apply Nat.coprime_of_dvd
    intro p hp hpn hpc
    have hp_one : 1 ≤ p := hp.one_le
    have hp_choose_one : p ∣ Nat.choose n 1 := by
      simpa [Nat.choose_one_right] using hpn
    exact hnone p ⟨hp, hp_one, hp_choose_one, hpc⟩
  have hidentity :
      n * Nat.choose (n - 1) (j - 1) = Nat.choose n j * j := by
    have h := Nat.add_one_mul_choose_eq (n - 1) (j - 1)
    have hn_sub : n - 1 + 1 = n := Nat.sub_add_cancel hn_pos
    have hj_sub : j - 1 + 1 = j := Nat.sub_add_cancel hj_pos
    simpa [hn_sub, hj_sub] using h
  have hdiv_product : n ∣ j * Nat.choose n j := by
    rw [mul_comm j (Nat.choose n j), ← hidentity]
    exact dvd_mul_right n _
  have hdiv_j : n ∣ j := (hcop.dvd_mul_right).mp hdiv_product
  have hn_le_j : n ≤ j := Nat.le_of_dvd hj_pos hdiv_j
  omega

/-- A prime `p` is relevant to row `i` exactly when `p ≥ i`. -/
def relevantPrime (i p : ℕ) : Prop :=
  p.Prime ∧ i ≤ p

theorem relevantPrime_ignores_small {i p : ℕ} (hp : p < i) :
    ¬ relevantPrime i p := by
  intro h
  exact Nat.not_le_of_gt hp h.2

/-- The corrected obstruction criterion: only primes `p ≥ i` are constrained. -/
def obstructionCriterion (n i j : ℕ) : Prop :=
  ∀ p : ℕ, relevantPrime i p → dominated i n p ∨ dominated j n p

theorem no_commonPrimeDivisor_iff_obstructionCriterion (n i j : ℕ) :
    (∀ p : ℕ, ¬ commonPrimeDivisor n i j p) ↔ obstructionCriterion n i j := by
  classical
  constructor
  · intro hnone p hrel
    by_cases hi : dominated i n p
    · exact Or.inl hi
    · right
      by_contra hj
      exact hnone p
        ⟨hrel.1, hrel.2, prime_dvd_choose_of_not_dominated hrel.1 hi,
          prime_dvd_choose_of_not_dominated hrel.1 hj⟩
  · intro hcrit p hcommon
    rcases hcommon with ⟨hp, hge, hpi, hpj⟩
    rcases hcrit p ⟨hp, hge⟩ with hdom_i | hdom_j
    · have hnonzero := (lucas_nonzero_mod_prime_iff_dominated hp).mpr hdom_i
      exact hnonzero (Nat.dvd_iff_mod_eq_zero.mp hpi)
    · have hnonzero := (lucas_nonzero_mod_prime_iff_dominated hp).mpr hdom_j
      exact hnonzero (Nat.dvd_iff_mod_eq_zero.mp hpj)

end Erdos699
