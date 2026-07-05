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

theorem prime_dvd_of_pow_dvd {p e m : ℕ} (he : 0 < e) (h : p ^ e ∣ m) :
    p ∣ m := by
  rcases h with ⟨a, ha⟩
  rcases Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt he) with ⟨c, hc⟩
  refine ⟨p ^ c * a, ?_⟩
  rw [ha, hc, pow_succ']
  ac_rfl

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
    have hbase : (p ^ r * (p ^ (e - r) * a) + 1) / p ^ r =
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

theorem i_three_window_one_dominated_of_prime_pow_dvd_sub_one {n j p e : ℕ}
    (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor n 3 j q)
    (hp : p.Prime) (hp5 : 5 ≤ p) (hn : 1 < n) (he_pos : 0 < e)
    (hpdvd : p ^ e ∣ n - 1) :
    dominated j n p := by
  have hchoose3 : p ∣ Nat.choose n 3 := by
    apply prime_dvd_choose_of_not_dominated hp
    intro hdom
    have hdigits := (dominated_iff_forall_digits hp.two_le).mp hdom 0
    have hn_mod : n % p = 1 :=
      by simpa [digit] using
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

/-- Product of the full prime-power divisors of `m` whose prime is at least `lo`. -/
def primePowerPartGE (lo m : ℕ) : ℕ :=
  ∏ p ∈ m.primeFactors.filter (fun p => lo ≤ p), p ^ m.factorization p

theorem prime_power_coprime_finset_prime_power_prod_of_not_mem {p : ℕ} {e : ℕ}
    {s : Finset ℕ} {f : ℕ → ℕ} (hp : p.Prime)
    (hs : ∀ q ∈ s, q.Prime) (hnot : p ∉ s) :
    (p ^ e).Coprime (∏ q ∈ s, q ^ f q) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp
  | insert a s ha ih =>
      rw [Finset.prod_insert ha]
      have hp_ne_a : p ≠ a := by
        intro hpa
        apply hnot
        rw [hpa]
        exact Finset.mem_insert_self a s
      have hpa_coprime : (p ^ e).Coprime (a ^ f a) :=
        Nat.coprime_pow_primes e (f a) hp
          (hs a (Finset.mem_insert_self a s)) hp_ne_a
      have hp_not_s : p ∉ s := by
        intro hps
        exact hnot (Finset.mem_insert_of_mem hps)
      have hprod : (p ^ e).Coprime (∏ q ∈ s, q ^ f q) :=
        ih (fun q hq => hs q (Finset.mem_insert_of_mem hq)) hp_not_s
      exact hpa_coprime.mul_right hprod

theorem finset_prod_prime_powers_dvd_of_forall_dvd {s : Finset ℕ} {e : ℕ → ℕ}
    {x : ℕ} (hprime : ∀ p ∈ s, p.Prime)
    (hdiv : ∀ p ∈ s, p ^ e p ∣ x) :
    (∏ p ∈ s, p ^ e p) ∣ x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp
  | insert a s ha ih =>
      rw [Finset.prod_insert ha]
      have hacoprime : (a ^ e a).Coprime (∏ p ∈ s, p ^ e p) :=
        prime_power_coprime_finset_prime_power_prod_of_not_mem
          (p := a) (e := e a) (s := s) (f := e)
          (hprime a (Finset.mem_insert_self a s))
          (fun p hp => hprime p (Finset.mem_insert_of_mem hp)) ha
      exact Nat.Coprime.mul_dvd_of_dvd_of_dvd hacoprime
        (hdiv a (Finset.mem_insert_self a s))
        (ih (fun p hp => hprime p (Finset.mem_insert_of_mem hp))
          (fun p hp => hdiv p (Finset.mem_insert_of_mem hp)))

theorem primePowerPartGE_dvd_of_forall_prime_power_dvd {lo m x : ℕ}
    (h : ∀ p : ℕ, p.Prime → lo ≤ p → p ∣ m → p ^ m.factorization p ∣ x) :
    primePowerPartGE lo m ∣ x := by
  classical
  unfold primePowerPartGE
  apply finset_prod_prime_powers_dvd_of_forall_dvd
  · intro p hp_mem
    exact (Nat.mem_primeFactors.mp (Finset.mem_filter.mp hp_mem).1).1
  · intro p hp_mem
    rcases Finset.mem_filter.mp hp_mem with ⟨hpm, hlo⟩
    exact h p (Nat.mem_primeFactors.mp hpm).1 hlo (Nat.mem_primeFactors.mp hpm).2.1

theorem i_three_window_one_primePowerPartGE_dvd {n j : ℕ}
    (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor n 3 j q) (hn : 1 < n) :
    primePowerPartGE 5 (n - 1) ∣ j * (j - 1) := by
  apply primePowerPartGE_dvd_of_forall_prime_power_dvd
  intro p hp hp5 _hpdvd
  have hm_ne : n - 1 ≠ 0 := by omega
  have hpowdvd : p ^ (n - 1).factorization p ∣ n - 1 :=
    (hp.pow_dvd_iff_le_factorization hm_ne).mpr le_rfl
  exact i_three_window_one_prime_pow_dvd_mul_sub_one hnone hp hp5 hn hpowdvd

theorem i_three_window_two_primePowerPartGE_dvd {n j : ℕ}
    (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor n 3 j q) (hn : 2 < n) :
    primePowerPartGE 5 (n - 2) ∣ j * (j - 1) * (j - 2) := by
  apply primePowerPartGE_dvd_of_forall_prime_power_dvd
  intro p hp hp5 _hpdvd
  have hm_ne : n - 2 ≠ 0 := by omega
  have hpowdvd : p ^ (n - 2).factorization p ∣ n - 2 :=
    (hp.pow_dvd_iff_le_factorization hm_ne).mpr le_rfl
  exact i_three_window_two_prime_pow_dvd_mul_sub_one_sub_two hnone hp hp5 hn hpowdvd

theorem primePowerPartGE_eq_self_of_forall_prime_ge {lo m : ℕ}
    (hm : m ≠ 0) (hlo : ∀ p : ℕ, p.Prime → p ∣ m → lo ≤ p) :
    primePowerPartGE lo m = m := by
  classical
  unfold primePowerPartGE
  have hfilter : m.primeFactors.filter (fun p => lo ≤ p) = m.primeFactors := by
    ext p
    constructor
    · intro hp
      exact (Finset.mem_filter.mp hp).1
    · intro hp
      exact Finset.mem_filter.mpr
        ⟨hp, hlo p (Nat.mem_primeFactors.mp hp).1 (Nat.mem_primeFactors.mp hp).2.1⟩
  rw [hfilter]
  simpa [Nat.prod_factorization_eq_prod_primeFactors] using
    Nat.prod_factorization_pow_eq_self hm

theorem primePowerPartGE_dvd_self {lo m : ℕ} (hm : m ≠ 0) :
    primePowerPartGE lo m ∣ m := by
  apply primePowerPartGE_dvd_of_forall_prime_power_dvd
  intro p hp _hlo _hpdvd
  exact (hp.pow_dvd_iff_le_factorization hm).mpr le_rfl

theorem finset_prod_prime_powers_coprime_four_of_ge_five {s : Finset ℕ}
    {f : ℕ → ℕ} (hge : ∀ p ∈ s, 5 ≤ p) (hprime : ∀ p ∈ s, p.Prime) :
    (∏ p ∈ s, p ^ f p).Coprime 4 := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp
  | insert a s ha ih =>
      rw [Finset.prod_insert ha]
      have ha_coprime_four : a.Coprime 4 := by
        exact (hprime a (Finset.mem_insert_self a s)).coprime_iff_not_dvd.mpr (by
          intro hdiv
          have ha_le_four : a ≤ 4 := Nat.le_of_dvd (by norm_num : 0 < 4) hdiv
          have ha_ge_five : 5 ≤ a := hge a (Finset.mem_insert_self a s)
          omega)
      have hpow : (a ^ f a).Coprime 4 := ha_coprime_four.pow_left (f a)
      exact hpow.mul_left
        (ih (fun p hp => hge p (Finset.mem_insert_of_mem hp))
          (fun p hp => hprime p (Finset.mem_insert_of_mem hp)))

theorem primePowerPartGE_five_coprime_four (m : ℕ) :
    (primePowerPartGE 5 m).Coprime 4 := by
  classical
  unfold primePowerPartGE
  apply finset_prod_prime_powers_coprime_four_of_ge_five
  · intro p hp_mem
    exact (Finset.mem_filter.mp hp_mem).2
  · intro p hp_mem
    exact (Nat.mem_primeFactors.mp (Finset.mem_filter.mp hp_mem).1).1

theorem i_three_window_one_sub_one_dvd_mul_sub_one_of_even_three_dvd {n j : ℕ}
    (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor n 3 j q)
    (hn : 1 < n) (h2n : 2 ∣ n) (h3n : 3 ∣ n) :
    n - 1 ∣ j * (j - 1) := by
  have hlarge : primePowerPartGE 5 (n - 1) = n - 1 := by
    apply primePowerPartGE_eq_self_of_forall_prime_ge
    · omega
    · intro p hp hpdvd
      by_cases hp2 : p = 2
      · subst p
        rcases h2n with ⟨a, ha⟩
        rcases hpdvd with ⟨b, hb⟩
        omega
      by_cases hp3 : p = 3
      · subst p
        rcases h3n with ⟨a, ha⟩
        rcases hpdvd with ⟨b, hb⟩
        omega
      have hp4 : p ≠ 4 := by
        intro hp_eq
        subst p
        exact (by decide : ¬ Nat.Prime 4) hp
      have hp2le : 2 ≤ p := hp.two_le
      omega
  rw [← hlarge]
  exact i_three_window_one_primePowerPartGE_dvd hnone hn

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

theorem i_three_caseI_row_one_sub_one_dvd_t_mul_X_sub_t {n F X j t : ℕ}
    (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor n 3 j q)
    (hn : n = F * X) (hj : j = F * t) (hn_gt : 2 < n) (hj_pos : 0 < j)
    (h2n : 2 ∣ n) (h3n : 3 ∣ n) (htX : t ≤ X) :
    n - 1 ∣ t * (X - t) :=
  sub_one_dvd_t_mul_X_sub_t_of_factor_dvd_mul_sub_one hn hj hn_gt hj_pos htX
    (i_three_window_one_sub_one_dvd_mul_sub_one_of_even_three_dvd
      hnone (by omega : 1 < n) h2n h3n)

theorem four_mul_t_mul_X_sub_t_le_sq {X t : ℕ} (h2tX : 2 * t ≤ X) :
    4 * (t * (X - t)) ≤ X * X := by
  have htX : t ≤ X := by omega
  have hcast_sub : ((X - t : ℕ) : ℤ) = (X : ℤ) - (t : ℤ) := Nat.cast_sub htX
  have hcalc :
      (4 : ℤ) * ((t : ℤ) * ((X : ℤ) - (t : ℤ))) ≤ (X : ℤ) * (X : ℤ) := by
    nlinarith [sq_nonneg ((X : ℤ) - 2 * (t : ℤ))]
  have h_int : ((4 * (t * (X - t)) : ℕ) : ℤ) ≤ ((X * X : ℕ) : ℤ) := by
    simpa [hcast_sub] using hcalc
  exact_mod_cast h_int

theorem four_mul_d_le_sq_of_dvd_t_mul_X_sub_t {d X t : ℕ}
    (ht_pos : 0 < t) (h2tX : 2 * t ≤ X) (hdvd : d ∣ t * (X - t)) :
    4 * d ≤ X * X := by
  have htX : t ≤ X := by omega
  have hXt_pos : 0 < X - t := by omega
  have hprod_pos : 0 < t * (X - t) := Nat.mul_pos ht_pos hXt_pos
  have hd_le : d ≤ t * (X - t) := Nat.le_of_dvd hprod_pos hdvd
  exact (Nat.mul_le_mul_left 4 hd_le).trans (four_mul_t_mul_X_sub_t_le_sq h2tX)

theorem four_mul_sub_one_le_sq_of_factor_dvd_mul_sub_one {n F X j t : ℕ}
    (hn : n = F * X) (hj : j = F * t) (hn_gt : 2 < n) (hj_pos : 0 < j)
    (h2tX : 2 * t ≤ X) (hdvd : n - 1 ∣ j * (j - 1)) :
    4 * (n - 1) ≤ X * X := by
  have ht_pos : 0 < t := by
    by_cases ht0 : t = 0
    · subst t
      simp at hj
      omega
    · exact Nat.pos_of_ne_zero ht0
  exact four_mul_d_le_sq_of_dvd_t_mul_X_sub_t ht_pos h2tX
    (sub_one_dvd_t_mul_X_sub_t_of_factor_dvd_mul_sub_one
      hn hj hn_gt hj_pos (by omega : t ≤ X) hdvd)

theorem i_three_caseI_row_one_four_mul_sub_one_le_X_sq {n F X j t : ℕ}
    (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor n 3 j q)
    (hn : n = F * X) (hj : j = F * t) (hn_gt : 2 < n) (hj_pos : 0 < j)
    (h2n : 2 ∣ n) (h3n : 3 ∣ n) (h2tX : 2 * t ≤ X) :
    4 * (n - 1) ≤ X * X :=
  four_mul_sub_one_le_sq_of_factor_dvd_mul_sub_one hn hj hn_gt hj_pos h2tX
    (i_three_window_one_sub_one_dvd_mul_sub_one_of_even_three_dvd
      hnone (by omega : 1 < n) h2n h3n)

theorem sub_two_divisor_dvd_t_mul_X_sub_t_mul_X_sub_two_t_of_factor_dvd_triple
    {d n F X j t : ℕ} (hdn : d ∣ n - 2) (hcop4 : d.Coprime 4)
    (hn : n = F * X) (hj : j = F * t) (hn_ge_two : 2 ≤ n) (hj_two : 2 ≤ j)
    (htX : t ≤ X) (h2tX : 2 * t ≤ X)
    (hdvd : d ∣ j * (j - 1) * (j - 2)) :
    d ∣ t * (X - t) * (X - 2 * t) := by
  let target := t * (X - t) * (X - 2 * t)
  have hn_mod_int : (n : ℤ) ≡ 2 [ZMOD (d : ℤ)] := by
    rcases hdn with ⟨a, ha⟩
    have hsub_cast : ((n - 2 : ℕ) : ℤ) = (n : ℤ) - 2 := Nat.cast_sub hn_ge_two
    have hdiff : (2 : ℤ) - (n : ℤ) = (d : ℤ) * (-(a : ℤ)) := by
      rw [← neg_sub]
      calc
        -((n : ℤ) - 2) = -((n - 2 : ℕ) : ℤ) := by rw [hsub_cast]
        _ = -((d * a : ℕ) : ℤ) := by rw [ha]
        _ = (d : ℤ) * (-(a : ℤ)) := by rw [Nat.cast_mul]; ring
    exact Int.modEq_iff_dvd.mpr ⟨-(a : ℤ), hdiff⟩
  have hFX_int : (F : ℤ) * (X : ℤ) ≡ 2 [ZMOD (d : ℤ)] := by
    have hn_int : (n : ℤ) = (F : ℤ) * (X : ℤ) := by exact_mod_cast hn
    simpa [hn_int] using hn_mod_int
  have hzero_nat : j * (j - 1) * (j - 2) ≡ 0 [MOD d] :=
    Nat.modEq_zero_iff_dvd.mpr hdvd
  have hzero_int :
      (j : ℤ) * ((j : ℤ) - 1) * ((j : ℤ) - 2) ≡ 0 [ZMOD (d : ℤ)] := by
    have hj_one : 1 ≤ j := by omega
    have hcast :
        ((j * (j - 1) * (j - 2) : ℕ) : ℤ) =
          (j : ℤ) * ((j : ℤ) - 1) * ((j : ℤ) - 2) := by
      rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_sub hj_one, Nat.cast_sub hj_two]
      norm_num
    simpa [hcast] using (Int.natCast_modEq_iff.mpr hzero_nat)
  have hj_int : (j : ℤ) = (F : ℤ) * (t : ℤ) := by exact_mod_cast hj
  have hzero_Ft :
      ((F : ℤ) * (t : ℤ)) * (((F : ℤ) * (t : ℤ)) - 1) *
          (((F : ℤ) * (t : ℤ)) - 2) ≡ 0 [ZMOD (d : ℤ)] := by
    simpa [hj_int] using hzero_int
  have hfirst :
      (X : ℤ) * ((F : ℤ) * (t : ℤ)) ≡ 2 * (t : ℤ) [ZMOD (d : ℤ)] := by
    have h := hFX_int.mul_right (t : ℤ)
    simpa [mul_assoc, mul_comm, mul_left_comm] using h
  have hsecond :
      (X : ℤ) * (((F : ℤ) * (t : ℤ)) - 1) ≡
        2 * (t : ℤ) - (X : ℤ) [ZMOD (d : ℤ)] := by
    have h := hfirst.sub (Int.ModEq.refl (a := (X : ℤ)) (n := (d : ℤ)))
    simpa [mul_sub] using h
  have hthird :
      (X : ℤ) * (((F : ℤ) * (t : ℤ)) - 2) ≡
        2 * (t : ℤ) - 2 * (X : ℤ) [ZMOD (d : ℤ)] := by
    have h := hfirst.sub (Int.ModEq.refl (a := (2 : ℤ) * (X : ℤ)) (n := (d : ℤ)))
    simpa [mul_sub, two_mul, mul_assoc, mul_comm, mul_left_comm] using h
  have hprod_raw := (hfirst.mul hsecond).mul hthird
  have hprod :
      ((X : ℤ) ^ 3) *
          (((F : ℤ) * (t : ℤ)) * (((F : ℤ) * (t : ℤ)) - 1) *
            (((F : ℤ) * (t : ℤ)) - 2)) ≡
        4 * ((t : ℤ) * ((X : ℤ) - (t : ℤ)) * ((X : ℤ) - 2 * (t : ℤ)))
          [ZMOD (d : ℤ)] := by
    convert hprod_raw using 1 <;> ring
  have hscaled_zero :
      ((X : ℤ) ^ 3) *
          (((F : ℤ) * (t : ℤ)) * (((F : ℤ) * (t : ℤ)) - 1) *
            (((F : ℤ) * (t : ℤ)) - 2)) ≡ 0 [ZMOD (d : ℤ)] := by
    simpa using hzero_Ft.mul_left ((X : ℤ) ^ 3)
  have hfour_target_zero :
      4 * ((t : ℤ) * ((X : ℤ) - (t : ℤ)) * ((X : ℤ) - 2 * (t : ℤ))) ≡
        0 [ZMOD (d : ℤ)] :=
    hprod.symm.trans hscaled_zero
  have htarget_cast :
      ((target : ℕ) : ℤ) =
        (t : ℤ) * ((X : ℤ) - (t : ℤ)) * ((X : ℤ) - 2 * (t : ℤ)) := by
    have hcast_xt : ((X - t : ℕ) : ℤ) = (X : ℤ) - (t : ℤ) := Nat.cast_sub htX
    have hcast_x2t : ((X - 2 * t : ℕ) : ℤ) = (X : ℤ) - (2 * t : ℕ) :=
      Nat.cast_sub h2tX
    dsimp [target]
    rw [hcast_xt, hcast_x2t, Nat.cast_mul]
    norm_num
  have hfour_target_nat_int : (((4 * target : ℕ) : ℤ)) ≡ 0 [ZMOD (d : ℤ)] := by
    have hcast :
        (((4 * target : ℕ) : ℤ)) =
          4 * ((t : ℤ) * ((X : ℤ) - (t : ℤ)) * ((X : ℤ) - 2 * (t : ℤ))) := by
      rw [Nat.cast_mul, htarget_cast]
      norm_num
    simpa [hcast] using hfour_target_zero
  have hdvd_four_int : (d : ℤ) ∣ ((4 * target : ℕ) : ℤ) :=
    Int.modEq_zero_iff_dvd.mp hfour_target_nat_int
  have hdvd_four_nat : d ∣ 4 * target := Int.natCast_dvd_natCast.mp hdvd_four_int
  exact hcop4.dvd_of_dvd_mul_left hdvd_four_nat

theorem i_three_caseI_row_two_primePowerPartGE_dvd_t_mul_X_sub_t_mul_X_sub_two_t
    {n F X j t : ℕ} (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor n 3 j q)
    (hn : n = F * X) (hj : j = F * t) (hn_ge_two : 2 ≤ n) (hn_gt_two : 2 < n)
    (hj_two : 2 ≤ j) (htX : t ≤ X) (h2tX : 2 * t ≤ X) :
    primePowerPartGE 5 (n - 2) ∣ t * (X - t) * (X - 2 * t) :=
  sub_two_divisor_dvd_t_mul_X_sub_t_mul_X_sub_two_t_of_factor_dvd_triple
    (primePowerPartGE_dvd_self (by omega : n - 2 ≠ 0))
    (primePowerPartGE_five_coprime_four (n - 2)) hn hj hn_ge_two hj_two htX h2tX
    (i_three_window_two_primePowerPartGE_dvd hnone hn_gt_two)

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
