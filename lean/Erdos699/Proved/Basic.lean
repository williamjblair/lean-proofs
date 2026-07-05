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

/-- The consecutive-divisor kernel: two fixed divisors packed into products of
one, then two, consecutive gaps from `t`. -/
def consecutiveDivisorKernel (N1 N2 t : ℕ) : Prop :=
  N1 ∣ t * (t - 1) ∧ N2 ∣ t * (t - 1) * (t - 2)

/-- The same kernel with the problem's half-row bound. -/
def consecutiveDivisorKernelBelow (N1 N2 bound t : ℕ) : Prop :=
  2 * t ≤ bound ∧ consecutiveDivisorKernel N1 N2 t

/-- A row-one divisor split: one factor of `N1` is assigned to `t`, and the
other to `t - 1`. This is the formal version of the `{0,1}` choices used by
the CRT kernel scanner. -/
def rowOneDivisorSplit (N1 zeroPart onePart t : ℕ) : Prop :=
  zeroPart * onePart = N1 ∧ zeroPart ∣ t ∧ onePart ∣ t - 1

theorem rowOneDivisorSplit_dvd_mul_sub_one {N1 zeroPart onePart t : ℕ}
    (hsplit : rowOneDivisorSplit N1 zeroPart onePart t) :
    N1 ∣ t * (t - 1) := by
  rcases hsplit with ⟨hprod, hzero, hone⟩
  rw [← hprod]
  exact Nat.mul_dvd_mul hzero hone

theorem rowOneDivisorSplit_modEq_zero {N1 zeroPart onePart t : ℕ}
    (hsplit : rowOneDivisorSplit N1 zeroPart onePart t) :
    t ≡ 0 [MOD zeroPart] := by
  exact Nat.modEq_zero_iff_dvd.mpr hsplit.2.1

theorem rowOneDivisorSplit_modEq_one_of_one_le {N1 zeroPart onePart t : ℕ}
    (hsplit : rowOneDivisorSplit N1 zeroPart onePart t) (ht : 1 ≤ t) :
    t ≡ 1 [MOD onePart] := by
  exact ((Nat.modEq_iff_dvd' ht).mpr hsplit.2.2).symm

theorem rowOneDivisorSplit_of_modEq {N1 zeroPart onePart t : ℕ}
    (hprod : zeroPart * onePart = N1) (hzero : t ≡ 0 [MOD zeroPart])
    (hone : t ≡ 1 [MOD onePart]) (ht : 1 ≤ t) :
    rowOneDivisorSplit N1 zeroPart onePart t := by
  exact
    ⟨hprod, Nat.modEq_zero_iff_dvd.mp hzero,
      (Nat.modEq_iff_dvd' ht).mp hone.symm⟩

theorem rowOneDivisorSplit_iff_modEq_of_one_le {N1 zeroPart onePart t : ℕ}
    (hprod : zeroPart * onePart = N1) (ht : 1 ≤ t) :
    rowOneDivisorSplit N1 zeroPart onePart t ↔
      t ≡ 0 [MOD zeroPart] ∧ t ≡ 1 [MOD onePart] := by
  constructor
  · intro hsplit
    exact
      ⟨rowOneDivisorSplit_modEq_zero hsplit,
        rowOneDivisorSplit_modEq_one_of_one_le hsplit ht⟩
  · intro hmods
    exact rowOneDivisorSplit_of_modEq hprod hmods.1 hmods.2 ht

theorem rowOneDivisorSplit_coprime_of_one_le {N1 zeroPart onePart t : ℕ}
    (hsplit : rowOneDivisorSplit N1 zeroPart onePart t) (ht : 1 ≤ t) :
    zeroPart.Coprime onePart := by
  exact Nat.Coprime.of_dvd hsplit.2.1 hsplit.2.2
    ((Nat.coprime_self_sub_right ht).mpr (by simp))

theorem rowOneDivisorSplit_modEq_chineseRemainder_of_coprime
    {N1 zeroPart onePart t : ℕ} (hcop : zeroPart.Coprime onePart)
    (hsplit : rowOneDivisorSplit N1 zeroPart onePart t) (ht : 1 ≤ t) :
    t ≡ (Nat.chineseRemainder hcop 0 1 : ℕ) [MOD N1] := by
  have hcrt :
      t ≡ (Nat.chineseRemainder hcop 0 1 : ℕ) [MOD zeroPart * onePart] :=
    Nat.chineseRemainder_modEq_unique hcop
      (rowOneDivisorSplit_modEq_zero hsplit)
      (rowOneDivisorSplit_modEq_one_of_one_le hsplit ht)
  simpa [hsplit.1] using hcrt

theorem rowOneDivisorSplit_modEq_unique_of_coprime
    {N1 zeroPart onePart t u : ℕ} (hcop : zeroPart.Coprime onePart)
    (htsplit : rowOneDivisorSplit N1 zeroPart onePart t)
    (husplit : rowOneDivisorSplit N1 zeroPart onePart u) (ht : 1 ≤ t)
    (hu : 1 ≤ u) :
    t ≡ u [MOD N1] := by
  have htcrt :
      t ≡ (Nat.chineseRemainder hcop 0 1 : ℕ) [MOD N1] :=
    rowOneDivisorSplit_modEq_chineseRemainder_of_coprime hcop htsplit ht
  have hucrt :
      u ≡ (Nat.chineseRemainder hcop 0 1 : ℕ) [MOD N1] :=
    rowOneDivisorSplit_modEq_chineseRemainder_of_coprime hcop husplit hu
  exact htcrt.trans hucrt.symm

theorem rowOneDivisorSplit_modEq_unique
    {N1 zeroPart onePart t u : ℕ}
    (htsplit : rowOneDivisorSplit N1 zeroPart onePart t)
    (husplit : rowOneDivisorSplit N1 zeroPart onePart u) (ht : 1 ≤ t)
    (hu : 1 ≤ u) :
    t ≡ u [MOD N1] := by
  exact rowOneDivisorSplit_modEq_unique_of_coprime
    (rowOneDivisorSplit_coprime_of_one_le htsplit ht) htsplit husplit ht hu

theorem rowOneDivisorSplit_eq_of_lt
    {N1 zeroPart onePart t u : ℕ}
    (htsplit : rowOneDivisorSplit N1 zeroPart onePart t)
    (husplit : rowOneDivisorSplit N1 zeroPart onePart u) (ht : 1 ≤ t)
    (hu : 1 ≤ u) (htlt : t < N1) (hult : u < N1) :
    t = u := by
  exact Nat.ModEq.eq_of_lt_of_lt
    (rowOneDivisorSplit_modEq_unique htsplit husplit ht hu) htlt hult

theorem rowOneDivisorSplit_eq_of_half_bound
    {N1 bound zeroPart onePart t u : ℕ} (hbound : bound < 2 * N1)
    (htsplit : rowOneDivisorSplit N1 zeroPart onePart t)
    (husplit : rowOneDivisorSplit N1 zeroPart onePart u) (ht : 1 ≤ t)
    (hu : 1 ≤ u) (htbound : 2 * t ≤ bound) (hubound : 2 * u ≤ bound) :
    t = u := by
  have ht_double_lt : 2 * t < 2 * N1 := lt_of_le_of_lt htbound hbound
  have hu_double_lt : 2 * u < 2 * N1 := lt_of_le_of_lt hubound hbound
  exact rowOneDivisorSplit_eq_of_lt htsplit husplit ht hu
    (Nat.lt_of_mul_lt_mul_left ht_double_lt)
    (Nat.lt_of_mul_lt_mul_left hu_double_lt)

theorem rowOneDivisorSplit_eq_of_consecutiveDivisorKernelBelow_short
    {N1 N2 bound zeroPart onePart t u : ℕ} (hbound : bound < 2 * N1)
    (htsplit : rowOneDivisorSplit N1 zeroPart onePart t)
    (husplit : rowOneDivisorSplit N1 zeroPart onePart u) (ht : 1 ≤ t)
    (hu : 1 ≤ u) (htkernel : consecutiveDivisorKernelBelow N1 N2 bound t)
    (hukernel : consecutiveDivisorKernelBelow N1 N2 bound u) :
    t = u :=
  rowOneDivisorSplit_eq_of_half_bound hbound htsplit husplit ht hu
    htkernel.1 hukernel.1

theorem sub_one_short_bound_of_two_lt {n : ℕ} (hn : 2 < n) :
    n < 2 * (n - 1) := by
  omega

theorem rowOneDivisorSplit_eq_of_sub_one_consecutiveDivisorKernelBelow
    {n N2 zeroPart onePart t u : ℕ} (hn : 2 < n)
    (htsplit : rowOneDivisorSplit (n - 1) zeroPart onePart t)
    (husplit : rowOneDivisorSplit (n - 1) zeroPart onePart u)
    (ht : 1 ≤ t) (hu : 1 ≤ u)
    (htkernel : consecutiveDivisorKernelBelow (n - 1) N2 n t)
    (hukernel : consecutiveDivisorKernelBelow (n - 1) N2 n u) :
    t = u :=
  rowOneDivisorSplit_eq_of_consecutiveDivisorKernelBelow_short
    (sub_one_short_bound_of_two_lt hn) htsplit husplit ht hu htkernel hukernel

theorem rowOneDivisorSplit_kernel_iff_row_two {N1 N2 zeroPart onePart t : ℕ}
    (hsplit : rowOneDivisorSplit N1 zeroPart onePart t) :
    consecutiveDivisorKernel N1 N2 t ↔ N2 ∣ t * (t - 1) * (t - 2) := by
  constructor
  · intro hkernel
    exact hkernel.2
  · intro hrowTwo
    exact ⟨rowOneDivisorSplit_dvd_mul_sub_one hsplit, hrowTwo⟩

theorem not_consecutiveDivisorKernel_of_row_two_gcd_lt {N1 N2 t : ℕ}
    (hgcd : Nat.gcd (t * (t - 1) * (t - 2)) N2 < N2) :
    ¬ consecutiveDivisorKernel N1 N2 t := by
  intro hkernel
  have hgcd_eq :
      Nat.gcd (t * (t - 1) * (t - 2)) N2 = N2 :=
    Nat.gcd_eq_right hkernel.2
  omega

theorem rowOneDivisorSplit_not_consecutiveDivisorKernel_of_row_two_gcd_lt
    {N1 N2 zeroPart onePart t : ℕ}
    (_hsplit : rowOneDivisorSplit N1 zeroPart onePart t)
    (hgcd : Nat.gcd (t * (t - 1) * (t - 2)) N2 < N2) :
    ¬ consecutiveDivisorKernel N1 N2 t :=
  not_consecutiveDivisorKernel_of_row_two_gcd_lt hgcd

theorem not_consecutiveDivisorKernelBelow_of_row_two_gcd_lt {N1 N2 bound t : ℕ}
    (hgcd : Nat.gcd (t * (t - 1) * (t - 2)) N2 < N2) :
    ¬ consecutiveDivisorKernelBelow N1 N2 bound t := by
  intro hkernel
  exact not_consecutiveDivisorKernel_of_row_two_gcd_lt hgcd hkernel.2

theorem rowOneDivisorSplit_not_consecutiveDivisorKernelBelow_of_row_two_gcd_lt
    {N1 N2 zeroPart onePart bound t : ℕ}
    (_hsplit : rowOneDivisorSplit N1 zeroPart onePart t)
    (hgcd : Nat.gcd (t * (t - 1) * (t - 2)) N2 < N2) :
    ¬ consecutiveDivisorKernelBelow N1 N2 bound t :=
  not_consecutiveDivisorKernelBelow_of_row_two_gcd_lt hgcd

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

theorem divisor_dvd_i_three_window_two_product_of_forall_prime_ge_five {d n j : ℕ}
    (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor n 3 j q)
    (hd0 : d ≠ 0) (hdn : d ∣ n - 2)
    (hrel : ∀ p : ℕ, p.Prime → p ∣ d → 5 ≤ p) (hn : 2 < n) :
    d ∣ j * (j - 1) * (j - 2) := by
  have hd_eq : primePowerPartGE 5 d = d := by
    exact primePowerPartGE_eq_self_of_forall_prime_ge hd0 hrel
  rw [← hd_eq]
  apply primePowerPartGE_dvd_of_forall_prime_power_dvd
  intro p hp hp5 _hpdvd
  have hpow_dvd_d : p ^ d.factorization p ∣ d :=
    (hp.pow_dvd_iff_le_factorization hd0).mpr le_rfl
  have hpow_dvd_sub_two : p ^ d.factorization p ∣ n - 2 :=
    Nat.dvd_trans hpow_dvd_d hdn
  exact i_three_window_two_prime_pow_dvd_mul_sub_one_sub_two
    hnone hp hp5 hn hpow_dvd_sub_two

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

theorem i_three_caseI_row_one_exists_factor {n F X j t : ℕ}
    (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor n 3 j q)
    (hn : n = F * X) (hj : j = F * t) (hn_gt : 2 < n) (hj_pos : 0 < j)
    (h2n : 2 ∣ n) (h3n : 3 ∣ n) (htX : t ≤ X) :
    ∃ g : ℕ, t * (X - t) = g * (n - 1) := by
  rcases i_three_caseI_row_one_sub_one_dvd_t_mul_X_sub_t
      hnone hn hj hn_gt hj_pos h2n h3n htX with ⟨g, hg⟩
  exact ⟨g, by simpa [mul_comm] using hg⟩

theorem central_branch_false_of_sub_one_dvd_t_mul_X_sub_t {n F X t : ℕ}
    (hn : n = F * X) (hn_gt : 2 < n) (hcentral : 2 * t = X)
    (hdvd : n - 1 ∣ t * (X - t)) : False := by
  have hcop_n : (n - 1).Coprime n := by
    have hsucc : n = (n - 1) + 1 := by omega
    rw [hsucc]
    exact Nat.coprime_self_add_right.mpr (by simp)
  have hX_dvd_n : X ∣ n := by
    rw [hn]
    exact dvd_mul_left X F
  have hcop_X : (n - 1).Coprime X :=
    Nat.Coprime.coprime_dvd_right hX_dvd_n hcop_n
  have ht_dvd_X : t ∣ X := by
    refine ⟨2, ?_⟩
    omega
  have hcop_t : (n - 1).Coprime t :=
    Nat.Coprime.coprime_dvd_right ht_dvd_X hcop_X
  have hXt : X - t = t := by omega
  have hdvd_tt : n - 1 ∣ t * t := by
    simpa [hXt] using hdvd
  have hdvd_t : n - 1 ∣ t := hcop_t.dvd_of_dvd_mul_left hdvd_tt
  have hself : (n - 1).Coprime (n - 1) :=
    Nat.Coprime.coprime_dvd_right hdvd_t hcop_t
  have hnm1_eq_one : n - 1 = 1 := by
    exact (Nat.coprime_self (n - 1)).mp hself
  omega

theorem i_three_caseI_central_branch_false {n F X j t : ℕ}
    (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor n 3 j q)
    (hn : n = F * X) (hj : j = F * t) (hn_gt : 2 < n) (hj_pos : 0 < j)
    (h2n : 2 ∣ n) (h3n : 3 ∣ n) (hcentral : 2 * t = X) : False :=
  central_branch_false_of_sub_one_dvd_t_mul_X_sub_t hn hn_gt hcentral
    (i_three_caseI_row_one_sub_one_dvd_t_mul_X_sub_t
      hnone hn hj hn_gt hj_pos h2n h3n (by omega : t ≤ X))

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

theorem four_mul_factor_le_of_even_four_le_of_four_mul_sub_one_le_sq {n F X : ℕ}
    (hn : n = F * X) (hX_even : 2 ∣ X) (hX_four : 4 ≤ X)
    (hsize : 4 * (n - 1) ≤ X * X) :
    4 * F ≤ X := by
  by_contra hnot
  have hlt : X < 4 * F := Nat.lt_of_not_ge hnot
  have hn_pos : 0 < n := by
    subst n
    have hF_pos : 0 < F := by omega
    have hX_pos : 0 < X := by omega
    exact Nat.mul_pos hF_pos hX_pos
  have hcast_sub : ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 :=
    Nat.cast_sub (by omega : 1 ≤ n)
  have hsize_int : (4 : ℤ) * ((n : ℤ) - 1) ≤ (X : ℤ) * (X : ℤ) := by
    have h := hsize
    have hcast : ((4 * (n - 1) : ℕ) : ℤ) = (4 : ℤ) * ((n : ℤ) - 1) := by
      rw [Nat.cast_mul, hcast_sub]
      norm_num
    have hcast_right : ((X * X : ℕ) : ℤ) = (X : ℤ) * (X : ℤ) := by norm_num
    exact hcast ▸ hcast_right ▸ (by exact_mod_cast h)
  have hn_int : (n : ℤ) = (F : ℤ) * (X : ℤ) := by exact_mod_cast hn
  have hdiff_ge_two_nat : 2 ≤ 4 * F - X := by
    rcases hX_even with ⟨a, ha⟩
    subst X
    have hdiff_pos : 0 < 4 * F - 2 * a := by omega
    have hdiff_even : 2 ∣ 4 * F - 2 * a := by
      refine ⟨2 * F - a, ?_⟩
      omega
    rcases hdiff_even with ⟨b, hb⟩
    have hb_pos : 0 < b := by omega
    omega
  have hcast_diff : ((4 * F - X : ℕ) : ℤ) = (4 : ℤ) * (F : ℤ) - (X : ℤ) :=
    Nat.cast_sub hlt.le
  have hdiff_ge_two : (2 : ℤ) ≤ (4 : ℤ) * (F : ℤ) - (X : ℤ) := by
    have h : (2 : ℤ) ≤ ((4 * F - X : ℕ) : ℤ) := by
      exact_mod_cast hdiff_ge_two_nat
    simpa [hcast_diff] using h
  have hX_four_int : (4 : ℤ) ≤ X := by exact_mod_cast hX_four
  nlinarith

theorem four_dvd_right_factor_of_four_dvd_mul_odd {F X : ℕ}
    (hFodd : Odd F) (h4 : 4 ∣ F * X) :
    4 ∣ X := by
  have h2mul : 2 ∣ F * X := Nat.dvd_trans (by norm_num : 2 ∣ 4) h4
  have h2X : 2 ∣ X := by
    rcases (by decide : Nat.Prime 2).dvd_mul.mp h2mul with h2F | h2X
    · have hnot_odd : ¬ Odd F :=
        Nat.not_odd_iff_even.mpr (even_iff_two_dvd.mpr h2F)
      exact False.elim (hnot_odd hFodd)
    · exact h2X
  rcases h2X with ⟨Y, hX⟩
  subst X
  have h2FY : 2 ∣ F * Y := by
    rcases h4 with ⟨a, ha⟩
    refine ⟨a, ?_⟩
    have hdouble : F * Y * 2 = (2 * a) * 2 := by
      calc
        F * Y * 2 = F * (2 * Y) := by ring
        _ = 4 * a := ha
        _ = (2 * a) * 2 := by ring
    exact Nat.mul_right_cancel (by decide : 0 < 2) hdouble
  have h2Y : 2 ∣ Y := by
    rcases (by decide : Nat.Prime 2).dvd_mul.mp h2FY with h2F | h2Y
    · have hnot_odd : ¬ Odd F :=
        Nat.not_odd_iff_even.mpr (even_iff_two_dvd.mpr h2F)
      exact False.elim (hnot_odd hFodd)
    · exact h2Y
  rcases h2Y with ⟨Z, hY⟩
  refine ⟨Z, ?_⟩
  omega

theorem i_three_caseI_row_one_four_mul_factor_le_X {n F X j t : ℕ}
    (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor n 3 j q)
    (hn : n = F * X) (hj : j = F * t) (hn_gt : 2 < n) (hj_pos : 0 < j)
    (h2n : 2 ∣ n) (h3n : 3 ∣ n) (hX_even : 2 ∣ X) (hX_four : 4 ≤ X)
    (h2tX : 2 * t ≤ X) :
    4 * F ≤ X :=
  four_mul_factor_le_of_even_four_le_of_four_mul_sub_one_le_sq hn hX_even hX_four
    (i_three_caseI_row_one_four_mul_sub_one_le_X_sq
      hnone hn hj hn_gt hj_pos h2n h3n h2tX)

theorem dvd_factor_mul_of_eq_mul_and_coprime {d e a b g : ℕ}
    (ha : a = g * d) (hcop : e.Coprime d) (hedvd : e ∣ a * b) :
    e ∣ g * b := by
  have hdiv : e ∣ (g * b) * d := by
    simpa [ha, mul_assoc, mul_comm, mul_left_comm] using hedvd
  exact hcop.dvd_of_dvd_mul_right hdiv

theorem exists_factor_dvd_factor_mul_of_dvd_and_coprime {d e a b : ℕ}
    (hda : d ∣ a) (hcop : e.Coprime d) (hedvd : e ∣ a * b) :
    ∃ g : ℕ, a = g * d ∧ e ∣ g * b := by
  rcases hda with ⟨g, hg⟩
  refine ⟨g, ?_, ?_⟩
  · simpa [mul_comm] using hg
  · exact dvd_factor_mul_of_eq_mul_and_coprime (by simpa [mul_comm] using hg) hcop hedvd

theorem primePowerPartGE_five_sub_two_coprime_sub_one {n : ℕ} (hn : 2 < n) :
    (primePowerPartGE 5 (n - 2)).Coprime (n - 1) := by
  have hbase : (n - 2).Coprime (n - 1) := by
    have hsucc : n - 1 = (n - 2) + 1 := by omega
    rw [hsucc]
    exact Nat.coprime_self_add_right.mpr (by simp)
  exact Nat.Coprime.coprime_dvd_left
    (primePowerPartGE_dvd_self (by omega : n - 2 ≠ 0)) hbase

theorem half_sub_one_dvd_sub_two_of_even {n : ℕ} (h2n : 2 ∣ n) :
    n / 2 - 1 ∣ n - 2 := by
  rcases h2n with ⟨m, hm⟩
  subst n
  refine ⟨2, ?_⟩
  omega

theorem half_sub_one_ne_zero_of_even {n : ℕ} (h2n : 2 ∣ n) (hn : 2 < n) :
    n / 2 - 1 ≠ 0 := by
  rcases h2n with ⟨m, hm⟩
  subst n
  omega

theorem half_sub_one_ne_zero_of_even_three_dvd {n : ℕ}
    (h2n : 2 ∣ n) (h3n : 3 ∣ n) (hn : 2 < n) :
    n / 2 - 1 ≠ 0 := by
  rcases h2n with ⟨m, hm⟩
  subst n
  have h3m : 3 ∣ m := by
    have h3_two_mul : 3 ∣ 2 * m := by simpa [mul_comm] using h3n
    rcases (by decide : Nat.Prime 3).dvd_mul.mp h3_two_mul with h32 | h3m
    · norm_num at h32
    · exact h3m
  rcases h3m with ⟨a, ha⟩
  omega

theorem not_two_dvd_of_coprime_four {d : ℕ} (hcop4 : d.Coprime 4) :
    ¬ 2 ∣ d := by
  intro h2d
  have h2g : 2 ∣ Nat.gcd d 4 := Nat.dvd_gcd h2d (by norm_num : 2 ∣ 4)
  have hgcd : Nat.gcd d 4 = 1 := hcop4.gcd_eq_one
  rw [hgcd] at h2g
  norm_num at h2g

theorem not_three_dvd_half_sub_one_of_even_three_dvd {n : ℕ}
    (h2n : 2 ∣ n) (h3n : 3 ∣ n) (hn : 2 < n) :
    ¬ 3 ∣ n / 2 - 1 := by
  rcases h2n with ⟨m, hm⟩
  subst n
  have h3m : 3 ∣ m := by
    have h3_two_mul : 3 ∣ 2 * m := by simpa [mul_comm] using h3n
    rcases (by decide : Nat.Prime 3).dvd_mul.mp h3_two_mul with h32 | h3m
    · norm_num at h32
    · exact h3m
  intro h
  rcases h3m with ⟨a, ha⟩
  rcases h with ⟨b, hb⟩
  omega

theorem half_sub_one_prime_ge_five_of_even_three_dvd_coprime_four {n : ℕ}
    (h2n : 2 ∣ n) (h3n : 3 ∣ n) (hn : 2 < n)
    (hcop4 : (n / 2 - 1).Coprime 4) :
    ∀ p : ℕ, p.Prime → p ∣ n / 2 - 1 → 5 ≤ p := by
  intro p hp hpd
  by_cases hp2 : p = 2
  · subst p
    exact False.elim (not_two_dvd_of_coprime_four hcop4 hpd)
  by_cases hp3 : p = 3
  · subst p
    exact False.elim (not_three_dvd_half_sub_one_of_even_three_dvd h2n h3n hn hpd)
  have hp4 : p ≠ 4 := by
    intro hp_eq
    subst p
    exact (by decide : ¬ Nat.Prime 4) hp
  have hp2le : 2 ≤ p := hp.two_le
  omega

theorem half_sub_one_coprime_sub_one_of_even {n : ℕ}
    (h2n : 2 ∣ n) (hn : 2 < n) :
    (n / 2 - 1).Coprime (n - 1) := by
  rcases h2n with ⟨m, hm⟩
  subst n
  have hdiv : 2 * m / 2 = m := by omega
  have hsub_one : 2 * m - 1 = (m - 1) + ((m - 1) + 1) := by omega
  have hbase : (m - 1).Coprime ((m - 1) + 1) :=
    Nat.coprime_self_add_right.mpr (by simp)
  have htarget : (m - 1).Coprime ((m - 1) + ((m - 1) + 1)) :=
    Nat.coprime_self_add_right.mpr hbase
  rw [hdiv, hsub_one]
  exact htarget

theorem half_sub_one_coprime_four_of_four_dvd {n : ℕ}
    (h4n : 4 ∣ n) (hn : 2 < n) :
    (n / 2 - 1).Coprime 4 := by
  rcases h4n with ⟨m, hm⟩
  subst n
  have hdiv : 4 * m / 2 = 2 * m := by omega
  rw [hdiv]
  apply Nat.coprime_of_dvd
  intro p hp hpd hp4
  have hp_eq_two : p = 2 := by
    have hp_le_four : p ≤ 4 := Nat.le_of_dvd (by norm_num : 0 < 4) hp4
    interval_cases p
    · exact False.elim ((by decide : ¬ Nat.Prime 0) hp)
    · exact False.elim ((by decide : ¬ Nat.Prime 1) hp)
    · rfl
    · exact False.elim (by norm_num at hp4)
    · exact False.elim ((by decide : ¬ Nat.Prime 4) hp)
  subst p
  rcases hpd with ⟨a, ha⟩
  omega

theorem primePowerPartGE_five_half_sub_one_eq_self_of_four_dvd_three_dvd {n : ℕ}
    (h4n : 4 ∣ n) (h3n : 3 ∣ n) (hn : 2 < n) :
    primePowerPartGE 5 (n / 2 - 1) = n / 2 - 1 := by
  have h2n : 2 ∣ n := Nat.dvd_trans (by norm_num : 2 ∣ 4) h4n
  exact primePowerPartGE_eq_self_of_forall_prime_ge
    (half_sub_one_ne_zero_of_even h2n hn)
    (half_sub_one_prime_ge_five_of_even_three_dvd_coprime_four h2n h3n hn
      (half_sub_one_coprime_four_of_four_dvd h4n hn))

theorem primePowerPartGE_five_half_sub_one_coprime_sub_one {n : ℕ}
    (h2n : 2 ∣ n) (hn : 2 < n) :
    (primePowerPartGE 5 (n / 2 - 1)).Coprime (n - 1) :=
  Nat.Coprime.coprime_dvd_left
    (primePowerPartGE_dvd_self (half_sub_one_ne_zero_of_even h2n hn))
    (half_sub_one_coprime_sub_one_of_even h2n hn)

theorem i_three_caseI_half_sub_one_large_part_dvd_row_two_product {n j : ℕ}
    (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor n 3 j q)
    (h2n : 2 ∣ n) (hn : 2 < n) :
    primePowerPartGE 5 (n / 2 - 1) ∣ j * (j - 1) * (j - 2) := by
  apply primePowerPartGE_dvd_of_forall_prime_power_dvd
  intro p hp hp5 _hpdvd
  have hhalf_ne : n / 2 - 1 ≠ 0 := half_sub_one_ne_zero_of_even h2n hn
  have hpow_dvd_half : p ^ (n / 2 - 1).factorization p ∣ n / 2 - 1 :=
    (hp.pow_dvd_iff_le_factorization hhalf_ne).mpr le_rfl
  have hpow_dvd_sub_two : p ^ (n / 2 - 1).factorization p ∣ n - 2 :=
    Nat.dvd_trans hpow_dvd_half (half_sub_one_dvd_sub_two_of_even h2n)
  exact i_three_window_two_prime_pow_dvd_mul_sub_one_sub_two
    hnone hp hp5 hn hpow_dvd_sub_two

theorem i_three_caseI_half_sub_one_dvd_row_two_product {n j : ℕ}
    (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor n 3 j q)
    (h2n : 2 ∣ n) (h3n : 3 ∣ n) (hn : 2 < n)
    (hcop4 : (n / 2 - 1).Coprime 4) :
    n / 2 - 1 ∣ j * (j - 1) * (j - 2) :=
  divisor_dvd_i_three_window_two_product_of_forall_prime_ge_five hnone
    (half_sub_one_ne_zero_of_even_three_dvd h2n h3n hn)
    (half_sub_one_dvd_sub_two_of_even h2n)
    (half_sub_one_prime_ge_five_of_even_three_dvd_coprime_four h2n h3n hn hcop4)
    hn

theorem i_three_caseI_four_dvd_consecutive_kernel_below_from_no_common {n j : ℕ}
    (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor n 3 j q)
    (hn_gt : 2 < n) (h2n : 2 ∣ n) (h3n : 3 ∣ n) (h4n : 4 ∣ n)
    (hjn : 2 * j ≤ n) :
    (n - 1).Coprime (n / 2 - 1) ∧
      consecutiveDivisorKernelBelow (n - 1) (n / 2 - 1) n j := by
  have hcop : (n - 1).Coprime (n / 2 - 1) :=
    (half_sub_one_coprime_sub_one_of_even h2n hn_gt).symm
  have hrow1 : n - 1 ∣ j * (j - 1) :=
    i_three_window_one_sub_one_dvd_mul_sub_one_of_even_three_dvd
      hnone (by omega : 1 < n) h2n h3n
  have hrow2 : n / 2 - 1 ∣ j * (j - 1) * (j - 2) :=
    i_three_caseI_half_sub_one_dvd_row_two_product hnone h2n h3n hn_gt
      (half_sub_one_coprime_four_of_four_dvd h4n hn_gt)
  refine ⟨hcop, ?_⟩
  exact ⟨hjn, hrow1, hrow2⟩

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

theorem i_three_caseI_row_two_half_sub_one_dvd_t_mul_X_sub_t_mul_X_sub_two_t
    {n F X j t : ℕ} (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor n 3 j q)
    (hn : n = F * X) (hj : j = F * t) (hn_gt : 2 < n) (hj_two : 2 ≤ j)
    (h2n : 2 ∣ n) (h3n : 3 ∣ n) (hcop4 : (n / 2 - 1).Coprime 4)
    (htX : t ≤ X) (h2tX : 2 * t ≤ X) :
    n / 2 - 1 ∣ t * (X - t) * (X - 2 * t) :=
  sub_two_divisor_dvd_t_mul_X_sub_t_mul_X_sub_two_t_of_factor_dvd_triple
    (half_sub_one_dvd_sub_two_of_even h2n) hcop4 hn hj (by omega : 2 ≤ n)
    hj_two htX h2tX
    (i_three_caseI_half_sub_one_dvd_row_two_product hnone h2n h3n hn_gt hcop4)

theorem i_three_caseI_row_two_half_sub_one_large_part_dvd_t_mul_X_sub_t_mul_X_sub_two_t
    {n F X j t : ℕ} (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor n 3 j q)
    (hn : n = F * X) (hj : j = F * t) (hn_gt : 2 < n) (hj_two : 2 ≤ j)
    (h2n : 2 ∣ n) (htX : t ≤ X) (h2tX : 2 * t ≤ X) :
    primePowerPartGE 5 (n / 2 - 1) ∣ t * (X - t) * (X - 2 * t) := by
  have hlarge_dvd_sub_two : primePowerPartGE 5 (n / 2 - 1) ∣ n - 2 :=
    Nat.dvd_trans
      (primePowerPartGE_dvd_self (half_sub_one_ne_zero_of_even h2n hn_gt))
      (half_sub_one_dvd_sub_two_of_even h2n)
  exact sub_two_divisor_dvd_t_mul_X_sub_t_mul_X_sub_two_t_of_factor_dvd_triple
    hlarge_dvd_sub_two (primePowerPartGE_five_coprime_four (n / 2 - 1))
    hn hj (by omega : 2 ≤ n) hj_two htX h2tX
    (i_three_caseI_half_sub_one_large_part_dvd_row_two_product hnone h2n hn_gt)

theorem i_three_caseI_joint_large_part_dvd_factor_mul_X_sub_two_t {n F X j t g : ℕ}
    (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor n 3 j q)
    (hn : n = F * X) (hj : j = F * t) (hn_ge_two : 2 ≤ n) (hn_gt_two : 2 < n)
    (hj_two : 2 ≤ j) (htX : t ≤ X) (h2tX : 2 * t ≤ X)
    (hrow1 : t * (X - t) = g * (n - 1)) :
    primePowerPartGE 5 (n - 2) ∣ g * (X - 2 * t) :=
  dvd_factor_mul_of_eq_mul_and_coprime hrow1
    (primePowerPartGE_five_sub_two_coprime_sub_one hn_gt_two)
    (i_three_caseI_row_two_primePowerPartGE_dvd_t_mul_X_sub_t_mul_X_sub_two_t
      hnone hn hj hn_ge_two hn_gt_two hj_two htX h2tX)

theorem i_three_caseI_joint_half_sub_one_dvd_factor_mul_X_sub_two_t {n F X j t g : ℕ}
    (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor n 3 j q)
    (hn : n = F * X) (hj : j = F * t) (hn_gt : 2 < n) (hj_two : 2 ≤ j)
    (h2n : 2 ∣ n) (h3n : 3 ∣ n) (hcop4 : (n / 2 - 1).Coprime 4)
    (htX : t ≤ X) (h2tX : 2 * t ≤ X)
    (hrow1 : t * (X - t) = g * (n - 1)) :
    n / 2 - 1 ∣ g * (X - 2 * t) :=
  dvd_factor_mul_of_eq_mul_and_coprime hrow1
    (half_sub_one_coprime_sub_one_of_even h2n hn_gt)
    (i_three_caseI_row_two_half_sub_one_dvd_t_mul_X_sub_t_mul_X_sub_two_t
      hnone hn hj hn_gt hj_two h2n h3n hcop4 htX h2tX)

theorem i_three_caseI_joint_half_sub_one_large_part_dvd_factor_mul_X_sub_two_t
    {n F X j t g : ℕ} (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor n 3 j q)
    (hn : n = F * X) (hj : j = F * t) (hn_gt : 2 < n) (hj_two : 2 ≤ j)
    (h2n : 2 ∣ n) (htX : t ≤ X) (h2tX : 2 * t ≤ X)
    (hrow1 : t * (X - t) = g * (n - 1)) :
    primePowerPartGE 5 (n / 2 - 1) ∣ g * (X - 2 * t) :=
  dvd_factor_mul_of_eq_mul_and_coprime hrow1
    (primePowerPartGE_five_half_sub_one_coprime_sub_one h2n hn_gt)
    (i_three_caseI_row_two_half_sub_one_large_part_dvd_t_mul_X_sub_t_mul_X_sub_two_t
      hnone hn hj hn_gt hj_two h2n htX h2tX)

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

theorem i_three_caseI_joint_half_sub_one_large_part_le_factor_mul_X_sub_two_t
    {n F X j t g : ℕ} (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor n 3 j q)
    (hn : n = F * X) (hj : j = F * t) (hn_gt : 2 < n)
    (hj_two : 2 ≤ j) (h2n : 2 ∣ n) (hrow1 : t * (X - t) = g * (n - 1))
    (hbranch : 0 < X - 2 * t) :
    primePowerPartGE 5 (n / 2 - 1) ≤ g * (X - 2 * t) := by
  have hdvd : primePowerPartGE 5 (n / 2 - 1) ∣ g * (X - 2 * t) :=
    i_three_caseI_joint_half_sub_one_large_part_dvd_factor_mul_X_sub_two_t
      hnone hn hj hn_gt hj_two h2n (by omega : t ≤ X) (by omega : 2 * t ≤ X)
      hrow1
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

theorem i_three_caseI_joint_large_part_gap_bound {n F X j t g : ℕ}
    (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor n 3 j q)
    (hn : n = F * X) (hj : j = F * t) (hn_gt : 2 < n)
    (hj_two : 2 ≤ j) (hrow1 : t * (X - t) = g * (n - 1))
    (hbranch : 0 < X - 2 * t) :
    4 * ((n - 1) * primePowerPartGE 5 (n - 2)) ≤ X * X * (X - 2 * t) := by
  have hlarge :
      primePowerPartGE 5 (n - 2) ≤ g * (X - 2 * t) :=
    i_three_caseI_joint_large_part_le_factor_mul_X_sub_two_t
      hnone hn hj hn_gt hj_two hrow1 hbranch
  have hrow_bound : 4 * (g * (n - 1)) ≤ X * X := by
    simpa [hrow1] using four_mul_t_mul_X_sub_t_le_sq (by omega : 2 * t ≤ X)
  calc
    4 * ((n - 1) * primePowerPartGE 5 (n - 2))
        ≤ 4 * ((n - 1) * (g * (X - 2 * t))) := by
          exact Nat.mul_le_mul_left 4 (Nat.mul_le_mul_left (n - 1) hlarge)
    _ = (4 * (g * (n - 1))) * (X - 2 * t) := by ring
    _ ≤ (X * X) * (X - 2 * t) := by
          exact Nat.mul_le_mul_right (X - 2 * t) hrow_bound
    _ = X * X * (X - 2 * t) := by ring

theorem i_three_caseI_joint_half_sub_one_large_part_gap_bound {n F X j t g : ℕ}
    (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor n 3 j q)
    (hn : n = F * X) (hj : j = F * t) (hn_gt : 2 < n)
    (hj_two : 2 ≤ j) (h2n : 2 ∣ n) (hrow1 : t * (X - t) = g * (n - 1))
    (hbranch : 0 < X - 2 * t) :
    4 * ((n - 1) * primePowerPartGE 5 (n / 2 - 1)) ≤ X * X * (X - 2 * t) := by
  have hlarge : primePowerPartGE 5 (n / 2 - 1) ≤ g * (X - 2 * t) :=
    i_three_caseI_joint_half_sub_one_large_part_le_factor_mul_X_sub_two_t
      hnone hn hj hn_gt hj_two h2n hrow1 hbranch
  have hrow_bound : 4 * (g * (n - 1)) ≤ X * X := by
    simpa [hrow1] using four_mul_t_mul_X_sub_t_le_sq (by omega : 2 * t ≤ X)
  calc
    4 * ((n - 1) * primePowerPartGE 5 (n / 2 - 1))
        ≤ 4 * ((n - 1) * (g * (X - 2 * t))) := by
          exact Nat.mul_le_mul_left 4 (Nat.mul_le_mul_left (n - 1) hlarge)
    _ = (4 * (g * (n - 1))) * (X - 2 * t) := by ring
    _ ≤ (X * X) * (X - 2 * t) := by
          exact Nat.mul_le_mul_right (X - 2 * t) hrow_bound
    _ = X * X * (X - 2 * t) := by ring

theorem i_three_caseI_joint_large_part_cube_bound {n F X j t g : ℕ}
    (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor n 3 j q)
    (hn : n = F * X) (hj : j = F * t) (hn_gt : 2 < n)
    (hj_two : 2 ≤ j) (hrow1 : t * (X - t) = g * (n - 1))
    (hbranch : 0 < X - 2 * t) :
    4 * ((n - 1) * primePowerPartGE 5 (n - 2)) ≤ X * X * X := by
  have hgap :=
    i_three_caseI_joint_large_part_gap_bound hnone hn hj hn_gt hj_two hrow1 hbranch
  have hgap_le : X - 2 * t ≤ X := Nat.sub_le X (2 * t)
  exact hgap.trans (by
    simpa [mul_assoc] using Nat.mul_le_mul_left (X * X) hgap_le)

theorem i_three_caseI_joint_half_sub_one_large_part_cube_bound {n F X j t g : ℕ}
    (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor n 3 j q)
    (hn : n = F * X) (hj : j = F * t) (hn_gt : 2 < n)
    (hj_two : 2 ≤ j) (h2n : 2 ∣ n) (hrow1 : t * (X - t) = g * (n - 1))
    (hbranch : 0 < X - 2 * t) :
    4 * ((n - 1) * primePowerPartGE 5 (n / 2 - 1)) ≤ X * X * X := by
  have hgap :=
    i_three_caseI_joint_half_sub_one_large_part_gap_bound
      hnone hn hj hn_gt hj_two h2n hrow1 hbranch
  have hgap_le : X - 2 * t ≤ X := Nat.sub_le X (2 * t)
  exact hgap.trans (by
    simpa [mul_assoc] using Nat.mul_le_mul_left (X * X) hgap_le)

theorem i_three_caseI_exists_joint_half_sub_one_large_part_cube_bound {n F X j t : ℕ}
    (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor n 3 j q)
    (hn : n = F * X) (hj : j = F * t) (hn_gt : 2 < n) (hj_pos : 0 < j)
    (hj_two : 2 ≤ j) (h2n : 2 ∣ n) (h3n : 3 ∣ n) (hbranch : 0 < X - 2 * t) :
    ∃ g : ℕ,
      t * (X - t) = g * (n - 1) ∧
        primePowerPartGE 5 (n / 2 - 1) ∣ g * (X - 2 * t) ∧
          primePowerPartGE 5 (n / 2 - 1) ≤ g * (X - 2 * t) ∧
            4 * ((n - 1) * primePowerPartGE 5 (n / 2 - 1)) ≤ X * X * X := by
  rcases i_three_caseI_row_one_exists_factor
      hnone hn hj hn_gt hj_pos h2n h3n (by omega : t ≤ X) with ⟨g, hrow1⟩
  exact ⟨g, hrow1,
    i_three_caseI_joint_half_sub_one_large_part_dvd_factor_mul_X_sub_two_t
      hnone hn hj hn_gt hj_two h2n (by omega : t ≤ X) (by omega : 2 * t ≤ X)
      hrow1,
    i_three_caseI_joint_half_sub_one_large_part_le_factor_mul_X_sub_two_t
      hnone hn hj hn_gt hj_two h2n hrow1 hbranch,
    i_three_caseI_joint_half_sub_one_large_part_cube_bound
      hnone hn hj hn_gt hj_two h2n hrow1 hbranch⟩

theorem i_three_caseI_noncentral_half_sub_one_large_part_cube_bound {n F X j t : ℕ}
    (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor n 3 j q)
    (hn : n = F * X) (hj : j = F * t) (hn_gt : 2 < n) (hj_pos : 0 < j)
    (hj_two : 2 ≤ j) (h2n : 2 ∣ n) (h3n : 3 ∣ n) (hbranch : 0 < X - 2 * t) :
    4 * ((n - 1) * primePowerPartGE 5 (n / 2 - 1)) ≤ X * X * X := by
  rcases i_three_caseI_exists_joint_half_sub_one_large_part_cube_bound
      hnone hn hj hn_gt hj_pos hj_two h2n h3n hbranch with
    ⟨_g, _hrow1, _hdvd, _hle, hcube⟩
  exact hcube

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

theorem i_three_caseI_exists_joint_large_part_gap_bound {n F X j t : ℕ}
    (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor n 3 j q)
    (hn : n = F * X) (hj : j = F * t) (hn_gt : 2 < n) (hj_pos : 0 < j)
    (hj_two : 2 ≤ j) (h2n : 2 ∣ n) (h3n : 3 ∣ n) (hbranch : 0 < X - 2 * t) :
    ∃ g : ℕ,
      t * (X - t) = g * (n - 1) ∧
        primePowerPartGE 5 (n - 2) ∣ g * (X - 2 * t) ∧
          primePowerPartGE 5 (n - 2) ≤ g * (X - 2 * t) ∧
            4 * ((n - 1) * primePowerPartGE 5 (n - 2)) ≤
              X * X * (X - 2 * t) := by
  rcases i_three_caseI_exists_joint_large_part_factor_le
      hnone hn hj hn_gt hj_pos hj_two h2n h3n hbranch with
    ⟨g, hrow1, hdvd, hle⟩
  exact ⟨g, hrow1, hdvd, hle,
    i_three_caseI_joint_large_part_gap_bound hnone hn hj hn_gt hj_two hrow1 hbranch⟩

theorem i_three_caseI_exists_joint_large_part_cube_bound {n F X j t : ℕ}
    (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor n 3 j q)
    (hn : n = F * X) (hj : j = F * t) (hn_gt : 2 < n) (hj_pos : 0 < j)
    (hj_two : 2 ≤ j) (h2n : 2 ∣ n) (h3n : 3 ∣ n) (hbranch : 0 < X - 2 * t) :
    ∃ g : ℕ,
      t * (X - t) = g * (n - 1) ∧
        primePowerPartGE 5 (n - 2) ∣ g * (X - 2 * t) ∧
          primePowerPartGE 5 (n - 2) ≤ g * (X - 2 * t) ∧
            4 * ((n - 1) * primePowerPartGE 5 (n - 2)) ≤ X * X * X := by
  rcases i_three_caseI_exists_joint_large_part_gap_bound
      hnone hn hj hn_gt hj_pos hj_two h2n h3n hbranch with
    ⟨g, hrow1, hdvd, hle, _hgap⟩
  exact ⟨g, hrow1, hdvd, hle,
    i_three_caseI_joint_large_part_cube_bound hnone hn hj hn_gt hj_two hrow1 hbranch⟩

theorem i_three_caseI_joint_lower_part_cube_bound {n F X j t g L : ℕ}
    (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor n 3 j q)
    (hn : n = F * X) (hj : j = F * t) (hn_gt : 2 < n)
    (hj_two : 2 ≤ j) (hrow1 : t * (X - t) = g * (n - 1))
    (hbranch : 0 < X - 2 * t) (hL : L ≤ primePowerPartGE 5 (n - 2)) :
    4 * ((n - 1) * L) ≤ X * X * X := by
  have hcube :=
    i_three_caseI_joint_large_part_cube_bound hnone hn hj hn_gt hj_two hrow1 hbranch
  exact (Nat.mul_le_mul_left 4 (Nat.mul_le_mul_left (n - 1) hL)).trans hcube

theorem i_three_caseI_joint_half_sub_one_cube_bound {n F X j t g : ℕ}
    (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor n 3 j q)
    (hn : n = F * X) (hj : j = F * t) (hn_gt : 2 < n)
    (hj_two : 2 ≤ j) (hrow1 : t * (X - t) = g * (n - 1))
    (hbranch : 0 < X - 2 * t)
    (hhalf : n / 2 - 1 ≤ primePowerPartGE 5 (n - 2)) :
    4 * ((n - 1) * (n / 2 - 1)) ≤ X * X * X :=
  i_three_caseI_joint_lower_part_cube_bound hnone hn hj hn_gt hj_two hrow1 hbranch hhalf

theorem i_three_caseI_exists_joint_half_sub_one_cube_bound {n F X j t : ℕ}
    (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor n 3 j q)
    (hn : n = F * X) (hj : j = F * t) (hn_gt : 2 < n) (hj_pos : 0 < j)
    (hj_two : 2 ≤ j) (h2n : 2 ∣ n) (h3n : 3 ∣ n) (hbranch : 0 < X - 2 * t)
    (hhalf : n / 2 - 1 ≤ primePowerPartGE 5 (n - 2)) :
    ∃ g : ℕ,
      t * (X - t) = g * (n - 1) ∧
        primePowerPartGE 5 (n - 2) ∣ g * (X - 2 * t) ∧
          primePowerPartGE 5 (n - 2) ≤ g * (X - 2 * t) ∧
            4 * ((n - 1) * (n / 2 - 1)) ≤ X * X * X := by
  rcases i_three_caseI_exists_joint_large_part_factor_le
      hnone hn hj hn_gt hj_pos hj_two h2n h3n hbranch with
    ⟨g, hrow1, hdvd, hle⟩
  exact ⟨g, hrow1, hdvd, hle,
    i_three_caseI_joint_half_sub_one_cube_bound
      hnone hn hj hn_gt hj_two hrow1 hbranch hhalf⟩

theorem i_three_caseI_noncentral_half_sub_one_cube_bound {n F X j t : ℕ}
    (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor n 3 j q)
    (hn : n = F * X) (hj : j = F * t) (hn_gt : 2 < n) (hj_pos : 0 < j)
    (hj_two : 2 ≤ j) (h2n : 2 ∣ n) (h3n : 3 ∣ n) (hbranch : 0 < X - 2 * t)
    (hhalf : n / 2 - 1 ≤ primePowerPartGE 5 (n - 2)) :
    4 * ((n - 1) * (n / 2 - 1)) ≤ X * X * X := by
  rcases i_three_caseI_exists_joint_half_sub_one_cube_bound
      hnone hn hj hn_gt hj_pos hj_two h2n h3n hbranch hhalf with
    ⟨_g, _hrow1, _hdvd, _hle, hcube⟩
  exact hcube

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
  have hk_pos : 0 < k := by
    dsimp [k]
    omega
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
  have hkey_int : (3 : ℤ) * (F : ℤ) ≤ 2 * ((a : ℤ) * (k : ℤ)) := by
    nlinarith
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
        (2 * (a : ℤ)) * (2 * (a : ℤ)) * (2 * (a : ℤ)) := by
      norm_num
    exact hleft ▸ hright ▸ (by exact_mod_cast h)
  have hmain_pos :
      (0 : ℤ) <
        (4 : ℤ) * (((F : ℤ) * (2 * (a : ℤ)) - 1) * ((F : ℤ) * (a : ℤ) - 1)) -
          (2 * (a : ℤ)) * (2 * (a : ℤ)) * (2 * (a : ℤ)) := by
    rw [hk_eq_int] at hkey_int
    nlinarith
  nlinarith

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

theorem i_three_caseI_noncentral_factor_sq_squeeze_of_half_coprime_four {n F X j t : ℕ}
    (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor n 3 j q)
    (hn : n = F * X) (hj : j = F * t) (hn_gt : 2 < n) (hj_pos : 0 < j)
    (hj_two : 2 ≤ j) (h2n : 2 ∣ n) (h3n : 3 ∣ n) (hX_even : 2 ∣ X)
    (hbranch : 0 < X - 2 * t) (hcop4 : (n / 2 - 1).Coprime 4) :
    2 * (F * F) ≤ X := by
  rcases i_three_caseI_row_one_exists_factor
      hnone hn hj hn_gt hj_pos h2n h3n (by omega : t ≤ X) with ⟨g, hrow1⟩
  have hdvd : n / 2 - 1 ∣ g * (X - 2 * t) :=
    i_three_caseI_joint_half_sub_one_dvd_factor_mul_X_sub_two_t
      hnone hn hj hn_gt hj_two h2n h3n hcop4 (by omega : t ≤ X)
      (by omega : 2 * t ≤ X) hrow1
  have hle : n / 2 - 1 ≤ g * (X - 2 * t) := by
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
  have hrow_bound : 4 * (g * (n - 1)) ≤ X * X := by
    simpa [hrow1] using four_mul_t_mul_X_sub_t_le_sq (by omega : 2 * t ≤ X)
  have hgap : 4 * ((n - 1) * (n / 2 - 1)) ≤ X * X * (X - 2 * t) := by
    calc
      4 * ((n - 1) * (n / 2 - 1))
          ≤ 4 * ((n - 1) * (g * (X - 2 * t))) := by
            exact Nat.mul_le_mul_left 4 (Nat.mul_le_mul_left (n - 1) hle)
      _ = (4 * (g * (n - 1))) * (X - 2 * t) := by ring
      _ ≤ (X * X) * (X - 2 * t) := by
            exact Nat.mul_le_mul_right (X - 2 * t) hrow_bound
      _ = X * X * (X - 2 * t) := by ring
  have hcube : 4 * ((n - 1) * (n / 2 - 1)) ≤ X * X * X := by
    exact hgap.trans (by
      simpa [mul_assoc] using Nat.mul_le_mul_left (X * X) (Nat.sub_le X (2 * t)))
  exact two_mul_factor_sq_le_of_even_half_cube_bound hn hn_gt hX_even hcube

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

theorem two_mul_t_le_X_of_factorized_half_bound {n F X j t : ℕ}
    (hn : n = F * X) (hj : j = F * t) (hj_pos : 0 < j) (hjn : 2 * j ≤ n) :
    2 * t ≤ X := by
  have hF_pos : 0 < F := by
    by_cases hF0 : F = 0
    · subst F
      simp at hj
      omega
    · exact Nat.pos_of_ne_zero hF0
  subst n
  subst j
  have hmul : F * (2 * t) ≤ F * X := by
    simpa [mul_assoc, mul_comm, mul_left_comm] using hjn
  exact Nat.le_of_mul_le_mul_left hmul hF_pos

theorem t_le_X_of_factorized_half_bound {n F X j t : ℕ}
    (hn : n = F * X) (hj : j = F * t) (hj_pos : 0 < j) (hjn : 2 * j ≤ n) :
    t ≤ X := by
  have h2tX := two_mul_t_le_X_of_factorized_half_bound hn hj hj_pos hjn
  omega

theorem i_three_caseI_row_one_sub_one_dvd_t_mul_X_sub_t_from_row_bound {n F X j t : ℕ}
    (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor n 3 j q)
    (hn : n = F * X) (hj : j = F * t) (hn_gt : 2 < n) (hj_pos : 0 < j)
    (h2n : 2 ∣ n) (h3n : 3 ∣ n) (hjn : 2 * j ≤ n) :
    n - 1 ∣ t * (X - t) :=
  i_three_caseI_row_one_sub_one_dvd_t_mul_X_sub_t
    hnone hn hj hn_gt hj_pos h2n h3n
    (t_le_X_of_factorized_half_bound hn hj hj_pos hjn)

theorem i_three_caseI_row_one_exists_factor_from_row_bound {n F X j t : ℕ}
    (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor n 3 j q)
    (hn : n = F * X) (hj : j = F * t) (hn_gt : 2 < n) (hj_pos : 0 < j)
    (h2n : 2 ∣ n) (h3n : 3 ∣ n) (hjn : 2 * j ≤ n) :
    ∃ g : ℕ, t * (X - t) = g * (n - 1) :=
  i_three_caseI_row_one_exists_factor
    hnone hn hj hn_gt hj_pos h2n h3n
    (t_le_X_of_factorized_half_bound hn hj hj_pos hjn)

theorem i_three_caseI_row_one_four_mul_sub_one_le_X_sq_from_row_bound {n F X j t : ℕ}
    (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor n 3 j q)
    (hn : n = F * X) (hj : j = F * t) (hn_gt : 2 < n) (hj_pos : 0 < j)
    (h2n : 2 ∣ n) (h3n : 3 ∣ n) (hjn : 2 * j ≤ n) :
    4 * (n - 1) ≤ X * X :=
  i_three_caseI_row_one_four_mul_sub_one_le_X_sq
    hnone hn hj hn_gt hj_pos h2n h3n
    (two_mul_t_le_X_of_factorized_half_bound hn hj hj_pos hjn)

theorem i_three_caseI_row_one_four_mul_factor_le_X_from_row_bound {n F X j t : ℕ}
    (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor n 3 j q)
    (hn : n = F * X) (hj : j = F * t) (hn_gt : 2 < n) (hj_pos : 0 < j)
    (h2n : 2 ∣ n) (h3n : 3 ∣ n) (hX_even : 2 ∣ X) (hX_four : 4 ≤ X)
    (hjn : 2 * j ≤ n) :
    4 * F ≤ X :=
  i_three_caseI_row_one_four_mul_factor_le_X
    hnone hn hj hn_gt hj_pos h2n h3n hX_even hX_four
    (two_mul_t_le_X_of_factorized_half_bound hn hj hj_pos hjn)

theorem i_three_caseI_row_one_four_mul_factor_le_X_of_four_dvd_odd_factor_from_row_bound
    {n F X j t : ℕ}
    (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor n 3 j q)
    (hn : n = F * X) (hj : j = F * t) (hn_gt : 2 < n) (hj_pos : 0 < j)
    (h2n : 2 ∣ n) (h3n : 3 ∣ n) (h4n : 4 ∣ n) (hFodd : Odd F)
    (hjn : 2 * j ≤ n) :
    4 * F ≤ X := by
  have h4X : 4 ∣ X := four_dvd_right_factor_of_four_dvd_mul_odd hFodd (by
    simpa [hn] using h4n)
  have hX_even : 2 ∣ X := Nat.dvd_trans (by norm_num : 2 ∣ 4) h4X
  have hX_pos : 0 < X := by
    by_contra hnot
    have hX0 : X = 0 := Nat.eq_zero_of_not_pos hnot
    subst X
    omega
  have hX_four : 4 ≤ X := Nat.le_of_dvd hX_pos h4X
  exact i_three_caseI_row_one_four_mul_factor_le_X_from_row_bound
    hnone hn hj hn_gt hj_pos h2n h3n hX_even hX_four hjn

theorem i_three_caseI_row_two_primePowerPartGE_dvd_t_mul_X_sub_t_mul_X_sub_two_t_from_row_bound
    {n F X j t : ℕ} (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor n 3 j q)
    (hn : n = F * X) (hj : j = F * t) (hn_gt : 2 < n) (hj_pos : 0 < j)
    (hj_two : 2 ≤ j) (hjn : 2 * j ≤ n) :
    primePowerPartGE 5 (n - 2) ∣ t * (X - t) * (X - 2 * t) :=
  i_three_caseI_row_two_primePowerPartGE_dvd_t_mul_X_sub_t_mul_X_sub_two_t
    hnone hn hj (by omega : 2 ≤ n) hn_gt hj_two
    (t_le_X_of_factorized_half_bound hn hj hj_pos hjn)
    (two_mul_t_le_X_of_factorized_half_bound hn hj hj_pos hjn)

theorem i_three_caseI_row_two_half_sub_one_dvd_t_mul_X_sub_t_mul_X_sub_two_t_from_row_bound
    {n F X j t : ℕ} (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor n 3 j q)
    (hn : n = F * X) (hj : j = F * t) (hn_gt : 2 < n) (hj_pos : 0 < j)
    (hj_two : 2 ≤ j) (h2n : 2 ∣ n) (h3n : 3 ∣ n)
    (hcop4 : (n / 2 - 1).Coprime 4) (hjn : 2 * j ≤ n) :
    n / 2 - 1 ∣ t * (X - t) * (X - 2 * t) :=
  i_three_caseI_row_two_half_sub_one_dvd_t_mul_X_sub_t_mul_X_sub_two_t
    hnone hn hj hn_gt hj_two h2n h3n hcop4
    (t_le_X_of_factorized_half_bound hn hj hj_pos hjn)
    (two_mul_t_le_X_of_factorized_half_bound hn hj hj_pos hjn)

theorem i_three_caseI_row_two_half_large_part_dvd_triple_from_row_bound
    {n F X j t : ℕ} (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor n 3 j q)
    (hn : n = F * X) (hj : j = F * t) (hn_gt : 2 < n) (hj_pos : 0 < j)
    (hj_two : 2 ≤ j) (h2n : 2 ∣ n) (hjn : 2 * j ≤ n) :
    primePowerPartGE 5 (n / 2 - 1) ∣ t * (X - t) * (X - 2 * t) :=
  i_three_caseI_row_two_half_sub_one_large_part_dvd_t_mul_X_sub_t_mul_X_sub_two_t
    hnone hn hj hn_gt hj_two h2n
    (t_le_X_of_factorized_half_bound hn hj hj_pos hjn)
    (two_mul_t_le_X_of_factorized_half_bound hn hj hj_pos hjn)

theorem i_three_caseI_joint_large_part_dvd_factor_mul_X_sub_two_t_from_row_bound
    {n F X j t g : ℕ} (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor n 3 j q)
    (hn : n = F * X) (hj : j = F * t) (hn_gt : 2 < n) (hj_pos : 0 < j)
    (hj_two : 2 ≤ j) (hjn : 2 * j ≤ n)
    (hrow1 : t * (X - t) = g * (n - 1)) :
    primePowerPartGE 5 (n - 2) ∣ g * (X - 2 * t) :=
  i_three_caseI_joint_large_part_dvd_factor_mul_X_sub_two_t
    hnone hn hj (by omega : 2 ≤ n) hn_gt hj_two
    (t_le_X_of_factorized_half_bound hn hj hj_pos hjn)
    (two_mul_t_le_X_of_factorized_half_bound hn hj hj_pos hjn) hrow1

theorem i_three_caseI_joint_half_sub_one_dvd_factor_mul_X_sub_two_t_from_row_bound
    {n F X j t g : ℕ} (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor n 3 j q)
    (hn : n = F * X) (hj : j = F * t) (hn_gt : 2 < n) (hj_pos : 0 < j)
    (hj_two : 2 ≤ j) (h2n : 2 ∣ n) (h3n : 3 ∣ n)
    (hcop4 : (n / 2 - 1).Coprime 4) (hjn : 2 * j ≤ n)
    (hrow1 : t * (X - t) = g * (n - 1)) :
    n / 2 - 1 ∣ g * (X - 2 * t) :=
  i_three_caseI_joint_half_sub_one_dvd_factor_mul_X_sub_two_t
    hnone hn hj hn_gt hj_two h2n h3n hcop4
    (t_le_X_of_factorized_half_bound hn hj hj_pos hjn)
    (two_mul_t_le_X_of_factorized_half_bound hn hj hj_pos hjn) hrow1

theorem i_three_caseI_joint_half_sub_one_large_part_dvd_factor_mul_X_sub_two_t_from_row_bound
    {n F X j t g : ℕ} (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor n 3 j q)
    (hn : n = F * X) (hj : j = F * t) (hn_gt : 2 < n) (hj_pos : 0 < j)
    (hj_two : 2 ≤ j) (h2n : 2 ∣ n) (hjn : 2 * j ≤ n)
    (hrow1 : t * (X - t) = g * (n - 1)) :
    primePowerPartGE 5 (n / 2 - 1) ∣ g * (X - 2 * t) :=
  i_three_caseI_joint_half_sub_one_large_part_dvd_factor_mul_X_sub_two_t
    hnone hn hj hn_gt hj_two h2n
    (t_le_X_of_factorized_half_bound hn hj hj_pos hjn)
    (two_mul_t_le_X_of_factorized_half_bound hn hj hj_pos hjn) hrow1

theorem x_sub_two_t_pos_of_row_bound {n F X j t : ℕ}
    (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor n 3 j q)
    (hn : n = F * X) (hj : j = F * t) (hn_gt : 2 < n) (hj_pos : 0 < j)
    (h2n : 2 ∣ n) (h3n : 3 ∣ n) (hjn : 2 * j ≤ n) :
    0 < X - 2 * t := by
  have h2tX := two_mul_t_le_X_of_factorized_half_bound hn hj hj_pos hjn
  by_cases hcentral : 2 * t = X
  · exact False.elim
      (i_three_caseI_central_branch_false hnone hn hj hn_gt hj_pos h2n h3n hcentral)
  · omega

theorem i_three_caseI_exists_joint_large_part_factor_le_from_row_bound
    {n F X j t : ℕ} (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor n 3 j q)
    (hn : n = F * X) (hj : j = F * t) (hn_gt : 2 < n) (hj_pos : 0 < j)
    (hj_two : 2 ≤ j) (h2n : 2 ∣ n) (h3n : 3 ∣ n) (hjn : 2 * j ≤ n) :
    ∃ g : ℕ,
      t * (X - t) = g * (n - 1) ∧
        primePowerPartGE 5 (n - 2) ∣ g * (X - 2 * t) ∧
          primePowerPartGE 5 (n - 2) ≤ g * (X - 2 * t) :=
  i_three_caseI_exists_joint_large_part_factor_le
    hnone hn hj hn_gt hj_pos hj_two h2n h3n
    (x_sub_two_t_pos_of_row_bound hnone hn hj hn_gt hj_pos h2n h3n hjn)

theorem i_three_caseI_exists_joint_large_part_gap_bound_from_row_bound
    {n F X j t : ℕ} (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor n 3 j q)
    (hn : n = F * X) (hj : j = F * t) (hn_gt : 2 < n) (hj_pos : 0 < j)
    (hj_two : 2 ≤ j) (h2n : 2 ∣ n) (h3n : 3 ∣ n) (hjn : 2 * j ≤ n) :
    ∃ g : ℕ,
      t * (X - t) = g * (n - 1) ∧
        primePowerPartGE 5 (n - 2) ∣ g * (X - 2 * t) ∧
          primePowerPartGE 5 (n - 2) ≤ g * (X - 2 * t) ∧
            4 * ((n - 1) * primePowerPartGE 5 (n - 2)) ≤
              X * X * (X - 2 * t) :=
  i_three_caseI_exists_joint_large_part_gap_bound
    hnone hn hj hn_gt hj_pos hj_two h2n h3n
    (x_sub_two_t_pos_of_row_bound hnone hn hj hn_gt hj_pos h2n h3n hjn)

theorem i_three_caseI_exists_joint_large_part_cube_bound_from_row_bound
    {n F X j t : ℕ} (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor n 3 j q)
    (hn : n = F * X) (hj : j = F * t) (hn_gt : 2 < n) (hj_pos : 0 < j)
    (hj_two : 2 ≤ j) (h2n : 2 ∣ n) (h3n : 3 ∣ n) (hjn : 2 * j ≤ n) :
    ∃ g : ℕ,
      t * (X - t) = g * (n - 1) ∧
        primePowerPartGE 5 (n - 2) ∣ g * (X - 2 * t) ∧
          primePowerPartGE 5 (n - 2) ≤ g * (X - 2 * t) ∧
            4 * ((n - 1) * primePowerPartGE 5 (n - 2)) ≤ X * X * X :=
  i_three_caseI_exists_joint_large_part_cube_bound
    hnone hn hj hn_gt hj_pos hj_two h2n h3n
    (x_sub_two_t_pos_of_row_bound hnone hn hj hn_gt hj_pos h2n h3n hjn)

theorem i_three_caseI_exists_joint_half_large_part_cube_from_row_bound
    {n F X j t : ℕ} (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor n 3 j q)
    (hn : n = F * X) (hj : j = F * t) (hn_gt : 2 < n) (hj_pos : 0 < j)
    (hj_two : 2 ≤ j) (h2n : 2 ∣ n) (h3n : 3 ∣ n) (hjn : 2 * j ≤ n) :
    ∃ g : ℕ,
      t * (X - t) = g * (n - 1) ∧
        primePowerPartGE 5 (n / 2 - 1) ∣ g * (X - 2 * t) ∧
          primePowerPartGE 5 (n / 2 - 1) ≤ g * (X - 2 * t) ∧
            4 * ((n - 1) * primePowerPartGE 5 (n / 2 - 1)) ≤ X * X * X :=
  i_three_caseI_exists_joint_half_sub_one_large_part_cube_bound
    hnone hn hj hn_gt hj_pos hj_two h2n h3n
    (x_sub_two_t_pos_of_row_bound hnone hn hj hn_gt hj_pos h2n h3n hjn)

theorem i_three_caseI_half_large_part_cube_from_row_bound {n F X j t : ℕ}
    (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor n 3 j q)
    (hn : n = F * X) (hj : j = F * t) (hn_gt : 2 < n) (hj_pos : 0 < j)
    (hj_two : 2 ≤ j) (h2n : 2 ∣ n) (h3n : 3 ∣ n) (hjn : 2 * j ≤ n) :
    4 * ((n - 1) * primePowerPartGE 5 (n / 2 - 1)) ≤ X * X * X := by
  rcases i_three_caseI_exists_joint_half_large_part_cube_from_row_bound
      hnone hn hj hn_gt hj_pos hj_two h2n h3n hjn with
    ⟨_g, _hrow1, _hdvd, _hle, hcube⟩
  exact hcube

theorem i_three_caseI_exists_joint_half_sub_one_cube_from_four_dvd_row_bound
    {n F X j t : ℕ} (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor n 3 j q)
    (hn : n = F * X) (hj : j = F * t) (hn_gt : 2 < n) (hj_pos : 0 < j)
    (hj_two : 2 ≤ j) (h2n : 2 ∣ n) (h3n : 3 ∣ n) (h4n : 4 ∣ n)
    (hjn : 2 * j ≤ n) :
    ∃ g : ℕ,
      t * (X - t) = g * (n - 1) ∧
        n / 2 - 1 ∣ g * (X - 2 * t) ∧
          n / 2 - 1 ≤ g * (X - 2 * t) ∧
            4 * ((n - 1) * (n / 2 - 1)) ≤ X * X * X := by
  have hlarge :=
    i_three_caseI_exists_joint_half_large_part_cube_from_row_bound
      hnone hn hj hn_gt hj_pos hj_two h2n h3n hjn
  simpa [primePowerPartGE_five_half_sub_one_eq_self_of_four_dvd_three_dvd
    h4n h3n hn_gt] using hlarge

theorem i_three_caseI_half_sub_one_cube_from_four_dvd_row_bound {n F X j t : ℕ}
    (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor n 3 j q)
    (hn : n = F * X) (hj : j = F * t) (hn_gt : 2 < n) (hj_pos : 0 < j)
    (hj_two : 2 ≤ j) (h2n : 2 ∣ n) (h3n : 3 ∣ n) (h4n : 4 ∣ n)
    (hjn : 2 * j ≤ n) :
    4 * ((n - 1) * (n / 2 - 1)) ≤ X * X * X := by
  rcases i_three_caseI_exists_joint_half_sub_one_cube_from_four_dvd_row_bound
      hnone hn hj hn_gt hj_pos hj_two h2n h3n h4n hjn with
    ⟨_g, _hrow1, _hdvd, _hle, hcube⟩
  exact hcube

theorem i_three_caseI_factor_sq_squeeze_of_half_bound_from_row_bound {n F X j t : ℕ}
    (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor n 3 j q)
    (hn : n = F * X) (hj : j = F * t) (hn_gt : 2 < n) (hj_pos : 0 < j)
    (hj_two : 2 ≤ j) (h2n : 2 ∣ n) (h3n : 3 ∣ n) (hX_even : 2 ∣ X)
    (hjn : 2 * j ≤ n) (hhalf : n / 2 - 1 ≤ primePowerPartGE 5 (n - 2)) :
    2 * (F * F) ≤ X :=
  i_three_caseI_factor_sq_squeeze_of_half_bound
    hnone hn hj hn_gt hj_pos hj_two h2n h3n hX_even
    (two_mul_t_le_X_of_factorized_half_bound hn hj hj_pos hjn) hhalf

theorem i_three_caseI_factor_sq_squeeze_of_half_coprime_four_from_row_bound {n F X j t : ℕ}
    (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor n 3 j q)
    (hn : n = F * X) (hj : j = F * t) (hn_gt : 2 < n) (hj_pos : 0 < j)
    (hj_two : 2 ≤ j) (h2n : 2 ∣ n) (h3n : 3 ∣ n) (hX_even : 2 ∣ X)
    (hjn : 2 * j ≤ n) (hcop4 : (n / 2 - 1).Coprime 4) :
    2 * (F * F) ≤ X :=
  i_three_caseI_factor_sq_squeeze_of_half_coprime_four
    hnone hn hj hn_gt hj_pos hj_two h2n h3n hX_even
    (two_mul_t_le_X_of_factorized_half_bound hn hj hj_pos hjn) hcop4

theorem i_three_caseI_factor_sq_squeeze_of_four_dvd_from_row_bound {n F X j t : ℕ}
    (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor n 3 j q)
    (hn : n = F * X) (hj : j = F * t) (hn_gt : 2 < n) (hj_pos : 0 < j)
    (hj_two : 2 ≤ j) (h2n : 2 ∣ n) (h3n : 3 ∣ n) (h4n : 4 ∣ n)
    (hX_even : 2 ∣ X) (hjn : 2 * j ≤ n) :
    2 * (F * F) ≤ X :=
  i_three_caseI_factor_sq_squeeze_of_half_coprime_four_from_row_bound
    hnone hn hj hn_gt hj_pos hj_two h2n h3n hX_even hjn
    (half_sub_one_coprime_four_of_four_dvd h4n hn_gt)

theorem i_three_caseI_factor_sq_squeeze_of_four_dvd_odd_factor_from_row_bound
    {n F X j t : ℕ}
    (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor n 3 j q)
    (hn : n = F * X) (hj : j = F * t) (hn_gt : 2 < n) (hj_pos : 0 < j)
    (hj_two : 2 ≤ j) (h2n : 2 ∣ n) (h3n : 3 ∣ n) (h4n : 4 ∣ n)
    (hFodd : Odd F) (hjn : 2 * j ≤ n) :
    2 * (F * F) ≤ X := by
  have h4X : 4 ∣ X := four_dvd_right_factor_of_four_dvd_mul_odd hFodd (by
    simpa [hn] using h4n)
  have hX_even : 2 ∣ X := Nat.dvd_trans (by norm_num : 2 ∣ 4) h4X
  exact i_three_caseI_factor_sq_squeeze_of_four_dvd_from_row_bound
    hnone hn hj hn_gt hj_pos hj_two h2n h3n h4n hX_even hjn

theorem i_three_caseI_four_dvd_odd_factor_joint_package_from_row_bound
    {n F X j t : ℕ}
    (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor n 3 j q)
    (hn : n = F * X) (hj : j = F * t) (hn_gt : 2 < n) (hj_pos : 0 < j)
    (hj_two : 2 ≤ j) (h2n : 2 ∣ n) (h3n : 3 ∣ n) (h4n : 4 ∣ n)
    (hFodd : Odd F) (hjn : 2 * j ≤ n) :
    ∃ g : ℕ,
      t * (X - t) = g * (n - 1) ∧
        n / 2 - 1 ∣ g * (X - 2 * t) ∧
          n / 2 - 1 ≤ g * (X - 2 * t) ∧
            4 * ((n - 1) * (n / 2 - 1)) ≤ X * X * X ∧
              4 * F ≤ X ∧
                2 * (F * F) ≤ X := by
  rcases i_three_caseI_exists_joint_half_sub_one_cube_from_four_dvd_row_bound
      hnone hn hj hn_gt hj_pos hj_two h2n h3n h4n hjn with
    ⟨g, hrow1, hdvd, hle, hcube⟩
  have hrow :
      4 * F ≤ X :=
    i_three_caseI_row_one_four_mul_factor_le_X_of_four_dvd_odd_factor_from_row_bound
      hnone hn hj hn_gt hj_pos h2n h3n h4n hFodd hjn
  have hsq :
      2 * (F * F) ≤ X :=
    i_three_caseI_factor_sq_squeeze_of_four_dvd_odd_factor_from_row_bound
      hnone hn hj hn_gt hj_pos hj_two h2n h3n h4n hFodd hjn
  exact ⟨g, hrow1, hdvd, hle, hcube, hrow, hsq⟩

theorem i_three_caseI_four_dvd_odd_factor_joint_squeeze_from_row_bound
    {n F X j t : ℕ}
    (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor n 3 j q)
    (hn : n = F * X) (hj : j = F * t) (hn_gt : 2 < n) (hj_pos : 0 < j)
    (hj_two : 2 ≤ j) (h2n : 2 ∣ n) (h3n : 3 ∣ n) (h4n : 4 ∣ n)
    (hFodd : Odd F) (hjn : 2 * j ≤ n) :
    4 * F ≤ X ∧ 2 * (F * F) ≤ X := by
  rcases
      i_three_caseI_four_dvd_odd_factor_joint_package_from_row_bound
        hnone hn hj hn_gt hj_pos hj_two h2n h3n h4n hFodd hjn with
    ⟨_g, _hrow1, _hdvd, _hle, _hcube, hrow, hsq⟩
  exact ⟨hrow, hsq⟩

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
