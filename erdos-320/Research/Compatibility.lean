import Research.GoodIndices
import Mathlib.Data.Rat.Lemmas

/-! # Compatible-prime propagation of exact-doubling denominators -/

namespace Research

/-- A zero-based signed coefficient function. -/
def SignedCoefficients (w : ℕ → ℤ) : Prop :=
  ∀ i, w i = -1 ∨ w i = 0 ∨ w i = 1

/-- Signed reciprocal sum using denominators `1,...,d-1`. -/
noncomputable def signedReciprocalSum (d : ℕ) (w : ℕ → ℤ) : ℚ :=
  ∑ i ∈ Finset.range (d - 1), (w i : ℚ) / (i + 1 : ℕ)

/-- Arithmetic good-denominator predicate convenient for modular arguments. -/
def CoeffGoodDenominator (d : ℕ) : Prop :=
  0 < d ∧ ∀ w : ℕ → ℤ, SignedCoefficients w →
    signedReciprocalSum d w ≠ (1 : ℚ) / d

/-- The coefficient formulation implies the subset-pair formulation used in
F-029. -/
theorem goodDenominator_of_coeffGood {d : ℕ} (hd : CoeffGoodDenominator d) :
    GoodDenominator d := by
  rcases hd with ⟨hdpos, hdgood⟩
  refine ⟨hdpos, ?_⟩
  intro A hA B hB hEq
  let w : ℕ → ℤ := fun i =>
    (if i ∈ A then 1 else 0) - (if i ∈ B then 1 else 0)
  have hw : SignedCoefficients w := by
    intro i
    dsimp [w]
    by_cases hiA : i ∈ A <;> by_cases hiB : i ∈ B <;> simp [hiA, hiB]
  have hEq' : reciprocalSubsetSum A - reciprocalSubsetSum B =
      (1 : ℚ) / d := by
    have hs : d - 1 + 1 = d := by omega
    have hsR : ((d - 1 : ℕ) : ℚ) + 1 = d := by exact_mod_cast hs
    rw [hsR] at hEq
    exact hEq
  apply hdgood w hw
  rw [← hEq']
  rw [signedReciprocalSum, reciprocalSubsetSum, reciprocalSubsetSum]
  have hAsub : A ⊆ Finset.range (d - 1) := by
    simpa [Finset.mem_powerset] using hA
  have hBsub : B ⊆ Finset.range (d - 1) := by
    simpa [Finset.mem_powerset] using hB
  simp only [w, Int.cast_sub, Int.cast_ite, Int.cast_one, Int.cast_zero]
  simp_rw [sub_div]
  rw [Finset.sum_sub_distrib]
  congr 1
  · rw [← Finset.sum_subset hAsub]
    · apply Finset.sum_congr rfl
      intro i hi
      simp [hi]
    · intro i hi hiA
      simp [hiA]
  · rw [← Finset.sum_subset hBsub]
    · apply Finset.sum_congr rfl
      intro i hi
      simp [hi]
    · intro i hi hiB
      simp [hiB]

/-- A prime is compatible with `d` if it divides no numerator of a nonzero
signed discrepancy at `d`. -/
def PrimeCompatible (p d : ℕ) : Prop :=
  ∀ w : ℕ → ℤ, SignedCoefficients w →
    (1 : ℚ) / d - signedReciprocalSum d w ≠ 0 →
      ¬(p : ℤ) ∣ ((1 : ℚ) / d - signedReciprocalSum d w).num

/-- If `q=p*r` and `p` does not divide the reduced denominator of `r`, then
`p` divides the reduced numerator of `q`. -/
theorem prime_dvd_rat_num_of_eq_mul {q r : ℚ} {p : ℕ} (hp : p.Prime)
    (heq : q = (p : ℚ) * r) (hden : ¬p ∣ r.den) :
    (p : ℤ) ∣ q.num := by
  have hcrossQ : (q.num : ℚ) * r.den =
      (p : ℚ) * r.num * q.den := by
    calc
      (q.num : ℚ) * r.den = (q.den : ℚ) * q * r.den := by
        rw [Rat.den_mul_eq_num]
      _ = (q.den : ℚ) * ((p : ℚ) * r) * r.den := by rw [heq]
      _ = (p : ℚ) * r.num * q.den := by
        rw [← Rat.den_mul_eq_num r]
        ring
  have hcross : q.num * (r.den : ℤ) =
      (p : ℤ) * r.num * q.den := by exact_mod_cast hcrossQ
  have hdvd : (p : ℤ) ∣ q.num * (r.den : ℤ) := by
    rw [hcross]
    exact ⟨r.num * q.den, by ring⟩
  have hor := ((Nat.prime_iff_prime_int.mp hp).dvd_mul).mp hdvd
  rcases hor with hqnum | hrden
  · exact hqnum
  · exfalso
    apply hden
    exact Int.natCast_dvd_natCast.mp hrden

/-- Denominator of a rational integer divided by a positive natural divides
that natural. -/
theorem rat_den_dvd_of_int_div_nat (a : ℤ) {n : ℕ} (hn : 0 < n) :
    ((a : ℚ) / (n : ℚ)).den ∣ n := by
  have h := Rat.den_dvd a (n : ℤ)
  rw [Rat.divInt_eq_div] at h
  exact Int.natCast_dvd_natCast.mp h

/-- Adding rationals whose reduced denominators are prime to `p` preserves
that property. -/
theorem prime_not_dvd_den_add {p : ℕ} (hp : p.Prime) {q r : ℚ}
    (hq : ¬p ∣ q.den) (hr : ¬p ∣ r.den) :
    ¬p ∣ (q + r).den := by
  intro hsum
  have hdvdProd : p ∣ q.den * r.den :=
    dvd_trans hsum (Rat.add_den_dvd q r)
  rcases (hp.dvd_mul.mp hdvdProd) with h | h
  · exact hq h
  · exact hr h

/-- A finite sum of terms with denominators prime to `p` again has denominator
prime to `p`. -/
theorem prime_not_dvd_den_sum {p : ℕ} (hp : p.Prime)
    (s : Finset ℕ) (f : ℕ → ℚ)
    (hf : ∀ i ∈ s, ¬p ∣ (f i).den) :
    ¬p ∣ (∑ i ∈ s, f i).den := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hp.not_dvd_one
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact prime_not_dvd_den_add hp (hf a (Finset.mem_insert_self ..))
        (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)))

/-- Part of a signed sum supported on denominators not divisible by `p`. -/
noncomputable def nonmultipleSignedSum (p d : ℕ) (w : ℕ → ℤ) : ℚ :=
  ∑ i ∈ (Finset.range (d - 1)).filter (fun i => ¬p ∣ i + 1),
    (w i : ℚ) / (i + 1 : ℕ)

/-- Coefficients induced on the `p`-divisible denominators. -/
def dividedCoefficients (p : ℕ) (w : ℕ → ℤ) : ℕ → ℤ :=
  fun j => w (p * (j + 1) - 1)

/-- Exact reindexing of the `p`-divisible part of a signed reciprocal sum. -/
theorem sum_filter_dvd_eq_divided (p m : ℕ) (hp : 0 < p) (hm : 0 < m)
    (w : ℕ → ℤ) :
    ∑ i ∈ (Finset.range (m * p - 1)).filter (fun i => p ∣ i + 1),
        (w i : ℚ) / (i + 1 : ℕ) =
      (1 : ℚ) / p * signedReciprocalSum m (dividedCoefficients p w) := by
  rw [signedReciprocalSum]
  symm
  rw [Finset.mul_sum]
  apply Finset.sum_bij (fun j _ => p * (j + 1) - 1)
  · intro j hj
    rw [Finset.mem_filter, Finset.mem_range]
    have hjlt : j < m - 1 := Finset.mem_range.mp hj
    constructor
    · have hjm : j + 1 < m := by omega
      have hmul : p * (j + 1) < p * m :=
        (Nat.mul_lt_mul_left hp).mpr hjm
      rw [Nat.mul_comm p m] at hmul
      have hpos : 1 ≤ p * (j + 1) := Nat.one_le_iff_ne_zero.mpr
        (Nat.mul_ne_zero (Nat.ne_of_gt hp) (by omega))
      exact Nat.sub_lt_sub_right hpos hmul
    · have hpos : 0 < p * (j + 1) := Nat.mul_pos hp (by omega)
      have heq : p * (j + 1) - 1 + 1 = p * (j + 1) := by omega
      exact ⟨j + 1, heq⟩
  · intro a ha b hb heq
    have ha' : a < m - 1 := Finset.mem_range.mp ha
    have hb' : b < m - 1 := Finset.mem_range.mp hb
    have hpa : 0 < p * (a + 1) := Nat.mul_pos hp (by omega)
    have hpb : 0 < p * (b + 1) := Nat.mul_pos hp (by omega)
    have heq' : p * (a + 1) = p * (b + 1) := by omega
    have := Nat.mul_left_cancel hp heq'
    omega
  · intro i hi
    rw [Finset.mem_filter, Finset.mem_range] at hi
    rcases hi.2 with ⟨t, ht⟩
    have htEq : i + 1 = p * t := by simpa [Nat.mul_comm] using ht
    have htPos : 0 < t := by
      by_contra h
      have : t = 0 := by omega
      subst t
      omega
    have htlt : t < m := by
      have hpt : p * t < p * m := by
        rw [← htEq, Nat.mul_comm p m]
        omega
      exact (Nat.mul_lt_mul_left hp).mp hpt
    refine ⟨t - 1, Finset.mem_range.mpr (by omega), ?_⟩
    have htback : t - 1 + 1 = t := by omega
    rw [htback]
    omega
  · intro j hj
    have hjlt : j < m - 1 := Finset.mem_range.mp hj
    rw [dividedCoefficients]
    have hpos : 0 < j + 1 := by omega
    have heq : p * (j + 1) - 1 + 1 = p * (j + 1) := by
      have : 0 < p * (j + 1) := Nat.mul_pos hp hpos
      omega
    rw [heq]
    push_cast
    field_simp

/-- A finite sum has denominator dividing any common multiple of all term
denominators. -/
theorem rat_den_sum_dvd_common (s : Finset ℕ) (f : ℕ → ℚ) (L : ℕ)
    (hf : ∀ i ∈ s, (f i).den ∣ L) :
    (∑ i ∈ s, f i).den ∣ L := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact (Rat.add_den_dvd_lcm (f a) (∑ i ∈ s, f i)).trans
        (Nat.lcm_dvd (hf a (Finset.mem_insert_self ..))
          (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))))

/-- Every positive `j≤m` divides `lcm(1,...,m)`. -/
theorem dvd_lcmUpto {j m : ℕ} (hj : 1 ≤ j) (hjm : j ≤ m) :
    j ∣ Nat.lcmUpto m := by
  rw [Nat.lcmUpto]
  exact Finset.dvd_lcm (Finset.mem_Icc.mpr ⟨hj, hjm⟩)

/-- Reduced denominator of a signed discrepancy at `m` divides
`lcm(1,...,m)`. -/
theorem discrepancy_den_dvd_lcmUpto {m : ℕ} (hm : 0 < m)
    (w : ℕ → ℤ) :
    ((1 : ℚ) / m - signedReciprocalSum m w).den ∣ Nat.lcmUpto m := by
  have hfirst : ((1 : ℚ) / m).den ∣ Nat.lcmUpto m := by
    exact (rat_den_dvd_of_int_div_nat 1 hm).trans
      (dvd_lcmUpto (by omega) le_rfl)
  have hsum : (signedReciprocalSum m w).den ∣ Nat.lcmUpto m := by
    rw [signedReciprocalSum]
    apply rat_den_sum_dvd_common
    intro i hi
    have hi' : i < m - 1 := Finset.mem_range.mp hi
    exact (rat_den_dvd_of_int_div_nat (w i) (by omega)).trans
      (dvd_lcmUpto (by omega) (by omega))
  exact (Rat.sub_den_dvd_lcm ((1 : ℚ) / m) (signedReciprocalSum m w)).trans
    (Nat.lcm_dvd hfirst hsum)

/-- Absolute value of a signed sum is at most its number of terms. -/
theorem abs_signedReciprocalSum_le {m : ℕ} (w : ℕ → ℤ)
    (hw : SignedCoefficients w) :
    |signedReciprocalSum m w| ≤ (m - 1 : ℕ) := by
  rw [signedReciprocalSum]
  calc
    |∑ i ∈ Finset.range (m - 1), (w i : ℚ) / (i + 1 : ℕ)| ≤
        ∑ i ∈ Finset.range (m - 1), |(w i : ℚ) / (i + 1 : ℕ)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ Finset.range (m - 1), (1 : ℚ) := by
      apply Finset.sum_le_sum
      intro i hi
      rcases hw i with h | h | h
      · rw [h, abs_div]
        norm_num
        exact inv_le_one_of_one_le₀
          (by exact_mod_cast (show 1 ≤ i + 1 by omega))
      · rw [h]
        norm_num
      · rw [h, abs_div]
        norm_num
        exact inv_le_one_of_one_le₀
          (by exact_mod_cast (show 1 ≤ i + 1 by omega))
    _ = (m - 1 : ℕ) := by simp

/-- A nonzero signed discrepancy has reduced numerator bounded by
`lcmUpto(m)*m`. -/
theorem discrepancy_num_natAbs_le {m : ℕ} (hm : 0 < m)
    (w : ℕ → ℤ) (hw : SignedCoefficients w) :
    ((1 : ℚ) / m - signedReciprocalSum m w).num.natAbs ≤
      Nat.lcmUpto m * m := by
  let q : ℚ := (1 : ℚ) / m - signedReciprocalSum m w
  have hdenDvd : q.den ∣ Nat.lcmUpto m :=
    discrepancy_den_dvd_lcmUpto hm w
  have hdenLe : q.den ≤ Nat.lcmUpto m :=
    Nat.le_of_dvd (Nat.lcmUpto_pos m) hdenDvd
  have hsum := abs_signedReciprocalSum_le (m := m) w hw
  have hfirst : |(1 : ℚ) / m| ≤ 1 := by
    rw [abs_of_nonneg (by positivity)]
    apply (div_le_one (by exact_mod_cast hm : (0 : ℚ) < (m : ℚ))).mpr
    exact_mod_cast (show 1 ≤ m by omega)
  have hq : |q| ≤ (m : ℚ) := by
    dsimp [q]
    calc
      |(1 : ℚ) / m - signedReciprocalSum m w| ≤
          |(1 : ℚ) / m| + |signedReciprocalSum m w| := abs_sub _ _
      _ ≤ 1 + (m - 1 : ℕ) := add_le_add hfirst hsum
      _ = (m : ℕ) := by
        have hs : 1 + (m - 1) = m := by omega
        exact_mod_cast hs
  have hnumQ : |(q.num : ℚ)| ≤ (Nat.lcmUpto m * m : ℕ) := by
    have heq := Rat.den_mul_eq_num q
    have habsEq : |(q.num : ℚ)| = (q.den : ℚ) * |q| := by
      rw [← heq, abs_mul, abs_of_nonneg (by positivity)]
    rw [habsEq]
    have hdenLeQ : (q.den : ℚ) ≤ Nat.lcmUpto m := by exact_mod_cast hdenLe
    have hmul := mul_le_mul hdenLeQ hq (abs_nonneg q)
      (by positivity : (0 : ℚ) ≤ Nat.lcmUpto m)
    norm_num only [Nat.cast_mul] at hmul ⊢
    exact hmul
  change q.num.natAbs ≤ Nat.lcmUpto m * m
  have hcastAbs : ((q.num.natAbs : ℕ) : ℚ) = |(q.num : ℚ)| := by
    norm_num [Int.natCast_natAbs]
  have hcast : ((q.num.natAbs : ℕ) : ℚ) ≤
      ((Nat.lcmUpto m * m : ℕ) : ℚ) := by
    rw [hcastAbs]
    exact hnumQ
  exact_mod_cast hcast

/-- Every prime above `lcmUpto(m)*m` is compatible with `m`. -/
theorem primeCompatible_of_large {m p : ℕ} (hm : 0 < m) (hp : p.Prime)
    (hlarge : Nat.lcmUpto m * m < p) :
    PrimeCompatible p m := by
  intro w hw hq0 hpnum
  let q : ℚ := (1 : ℚ) / m - signedReciprocalSum m w
  have hnum0 : q.num ≠ 0 := Rat.num_ne_zero.mpr hq0
  have hnatDvd : p ∣ q.num.natAbs := Int.natCast_dvd.mp hpnum
  have habsPos : 0 < q.num.natAbs := Int.natAbs_pos.mpr hnum0
  have hple : p ≤ q.num.natAbs := Nat.le_of_dvd habsPos hnatDvd
  have hbound := discrepancy_num_natAbs_le hm w hw
  change q.num.natAbs ≤ Nat.lcmUpto m * m at hbound
  omega

/-- Compatible-prime propagation: if `m` is good and `p` is compatible,
then `m*p` is good. -/
theorem coeffGood_mul_prime {m p : ℕ}
    (hm : CoeffGoodDenominator m) (hp : p.Prime)
    (hcompat : PrimeCompatible p m) :
    CoeffGoodDenominator (m * p) := by
  rcases hm with ⟨hmPos, hmGood⟩
  have hpPos : 0 < p := hp.pos
  refine ⟨Nat.mul_pos hmPos hpPos, ?_⟩
  intro w hw hrep
  let wm := dividedCoefficients p w
  have hwm : SignedCoefficients wm := by
    intro j
    exact hw (p * (j + 1) - 1)
  let q : ℚ := (1 : ℚ) / m - signedReciprocalSum m wm
  have hq0 : q ≠ 0 := by
    dsimp [q]
    intro h
    apply hmGood wm hwm
    linarith
  let r : ℚ := nonmultipleSignedSum p (m * p) w
  have hsplit : signedReciprocalSum (m * p) w =
      (1 : ℚ) / p * signedReciprocalSum m wm + r := by
    rw [signedReciprocalSum]
    have hpart := Finset.sum_filter_add_sum_filter_not
      (Finset.range (m * p - 1)) (fun i => p ∣ i + 1)
      (fun i => (w i : ℚ) / (i + 1 : ℕ))
    rw [sum_filter_dvd_eq_divided p m hpPos hmPos w] at hpart
    simpa [r, nonmultipleSignedSum, wm] using hpart.symm
  have hfrac : (1 : ℚ) / (m * p : ℕ) =
      (1 : ℚ) / p * ((1 : ℚ) / m) := by
    field_simp
    norm_num
    ring
  have hqeq : q = (p : ℚ) * r := by
    dsimp [q]
    rw [hsplit] at hrep
    rw [hfrac] at hrep
    have hpQ : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
    field_simp [hpQ] at hrep ⊢
    linarith
  have hden : ¬p ∣ r.den := by
    apply prime_not_dvd_den_sum hp
    intro i hi
    rw [Finset.mem_filter] at hi
    have hdvd := rat_den_dvd_of_int_div_nat (w i) (by omega : 0 < i + 1)
    intro hpden
    exact hi.2 (dvd_trans hpden hdvd)
  have hpnum : (p : ℤ) ∣ q.num :=
    prime_dvd_rat_num_of_eq_mul hp hqeq hden
  exact (hcompat wm hwm hq0) hpnum

/-- Large compatible primes preserve arithmetic goodness. -/
theorem coeffGood_mul_prime_of_large {m p : ℕ}
    (hm : CoeffGoodDenominator m) (hp : p.Prime)
    (hlarge : Nat.lcmUpto m * m < p) :
    CoeffGoodDenominator (m * p) :=
  coeffGood_mul_prime hm hp (primeCompatible_of_large hm.1 hp hlarge)

/-- Denominator one is the seed good denominator. -/
theorem coeffGood_one : CoeffGoodDenominator 1 := by
  refine ⟨by omega, ?_⟩
  intro w hw
  simp [signedReciprocalSum]

/-- In particular every prime denominator is good. -/
theorem goodDenominator_prime {p : ℕ} (hp : p.Prime) :
    GoodDenominator p := by
  apply goodDenominator_of_coeffGood
  have hlarge : Nat.lcmUpto 1 * 1 < p := by
    norm_num [Nat.lcmUpto]
    exact hp.one_lt
  simpa using coeffGood_mul_prime_of_large coeffGood_one hp hlarge

end Research
