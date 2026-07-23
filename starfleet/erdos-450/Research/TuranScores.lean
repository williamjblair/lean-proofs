import Research.MobiusDiscrepancy
import Mathlib.NumberTheory.SumPrimeReciprocals

namespace Erdos450

/-- Number of selected primes dividing `m`. -/
def primeScore (S : Finset ℕ) (m : ℕ) : ℕ :=
  (S.filter fun p => p ∣ m).card

/-- The two-level score, counting divisibility by `p` and by `p²`. -/
def primeSquareExtraScore (S : Finset ℕ) (m : ℕ) : ℕ :=
  ∑ p ∈ S, if p ^ 2 ∣ m then 1 else 0

def primeSquareScore (S : Finset ℕ) (m : ℕ) : ℕ :=
  primeScore S m + primeSquareExtraScore S m

/-- A common period for both selected-prime scores. -/
def primeSquarePeriod (S : Finset ℕ) : ℕ :=
  ∏ p ∈ S, p ^ 2

/-- Real reciprocal-prime mean of the one-level score. -/
noncomputable def primeReciprocalMean (S : Finset ℕ) : ℝ :=
  ∑ p ∈ S, (1 : ℝ) / p

/-- Sum of reciprocal prime squares. -/
noncomputable def primeReciprocalSqMean (S : Finset ℕ) : ℝ :=
  ∑ p ∈ S, (1 : ℝ) / p ^ 2

/-- Numerator of the mean of `primeScore` over its common period. -/
def primeScoreMeanNum (S : Finset ℕ) : ℕ :=
  ∑ p ∈ S, primeSquarePeriod S / p

/-- Extra numerator contributed by prime-square divisibility. -/
def primeSquareExtraNum (S : Finset ℕ) : ℕ :=
  ∑ p ∈ S, primeSquarePeriod S / p ^ 2

lemma primeScore_eq_sum (S : Finset ℕ) (m : ℕ) :
    primeScore S m = ∑ p ∈ S, if p ∣ m then 1 else 0 := by
  classical
  rw [primeScore, Finset.card_eq_sum_ones]
  exact Finset.sum_filter _ _

lemma primeSquarePeriod_pos (S : Finset ℕ)
    (hprime : ∀ p ∈ S, Nat.Prime p) : 0 < primeSquarePeriod S := by
  rw [primeSquarePeriod]
  exact Finset.prod_pos fun p hp => pow_pos (hprime p hp).pos 2

lemma pow_dvd_primeSquarePeriod (S : Finset ℕ) {p : ℕ} (hp : p ∈ S) :
    p ^ 2 ∣ primeSquarePeriod S := by
  unfold primeSquarePeriod
  exact Finset.dvd_prod_of_mem (fun q => q ^ 2) hp

lemma dvd_primeSquarePeriod (S : Finset ℕ) {p : ℕ} (hp : p ∈ S) :
    p ∣ primeSquarePeriod S :=
  dvd_trans (dvd_pow_self p (by omega : (2 : ℕ) ≠ 0))
    (pow_dvd_primeSquarePeriod S hp)

/-- The two-level score of a product dominates the sum of the one-level scores
of its factors; a prime occurring in both factors is then counted at level two. -/
theorem primeScore_product_le_squareScore (S : Finset ℕ) (a b : ℕ) :
    primeScore S a + primeScore S b ≤ primeSquareScore S (a * b) := by
  classical
  rw [primeScore_eq_sum, primeScore_eq_sum, primeSquareScore,
    primeScore_eq_sum, primeSquareExtraScore]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro p hp
  by_cases hpa : p ∣ a <;> by_cases hpb : p ∣ b
  · have hp2 : p ^ 2 ∣ a * b := by
      obtain ⟨a', rfl⟩ := hpa
      obtain ⟨b', rfl⟩ := hpb
      refine ⟨a' * b', ?_⟩
      ring
    simp [hpa, hpb, dvd_mul_of_dvd_left hpa b, hp2]
  · have hpab : p ∣ a * b := dvd_mul_of_dvd_left hpa b
    simp [hpa, hpb, hpab]
  · have hpab : p ∣ a * b := dvd_mul_of_dvd_right hpb a
    simp [hpa, hpb, hpab]
  · simp [hpa, hpb]

/-- Both score functions have the advertised period. -/
theorem primeScore_periodic (S : Finset ℕ) :
    Function.Periodic (primeScore S) (primeSquarePeriod S) := by
  intro m
  apply congrArg Finset.card
  apply Finset.filter_congr
  intro p hp
  exact (Nat.dvd_add_iff_left (dvd_primeSquarePeriod S hp)).symm

theorem primeSquareScore_periodic (S : Finset ℕ) :
    Function.Periodic (primeSquareScore S) (primeSquarePeriod S) := by
  intro m
  unfold primeSquareScore
  rw [primeScore_periodic S]
  congr 1
  unfold primeSquareExtraScore
  apply Finset.sum_congr rfl
  intro p hp
  have h2 : p ^ 2 ∣ m + primeSquarePeriod S ↔ p ^ 2 ∣ m :=
    (Nat.dvd_add_iff_left (pow_dvd_primeSquarePeriod S hp)).symm
  simp only [h2]

/-- Exact full-period count of multiples for a positive divisor of the period. -/
lemma multipleCount_zero_full_period (q Q : ℕ) (hq : 0 < q) (hqQ : q ∣ Q) :
    multipleCount q 0 Q = Q / q := by
  have hcancel : (Q / q) * q = Q := Nat.div_mul_cancel hqQ
  have h := periodic_filter_Ico_mul (fun m : ℕ => q ∣ m)
    (dvd_predicate_periodic q) (Q / q) 0
  rw [zero_add, hcancel, count_dvd_one_period q hq, Nat.mul_one] at h
  simpa only [multipleCount, zero_add] using h

/-- The sum of the one-level score over one period is its stated numerator. -/
theorem sum_primeScore_one_period (S : Finset ℕ)
    (hprime : ∀ p ∈ S, Nat.Prime p) :
    (∑ m ∈ Finset.range (primeSquarePeriod S), primeScore S m) =
      primeScoreMeanNum S := by
  classical
  simp_rw [primeScore_eq_sum]
  rw [Finset.sum_comm]
  unfold primeScoreMeanNum
  apply Finset.sum_congr rfl
  intro p hp
  have hpQ := dvd_primeSquarePeriod S hp
  have hp0 := (hprime p hp).pos
  calc
    (∑ m ∈ Finset.range (primeSquarePeriod S), if p ∣ m then 1 else 0) =
        multipleCount p 0 (primeSquarePeriod S) := by
      rw [Finset.sum_boole]
      simp only [multipleCount, zero_add, Finset.range_eq_Ico]
      norm_cast
    _ = primeSquarePeriod S / p :=
      multipleCount_zero_full_period p _ hp0 hpQ

/-- Pair correlation of distinct selected prime-divisibility indicators. -/
lemma sum_prime_dvd_pair_one_period (S : Finset ℕ)
    (hprime : ∀ p ∈ S, Nat.Prime p) {p r : ℕ}
    (hp : p ∈ S) (hr : r ∈ S) (hne : p ≠ r) :
    (∑ m ∈ Finset.range (primeSquarePeriod S),
      (if p ∣ m then 1 else 0) * (if r ∣ m then 1 else 0)) =
      primeSquarePeriod S / (p * r) := by
  classical
  have hcop : p.Coprime r :=
    (Nat.coprime_primes (hprime p hp) (hprime r hr)).2 hne
  have hprQ : p * r ∣ primeSquarePeriod S :=
    hcop.mul_dvd_of_dvd_of_dvd (dvd_primeSquarePeriod S hp)
      (dvd_primeSquarePeriod S hr)
  have hiff (m : ℕ) : (p ∣ m ∧ r ∣ m) ↔ p * r ∣ m := by
    constructor
    · rintro ⟨hpm, hrm⟩
      exact hcop.mul_dvd_of_dvd_of_dvd hpm hrm
    · intro h
      exact ⟨dvd_trans (dvd_mul_right p r) h,
        dvd_trans (dvd_mul_left r p) (by simpa [Nat.mul_comm] using h)⟩
  calc
    (∑ m ∈ Finset.range (primeSquarePeriod S),
      (if p ∣ m then 1 else 0) * (if r ∣ m then 1 else 0)) =
        ∑ m ∈ Finset.range (primeSquarePeriod S),
          if p * r ∣ m then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro m hm
      by_cases hpm : p ∣ m <;> by_cases hrm : r ∣ m <;>
        simp [hpm, hrm, ← hiff]
    _ = multipleCount (p * r) 0 (primeSquarePeriod S) := by
      rw [Finset.sum_boole]
      simp only [multipleCount, zero_add, Finset.range_eq_Ico]
      norm_cast
    _ = primeSquarePeriod S / (p * r) := by
      apply multipleCount_zero_full_period _ _
      · exact Nat.mul_pos (hprime p hp).pos (hprime r hr).pos
      · exact hprQ

/-- Exact second moment of the selected-prime score. -/
theorem sum_primeScore_sq_one_period (S : Finset ℕ)
    (hprime : ∀ p ∈ S, Nat.Prime p) :
    (∑ m ∈ Finset.range (primeSquarePeriod S), (primeScore S m) ^ 2) =
      ∑ p ∈ S, ∑ r ∈ S,
        if p = r then primeSquarePeriod S / p
        else primeSquarePeriod S / (p * r) := by
  classical
  simp_rw [primeScore_eq_sum, pow_two, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p hp
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r hr
  by_cases hpr : p = r
  · subst r
    simp only [↓reduceIte]
    calc
      (∑ m ∈ Finset.range (primeSquarePeriod S),
        (if p ∣ m then 1 else 0) * if p ∣ m then 1 else 0) =
          ∑ m ∈ Finset.range (primeSquarePeriod S),
            if p ∣ m then 1 else 0 := by
        apply Finset.sum_congr rfl
        intro m hm
        by_cases h : p ∣ m <;> simp [h]
      _ = primeSquarePeriod S / p := by
        rw [Finset.sum_boole]
        norm_cast
        simpa only [multipleCount, zero_add, Finset.range_eq_Ico] using
          multipleCount_zero_full_period p _ (hprime p hp).pos
            (dvd_primeSquarePeriod S hp)
  · simp only [hpr, ↓reduceIte]
    exact sum_prime_dvd_pair_one_period S hprime hp hr hpr

/-- Cast of the integral mean numerator. -/
lemma primeScoreMeanNum_cast (S : Finset ℕ)
    (hprime : ∀ p ∈ S, Nat.Prime p) :
    (primeScoreMeanNum S : ℝ) =
      (primeSquarePeriod S : ℝ) * primeReciprocalMean S := by
  unfold primeScoreMeanNum primeReciprocalMean
  push_cast
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  rw [Nat.cast_div_charZero (dvd_primeSquarePeriod S hp)]
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast (hprime p hp).ne_zero
  field_simp

lemma primeSquareExtraNum_cast (S : Finset ℕ)
    (hprime : ∀ p ∈ S, Nat.Prime p) :
    (primeSquareExtraNum S : ℝ) =
      (primeSquarePeriod S : ℝ) * primeReciprocalSqMean S := by
  unfold primeSquareExtraNum primeReciprocalSqMean
  push_cast
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  rw [Nat.cast_div_charZero (pow_dvd_primeSquarePeriod S hp)]
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast (hprime p hp).ne_zero
  field_simp
  norm_num

/-- Exact real second moment, in independent Bernoulli form. -/
theorem sum_primeScore_sq_one_period_real (S : Finset ℕ)
    (hprime : ∀ p ∈ S, Nat.Prime p) :
    (∑ m ∈ Finset.range (primeSquarePeriod S), (primeScore S m : ℝ) ^ 2) =
      (primeSquarePeriod S : ℝ) *
        (primeReciprocalMean S ^ 2 + primeReciprocalMean S -
          primeReciprocalSqMean S) := by
  have hnat := sum_primeScore_sq_one_period S hprime
  have hnatR := congrArg (fun z : ℕ => (z : ℝ)) hnat
  simp only [Nat.cast_sum, Nat.cast_pow] at hnatR
  classical
  unfold primeReciprocalMean primeReciprocalSqMean
  calc
    (∑ m ∈ Finset.range (primeSquarePeriod S), (primeScore S m : ℝ) ^ 2) =
        ∑ p ∈ S, ∑ r ∈ S,
          (((if p = r then primeSquarePeriod S / p
            else primeSquarePeriod S / (p * r)) : ℕ) : ℝ) := hnatR
    _ = (primeSquarePeriod S : ℝ) *
        ((∑ p ∈ S, (1 : ℝ) / p) ^ 2 +
          ∑ p ∈ S, (1 : ℝ) / p - ∑ p ∈ S, (1 : ℝ) / p ^ 2) := by
      let Q : ℝ := primeSquarePeriod S
      have hterm (p : ℕ) (hp : p ∈ S) (r : ℕ) (hr : r ∈ S) :
          (((if p = r then primeSquarePeriod S / p
            else primeSquarePeriod S / (p * r)) : ℕ) : ℝ) =
          Q * ((1 / (p : ℝ)) * (1 / (r : ℝ)) +
            if p = r then (1 / (p : ℝ) - 1 / (p : ℝ) ^ 2) else 0) := by
        by_cases hpr : p = r
        · subst r
          simp only [↓reduceIte]
          rw [Nat.cast_div_charZero (dvd_primeSquarePeriod S hp)]
          dsimp only [Q]
          field_simp [(hprime p hp).ne_zero]
          ring
        · simp only [hpr, ↓reduceIte, add_zero]
          have hc : p.Coprime r :=
            (Nat.coprime_primes (hprime p hp) (hprime r hr)).2 hpr
          have hd : p * r ∣ primeSquarePeriod S :=
            hc.mul_dvd_of_dvd_of_dvd (dvd_primeSquarePeriod S hp)
              (dvd_primeSquarePeriod S hr)
          dsimp only [Q]
          field_simp [(hprime p hp).ne_zero, (hprime r hr).ne_zero]
          exact_mod_cast (by
            simpa only [Nat.mul_assoc] using Nat.div_mul_cancel hd)
      have hmain :
          (∑ p ∈ S, ∑ r ∈ S,
            Q * ((1 / (p : ℝ)) * (1 / (r : ℝ)))) =
            Q * (∑ p ∈ S, (1 : ℝ) / p) ^ 2 := by
        calc
          (∑ p ∈ S, ∑ r ∈ S,
            Q * ((1 / (p : ℝ)) * (1 / (r : ℝ)))) =
              ∑ p ∈ S, (Q * (1 / (p : ℝ))) *
                (∑ r ∈ S, (1 : ℝ) / r) := by
            apply Finset.sum_congr rfl
            intro p hp
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro r hr
            ring
          _ = Q * (∑ p ∈ S, (1 : ℝ) / p) *
              (∑ r ∈ S, (1 : ℝ) / r) := by
            rw [← Finset.sum_mul, ← Finset.mul_sum]
          _ = Q * (∑ p ∈ S, (1 : ℝ) / p) ^ 2 := by ring
      have hdiag :
          (∑ p ∈ S, ∑ r ∈ S,
            Q * (if p = r then
              (1 / (p : ℝ) - 1 / (p : ℝ) ^ 2) else 0)) =
            Q * ((∑ p ∈ S, (1 : ℝ) / p) -
              ∑ p ∈ S, (1 : ℝ) / p ^ 2) := by
        calc
          (∑ p ∈ S, ∑ r ∈ S,
            Q * (if p = r then
              (1 / (p : ℝ) - 1 / (p : ℝ) ^ 2) else 0)) =
              ∑ p ∈ S, Q *
                (1 / (p : ℝ) - 1 / (p : ℝ) ^ 2) := by
            apply Finset.sum_congr rfl
            intro p hp
            rw [← Finset.mul_sum, Finset.sum_ite_eq S p]
            simp only [hp, ↓reduceIte]
          _ = Q * ((∑ p ∈ S, (1 : ℝ) / p) -
              ∑ p ∈ S, (1 : ℝ) / p ^ 2) := by
            rw [← Finset.mul_sum, Finset.sum_sub_distrib]
      calc
        (∑ p ∈ S, ∑ r ∈ S,
          (((if p = r then primeSquarePeriod S / p
            else primeSquarePeriod S / (p * r)) : ℕ) : ℝ)) =
            ∑ p ∈ S, ∑ r ∈ S,
              Q * ((1 / (p : ℝ)) * (1 / (r : ℝ)) +
                if p = r then (1 / (p : ℝ) - 1 / (p : ℝ) ^ 2) else 0) := by
          apply Finset.sum_congr rfl
          intro p hp
          apply Finset.sum_congr rfl
          intro r hr
          exact hterm p hp r hr
        _ = Q * ((∑ p ∈ S, (1 : ℝ) / p) ^ 2 +
            ∑ p ∈ S, (1 : ℝ) / p - ∑ p ∈ S, (1 : ℝ) / p ^ 2) := by
          simp_rw [mul_add, Finset.sum_add_distrib]
          rw [hmain, hdiag]
          ring
        _ = (primeSquarePeriod S : ℝ) *
            ((∑ p ∈ S, (1 : ℝ) / p) ^ 2 +
              ∑ p ∈ S, (1 : ℝ) / p - ∑ p ∈ S, (1 : ℝ) / p ^ 2) := by
          simp only [Q]
  


/-- Variance bound for the one-level selected-prime score. -/
theorem sum_primeScore_deviation_sq_le (S : Finset ℕ)
    (hprime : ∀ p ∈ S, Nat.Prime p) :
    (∑ m ∈ Finset.range (primeSquarePeriod S),
      ((primeScore S m : ℝ) - primeReciprocalMean S) ^ 2) ≤
      (primeSquarePeriod S : ℝ) * primeReciprocalMean S := by
  have hmeanN := sum_primeScore_one_period S hprime
  have hmean :
      (∑ m ∈ Finset.range (primeSquarePeriod S), (primeScore S m : ℝ)) =
        (primeSquarePeriod S : ℝ) * primeReciprocalMean S := by
    have hmeanR := congrArg (fun z : ℕ => (z : ℝ)) hmeanN
    push_cast at hmeanR
    rw [hmeanR, primeScoreMeanNum_cast S hprime]
  have hsquare := sum_primeScore_sq_one_period_real S hprime
  have hsqnonneg : 0 ≤ primeReciprocalSqMean S := by
    unfold primeReciprocalSqMean
    positivity
  have hcross :
      (∑ m ∈ Finset.range (primeSquarePeriod S),
        2 * (primeScore S m : ℝ) * primeReciprocalMean S) =
      2 * primeReciprocalMean S *
        (∑ m ∈ Finset.range (primeSquarePeriod S), (primeScore S m : ℝ)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m hm
    ring
  calc
    (∑ m ∈ Finset.range (primeSquarePeriod S),
        ((primeScore S m : ℝ) - primeReciprocalMean S) ^ 2) =
        (∑ m ∈ Finset.range (primeSquarePeriod S),
          (primeScore S m : ℝ) ^ 2) -
        2 * primeReciprocalMean S *
          (∑ m ∈ Finset.range (primeSquarePeriod S), (primeScore S m : ℝ)) +
        (primeSquarePeriod S : ℝ) * primeReciprocalMean S ^ 2 := by
      simp_rw [sub_sq]
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
        Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      rw [hcross]
    _ = (primeSquarePeriod S : ℝ) *
        (primeReciprocalMean S - primeReciprocalSqMean S) := by
      rw [hsquare, hmean]
      ring
    _ ≤ (primeSquarePeriod S : ℝ) * primeReciprocalMean S := by
      exact mul_le_mul_of_nonneg_left (sub_le_self _ hsqnonneg)
        (by positivity)

/-- The extra square-divisibility score has the analogous exact mean. -/
theorem sum_primeSquareExtra_one_period (S : Finset ℕ)
    (hprime : ∀ p ∈ S, Nat.Prime p) :
    (∑ m ∈ Finset.range (primeSquarePeriod S),
      primeSquareExtraScore S m) = primeSquareExtraNum S := by
  simp only [primeSquareExtraScore]
  classical
  rw [Finset.sum_comm]
  unfold primeSquareExtraNum
  apply Finset.sum_congr rfl
  intro p hp
  have hpQ := pow_dvd_primeSquarePeriod S hp
  have hp0 : 0 < p ^ 2 := pow_pos (hprime p hp).pos 2
  calc
    (∑ m ∈ Finset.range (primeSquarePeriod S), if p ^ 2 ∣ m then 1 else 0) =
        multipleCount (p ^ 2) 0 (primeSquarePeriod S) := by
      rw [Finset.sum_boole]
      simp only [multipleCount, zero_add, Finset.range_eq_Ico]
      norm_cast
    _ = primeSquarePeriod S / p ^ 2 :=
      multipleCount_zero_full_period (p ^ 2) _ hp0 hpQ

/-- A finite Markov inequality in cardinal form. -/
lemma filter_card_mul_le_sum_of_pointwise
    {α : Type*} [DecidableEq α] (s : Finset α) (p : α → Prop)
    [DecidablePred p] (f : α → ℝ) (c : ℝ)
    (hf : ∀ x ∈ s, 0 ≤ f x)
    (hpoint : ∀ x ∈ s, p x → c ≤ f x) :
    (((s.filter p).card : ℝ) * c) ≤ ∑ x ∈ s, f x := by
  calc
    ((s.filter p).card : ℝ) * c = ∑ _x ∈ s.filter p, c := by simp
    _ ≤ ∑ x ∈ s.filter p, f x := by
      apply Finset.sum_le_sum
      intro x hx
      have hx' := Finset.mem_filter.mp hx
      exact hpoint x hx'.1 hx'.2
    _ ≤ ∑ x ∈ s, f x := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · exact Finset.filter_subset _ _
      · intro x hxs hnot
        exact hf x hxs

/-- Selected primes at least five contribute at most one fifth as much at
square level as at first level. -/
theorem reciprocalSqMean_le_one_fifth (S : Finset ℕ)
    (hfive : ∀ p ∈ S, 5 ≤ p) :
    primeReciprocalSqMean S ≤ (1 / 5 : ℝ) * primeReciprocalMean S := by
  unfold primeReciprocalSqMean primeReciprocalMean
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro p hp
  have hpR : (5 : ℝ) ≤ p := by exact_mod_cast hfive p hp
  have hp0 : (0 : ℝ) < p := lt_of_lt_of_le (by norm_num) hpR
  field_simp
  nlinarith

/-- Lower-tail Chebyshev bound in one complete period. -/
theorem low_primeScore_period_bound (S : Finset ℕ)
    (hprime : ∀ p ∈ S, Nat.Prime p)
    (hmu : 0 < primeReciprocalMean S) :
    (((Finset.range (primeSquarePeriod S)).filter (fun m =>
        (primeScore S m : ℝ) ≤ (3 / 4 : ℝ) * primeReciprocalMean S)).card : ℝ) *
        primeReciprocalMean S ≤ 16 * primeSquarePeriod S := by
  classical
  have hpoint (m : ℕ) (hm : m ∈ Finset.range (primeSquarePeriod S))
      (hlow : (primeScore S m : ℝ) ≤ (3 / 4 : ℝ) * primeReciprocalMean S) :
      (primeReciprocalMean S / 4) ^ 2 ≤
        ((primeScore S m : ℝ) - primeReciprocalMean S) ^ 2 := by
    nlinarith [sq_nonneg ((primeScore S m : ℝ) -
      (3 / 4 : ℝ) * primeReciprocalMean S)]
  have hmark := filter_card_mul_le_sum_of_pointwise
    (Finset.range (primeSquarePeriod S))
    (fun m => (primeScore S m : ℝ) ≤
      (3 / 4 : ℝ) * primeReciprocalMean S)
    (fun m => ((primeScore S m : ℝ) - primeReciprocalMean S) ^ 2)
    ((primeReciprocalMean S / 4) ^ 2)
    (fun _ _ => sq_nonneg _) hpoint
  have hvar := sum_primeScore_deviation_sq_le S hprime
  have hQ : (0 : ℝ) ≤ primeSquarePeriod S := by positivity
  nlinarith

/-- The same Chebyshev argument controls the upper tail of the one-level score. -/
theorem high_primeScore_period_bound (S : Finset ℕ)
    (hprime : ∀ p ∈ S, Nat.Prime p)
    (hmu : 0 < primeReciprocalMean S) :
    (((Finset.range (primeSquarePeriod S)).filter (fun m =>
        (5 / 4 : ℝ) * primeReciprocalMean S ≤ (primeScore S m : ℝ))).card : ℝ) *
        primeReciprocalMean S ≤ 16 * primeSquarePeriod S := by
  classical
  have hpoint (m : ℕ) (hm : m ∈ Finset.range (primeSquarePeriod S))
      (hhigh : (5 / 4 : ℝ) * primeReciprocalMean S ≤ (primeScore S m : ℝ)) :
      (primeReciprocalMean S / 4) ^ 2 ≤
        ((primeScore S m : ℝ) - primeReciprocalMean S) ^ 2 := by
    nlinarith [sq_nonneg ((primeScore S m : ℝ) -
      (5 / 4 : ℝ) * primeReciprocalMean S)]
  have hmark := filter_card_mul_le_sum_of_pointwise
    (Finset.range (primeSquarePeriod S))
    (fun m => (5 / 4 : ℝ) * primeReciprocalMean S ≤ (primeScore S m : ℝ))
    (fun m => ((primeScore S m : ℝ) - primeReciprocalMean S) ^ 2)
    ((primeReciprocalMean S / 4) ^ 2)
    (fun _ _ => sq_nonneg _) hpoint
  have hvar := sum_primeScore_deviation_sq_le S hprime
  have hQ : (0 : ℝ) ≤ primeSquarePeriod S := by positivity
  nlinarith

/-- Markov bound for unusually many selected prime squares. -/
theorem high_primeSquareExtra_period_bound (S : Finset ℕ)
    (hprime : ∀ p ∈ S, Nat.Prime p)
    (_hmu : 0 < primeReciprocalMean S) :
    (((Finset.range (primeSquarePeriod S)).filter (fun m =>
        primeReciprocalMean S / 4 ≤ (primeSquareExtraScore S m : ℝ))).card : ℝ) *
        primeReciprocalMean S ≤
      4 * primeSquarePeriod S * primeReciprocalSqMean S := by
  classical
  have hpoint (m : ℕ) (hm : m ∈ Finset.range (primeSquarePeriod S))
      (hhigh : primeReciprocalMean S / 4 ≤ (primeSquareExtraScore S m : ℝ)) :
      primeReciprocalMean S / 4 ≤ (primeSquareExtraScore S m : ℝ) := hhigh
  have hmark := filter_card_mul_le_sum_of_pointwise
    (Finset.range (primeSquarePeriod S))
    (fun m => primeReciprocalMean S / 4 ≤ (primeSquareExtraScore S m : ℝ))
    (fun m => (primeSquareExtraScore S m : ℝ))
    (primeReciprocalMean S / 4)
    (fun _ _ => Nat.cast_nonneg _) hpoint
  have hsumN := sum_primeSquareExtra_one_period S hprime
  have hsumR := congrArg (fun z : ℕ => (z : ℝ)) hsumN
  push_cast at hsumR
  rw [hsumR, primeSquareExtraNum_cast S hprime] at hmark
  nlinarith

/-- The reciprocal-square contribution of any finite prime set is absolutely bounded. -/
theorem reciprocalSqMean_le_three (S : Finset ℕ) :
    primeReciprocalSqMean S ≤ 3 := by
  unfold primeReciprocalSqMean
  have hsumm : Summable (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2) :=
    hasSum_zeta_two.summable
  calc
    (∑ p ∈ S, (1 : ℝ) / (p : ℝ) ^ 2) ≤
        ∑' n : ℕ, (1 : ℝ) / (n : ℝ) ^ 2 := by
      exact hsumm.sum_le_tsum S (fun _ _ => by positivity)
    _ = Real.pi ^ 2 / 6 := hasSum_zeta_two.tsum_eq
    _ ≤ 3 := by
      have hpipos : 0 ≤ Real.pi := Real.pi_pos.le
      have hpile := Real.pi_le_four
      nlinarith

/-- Upper-tail bound for the two-level score.  If it is at least `3μ/2`,
either the first-level score is `≥5μ/4` or the extra square score is `≥μ/4`. -/
theorem high_primeSquareScore_period_bound (S : Finset ℕ)
    (hprime : ∀ p ∈ S, Nat.Prime p)
    (_hfive : ∀ p ∈ S, 5 ≤ p)
    (hmu : 0 < primeReciprocalMean S) :
    (((Finset.range (primeSquarePeriod S)).filter (fun m =>
        (3 / 2 : ℝ) * primeReciprocalMean S ≤
          (primeSquareScore S m : ℝ))).card : ℝ) *
        primeReciprocalMean S ≤ 28 * primeSquarePeriod S := by
  classical
  let R := Finset.range (primeSquarePeriod S)
  let H := R.filter (fun m => (3 / 2 : ℝ) * primeReciprocalMean S ≤
    (primeSquareScore S m : ℝ))
  let H₁ := R.filter (fun m => (5 / 4 : ℝ) * primeReciprocalMean S ≤
    (primeScore S m : ℝ))
  let H₂ := R.filter (fun m => primeReciprocalMean S / 4 ≤
    (primeSquareExtraScore S m : ℝ))
  have hsub : H ⊆ H₁ ∪ H₂ := by
    intro m hm
    have hm' := Finset.mem_filter.mp hm
    have hmR : m ∈ R := hm'.1
    have hhigh := hm'.2
    by_cases h1 : (5 / 4 : ℝ) * primeReciprocalMean S ≤ (primeScore S m : ℝ)
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hmR, h1⟩)
    · apply Finset.mem_union_right
      apply Finset.mem_filter.mpr
      refine ⟨hmR, ?_⟩
      rw [primeSquareScore] at hhigh
      push_cast at hhigh
      nlinarith
  have hcard : H.card ≤ H₁.card + H₂.card :=
    le_trans (Finset.card_le_card hsub) (Finset.card_union_le H₁ H₂)
  have h1bound := high_primeScore_period_bound S hprime hmu
  have h2bound := high_primeSquareExtra_period_bound S hprime hmu
  have hnubound := reciprocalSqMean_le_three S
  have h2simple : (H₂.card : ℝ) * primeReciprocalMean S ≤
      12 * primeSquarePeriod S := by
    dsimp only [H₂, R]
    calc
      (((Finset.range (primeSquarePeriod S)).filter (fun m =>
          primeReciprocalMean S / 4 ≤
            (primeSquareExtraScore S m : ℝ))).card : ℝ) *
          primeReciprocalMean S
          ≤ 4 * primeSquarePeriod S * primeReciprocalSqMean S := h2bound
      _ ≤ 12 * primeSquarePeriod S := by
        have hQ : (0 : ℝ) ≤ primeSquarePeriod S := by positivity
        nlinarith
  have hcardR : (H.card : ℝ) ≤ H₁.card + H₂.card := by exact_mod_cast hcard
  dsimp only [H, H₁, H₂, R] at hcardR h2simple ⊢
  have hmu0 := hmu.le
  nlinarith

/-- A period proportion bound transfers to every interval, with one period of
boundary loss. -/
theorem periodic_filter_interval_weighted_bound
    (p : ℕ → Prop) [DecidablePred p] (Q x l : ℕ) (μ C : ℝ)
    (hQ : 0 < Q) (hμ : 0 ≤ μ) (hC : 0 ≤ C)
    (hp : Function.Periodic p Q)
    (hperiod : (Nat.count p Q : ℝ) * μ ≤ C * Q) :
    ((((Finset.Ico x (x + l)).filter p).card : ℝ) * μ) ≤
      C * (l + Q) := by
  have hcard := periodic_filter_Ico_le p hQ hp x l
  have hcardR :
      ((((Finset.Ico x (x + l)).filter p).card : ℝ)) ≤
        ((l / Q + 1) * Nat.count p Q : ℕ) := by
    exact_mod_cast hcard
  have hmul :
      ((((Finset.Ico x (x + l)).filter p).card : ℝ) * μ) ≤
        (((l / Q + 1) * Nat.count p Q : ℕ) : ℝ) * μ :=
    mul_le_mul_of_nonneg_right hcardR hμ
  have hfloor : Q * (l / Q) ≤ l := by
    simpa only [Nat.mul_comm] using Nat.div_mul_le_self l Q
  have hfloorR : (Q : ℝ) * (l / Q : ℕ) ≤ l := by exact_mod_cast hfloor
  calc
    ((((Finset.Ico x (x + l)).filter p).card : ℝ) * μ)
        ≤ (((l / Q + 1) * Nat.count p Q : ℕ) : ℝ) * μ := hmul
    _ = ((l / Q : ℕ) + 1 : ℝ) * ((Nat.count p Q : ℝ) * μ) := by
      push_cast
      ring
    _ ≤ ((l / Q : ℕ) + 1 : ℝ) * (C * Q) := by
      gcongr
    _ ≤ C * (l + Q) := by
      nlinarith

/-- Uniform interval count for the low one-level score. -/
theorem low_primeScore_interval_bound (S : Finset ℕ)
    (hprime : ∀ p ∈ S, Nat.Prime p)
    (hmu : 0 < primeReciprocalMean S) (x l : ℕ) :
    ((((Finset.Ico x (x + l)).filter (fun m =>
        (primeScore S m : ℝ) ≤ (3 / 4 : ℝ) * primeReciprocalMean S)).card : ℝ) *
      primeReciprocalMean S) ≤
        16 * (l + primeSquarePeriod S) := by
  classical
  apply periodic_filter_interval_weighted_bound _ _ _ _ _ 16
    (primeSquarePeriod_pos S hprime) hmu.le (by norm_num)
  · intro m
    apply propext
    change (primeScore S (m + primeSquarePeriod S) : ℝ) ≤ _ ↔
      (primeScore S m : ℝ) ≤ _
    rw [primeScore_periodic S m]
  · simpa only [Nat.count_eq_card_filter_range] using
      low_primeScore_period_bound S hprime hmu

/-- Uniform interval count for the high two-level score. -/
theorem high_primeSquareScore_interval_bound (S : Finset ℕ)
    (hprime : ∀ p ∈ S, Nat.Prime p) (hfive : ∀ p ∈ S, 5 ≤ p)
    (hmu : 0 < primeReciprocalMean S) (x l : ℕ) :
    ((((Finset.Ico x (x + l)).filter (fun m =>
        (3 / 2 : ℝ) * primeReciprocalMean S ≤
          (primeSquareScore S m : ℝ))).card : ℝ) *
      primeReciprocalMean S) ≤
        28 * (l + primeSquarePeriod S) := by
  classical
  apply periodic_filter_interval_weighted_bound _ _ _ _ _ 28
    (primeSquarePeriod_pos S hprime) hmu.le (by norm_num)
  · intro m
    apply propext
    change _ ≤ (primeSquareScore S (m + primeSquarePeriod S) : ℝ) ↔
      _ ≤ (primeSquareScore S m : ℝ)
    rw [primeSquareScore_periodic S m]
  · simpa only [Nat.count_eq_card_filter_range] using
      high_primeSquareScore_period_bound S hprime hfive hmu

end Erdos450
