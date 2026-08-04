import Research.Structural
import Mathlib.NumberTheory.Padics.PadicNorm

namespace Erdos321

/-- The primes in the interval `{1, …, N}`. -/
def primeDenominators (N : ℕ) : Finset ℕ :=
  (Finset.Icc 1 N).filter Nat.Prime

private theorem padicNorm_inv_prime_eq (p : ℕ) [Fact p.Prime] :
    padicNorm p ((p : ℚ)⁻¹) = (p : ℚ) := by
  rw [show ((p : ℚ)⁻¹) = (1 : ℚ) / p by simp, padicNorm.div,
    padicNorm.one, padicNorm.padicNorm_p_of_prime]
  simp

private theorem padicNorm_inv_other_prime_eq_one
    {p q : ℕ} [Fact p.Prime] (hq : q.Prime) (hpq : p ≠ q) :
    padicNorm p ((q : ℚ)⁻¹) = 1 := by
  letI : Fact q.Prime := ⟨hq⟩
  rw [show ((q : ℚ)⁻¹) = (1 : ℚ) / q by simp, padicNorm.div,
    padicNorm.one, padicNorm.padicNorm_of_prime_of_ne hpq]
  norm_num

/-- Reciprocals of distinct primes have distinct subset sums.  This is the
basic private-prime construction giving the first-order lower bound. -/
theorem valid_primeDenominators (N : ℕ) : Valid (primeDenominators N) := by
  classical
  rw [valid_iff_no_disjoint_collision]
  intro hCollision
  obtain ⟨S, hS, T, hT, hDisjoint, hNonempty, hEq⟩ := hCollision
  have impossible (X Y : Finset ℕ)
      (hX : X ∈ (primeDenominators N).powerset)
      (hY : Y ∈ (primeDenominators N).powerset)
      (hXY : Disjoint X Y) (hXne : X.Nonempty)
      (hSum : reciprocalSubsetSum X = reciprocalSubsetSum Y) : False := by
    obtain ⟨p, hpX⟩ := hXne
    have hpPrime : p.Prime := by
      have hpAll : p ∈ primeDenominators N := Finset.mem_powerset.mp hX hpX
      exact (Finset.mem_filter.mp hpAll).2
    letI : Fact p.Prime := ⟨hpPrime⟩
    have hNormY : padicNorm p (reciprocalSubsetSum Y) ≤ 1 := by
      apply padicNorm.sum_le'
      · intro q hq
        have hqPrime : q.Prime := by
          have hqAll : q ∈ primeDenominators N := Finset.mem_powerset.mp hY hq
          exact (Finset.mem_filter.mp hqAll).2
        have hpq : p ≠ q := by
          intro hpq
          subst q
          exact (Finset.disjoint_left.mp hXY hpX) hq
        rw [padicNorm_inv_other_prime_eq_one hqPrime hpq]
      · norm_num
    have hNormErase : padicNorm p (reciprocalSubsetSum (X.erase p)) ≤ 1 := by
      apply padicNorm.sum_le'
      · intro q hq
        have hqX : q ∈ X := (Finset.mem_erase.mp hq).2
        have hqPrime : q.Prime := by
          have hqAll : q ∈ primeDenominators N := Finset.mem_powerset.mp hX hqX
          exact (Finset.mem_filter.mp hqAll).2
        have hpq : p ≠ q := (Finset.mem_erase.mp hq).1.symm
        rw [padicNorm_inv_other_prime_eq_one hqPrime hpq]
      · norm_num
    have hDecomp : reciprocalSubsetSum (X.erase p) + ((p : ℚ)⁻¹) =
        reciprocalSubsetSum X := by
      simpa [reciprocalSubsetSum] using
        (Finset.sum_erase_add X (fun n : ℕ => ((n : ℚ)⁻¹)) hpX)
    have hIsolate : ((p : ℚ)⁻¹) =
        reciprocalSubsetSum Y - reciprocalSubsetSum (X.erase p) := by
      linarith
    have hNormRhs : padicNorm p
        (reciprocalSubsetSum Y - reciprocalSubsetSum (X.erase p)) ≤ 1 :=
      padicNorm.sub.trans (max_le hNormY hNormErase)
    rw [← hIsolate, padicNorm_inv_prime_eq] at hNormRhs
    exact (not_le_of_gt (by exact_mod_cast hpPrime.one_lt)) hNormRhs
  rcases hNonempty with hSne | hTne
  · exact impossible S T hS hT hDisjoint hSne hEq
  · exact impossible T S hT hS hDisjoint.symm hTne hEq.symm

/-- The concrete prime finset agrees with Mathlib's prime-counting finset. -/
theorem primeDenominators_eq_primesLE (N : ℕ) :
    primeDenominators N = Nat.primesLE N := by
  ext p
  constructor
  · intro hp
    have hp' := Finset.mem_filter.mp hp
    exact Nat.mem_primesLE.mpr ⟨(Finset.mem_Icc.mp hp'.1).2, hp'.2⟩
  · intro hp
    have hp' := Nat.mem_primesLE.mp hp
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hp'.2.one_le, hp'.1⟩, hp'.2⟩

@[simp] theorem card_primeDenominators (N : ℕ) :
    (primeDenominators N).card = Nat.primeCounting N := by
  rw [primeDenominators_eq_primesLE]
  exact Nat.primesLE_card_eq_primeCounting N

/-- The prime denominators are an admissible set of exactly `π(N)` elements. -/
theorem admissible_primeDenominators (N : ℕ) :
    Admissible N (primeDenominators N) := by
  constructor
  · intro p hp
    exact (Finset.mem_filter.mp hp).1
  · exact valid_primeDenominators N

/-- The elementary prime construction gives `π(N) ≤ R(N)`. -/
theorem primeCounting_le_extremalSize (N : ℕ) :
    Nat.primeCounting N ≤ extremalSize N := by
  rw [← card_primeDenominators]
  exact card_le_extremalSize (admissible_primeDenominators N)

end Erdos321
