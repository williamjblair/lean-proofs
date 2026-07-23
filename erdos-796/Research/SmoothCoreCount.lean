import Research.GreatestPrime
import Mathlib.Analysis.SpecificLimits.Normed

namespace Erdos796

open Filter Topology

/-- All prime divisors of `d` lie through `S`. -/
def PrimeFactorsLE (S d : ℕ) : Prop :=
  ∀ p, p.Prime → p ∣ d → p ≤ S

/-- Positive `S`-smooth integers through `X`. -/
noncomputable def smoothCoresUpTo (S X : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Icc 1 X).filter (PrimeFactorsLE S)

lemma mem_smoothCoresUpTo {S X d : ℕ} :
    d ∈ smoothCoresUpTo S X ↔
      1 ≤ d ∧ d ≤ X ∧ PrimeFactorsLE S d := by
  classical
  simp [smoothCoresUpTo, and_assoc]

/-- Exponent vector over the primes through `S`, for a smooth integer through
`2^j`. -/
noncomputable def smoothExponentVector (S j : ℕ)
    (d : ↥(smoothCoresUpTo S (2 ^ j))) :
    ↥(Nat.primesLE S) → Fin (j + 1) := fun p => by
  have hdle : d.1 ≤ 2 ^ j := (mem_smoothCoresUpTo.mp d.2).2.1
  have hp2 : 2 ≤ p.1 := (Nat.mem_primesLE.mp p.2).2.two_le
  have hpow : d.1 ≤ p.1 ^ j := hdle.trans (Nat.pow_le_pow_left hp2 j)
  exact ⟨d.1.factorization p.1,
    Nat.lt_succ_of_le (Nat.factorization_le_of_le_pow hpow)⟩

/-- Smooth exponent vectors determine their integers. -/
theorem smoothExponentVector_injective (S j : ℕ) :
    Function.Injective (smoothExponentVector S j) := by
  intro d e hde
  apply Subtype.ext
  apply Nat.factorization_inj
  · exact Nat.ne_of_gt (mem_smoothCoresUpTo.mp d.2).1
  · exact Nat.ne_of_gt (mem_smoothCoresUpTo.mp e.2).1
  ext p
  by_cases hp : p.Prime
  · by_cases hpS : p ≤ S
    · let ps : ↥(Nat.primesLE S) :=
        ⟨p, Nat.mem_primesLE.mpr ⟨hpS, hp⟩⟩
      have hv := congrArg (fun v => ((v ps : Fin (j + 1)) : ℕ)) hde
      change d.1.factorization p = e.1.factorization p at hv
      exact hv
    · have hdSmooth := (mem_smoothCoresUpTo.mp d.2).2.2
      have heSmooth := (mem_smoothCoresUpTo.mp e.2).2.2
      have hnd : ¬p ∣ d.1 := fun hpd => hpS (hdSmooth p hp hpd)
      have hne : ¬p ∣ e.1 := fun hpe => hpS (heSmooth p hp hpe)
      rw [Nat.factorization_eq_zero_of_not_dvd hnd,
        Nat.factorization_eq_zero_of_not_dvd hne]
  · rw [Nat.factorization_eq_zero_of_not_prime d.1 hp,
      Nat.factorization_eq_zero_of_not_prime e.1 hp]

/-- Elementary polynomial-in-log census of fixed-smooth integers. -/
theorem smoothCoresUpTo_two_pow_card_le (S j : ℕ) :
    (smoothCoresUpTo S (2 ^ j)).card ≤
      (j + 1) ^ Nat.primeCounting S := by
  have hc := Fintype.card_le_of_injective (smoothExponentVector S j)
    (smoothExponentVector_injective S j)
  rw [Fintype.card_coe, Fintype.card_fun, Fintype.card_fin,
    Fintype.card_coe, Nat.primesLE_card_eq_primeCounting] at hc
  exact hc

/-- One dyadic block of positive fixed-smooth cores. -/
noncomputable def smoothCoreDyadicBlock (S j : ℕ) : Finset ℕ :=
  (smoothCoresUpTo S (2 ^ (j + 1))).filter fun d => 2 ^ j ≤ d

/-- Reciprocal mass in one fixed-smooth dyadic block. -/
noncomputable def smoothCoreDyadicMass (S j : ℕ) : ℝ :=
  ∑ d ∈ smoothCoreDyadicBlock S j, (1 : ℝ) / d

/-- Fixed-smooth dyadic reciprocal majorants form a summable series. -/
theorem summable_smoothDyadicMajorant (S : ℕ) :
    Summable (fun j : ℕ =>
      (((j + 2) ^ Nat.primeCounting S : ℕ) : ℝ) / (2 : ℝ) ^ j) := by
  have h := summable_pow_mul_geometric_of_norm_lt_one
    (R := ℝ) (Nat.primeCounting S) (r := (1 : ℝ) / 2) (by norm_num)
  have hshift : Summable (fun j : ℕ =>
      ((j + 2 : ℕ) : ℝ) ^ Nat.primeCounting S * ((1 : ℝ) / 2) ^ (j + 2)) := by
    simpa only [Nat.cast_add, Nat.cast_ofNat] using
      ((summable_nat_add_iff 2).mpr h)
  have hmul := hshift.mul_left (4 : ℝ)
  apply hmul.congr
  intro j
  push_cast
  rw [div_pow]
  ring

lemma smoothCoreDyadicMass_nonneg (S j : ℕ) :
    0 ≤ smoothCoreDyadicMass S j := by
  unfold smoothCoreDyadicMass
  positivity

/-- Polynomial-over-geometric pointwise bound for a smooth dyadic block. -/
theorem smoothCoreDyadicMass_le (S j : ℕ) :
    smoothCoreDyadicMass S j ≤
      (((j + 2) ^ Nat.primeCounting S : ℕ) : ℝ) / (2 : ℝ) ^ j := by
  have hcard : (smoothCoreDyadicBlock S j).card ≤
      (j + 2) ^ Nat.primeCounting S := by
    apply (Finset.card_le_card (Finset.filter_subset _ _)).trans
    simpa [Nat.add_assoc] using smoothCoresUpTo_two_pow_card_le S (j + 1)
  have hterm : ∀ d ∈ smoothCoreDyadicBlock S j,
      (1 : ℝ) / d ≤ (1 : ℝ) / (2 : ℝ) ^ j := by
    intro d hd
    have hdlo := (Finset.mem_filter.mp hd).2
    exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast hdlo)
  unfold smoothCoreDyadicMass
  calc
    (∑ d ∈ smoothCoreDyadicBlock S j, (1 : ℝ) / d)
      ≤ ∑ _d ∈ smoothCoreDyadicBlock S j,
          (1 : ℝ) / (2 : ℝ) ^ j := Finset.sum_le_sum hterm
    _ = ((smoothCoreDyadicBlock S j).card : ℝ) / (2 : ℝ) ^ j := by
      rw [Finset.sum_const, nsmul_eq_mul]
      ring
    _ ≤ (((j + 2) ^ Nat.primeCounting S : ℕ) : ℝ) / (2 : ℝ) ^ j := by
      gcongr

/-- Fixed-smooth reciprocal dyadic masses are summable. -/
theorem summable_smoothCoreDyadicMass (S : ℕ) :
    Summable (smoothCoreDyadicMass S) :=
  Summable.of_nonneg_of_le (smoothCoreDyadicMass_nonneg S)
    (smoothCoreDyadicMass_le S) (summable_smoothDyadicMajorant S)

/-- The reciprocal mass of fixed-smooth dyadic blocks beyond a moving index
tends to zero. -/
theorem tendsto_smoothCoreDyadicTail_zero (S : ℕ) :
    Tendsto (fun J : ℕ => ∑' j : ℕ, smoothCoreDyadicMass S (j + J))
      Filter.atTop (nhds 0) := by
  let f := smoothCoreDyadicMass S
  have hf : Summable f := summable_smoothCoreDyadicMass S
  have hpartial := hf.hasSum.tendsto_sum_nat
  have hdiff : Tendsto (fun J : ℕ =>
      (∑' j : ℕ, f j) - ∑ j ∈ Finset.range J, f j)
      Filter.atTop (nhds 0) := by
    have hc : Tendsto (fun _ : ℕ => ∑' j : ℕ, f j)
        Filter.atTop (nhds (∑' j : ℕ, f j)) := tendsto_const_nhds
    simpa using (hc.sub hpartial)
  apply hdiff.congr'
  filter_upwards with J
  have hid := hf.sum_add_tsum_nat_add J
  dsimp [f] at hid ⊢
  linarith

end Erdos796
