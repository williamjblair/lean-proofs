import Research.AnalyticRecurrence

/-! # Combining the exact recurrence with prime quotient bins -/

namespace Research

/-- Primes for which `floor(N/p)=m`. -/
def quotientPrimeBin (N m : ℕ) : Finset ℕ :=
  (Finset.Ioc (N / (m + 1)) (N / m)).filter Nat.Prime

/-- Exact characterization of a natural floor-quotient fiber. -/
theorem mem_quotientPrimeBin_iff {N m p : ℕ} (hm : 0 < m) :
    p ∈ quotientPrimeBin N m ↔ p.Prime ∧ N / p = m := by
  rw [quotientPrimeBin, Finset.mem_filter, Finset.mem_Ioc]
  constructor
  · rintro ⟨⟨hlo, hhi⟩, hp⟩
    have hmle : m ≤ N / p := by
      rw [Nat.le_div_iff_mul_le hp.pos]
      have := (Nat.le_div_iff_mul_le hm).mp hhi
      simpa [Nat.mul_comm] using this
    have hlt : N / p < m + 1 := by
      rw [Nat.div_lt_iff_lt_mul hp.pos]
      simpa [Nat.mul_comm] using
        (Nat.div_lt_iff_lt_mul (by omega : 0 < m + 1)).mp hlo
    exact ⟨hp, by omega⟩
  · rintro ⟨hp, hquot⟩
    refine ⟨⟨?_, ?_⟩, hp⟩
    · rw [Nat.div_lt_iff_lt_mul (by omega : 0 < m + 1)]
      have hlt : N / p < m + 1 := by omega
      simpa [Nat.mul_comm] using (Nat.div_lt_iff_lt_mul hp.pos).mp hlt
    · rw [Nat.le_div_iff_mul_le hm]
      have : m * p ≤ N := by
        rw [← Nat.le_div_iff_mul_le hp.pos]
        omega
      simpa [Nat.mul_comm] using this

/-- If `Q=floor(N/y)`, every large prime maps to an index in `1,...,y-1`. -/
theorem largePrime_quotient_mem_Ico {N y p : ℕ} (hy : 0 < y)
    (hp : p ∈ largePrimes N (N / y)) :
    N / p ∈ Finset.Ico 1 y := by
  rw [largePrimes, Finset.mem_filter, Finset.mem_Icc] at hp
  have hpPrime := hp.2
  have hpN := hp.1.2
  have hQp : N / y < p := Nat.lt_of_succ_le hp.1.1
  rw [Finset.mem_Ico]
  constructor
  · exact (Nat.le_div_iff_mul_le hpPrime.pos).mpr (by simpa using hpN)
  · rw [Nat.div_lt_iff_lt_mul hpPrime.pos]
    exact lt_of_lt_of_le (Nat.lt_mul_div_succ N hy)
      (Nat.mul_le_mul_left y (Nat.succ_le_iff.mpr hQp))

/-- In this range, a large-prime quotient fiber equals its prime interval. -/
theorem largePrime_fiber_eq_bin {N y m : ℕ}
    (hm : m ∈ Finset.Ico 1 y) :
    (largePrimes N (N / y)).filter (fun p => N / p = m) =
      quotientPrimeBin N m := by
  have hmPos : 0 < m := (Finset.mem_Ico.mp hm).1
  have hmy : m < y := (Finset.mem_Ico.mp hm).2
  ext p
  constructor
  · intro hp
    rw [Finset.mem_filter] at hp
    exact (mem_quotientPrimeBin_iff hmPos).mpr ⟨
      (by
        rw [largePrimes, Finset.mem_filter] at hp
        exact hp.1.2), hp.2⟩
  · intro hp
    rw [mem_quotientPrimeBin_iff hmPos] at hp
    rw [Finset.mem_filter]
    refine ⟨?_, hp.2⟩
    rw [largePrimes, Finset.mem_filter, Finset.mem_Icc]
    have hbounds :
        N / (m + 1) < p ∧ p ≤ N / m := by
      simpa [quotientPrimeBin] using
        ((Finset.mem_filter.mp
          (show p ∈ quotientPrimeBin N m from
            (mem_quotientPrimeBin_iff hmPos).mpr hp)).1)
    refine ⟨⟨?_, ?_⟩, hp.1⟩
    · have hdiv : N / y ≤ N / (m + 1) :=
        Nat.div_le_div_left (by omega : m + 1 ≤ y) (by omega : 0 < m + 1)
      omega
    · exact le_trans hbounds.2 (Nat.div_le_self N m)

/-- Exact grouping of the large-prime sum by `m=floor(N/p)`. -/
theorem sum_largePrimes_eq_sum_bins (f : ℕ → ℝ) {N y : ℕ} (hy : 0 < y) :
    ∑ p ∈ largePrimes N (N / y), f (N / p) =
      ∑ m ∈ Finset.Ico 1 y, (quotientPrimeBin N m).card * f m := by
  have hgroup := Finset.sum_fiberwise_of_maps_to'
    (s := largePrimes N (N / y)) (t := Finset.Ico 1 y)
    (g := fun p => N / p)
    (fun p hp => largePrime_quotient_mem_Ico hy hp) f
  rw [← hgroup]
  apply Finset.sum_congr rfl
  intro m hm
  rw [largePrime_fiber_eq_bin hm]
  simp

/-- F-007 in exact quotient-bin form. -/
theorem logS_le_error_add_binSum (N y : ℕ) (hN : 1 ≤ N) (hy : 0 < y)
    (hNQ : N ≤ (N / y) * (N / y)) :
    logS N ≤ Real.log 2 + Real.log N +
      (Real.log 4 + 4) * ((N / y : ℕ) : ℝ) +
      2 * (Real.log 4 + 4) * N.sqrt +
        ∑ m ∈ Finset.Ico 1 y,
          (quotientPrimeBin N m).card * logS m := by
  rw [← sum_largePrimes_eq_sum_bins logS hy]
  exact logS_le_error_add_primeSum N (N / y) hN hNQ

end Research
