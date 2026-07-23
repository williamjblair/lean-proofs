import Research.PrimeSelection
import Research.DenseBlock

namespace Erdos450

/-- For positive `ε`, choose a finite set of primes at least five whose
reciprocal mass exceeds `152/ε`.  The nonpositive branch is irrelevant to the
asymptotic specification. -/
noncomputable def turanPrimeSet (ε : ℝ) : Finset ℕ :=
  if _hε : 0 < ε then
    Classical.choose (exists_large_primeReciprocalMean (152 / ε))
  else ∅

theorem turanPrimeSet_spec (ε : ℝ) (hε : 0 < ε) :
    (∀ p ∈ turanPrimeSet ε, Nat.Prime p) ∧
    (∀ p ∈ turanPrimeSet ε, 5 ≤ p) ∧
    152 / ε < primeReciprocalMean (turanPrimeSet ε) := by
  rw [turanPrimeSet, dif_pos hε]
  exact Classical.choose_spec (exists_large_primeReciprocalMean (152 / ε))

/-- The explicit answer: a constant depending only on `ε`, namely the square
prime period of a finite selected set plus two, times `n`. -/
noncomputable def turanLinearAnswer (ε : ℝ) (n : ℕ) : ℕ :=
  n * (primeSquarePeriod (turanPrimeSet ε) + 2)

/-- Main upper bound: Erdős Problem 450 admits a translate-uniform linear scale
`y = C(ε)n`. -/
theorem turanLinearAnswer_isSufficientScale :
    IsSufficientScale turanLinearAnswer := by
  intro ε hε
  have hs := turanPrimeSet_spec ε hε
  have hCpos : 0 < (152 : ℝ) / ε := div_pos (by norm_num) hε
  have hmu : 0 < primeReciprocalMean (turanPrimeSet ε) :=
    lt_trans hCpos hs.2.2
  have hbudget : 152 ≤ ε * primeReciprocalMean (turanPrimeSet ε) := by
    have hstrict : (152 : ℝ) <
        ε * primeReciprocalMean (turanPrimeSet ε) := by
      have := (div_lt_iff₀ hε).mp hs.2.2
      nlinarith
    exact hstrict.le
  obtain ⟨N, hN⟩ := eventually_uniformlySparse_turanLinearScale_of_budget
    (turanPrimeSet ε) hs.1 hs.2.1 hmu ε hbudget
  refine ⟨N, ?_⟩
  intro n hn y hy
  apply hN n hn y
  simpa only [turanLinearScale, turanLinearAnswer] using hy

/-- The factorial dense block gives a matching linear lower obstruction: for
every target below one, length exactly `n` fails for all sufficiently large
`n`. -/
theorem eventually_not_uniformlySparse_at_n
    (ε : ℝ) (hε : ε < 1) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ¬ UniformlySparse ε n n := by
  have hδ : 0 < (1 - ε : ℝ) := sub_pos.mpr hε
  obtain ⟨N₀, hN₀⟩ := exists_nat_gt ((1 : ℝ) / (1 - ε))
  refine ⟨max 2 N₀, ?_⟩
  intro n hn
  have hn2 : 2 ≤ n := le_trans (le_max_left _ _) hn
  have hN₀n : N₀ ≤ n := le_trans (le_max_right _ _) hn
  have hlarge : (1 : ℝ) / (1 - ε) < n :=
    lt_of_lt_of_le hN₀ (by exact_mod_cast hN₀n)
  have hprod : (1 : ℝ) < (n : ℝ) * (1 - ε) :=
    (div_lt_iff₀ hδ).mp hlarge
  apply not_uniformlySparse_of_lt_dense_block ε n n le_rfl
  rw [Nat.cast_sub (by omega : 1 ≤ n)]
  norm_num
  ring_nf at hprod ⊢
  linarith

/-- Consequently every sufficient eventual threshold has to exceed `n`
eventually for each fixed `0 < ε < 1`; together with the Turán upper theorem,
the optimal order is linear in `n` (with constants depending on `ε`). -/
theorem sufficientScale_eventually_gt_n
    (Y : ℝ → ℕ → ℕ) (hY : IsSufficientScale Y)
    (ε : ℝ) (hεpos : 0 < ε) (hεone : ε < 1) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → n < Y ε n := by
  obtain ⟨N₁, hN₁⟩ := hY ε hεpos
  obtain ⟨N₂, hN₂⟩ := eventually_not_uniformlySparse_at_n ε hεone
  refine ⟨max N₁ N₂, ?_⟩
  intro n hn
  have hn₁ : N₁ ≤ n := le_trans (le_max_left _ _) hn
  have hn₂ : N₂ ≤ n := le_trans (le_max_right _ _) hn
  by_contra hnot
  have hYn : Y ε n ≤ n := Nat.le_of_not_gt hnot
  exact hN₂ n hn₂ (hN₁ n hn₁ n hYn)

end Erdos450
