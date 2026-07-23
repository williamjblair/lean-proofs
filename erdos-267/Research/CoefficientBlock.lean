import Research.Lambert

/-!
# Finite selected Lambert coefficient blocks
-/

namespace Research

open scoped BigOperators

/-- Coefficient contributed by the first `K` selected indices. -/
def prefixFibLambertCoeff (n : ℕ → ℕ) (K m : ℕ) : ℤ :=
  ∑ k ∈ Finset.range K, fibLambertCoeff (n k) m

/-- Iterating the basic period preserves a single contribution under any
multiple of `4n`. -/
theorem fibLambertCoeff_add_period_mul (n m t : ℕ) :
    fibLambertCoeff n (m + t * (4 * n)) = fibLambertCoeff n m := by
  induction t with
  | zero => simp
  | succ t ih =>
      rw [show m + (t + 1) * (4 * n) =
        (m + t * (4 * n)) + 4 * n by ring,
        fibLambertCoeff_add_four_mul, ih]

/-- A common multiple of all first-`K` coefficient periods shifts their total
coefficient block identically. -/
theorem prefixFibLambertCoeff_add_commonPeriod
    (n : ℕ → ℕ) (K X : ℕ)
    (hperiod : ∀ k < K, 4 * n k ∣ X) (m : ℕ) :
    prefixFibLambertCoeff n K (m + X) = prefixFibLambertCoeff n K m := by
  unfold prefixFibLambertCoeff
  apply Finset.sum_congr rfl
  intro k hk
  obtain ⟨t, ht⟩ := hperiod k (Finset.mem_range.mp hk)
  subst X
  simpa [mul_comm] using fibLambertCoeff_add_period_mul (n k) m t

/-- The absolute size of a prefix coefficient is at most the number of selected
summands used to form it. -/
theorem abs_prefixFibLambertCoeff_le (n : ℕ → ℕ) (K m : ℕ) :
    |prefixFibLambertCoeff n K m| ≤ (K : ℤ) := by
  calc
    |prefixFibLambertCoeff n K m| ≤
        ∑ k ∈ Finset.range K, |fibLambertCoeff (n k) m| := by
          exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k ∈ Finset.range K, (1 : ℤ) := by
          apply Finset.sum_le_sum
          intro k hk
          exact abs_fibLambertCoeff_le_one (n k) m
    _ = (K : ℤ) := by simp

end Research
