import Research.FourthPhaseEnergyHierarchy
import Mathlib.Tactic

open scoped BigOperators

namespace Erdos521

/-- Pairing a linear phase sequence at lag `L` converts modular residual energy into a coercive
bound for the unwrapped increment `aL`. -/
lemma linearPhase_pair_lag_energy (N L : ℕ) (a b : ℝ) (m : ℕ → ℤ)
    (hL : L ≤ N) (hcenter : |a| * (L : ℝ) ≤ Real.pi / 2) :
    ((N - L : ℕ) : ℝ) * (a * (L : ℝ)) ^ 2 ≤
      4 * ∑ q ∈ Finset.range N,
        (b + a * (q : ℝ) - (m q : ℝ) * Real.pi) ^ 2 := by
  let r : ℕ → ℝ := fun q ↦ b + a * (q : ℝ) - (m q : ℝ) * Real.pi
  have hpoint (q : ℕ) :
      (a * (L : ℝ)) ^ 2 ≤ 2 * (r q ^ 2 + r (q + L) ^ 2) := by
    let z : ℤ := m (q + L) - m q
    have hcenter' : |a * (L : ℝ)| ≤ Real.pi / 2 := by
      rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (L : ℝ))]
      exact hcenter
    have hnear := sq_le_sq_sub_int_mul_pi hcenter' z
    have hdiff : r (q + L) - r q =
        a * (L : ℝ) - (z : ℝ) * Real.pi := by
      dsimp [r, z]
      push_cast
      ring
    rw [← hdiff] at hnear
    exact hnear.trans (first_difference_sq_le (r q) (r (q + L)))
  calc
    ((N - L : ℕ) : ℝ) * (a * (L : ℝ)) ^ 2 =
        ∑ q ∈ Finset.range (N - L), (a * (L : ℝ)) ^ 2 := by simp
    _ ≤ ∑ q ∈ Finset.range (N - L), 2 * (r q ^ 2 + r (q + L) ^ 2) :=
      Finset.sum_le_sum fun q hq ↦ hpoint q
    _ = 2 * ((∑ q ∈ Finset.range (N - L), r q ^ 2) +
        ∑ q ∈ Finset.range (N - L), r (q + L) ^ 2) := by
      simp_rw [mul_add, Finset.sum_add_distrib, ← Finset.mul_sum]
    _ ≤ 2 * ((∑ q ∈ Finset.range N, r q ^ 2) +
        ∑ q ∈ Finset.range N, r q ^ 2) := by
      have h0 : (∑ q ∈ Finset.range (N - L), r q ^ 2) ≤
          ∑ q ∈ Finset.range N, r q ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.range_mono (by omega : N - L ≤ N))
          (fun q hq hnot ↦ sq_nonneg _)
      have hshift : (∑ q ∈ Finset.range (N - L), r (q + L) ^ 2) ≤
          ∑ q ∈ Finset.range N, r q ^ 2 := by
        have h := sum_range_shift_le_sum_range_add (fun q ↦ r q ^ 2)
          (fun q ↦ sq_nonneg _) (N - L) L L le_rfl
        have hLN : L + (N - L) = N := by omega
        simpa [add_comm, hLN] using h
      nlinarith
    _ = 4 * ∑ q ∈ Finset.range N,
        (b + a * (q : ℝ) - (m q : ℝ) * Real.pi) ^ 2 := by
      dsimp [r]
      ring

end Erdos521
