import Research.FourthOriginalNoWrapDecay
import Mathlib.Tactic

open scoped BigOperators

namespace Erdos521

/-- Zero is a nearest `πℤ` representative throughout the centered half-period. -/
lemma abs_le_abs_sub_int_mul_pi {x : ℝ} (hx : |x| ≤ Real.pi / 2) (m : ℤ) :
    |x| ≤ |x - (m : ℝ) * Real.pi| := by
  by_cases hm : m = 0
  · subst m
    simp
  have hmabsZ : (1 : ℤ) ≤ |m| := Int.one_le_abs hm
  have hmabsR : (1 : ℝ) ≤ |(m : ℝ)| := by
    rw [← Int.cast_abs]
    exact_mod_cast hmabsZ
  have hmpi : Real.pi ≤ |(m : ℝ) * Real.pi| := by
    rw [abs_mul, abs_of_pos Real.pi_pos]
    nlinarith [Real.pi_pos]
  have htri : |(m : ℝ) * Real.pi| ≤
      |x - (m : ℝ) * Real.pi| + |x| := by
    calc
      |(m : ℝ) * Real.pi| = |((m : ℝ) * Real.pi - x) + x| := by ring_nf
      _ ≤ |(m : ℝ) * Real.pi - x| + |x| := abs_add_le _ _
      _ = |x - (m : ℝ) * Real.pi| + |x| := by rw [abs_sub_comm]
  nlinarith

lemma sq_le_sq_sub_int_mul_pi {x : ℝ} (hx : |x| ≤ Real.pi / 2) (m : ℤ) :
    x ^ 2 ≤ (x - (m : ℝ) * Real.pi) ^ 2 := by
  exact sq_le_sq.mpr (abs_le_abs_sub_int_mul_pi hx m)

/-- A shifted nonnegative finite sum is bounded by a slightly longer initial sum. -/
lemma sum_range_shift_le_sum_range_add (f : ℕ → ℝ) (hf : ∀ q, 0 ≤ f q)
    (N d D : ℕ) (hd : d ≤ D) :
    (∑ q ∈ Finset.range N, f (d + q)) ≤
      ∑ q ∈ Finset.range (N + D), f q := by
  have hfirst : (∑ q ∈ Finset.range N, f (d + q)) ≤
      ∑ q ∈ Finset.range (d + N), f q := by
    rw [Finset.sum_range_add]
    exact le_add_of_nonneg_left (Finset.sum_nonneg fun q hq ↦ hf q)
  have hsub : Finset.range (d + N) ⊆ Finset.range (N + D) := by
    apply Finset.range_mono
    omega
  exact hfirst.trans (Finset.sum_le_sum_of_subset_of_nonneg hsub
    (fun q hq hnot ↦ hf q))

/-- Summed first-difference modular energy. -/
lemma fourthPhase_first_difference_energy_sum (N : ℕ) (s t : ℝ) (m : ℕ → ℤ) :
    (∑ q ∈ Finset.range N,
      (s * fourthCoefficientB q + t * (q + 3 : ℝ) -
        (((m (q + 1) : ℤ) : ℝ) - (m q : ℝ)) * Real.pi) ^ 2) ≤
      4 * ∑ q ∈ Finset.range (N + 1),
        (fourthOldPolynomialPhase q s t - (m q : ℝ) * Real.pi) ^ 2 := by
  let r : ℕ → ℝ := fun q ↦
    (fourthOldPolynomialPhase q s t - (m q : ℝ) * Real.pi) ^ 2
  have hpoint (q : ℕ) :
      (s * fourthCoefficientB q + t * (q + 3 : ℝ) -
        ((m (q + 1) : ℝ) - (m q : ℝ)) * Real.pi) ^ 2 ≤
        2 * (r q + r (q + 1)) := by
    exact fourthPhase_first_difference_residue_sq_le q s t (m q) (m (q + 1))
  calc
    _ ≤ ∑ q ∈ Finset.range N, 2 * (r q + r (q + 1)) :=
      Finset.sum_le_sum fun q hq ↦ hpoint q
    _ = 2 * ((∑ q ∈ Finset.range N, r q) +
        ∑ q ∈ Finset.range N, r (q + 1)) := by
      simp_rw [mul_add, Finset.sum_add_distrib, ← Finset.mul_sum]
    _ ≤ 2 * ((∑ q ∈ Finset.range (N + 1), r q) +
        ∑ q ∈ Finset.range (N + 1), r q) := by
      have h0 : (∑ q ∈ Finset.range N, r q) ≤
          ∑ q ∈ Finset.range (N + 1), r q :=
        Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.range_mono (by omega : N ≤ N + 1))
          (fun q hq hnot ↦ sq_nonneg _)
      have h1 : (∑ q ∈ Finset.range N, r (q + 1)) ≤
          ∑ q ∈ Finset.range (N + 1), r q := by
        simpa [add_comm] using sum_range_shift_le_sum_range_add r
          (fun q ↦ sq_nonneg _) N 1 1 le_rfl
      nlinarith
    _ = 4 * ∑ q ∈ Finset.range (N + 1),
        (fourthOldPolynomialPhase q s t - (m q : ℝ) * Real.pi) ^ 2 := by
      dsimp [r]
      ring

/-- Summed second-difference modular energy. -/
lemma fourthPhase_second_difference_energy_sum (N : ℕ) (s t : ℝ) (m : ℕ → ℤ) :
    (∑ q ∈ Finset.range N,
      (s * (q + 3 : ℝ) + t -
        ((m (q + 2) : ℝ) - 2 * (m (q + 1) : ℝ) + (m q : ℝ)) * Real.pi) ^ 2) ≤
      18 * ∑ q ∈ Finset.range (N + 2),
        (fourthOldPolynomialPhase q s t - (m q : ℝ) * Real.pi) ^ 2 := by
  let r : ℕ → ℝ := fun q ↦
    (fourthOldPolynomialPhase q s t - (m q : ℝ) * Real.pi) ^ 2
  have hpoint (q : ℕ) :
      (s * (q + 3 : ℝ) + t -
        ((m (q + 2) : ℝ) - 2 * (m (q + 1) : ℝ) + (m q : ℝ)) * Real.pi) ^ 2 ≤
        6 * (r q + r (q + 1) + r (q + 2)) := by
    exact fourthPhase_second_difference_residue_sq_le q s t
      (m q) (m (q + 1)) (m (q + 2))
  calc
    _ ≤ ∑ q ∈ Finset.range N, 6 * (r q + r (q + 1) + r (q + 2)) :=
      Finset.sum_le_sum fun q hq ↦ hpoint q
    _ = 6 * ((∑ q ∈ Finset.range N, r q) +
        (∑ q ∈ Finset.range N, r (q + 1)) +
        ∑ q ∈ Finset.range N, r (q + 2)) := by
      simp_rw [mul_add, Finset.sum_add_distrib, ← Finset.mul_sum]
    _ ≤ 6 * ((∑ q ∈ Finset.range (N + 2), r q) +
        (∑ q ∈ Finset.range (N + 2), r q) +
        ∑ q ∈ Finset.range (N + 2), r q) := by
      have h0 : (∑ q ∈ Finset.range N, r q) ≤
          ∑ q ∈ Finset.range (N + 2), r q :=
        Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.range_mono (by omega : N ≤ N + 2))
          (fun q hq hnot ↦ sq_nonneg _)
      have h1 : (∑ q ∈ Finset.range N, r (q + 1)) ≤
          ∑ q ∈ Finset.range (N + 2), r q := by
        simpa [add_comm] using sum_range_shift_le_sum_range_add r
          (fun q ↦ sq_nonneg _) N 1 2 (by omega)
      have h2 : (∑ q ∈ Finset.range N, r (q + 2)) ≤
          ∑ q ∈ Finset.range (N + 2), r q := by
        simpa [add_comm] using sum_range_shift_le_sum_range_add r
          (fun q ↦ sq_nonneg _) N 2 2 le_rfl
      nlinarith
    _ = 18 * ∑ q ∈ Finset.range (N + 2),
        (fourthOldPolynomialPhase q s t - (m q : ℝ) * Real.pi) ^ 2 := by
      dsimp [r]
      ring

/-- Summed third-difference modular energy. -/
lemma fourthPhase_third_difference_energy_sum (N : ℕ) (s t : ℝ) (m : ℕ → ℤ) :
    (∑ q ∈ Finset.range N,
      (s - ((m (q + 3) : ℝ) - 3 * (m (q + 2) : ℝ) +
        3 * (m (q + 1) : ℝ) - (m q : ℝ)) * Real.pi) ^ 2) ≤
      80 * ∑ q ∈ Finset.range (N + 3),
        (fourthOldPolynomialPhase q s t - (m q : ℝ) * Real.pi) ^ 2 := by
  let r : ℕ → ℝ := fun q ↦
    (fourthOldPolynomialPhase q s t - (m q : ℝ) * Real.pi) ^ 2
  have hpoint (q : ℕ) :
      (s - ((m (q + 3) : ℝ) - 3 * (m (q + 2) : ℝ) +
        3 * (m (q + 1) : ℝ) - (m q : ℝ)) * Real.pi) ^ 2 ≤
        20 * (r q + r (q + 1) + r (q + 2) + r (q + 3)) := by
    exact fourthPhase_third_difference_residue_sq_le q s t
      (m q) (m (q + 1)) (m (q + 2)) (m (q + 3))
  calc
    _ ≤ ∑ q ∈ Finset.range N,
        20 * (r q + r (q + 1) + r (q + 2) + r (q + 3)) :=
      Finset.sum_le_sum fun q hq ↦ hpoint q
    _ = 20 * ((∑ q ∈ Finset.range N, r q) +
        (∑ q ∈ Finset.range N, r (q + 1)) +
        (∑ q ∈ Finset.range N, r (q + 2)) +
        ∑ q ∈ Finset.range N, r (q + 3)) := by
      simp_rw [mul_add, Finset.sum_add_distrib, ← Finset.mul_sum]
    _ ≤ 20 * ((∑ q ∈ Finset.range (N + 3), r q) +
        (∑ q ∈ Finset.range (N + 3), r q) +
        (∑ q ∈ Finset.range (N + 3), r q) +
        ∑ q ∈ Finset.range (N + 3), r q) := by
      have h0 : (∑ q ∈ Finset.range N, r q) ≤
          ∑ q ∈ Finset.range (N + 3), r q :=
        Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.range_mono (by omega : N ≤ N + 3))
          (fun q hq hnot ↦ sq_nonneg _)
      have h1 : (∑ q ∈ Finset.range N, r (q + 1)) ≤
          ∑ q ∈ Finset.range (N + 3), r q := by
        simpa [add_comm] using sum_range_shift_le_sum_range_add r
          (fun q ↦ sq_nonneg _) N 1 3 (by omega)
      have h2 : (∑ q ∈ Finset.range N, r (q + 2)) ≤
          ∑ q ∈ Finset.range (N + 3), r q := by
        simpa [add_comm] using sum_range_shift_le_sum_range_add r
          (fun q ↦ sq_nonneg _) N 2 3 (by omega)
      have h3 : (∑ q ∈ Finset.range N, r (q + 3)) ≤
          ∑ q ∈ Finset.range (N + 3), r q := by
        simpa [add_comm] using sum_range_shift_le_sum_range_add r
          (fun q ↦ sq_nonneg _) N 3 3 le_rfl
      nlinarith
    _ = 80 * ∑ q ∈ Finset.range (N + 3),
        (fourthOldPolynomialPhase q s t - (m q : ℝ) * Real.pi) ^ 2 := by
      dsimp [r]
      ring

/-- On the fundamental half-cell, total phase energy controls the cubic dual coordinate. -/
lemma fourthPhase_energy_controls_cubic_coordinate (N : ℕ) (s t : ℝ) (m : ℕ → ℤ)
    (hs : |s| ≤ Real.pi / 2) :
    (N : ℝ) * s ^ 2 ≤
      80 * ∑ q ∈ Finset.range (N + 3),
        (fourthOldPolynomialPhase q s t - (m q : ℝ) * Real.pi) ^ 2 := by
  calc
    (N : ℝ) * s ^ 2 = ∑ q ∈ Finset.range N, s ^ 2 := by simp
    _ ≤ ∑ q ∈ Finset.range N,
        (s - ((m (q + 3) : ℝ) - 3 * (m (q + 2) : ℝ) +
          3 * (m (q + 1) : ℝ) - (m q : ℝ)) * Real.pi) ^ 2 := by
      apply Finset.sum_le_sum
      intro q hq
      let z : ℤ := m (q + 3) - 3 * m (q + 2) + 3 * m (q + 1) - m q
      have hz := sq_le_sq_sub_int_mul_pi hs z
      have hzcast : (z : ℝ) = (m (q + 3) : ℝ) - 3 * (m (q + 2) : ℝ) +
          3 * (m (q + 1) : ℝ) - (m q : ℝ) := by
        dsimp [z]
        push_cast
        ring
      rw [hzcast] at hz
      exact hz
    _ ≤ _ := fourthPhase_third_difference_energy_sum N s t m

end Erdos521
