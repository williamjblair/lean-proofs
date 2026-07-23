import Research.FourthCharacteristicDampedTaylor
import Research.FourthSupportLattice
import Mathlib.Tactic

open scoped BigOperators

namespace Erdos521

/-- The global cosine Gaussian bound on a centered half-period. -/
lemma abs_cos_le_exp_neg_sq_pi_half {x : ℝ} (hx : |x| ≤ Real.pi / 2) :
    |Real.cos x| ≤ Real.exp (-(2 / Real.pi ^ 2) * x ^ 2) := by
  have hxpi : |x| ≤ Real.pi := hx.trans (by linarith [Real.pi_pos])
  have hxmem : x ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
    rw [Set.mem_Icc]
    exact ⟨neg_le_of_abs_le hx, le_of_abs_le hx⟩
  rw [abs_of_nonneg (Real.cos_nonneg_of_mem_Icc hxmem)]
  calc
    Real.cos x ≤ 1 - 2 / Real.pi ^ 2 * x ^ 2 :=
      Real.cos_le_one_sub_mul_cos_sq hxpi
    _ ≤ Real.exp (-(2 / Real.pi ^ 2) * x ^ 2) := by
      have h := Real.add_one_le_exp (-(2 / Real.pi ^ 2) * x ^ 2)
      linarith

lemma abs_cos_sub_int_mul_pi (x : ℝ) (m : ℤ) :
    |Real.cos (x - (m : ℝ) * Real.pi)| = |Real.cos x| := by
  rw [Real.cos_sub_int_mul_pi, abs_mul]
  simp

/-- A cosine factor is controlled by the square of any representative in its centered
`πℤ` residue class. -/
lemma abs_cos_le_exp_residue_sq (x : ℝ) (m : ℤ)
    (hres : |x - (m : ℝ) * Real.pi| ≤ Real.pi / 2) :
    |Real.cos x| ≤
      Real.exp (-(2 / Real.pi ^ 2) * (x - (m : ℝ) * Real.pi) ^ 2) := by
  rw [← abs_cos_sub_int_mul_pi x m]
  exact abs_cos_le_exp_neg_sq_pi_half hres

/-- Global modular-energy bound for the original-coordinate fourth characteristic product. -/
lemma fourthOriginalCharacteristicProduct_modular_decay (k : ℕ) (s t : ℝ)
    (m : Option (Fin (k + 1)) → ℤ)
    (hres : ∀ i, |fourthOriginalPhase k s t i - (m i : ℝ) * Real.pi| ≤
      Real.pi / 2) :
    |fourthOriginalCharacteristicProduct k s t| ≤
      Real.exp (-(2 / Real.pi ^ 2) *
        ∑ i : Option (Fin (k + 1)),
          (fourthOriginalPhase k s t i - (m i : ℝ) * Real.pi) ^ 2) := by
  classical
  unfold fourthOriginalCharacteristicProduct
  rw [Finset.abs_prod]
  calc
    (∏ i : Option (Fin (k + 1)), |Real.cos (fourthOriginalPhase k s t i)|) ≤
        ∏ i : Option (Fin (k + 1)),
          Real.exp (-(2 / Real.pi ^ 2) *
            (fourthOriginalPhase k s t i - (m i : ℝ) * Real.pi) ^ 2) := by
      exact Finset.prod_le_prod (fun i hi ↦ abs_nonneg _) fun i hi ↦
        abs_cos_le_exp_residue_sq _ _ (hres i)
    _ = Real.exp (∑ i : Option (Fin (k + 1)),
        (-(2 / Real.pi ^ 2) *
          (fourthOriginalPhase k s t i - (m i : ℝ) * Real.pi) ^ 2)) := by
      rw [Real.exp_sum]
    _ = Real.exp (-(2 / Real.pi ^ 2) *
        ∑ i : Option (Fin (k + 1)),
          (fourthOriginalPhase k s t i - (m i : ℝ) * Real.pi) ^ 2) := by
      congr 1
      rw [Finset.mul_sum]

/-- Any lower bound for the centered modular phase energy immediately gives an exponential
high-frequency bound. -/
lemma fourthOriginalCharacteristicProduct_decay_of_modular_energy
    (k : ℕ) (s t η : ℝ) (m : Option (Fin (k + 1)) → ℤ)
    (hres : ∀ i, |fourthOriginalPhase k s t i - (m i : ℝ) * Real.pi| ≤
      Real.pi / 2)
    (henergy : η ≤ ∑ i : Option (Fin (k + 1)),
      (fourthOriginalPhase k s t i - (m i : ℝ) * Real.pi) ^ 2) :
    |fourthOriginalCharacteristicProduct k s t| ≤
      Real.exp (-(2 / Real.pi ^ 2) * η) := by
  calc
    _ ≤ Real.exp (-(2 / Real.pi ^ 2) *
        ∑ i : Option (Fin (k + 1)),
          (fourthOriginalPhase k s t i - (m i : ℝ) * Real.pi) ^ 2) :=
      fourthOriginalCharacteristicProduct_modular_decay k s t m hres
    _ ≤ Real.exp (-(2 / Real.pi ^ 2) * η) := by
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonpos_left henergy (neg_nonpos.mpr (by positivity))

end Erdos521
