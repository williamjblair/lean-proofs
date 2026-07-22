/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import ErdosProblems.Erdos730.FixedDepthFourier

/-!
# Audit surface for the Erdős 730 fixed-depth Fourier argument

The concrete checks use the odd prime `5`.  They exercise the exact Fourier
identity, both cancellation mechanisms, the prime-power kernel count, the
degenerate Gauss identity, the harmonic frequency bound, and the digitwise
factorization independently of the symbolic producer proofs.
-/

namespace Erdos730
namespace FixedDepthFourier

theorem audit_interval_identity_mod_five :
    (intervalHitCount 3 (fun t ↦ (t : ZMod 5)) ({0, 2} : Finset (ZMod 5)) : ℂ) =
      (5 : ℂ)⁻¹ * ∑ h : ZMod 5,
        ZMod.dft (finsetIndicator ({0, 2} : Finset (ZMod 5))) h *
          intervalPhaseSum 3 (fun t ↦ (t : ZMod 5)) h := by
  exact intervalHitCount_fourier_identity 3
    (fun t ↦ (t : ZMod 5)) ({0, 2} : Finset (ZMod 5))

theorem audit_low_effective_modulus_vanishing :
    (∑ t ∈ Finset.range (5 ^ 2),
      ZMod.stdAddChar
        ((1 : ZMod 5) *
          fixedDepthQuadratic (p := 5) (m := 1)
            (1 : ZMod 5) 1 0 (t : ZMod 5))) = 0 := by
  have hu : (1 : ZMod 5) ≠ 0 := by
    decide
  exact incompleteFixedDepthQuadraticSum_eq_zero_of_le
    (p := 5) (m := 1) (r := 2) (by norm_num) (by omega)
    (hβ := isUnit_one) (1 : ZMod 5) 0 1 hu

theorem audit_complete_support_vanishing :
    (∑ z : ZMod (5 ^ 2),
      ZMod.stdAddChar
        (quadraticPhase
          ((5 : ZMod (5 ^ 2)) * (1 : ZMod (5 ^ 2)))
          (1 : ZMod (5 ^ 2)) 0 z)) = 0 := by
  exact completeQuadraticSum_eq_zero_of_not_dvd
    (p := 5) (m := 2) (alpha := 1) (b := 1) (gamma := 0)
    (by norm_num) (by omega) (by norm_num)

theorem audit_mul_five_kernel_card_mod_twenty_five :
    Fintype.card
      {z : ZMod (5 ^ 2) // (5 : ZMod (5 ^ 2)) * z = 0} = 5 := by
  exact card_primePow_mul_kernel (p := 5) (m := 2) (by norm_num) (by omega)

theorem audit_two_isUnit_mod_twenty_five :
    IsUnit (2 : ZMod (5 ^ 2)) := by
  exact natCast_isUnit_zmod_primePow (p := 5) (j := 2) (b := 2)
    (by norm_num) (by norm_num)

theorem audit_degenerate_gauss_normSq_mod_twenty_five :
    Complex.normSq
      (∑ x : ZMod (5 ^ 2),
        ZMod.stdAddChar
          (quadraticPhase
            ((5 : ZMod (5 ^ 2)) * (1 : ZMod (5 ^ 2)))
            ((5 : ZMod (5 ^ 2)) * (0 : ZMod (5 ^ 2))) 0 x)) = 125 := by
  simpa using primePowDegenerateQuadraticGaussSum_normSq
    (p := 5) (m := 2) (by norm_num) (by omega)
    (1 : ZMod (5 ^ 2)) 0 0 (by simpa using audit_two_isUnit_mod_twenty_five)

theorem audit_unshifted_mass_mod_five :
    (∑ s : ZMod 5,
      ‖geometricPhaseSum (ZMod.stdAddChar s) 3‖) ≤
        (5 : ℝ) * (2 + Real.log 5) := by
  exact unshifted_frequency_mass_le (p := 5) (N := 3)
    (by norm_num) (by norm_num)

theorem audit_shifted_mass_mod_five :
    (∑ j ∈ Finset.range 5,
      ‖geometricPhaseSum
        (realUnitPhase
          (2 * Real.pi * ((1 : ℝ) / 25 + (j : ℝ) / 5))) 3‖) ≤
      (5 : ℝ) * (3 + Real.log 5) := by
  exact shiftedGrid_frequency_mass_le (p := 5) (N := 3)
    (by norm_num) (by norm_num) ((1 : ℝ) / 25)
    (by positivity) (by norm_num)

theorem audit_two_digit_factorization (h : ZMod (5 ^ 2)) :
    digitBoxFourierCoeff
        (fun _i : Fin 2 ↦ Finset.range 3) h =
      ∏ i : Fin 2,
        digitFourierFactor (fun _i : Fin 2 ↦ Finset.range 3) h i := by
  exact digitBoxFourierCoeff_factorization
    (fun _i : Fin 2 ↦ Finset.range 3) h

theorem audit_two_digit_interval_box :
    IsIntervalDigitBox 5 (fun _i : Fin 2 ↦ Finset.range 3) := by
  intro i
  refine ⟨0, 3, ?_, by norm_num⟩
  rw [zero_add, Nat.Ico_zero_eq_range]

theorem audit_two_digit_logarithmic_l1 :
    (∑ h : ZMod (5 ^ 2),
      ‖digitBoxFourierCoeff (fun _i : Fin 2 ↦ Finset.range 3) h‖) ≤
      (5 : ℝ) ^ 2 * (3 + Real.log 5) ^ 2 := by
  exact digitBoxFourierCoeff_interval_l1_le
    (p := 5) (d := 2) (by norm_num)
    (fun _i : Fin 2 ↦ Finset.range 3) audit_two_digit_interval_box

theorem audit_translated_high_frequency_mod_five :
    ‖intervalPhaseSum (5 ^ 1)
        (fun t : ℕ ↦
          fixedDepthQuadratic
            (1 : ZMod (5 ^ 2)) (1 : ZMod (5 ^ 2)) 0
            ((7 + t : ℕ) : ZMod (5 ^ 2))) (1 : ZMod (5 ^ 2))‖ ≤
      Real.sqrt (5 : ℝ) * (5 * (1 + Real.log 5)) := by
  simpa using
    (norm_fixedDepthIntervalPhaseSum_le_uniform
      (p := 5) (r := 1) (alpha := 1) (beta := 1) (gamma := 0)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      7 (1 : ZMod (5 ^ 2)) (by decide))

theorem audit_translated_low_frequency_mod_five :
    ‖intervalPhaseSum (5 ^ 1)
        (fun t : ℕ ↦
          fixedDepthQuadratic
            (1 : ZMod (5 ^ 2)) (1 : ZMod (5 ^ 2)) 0
            ((7 + t : ℕ) : ZMod (5 ^ 2))) (5 : ZMod (5 ^ 2))‖ ≤
      Real.sqrt (5 : ℝ) * (5 * (1 + Real.log 5)) := by
  simpa using
    (norm_fixedDepthIntervalPhaseSum_le_uniform
      (p := 5) (r := 1) (alpha := 1) (beta := 1) (gamma := 0)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      7 (5 : ZMod (5 ^ 2)) (by decide))

theorem audit_final_discrepancy_mod_five
    (A : Finset (ZMod (5 ^ 2)))
    (hA :
      (∑ h : ZMod (5 ^ 2), ‖ZMod.dft (finsetIndicator A) h‖) ≤
        (25 : ℝ) * (3 + Real.log 5) ^ 2) :
    ‖(intervalHitCount 5
          (fun t : ℕ ↦
            fixedDepthQuadratic
              (1 : ZMod (5 ^ 2)) (1 : ZMod (5 ^ 2)) 0
              ((7 + t : ℕ) : ZMod (5 ^ 2))) A : ℂ) -
        (A.card : ℂ) * 5 / (5 ^ 2)‖ ≤
      Real.sqrt (5 : ℝ) * (5 * (1 + Real.log 5)) *
        (3 + Real.log 5) ^ 2 := by
  simpa using
    (fixedDepth_intervalHitCount_discrepancy_le
      (p := 5) (r := 1) (alpha := 1) (beta := 1) (gamma := 0)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      7 A (by simpa using hA))

theorem audit_final_real_count_mod_five
    (A : Finset (ZMod (5 ^ 2)))
    (hA :
      (∑ h : ZMod (5 ^ 2), ‖ZMod.dft (finsetIndicator A) h‖) ≤
        (25 : ℝ) * (3 + Real.log 5) ^ 2) :
    (intervalHitCount 5
        (fun t : ℕ ↦
          fixedDepthQuadratic
            (1 : ZMod (5 ^ 2)) (1 : ZMod (5 ^ 2)) 0
            ((7 + t : ℕ) : ZMod (5 ^ 2))) A : ℝ) ≤
      (A.card : ℝ) * 5 / 25 +
        Real.sqrt (5 : ℝ) * (5 * (1 + Real.log 5)) *
          (3 + Real.log 5) ^ 2 := by
  simpa using
    (fixedDepth_intervalHitCount_le
      (p := 5) (r := 1) (alpha := 1) (beta := 1) (gamma := 0)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      7 A (by simpa using hA))

#print axioms intervalHitCount_fourier_identity
#print axioms finiteCompletion_identity
#print axioms intervalHitCount_discrepancy_le
#print axioms completeQuadraticSum_eq_zero_of_not_dvd
#print axioms incompleteFixedDepthQuadraticSum_eq_zero_of_le
#print axioms card_primePow_mul_kernel
#print axioms primePowDegenerateQuadraticGaussSum_normSq
#print axioms primePowDegenerateQuadraticGaussSum_norm
#print axioms unshifted_frequency_mass_le
#print axioms shiftedGrid_frequency_mass_le
#print axioms digitBoxFourierCoeff_factorization
#print axioms digitBoxFourierCoeff_l1_le
#print axioms digitBoxFourierCoeff_interval_l1_le
#print axioms norm_fixedDepthIncompleteSum_shift_le_uniform
#print axioms norm_fixedDepthIntervalPhaseSum_le_uniform
#print axioms fixedDepth_intervalHitCount_discrepancy_le
#print axioms fixedDepth_intervalHitCount_le
#print axioms audit_interval_identity_mod_five
#print axioms audit_low_effective_modulus_vanishing
#print axioms audit_complete_support_vanishing
#print axioms audit_mul_five_kernel_card_mod_twenty_five
#print axioms audit_degenerate_gauss_normSq_mod_twenty_five
#print axioms audit_unshifted_mass_mod_five
#print axioms audit_shifted_mass_mod_five
#print axioms audit_two_digit_factorization
#print axioms audit_two_digit_logarithmic_l1
#print axioms audit_translated_high_frequency_mod_five
#print axioms audit_translated_low_frequency_mod_five
#print axioms audit_final_discrepancy_mod_five
#print axioms audit_final_real_count_mod_five

end FixedDepthFourier
end Erdos730
