/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import ErdosProblems.Erdos730LowerHalfFourier

/-! Independent audit surface for the concrete lower-half Fourier box. -/

namespace Erdos730.LowerHalfFourierAudit

open Erdos730.DigitBoxes Erdos730.FixedDepthFourier
  Erdos730.LowerHalfFourier

noncomputable section

theorem concrete_two_digit_box_eq :
    lowerHalfTupleResidues 5 2 = lowerHalfResidues 5 2 :=
  lowerHalfTupleResidues_eq_lowerHalfResidues (by norm_num)

theorem concrete_two_digit_dft_l1 :
    (∑ h : ZMod (5 ^ 2),
      ‖ZMod.dft (finsetIndicator (lowerHalfResidues 5 2)) h‖) ≤
      (5 : ℝ) ^ 2 * (3 + Real.log 5) ^ 2 :=
  dft_lowerHalfResidues_l1_le (by norm_num)

#print axioms concrete_two_digit_box_eq
#print axioms concrete_two_digit_dft_l1
#print axioms Erdos730.LowerHalfFourier.dft_lowerHalfResidues_l1_le

end

end Erdos730.LowerHalfFourierAudit
