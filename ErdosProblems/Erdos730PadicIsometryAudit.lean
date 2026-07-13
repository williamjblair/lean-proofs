/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import ErdosProblems.Erdos730PadicIsometry

/-!
# Audit surface for the Erdős 730 p-adic branch-map isometry

The concrete checks use `p=5`, modulus `5^3=125`, and residual coefficient
`b=2`.  They exercise the prime-unit conversion, congruence equivalence, and
permutation theorem independently of the symbolic proofs.
-/

namespace Erdos730

theorem audit_two_isUnit_mod_125 : IsUnit (2 : ZMod (5 ^ 3)) := by
  exact natCast_isUnit_zmod_primePow (p := 5) (j := 3) (b := 2)
    (by norm_num) (by norm_num)

theorem audit_concrete_branchMap_bijective :
    Function.Bijective
      (padicBranchMap (5 : ZMod (5 ^ 3)) 7 11 2 13) := by
  exact padicBranchMap_bijective (p := 5) (j := 3) (by norm_num)
    audit_two_isUnit_mod_125 7 11 13

theorem audit_concrete_congruence_iff (x y : ℤ) :
    padicBranchMap (5 : ZMod (5 ^ 3)) 7 11 2 13 x =
        padicBranchMap (5 : ZMod (5 ^ 3)) 7 11 2 13 y ↔
      x ≡ y [ZMOD 125] := by
  simpa using padicBranchMap_int_congr_iff
    (p := 5) (j := 3) (b := 2) (by norm_num) (by norm_num)
    (7 : ZMod (5 ^ 3)) 11 13 x y

theorem audit_depth_four_digit_box_count :
    Fintype.card (RestrictedDigitBox (Finset.range 3) 0 4) = 54 := by
  rw [restrictedDigitBox_card (A := Finset.range 3) (endpoint := 0)
    (d := 4) (H := 3) (by simp) (by simp)]
  norm_num

theorem audit_depth_one_digit_box_boundary :
    Fintype.card (RestrictedDigitBox (Finset.range 3) 0 1) = 2 := by
  rw [restrictedDigitBox_card (A := Finset.range 3) (endpoint := 0)
    (d := 1) (H := 3) (by simp) (by simp)]
  norm_num

#print axioms padicBranchMap_sub_factor
#print axioms zmod_primeMultiple_isNilpotent
#print axioms padicBranchMap_differenceFactor_isUnit
#print axioms padicBranchMap_eq_iff
#print axioms padicBranchMap_bijective
#print axioms natCast_isUnit_zmod_primePow
#print axioms padicBranchMap_int_congr_iff
#print axioms card_filter_preimage_of_bijective
#print axioms card_filter_preimage_erase_image
#print axioms restrictedDigitBox_card
#print axioms audit_two_isUnit_mod_125
#print axioms audit_concrete_branchMap_bijective
#print axioms audit_concrete_congruence_iff
#print axioms audit_depth_four_digit_box_count
#print axioms audit_depth_one_digit_box_boundary

end Erdos730
