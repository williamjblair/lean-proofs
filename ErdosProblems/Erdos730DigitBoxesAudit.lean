/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import ErdosProblems.Erdos730DigitBoxes

namespace Erdos730.DigitBoxesAudit

open KummerTransition DigitBoxes

theorem audit_card {p r : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    (lowerHalfResidues p r).card = halfDigitCount p ^ r := by
  apply lowerHalfResidues_card
  have := hp.two_le
  omega

theorem audit_membership {p r n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hn : LowerHalfDigits p n) :
    (n : ZMod (p ^ r)) ∈ lowerHalfResidues p r :=
  natCast_mem_lowerHalfResidues hp hp2 hn

#print axioms audit_card
#print axioms audit_membership

end Erdos730.DigitBoxesAudit
