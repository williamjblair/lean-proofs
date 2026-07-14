/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import ErdosProblems.Erdos730BranchEvents

namespace Erdos730.BranchEventsAudit

open BranchEvents ConsecutiveTransition FullDensityCore KummerTransition

theorem audit_three_boundary (x : ℕ) :
    R x * S x % 3 = 2 ∧
      (R x * S x - 1) / 2 % 3 = 2 := by
  exact ⟨R_mul_S_mod_three x, entry_three_test_mod x⟩

theorem audit_every_obstruction_has_unique_branch
    {x p a c : ℕ}
    (h : DropObstruction (n x) p a c ∨ EntryObstruction (n x) p a c) :
    ∃! L, TaggedObstruction L x p a c := by
  obtain ⟨L, hL⟩ := obstruction_has_branch h
  exact ⟨L, hL, fun K hK => taggedObstruction_branch_unique hK hL⟩

theorem audit_every_obstruction_has_local_branch_event
    {x p a c : ℕ}
    (h : DropObstruction (n x) p a c ∨ EntryObstruction (n x) p a c) :
    ∃ L d, LocalBranchObstruction L x p a d := by
  obtain ⟨L, hL⟩ := obstruction_has_branch h
  obtain ⟨d, hd⟩ := taggedObstruction_has_local hL
  exact ⟨L, d, hd⟩

theorem audit_finite_global_to_local_count (X : ℕ) :
    (DensityEvents.badParametersUpTo X).card ≤
      (localBranchWitnessesUpTo X).card :=
  bad_card_le_localBranchWitnesses_card X

theorem audit_local_four_range
    (X smallCut topCut : ℕ) (hcuts : smallCut ≤ topCut) :
    (localBranchWitnessesUpTo X).card =
      (localHigherPowerWitnessesUpTo X).card +
        ((localSmallPrimeWitnessesUpTo X smallCut).card +
          ((localTransitionPrimeWitnessesUpTo X smallCut topCut).card +
            (localTopPrimeWitnessesUpTo X topCut).card)) :=
  localBranchWitnesses_card_fourRange X smallCut topCut hcuts

#print axioms audit_three_boundary
#print axioms audit_every_obstruction_has_unique_branch
#print axioms audit_every_obstruction_has_local_branch_event
#print axioms audit_finite_global_to_local_count
#print axioms audit_local_four_range

end Erdos730.BranchEventsAudit
