/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import ErdosProblems.Erdos730FullDensityReduction

/-!
# Hostile audit surface for the Erdős 730 full-density reduction

These checks pin the former intake hypothesis, its concrete counting function,
and the historical reduction's axiom footprint.  The hypothesis is discharged
by `Erdos730.FullDensityTheorem.candidatePositiveDensity`.
-/

open Filter

namespace Erdos730.FullDensityReduction

open Erdos730.FullDensityCore

noncomputable section

local instance : DecidablePred GoodParameter :=
  fun _ => Classical.propDecidable _

theorem audit_goodParameter_expanded (x : ℕ) :
    GoodParameter x ↔
      1 ≤ x ∧
        (n x).centralBinom.primeFactors =
          (n x + 1).centralBinom.primeFactors := by
  rfl

theorem audit_candidate_claim_is_concrete :
    CandidatePositiveDensityClaim ↔
      (107 : ℝ) / 2500 <
        liminf (fun X : ℕ =>
          (((Finset.Icc 1 X).filter GoodParameter).card : ℝ) / X) atTop :=
  candidatePositiveDensityClaim_iff

theorem audit_target_is_upstream_pair_set
    (h : CandidatePositiveDensityClaim) :
    Set.Infinite
      {z : ℕ × ℕ | z.1 < z.2 ∧
        z.1.centralBinom.primeFactors = z.2.centralBinom.primeFactors} := by
  exact pairSet_infinite_of_candidatePositiveDensity h

#print axioms audit_candidate_claim_is_concrete
#print axioms audit_goodParameter_expanded
#print axioms audit_target_is_upstream_pair_set

end

end Erdos730.FullDensityReduction
