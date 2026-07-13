/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import ErdosProblems.Erdos730AnalyticInputs
import ErdosProblems.Erdos730ConsecutiveTransition
import ErdosProblems.Erdos730DominatedLimit
import ErdosProblems.Erdos730FixedDepthParity
import ErdosProblems.Erdos730FullDensityBudget
import ErdosProblems.Erdos730FullDensityCore
import ErdosProblems.Erdos730HigherPowerCount
import ErdosProblems.Erdos730KummerTransition
import ErdosProblems.Erdos730ObstructionMaps
import ErdosProblems.Erdos730PadicIsometry
import ErdosProblems.Erdos730PositiveDensityBridge

/-!
# Erdős 730: exact final reduction for the supplied positive-density proof

This module states the one remaining quantified density lemma and proves,
without any extra axiom, that it implies the exact upstream infinitude target.
The statement deliberately uses the explicit family from
`Erdos730FullDensityCore`; it is not a theorem-strength placeholder over an
arbitrary sequence.

The supplied paper proof claims the strict lower-density estimate below.  The
elementary family identities and its final numerical budget are separately
kernel-checked.  Formalizing the intervening Kummer/Mertens/PNT-in-progressions
argument remains the analytic intake boundary.
-/

open Filter

namespace Erdos730
namespace FullDensityReduction

open FullDensityCore

noncomputable section

local instance : DecidablePred GoodParameter :=
  fun _ => Classical.propDecidable _

/-- The single, explicit quantified lemma left by the Lean intake.

It says that more than `107/2500` of the positive integer parameters in the
four-linear-form family give equal prime support for the two consecutive
central binomial coefficients, in lower-density liminf. -/
def CandidatePositiveDensityClaim : Prop :=
  FullDensity.HasCandidatePositiveDensity GoodParameter

/-- Expanded form of the exact remaining lemma, useful for hostile audit. -/
theorem candidatePositiveDensityClaim_iff :
    CandidatePositiveDensityClaim ↔
      (107 : ℝ) / 2500 <
        liminf (fun X : ℕ =>
          (((Finset.Icc 1 X).filter GoodParameter).card : ℝ) / X) atTop := by
  rfl

/-- The exact density claim gives infinitely many good parameters. -/
theorem goodParameters_infinite_of_candidatePositiveDensity
    (h : CandidatePositiveDensityClaim) : GoodParameters.Infinite := by
  exact FullDensity.parameterSet_infinite_of_candidatePositiveDensity
    GoodParameter (by simpa [CandidatePositiveDensityClaim] using h)

/-- Kernel-clean final reduction to the exact upstream Erdős 730 set.

No analytic theorem is hidden here: the only hypothesis is the fully expanded
positive-density claim above. -/
theorem pairSet_infinite_of_candidatePositiveDensity
    (h : CandidatePositiveDensityClaim) : PairSet.Infinite := by
  exact pairSet_infinite_of_goodParameters_infinite
    (goodParameters_infinite_of_candidatePositiveDensity h)

/-- The checked numerical node used by the supplied density argument. -/
theorem supplied_density_budget_certificate :
    4 * densityBudgetSeries + (2 / 3) * Real.log 2 < (2393 : ℝ) / 2500 :=
  densityBudget_final_lt

#print axioms candidatePositiveDensityClaim_iff
#print axioms goodParameters_infinite_of_candidatePositiveDensity
#print axioms pairSet_infinite_of_candidatePositiveDensity
#print axioms supplied_density_budget_certificate

end

end FullDensityReduction
end Erdos730
