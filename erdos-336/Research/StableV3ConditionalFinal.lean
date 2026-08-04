import Research.EventualConditionalFinal
import Research.WideBlockScaleAsymptotic

namespace Erdos336

/-- The sole remaining V3 structural statement implies Erdős Problem 336. -/
theorem problem336_of_stableHighPowerStructureV3
    (hstruct : HasStableHighPowerStructureV3) :
    HasProblem336Value (1 / 3 : ℝ) := by
  apply problem336_of_eventual_cyclicRemovalUpperThird
  exact ⟨wideStructuralRemovalCost,
    eventually_cyclicRemovalBound_wideStructuralCost hstruct,
    tendsto_wideStructuralRemovalCost_third⟩

end Erdos336
