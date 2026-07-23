import Research.ElementaryConductor

namespace Erdos769

/-- The proposed asymptotic lower bound in Erdős Problem 769 is false. -/
theorem erdos769_lower_bound_false : ¬ Erdos769LowerBound := by
  exact erdos769LowerBound_false_of_eventually_odd_elementaryThreshold
    eventually_odd_elementaryThreshold_admissible

end Erdos769
