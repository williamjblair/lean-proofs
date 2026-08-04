import Research.PrimeConstruction
import Mathlib.NumberTheory.Chebyshev

namespace Erdos321

/-- Explicit Chebyshev baseline for the normalized lower recursion. -/
theorem chebyshev_lower_le_extremalSize (N : ℕ) :
    ((N : ℝ) * Real.log 2 - Real.log (N + 1)) / Real.log N ≤
      extremalSize N := by
  exact (Chebyshev.pi_ge N).trans (by
    exact_mod_cast primeCounting_le_extremalSize N)

end Erdos321
