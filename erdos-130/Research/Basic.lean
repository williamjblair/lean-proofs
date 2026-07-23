import Research.InfiniteAssembly

/-!
# Erdős Problem 130 — formal target and solution

This file discharges the exact statement pinned by the verifier using the
independently developed finite circle, inversion, and infinite-assembly chain.
-/

namespace Erdos130

/-- Central target of Erdős Problem 130: an infinite general-position set whose
integer-distance graph has no proper coloring by any finite number of colors. -/
theorem erdos130_infinite_chromatic :
    ∃ A : Set Point,
      A.Infinite ∧ GeneralPosition A ∧ ∀ k : ℕ, ¬ HasKColoring A k := by
  exact InfiniteAssembly.erdos130_infinite_chromatic_solution

end Erdos130
