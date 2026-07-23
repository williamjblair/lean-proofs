import Research.AllCutoffLower
import Research.UpperBound

/-!
# Two-sided estimate for Erdős Problem 1188
-/

namespace Research

/-- A single exact theorem collecting the explicit lower and upper estimates.
The lower index is asymptotic to `log x / log log x`. -/
theorem erdos1188_two_sided_estimate (x : ℕ) (hx : x ≠ 0)
    (hlarge : 6 ≤ lowerFrameIndex x) :
    2 ^ ((lowerFrameIndex x - 1) * 2 ^ (lowerFrameIndex x - 2)) ≤
      coveringCount x ∧ coveringCount x ≤ (x + 2) ^ (x + 1) := by
  exact ⟨explicit_all_cutoffs_lower_strong x hx hlarge,
    coveringCount_le_elementary x⟩

end Research
