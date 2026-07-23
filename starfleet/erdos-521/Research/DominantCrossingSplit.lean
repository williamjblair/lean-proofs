import Mathlib.Tactic

namespace Erdos521

/-- A crossing of a dominant value plus lower-order perturbations can occur only when the dominant
value is small or one of the perturbations is large.  This deterministic threshold split is the
basic device for paying only one meander-conditioning factor at a time. -/
lemma dominant_crossing_threshold_split {H J P P' T : ℝ} (hT : 0 ≤ T)
    (hcross : (H - P) * (H + J - P') ≤ 0) :
    |H| ≤ 2 * T ∨ T ≤ |J| ∨ T ≤ |P| ∨ T ≤ |P'| := by
  by_contra hbad
  push_neg at hbad
  rcases hbad with ⟨hH, hJ, hP, hP'⟩
  have ⟨hJlo, hJhi⟩ := (abs_lt.mp hJ)
  have ⟨hPlo, hPhi⟩ := (abs_lt.mp hP)
  have ⟨hP'lo, hP'hi⟩ := (abs_lt.mp hP')
  by_cases hHnonneg : 0 ≤ H
  · rw [abs_of_nonneg hHnonneg] at hH
    have hfirst : 0 < H - P := by linarith
    have hsecond : 0 < H + J - P' := by linarith
    nlinarith [mul_pos hfirst hsecond]
  · have hHneg : H < 0 := lt_of_not_ge hHnonneg
    rw [abs_of_neg hHneg] at hH
    have hfirst : H - P < 0 := by linarith
    have hsecond : H + J - P' < 0 := by linarith
    nlinarith [mul_pos_of_neg_of_neg hfirst hsecond]

/-- Equivalent non-strict-tail version convenient for indicator inclusions. -/
lemma dominant_crossing_threshold_split_le {H J P P' T : ℝ} (hT : 0 ≤ T)
    (hcross : (H - P) * (H + J - P') ≤ 0) :
    |H| ≤ 2 * T ∨ T ≤ |J| ∨ T ≤ |P| ∨ T ≤ |P'| :=
  dominant_crossing_threshold_split hT hcross

end Erdos521
