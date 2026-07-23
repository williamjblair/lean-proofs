import Research.ConeFourthCrossingTransfer
import Mathlib.Tactic

open scoped BigOperators

namespace Erdos521

noncomputable local instance coneSuffixMomentDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

/-- Weighted version of the prefix/suffix injection: every terminal word has at most as many good
extensions as there are good prefixes. -/
theorem sum_goodPaths_suffix_le (s r : ℕ) (C : AxisWord r → ℕ) :
    (∑ p : AxisGoodPath (s + r), C (axisSuffix p)) ≤
      Fintype.card (AxisGoodPath s) * ∑ w : AxisWord r, C w := by
  let A := Σ p : AxisGoodPath (s + r), Fin (C (axisSuffix p))
  let B := AxisGoodPath s × Σ w : AxisWord r, Fin (C w)
  let f : A → B := fun z ↦
    (axisGoodPrefix z.1, ⟨axisSuffix z.1, z.2⟩)
  have hf : Function.Injective f := by
    rintro ⟨p₁, j₁⟩ ⟨p₂, j₂⟩ hz
    have hpref : axisGoodPrefix p₁ = axisGoodPrefix p₂ := congrArg Prod.fst hz
    have hsuf : axisSuffix p₁ = axisSuffix p₂ :=
      congrArg (fun z ↦ z.2.1) hz
    have hp : p₁ = p₂ := axisGoodPrefix_suffix_injective s r (Prod.ext hpref hsuf)
    subst p₂
    have hj : j₁ = j₂ := Fin.ext (congrArg (fun z ↦ z.2.2.val) hz)
    rw [hj]
  have hcard := Fintype.card_le_of_injective f hf
  change Fintype.card A ≤ Fintype.card B at hcard
  simp only [A, B, Fintype.card_sigma, Fintype.card_fin, Fintype.card_prod] at hcard
  exact hcard

/-- Terminal conditioning inflates the expectation of every nonnegative integer-valued statistic
by at most `(s+r+1)/(s+1)`. -/
theorem goodPaths_suffix_mean_le (s r : ℕ) (C : AxisWord r → ℕ) :
    (∑ p : AxisGoodPath (s + r), (C (axisSuffix p) : ℝ)) /
        Fintype.card (AxisGoodPath (s + r)) ≤
      ((s + r + 1 : ℝ) / (s + 1 : ℝ)) *
        (∑ w : AxisWord r, (C w : ℝ)) / (4 : ℝ) ^ r := by
  have hsumNat := sum_goodPaths_suffix_le s r C
  have hsum : (∑ p : AxisGoodPath (s + r), (C (axisSuffix p) : ℝ)) ≤
      Fintype.card (AxisGoodPath s) * ∑ w : AxisWord r, (C w : ℝ) := by
    exact_mod_cast hsumNat
  have hden : (0 : ℝ) < Fintype.card (AxisGoodPath (s + r)) := by
    exact_mod_cast card_axisGoodPath_pos (s + r)
  apply (div_le_iff₀ hden).2
  have hscale := card_axisGoodPath_scaled_le s r
  have hspos : (0 : ℝ) < s + 1 := by positivity
  have hpow : (0 : ℝ) < 4 ^ r := by positivity
  have hmean_nonneg : 0 ≤ ∑ w : AxisWord r, (C w : ℝ) := by positivity
  calc
    (∑ p : AxisGoodPath (s + r), (C (axisSuffix p) : ℝ)) ≤
        Fintype.card (AxisGoodPath s) * ∑ w : AxisWord r, (C w : ℝ) := hsum
    _ ≤ (((s + r + 1 : ℝ) / (s + 1 : ℝ)) *
        (∑ w : AxisWord r, (C w : ℝ)) / (4 : ℝ) ^ r) *
          Fintype.card (AxisGoodPath (s + r)) := by
      have hm := mul_le_mul_of_nonneg_right hscale hmean_nonneg
      field_simp at hm ⊢
      nlinarith

end Erdos521
