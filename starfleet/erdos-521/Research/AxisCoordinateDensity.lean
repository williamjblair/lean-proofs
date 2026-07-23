import Research.AxisScheduleTail
import Mathlib.Tactic

namespace Erdos521

noncomputable local instance axisCoordinateDensityDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

lemma horizontalGoodMass_le_two_div_sqrt (n : ℕ) :
    horizontalGoodMass n ≤ 2 / Real.sqrt (n + 1 : ℝ) := by
  have hn : (0 : ℝ) < n + 1 := by positivity
  have hsqrt : 0 < Real.sqrt (n + 1 : ℝ) := Real.sqrt_pos.2 hn
  have hmass0 : 0 ≤ horizontalGoodMass n := by
    unfold horizontalGoodMass
    positivity
  have hright0 : 0 ≤ 2 / Real.sqrt (n + 1 : ℝ) := by positivity
  apply (sq_le_sq₀ hmass0 hright0).1
  have hs := horizontalGoodMass_sq_upper n
  calc
    horizontalGoodMass n ^ 2 ≤ 2 / (n + 1 : ℝ) := hs
    _ ≤ 4 / (n + 1 : ℝ) :=
      div_le_div_of_nonneg_right (by norm_num) hn.le
    _ = (2 / Real.sqrt (n + 1 : ℝ)) ^ 2 := by
      rw [div_pow, Real.sq_sqrt hn.le]
      norm_num

lemma axisGoodMass_pos (n : ℕ) : 0 < axisGoodMass n := by
  unfold axisGoodMass
  exact div_pos (by exact_mod_cast card_axisGoodPath_pos n) (by positivity)

/-- The product of the one-coordinate decoration cost and the ratio between one-coordinate and
quadrant survival masses is uniformly at most `64`. -/
lemma horizontal_to_axis_density_factor_le (n : ℕ) :
    (2 / Real.sqrt (n + 1 : ℝ)) *
        (horizontalGoodMass n / axisGoodMass n) ≤ 64 := by
  have hn : (0 : ℝ) < n + 1 := by positivity
  have hsqrt : 0 < Real.sqrt (n + 1 : ℝ) := Real.sqrt_pos.2 hn
  have hhor := horizontalGoodMass_le_two_div_sqrt n
  have haxis : 1 / (16 * (n + 1 : ℝ)) ≤ axisGoodMass n := by
    exact card_axisGoodPath_ratio_lower n
  have haxisPos := axisGoodMass_pos n
  rw [← mul_div_assoc]
  apply (div_le_iff₀ haxisPos).2
  have hfirst :
      (2 / Real.sqrt (n + 1 : ℝ)) * horizontalGoodMass n ≤
        4 / (n + 1 : ℝ) := by
    calc
      _ ≤ (2 / Real.sqrt (n + 1 : ℝ)) *
          (2 / Real.sqrt (n + 1 : ℝ)) :=
        mul_le_mul_of_nonneg_left hhor (by positivity)
      _ = 4 / (n + 1 : ℝ) := by
        rw [← pow_two, div_pow, Real.sq_sqrt hn.le]
        norm_num
  calc
    (2 / Real.sqrt (n + 1 : ℝ)) * horizontalGoodMass n ≤
        4 / (n + 1 : ℝ) := hfirst
    _ = 64 * (1 / (16 * (n + 1 : ℝ))) := by field_simp; norm_num
    _ ≤ 64 * axisGoodMass n := mul_le_mul_of_nonneg_left haxis (by norm_num)

/-- Every balanced event depending only on the schedule and horizontal compressed meander has
quadrant-conditioned density at most 64 times its density under horizontal-only survival. -/
theorem axisGood_balanced_core_density_le_horizontal {n : ℕ}
    (A : Finset (HorizontalCore n))
    (hbal : ∀ c ∈ A, n ≤ 4 * (c.1ᶜ).card) :
    (Fintype.card {p : AxisGoodPath n // axisHorizontalCore p ∈ A} : ℝ) /
        Fintype.card (AxisGoodPath n) ≤
      64 * ((Fintype.card {p : HorizontalGoodPath n //
          oneCoordinateHorizontalCore p ∈ A} : ℝ) /
        Fintype.card (HorizontalGoodPath n)) := by
  have hcompare := card_axisGood_core_mem_le_horizontal A hbal
  have haxisCard : (0 : ℝ) < Fintype.card (AxisGoodPath n) := by
    exact_mod_cast card_axisGoodPath_pos n
  have hhorCard : (0 : ℝ) < Fintype.card (HorizontalGoodPath n) := by
    exact_mod_cast horizontalGoodPath_card_pos n
  have hpow : (0 : ℝ) < (4 : ℝ) ^ n := by positivity
  have hfactor := horizontal_to_axis_density_factor_le n
  have heq :
      ((2 / Real.sqrt (n + 1 : ℝ)) *
          Fintype.card {p : HorizontalGoodPath n // oneCoordinateHorizontalCore p ∈ A}) /
          Fintype.card (AxisGoodPath n) =
        ((2 / Real.sqrt (n + 1 : ℝ)) *
          (horizontalGoodMass n / axisGoodMass n)) *
          (Fintype.card {p : HorizontalGoodPath n //
              oneCoordinateHorizontalCore p ∈ A} /
            Fintype.card (HorizontalGoodPath n)) := by
    unfold horizontalGoodMass axisGoodMass
    field_simp
  calc
    _ ≤ ((2 / Real.sqrt (n + 1 : ℝ)) *
          Fintype.card {p : HorizontalGoodPath n // oneCoordinateHorizontalCore p ∈ A}) /
          Fintype.card (AxisGoodPath n) :=
      div_le_div_of_nonneg_right hcompare haxisCard.le
    _ = _ := heq
    _ ≤ 64 * (Fintype.card {p : HorizontalGoodPath n //
          oneCoordinateHorizontalCore p ∈ A} /
        Fintype.card (HorizontalGoodPath n)) :=
      mul_le_mul_of_nonneg_right hfactor (by positivity)

end Erdos521
