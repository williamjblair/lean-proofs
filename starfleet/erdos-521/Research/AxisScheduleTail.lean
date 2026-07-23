import Research.AxisCoordinateCore
import Research.FiniteRademacherConcentration
import Mathlib.Tactic

open scoped BigOperators

namespace Erdos521

noncomputable local instance axisScheduleTailDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

noncomputable def finsetComplementEquiv (α : Type*) [Fintype α] [DecidableEq α] :
    Finset α ≃ Finset α where
  toFun A := Aᶜ
  invFun A := Aᶜ
  left_inv A := by simp
  right_inv A := by simp

/-- A Boolean word's false-set is the vertical schedule, so its complement is the horizontal
schedule. -/
noncomputable def boolEquivHorizontalSchedule (n : ℕ) :
    (Fin n → Bool) ≃ Finset (Fin n) :=
  (boolFunEquivFinset (Fin n)).trans (finsetComplementEquiv (Fin n))

@[simp] lemma boolEquivHorizontalSchedule_compl_card (n : ℕ) (e : Fin n → Bool) :
    ((boolEquivHorizontalSchedule n e)ᶜ).card =
      (Finset.univ.filter (fun i ↦ e i = false)).card := by
  simp [boolEquivHorizontalSchedule, finsetComplementEquiv, boolFunEquivFinset]

noncomputable def verticallyUnbalancedSchedules (n : ℕ) : Finset (Finset (Fin n)) :=
  Finset.univ.filter fun H ↦ 4 * (Hᶜ).card < n

lemma finiteRademacher_ones_eq_card {n : ℕ} (e : Fin n → Bool) :
    finiteRademacherRealSum (fun _ : Fin n ↦ (1 : ℝ)) e =
      (n : ℝ) - 2 * ((Finset.univ.filter (fun i ↦ e i = false)).card : ℝ) := by
  unfold finiteRademacherRealSum
  simp only [mul_one]
  simpa using sum_sign_eq_card_sub_false (Finset.univ : Finset (Fin n)) e

lemma unbalanced_schedule_maps_to_tail {n : ℕ} (H : Finset (Fin n))
    (hH : H ∈ verticallyUnbalancedSchedules n) :
    (n : ℝ) / 2 ≤ finiteRademacherRealSum (fun _ : Fin n ↦ (1 : ℝ))
      ((boolEquivHorizontalSchedule n).symm H) := by
  rw [finiteRademacher_ones_eq_card]
  have hsmall : 4 * (Hᶜ).card < n := by
    simpa [verticallyUnbalancedSchedules] using hH
  have hcard := boolEquivHorizontalSchedule_compl_card n
    ((boolEquivHorizontalSchedule n).symm H)
  rw [(boolEquivHorizontalSchedule n).apply_symm_apply] at hcard
  rw [← hcard]
  have hsmallR : (4 : ℝ) * (Hᶜ).card < n := by exact_mod_cast hsmall
  push_cast
  nlinarith

lemma card_unbalancedSchedules_le_tail (n : ℕ) :
    (verticallyUnbalancedSchedules n).card ≤
      (Finset.univ.filter fun e : Fin n → Bool ↦
        (n : ℝ) / 2 ≤ finiteRademacherRealSum (fun _ : Fin n ↦ (1 : ℝ)) e).card := by
  apply Finset.card_le_card_of_injOn (f := fun H ↦ (boolEquivHorizontalSchedule n).symm H)
  · intro H hH
    simpa using unbalanced_schedule_maps_to_tail H hH
  · exact (boolEquivHorizontalSchedule n).symm.injective.injOn

lemma finiteRademacherVariance_ones (n : ℕ) :
    finiteRademacherVariance (fun _ : Fin n ↦ (1 : ℝ)) = n := by
  unfold finiteRademacherVariance
  simp

/-- Schedules with fewer than one quarter vertical moves have exponentially small uniform mass. -/
theorem verticallyUnbalancedSchedules_density_le (n : ℕ) (hn : 1 ≤ n) :
    ((verticallyUnbalancedSchedules n).card : ℝ) / (2 : ℝ) ^ n ≤
      Real.exp (-(n : ℝ) / 8) := by
  have hcardNat := card_unbalancedSchedules_le_tail n
  have hcard : ((verticallyUnbalancedSchedules n).card : ℝ) ≤
      ((Finset.univ.filter fun e : Fin n → Bool ↦
        (n : ℝ) / 2 ≤ finiteRademacherRealSum (fun _ : Fin n ↦ (1 : ℝ)) e).card : ℝ) := by
    exact_mod_cast hcardNat
  have hden : (0 : ℝ) < 2 ^ n := by positivity
  calc
    ((verticallyUnbalancedSchedules n).card : ℝ) / (2 : ℝ) ^ n ≤
        ((Finset.univ.filter fun e : Fin n → Bool ↦
          (n : ℝ) / 2 ≤ finiteRademacherRealSum (fun _ : Fin n ↦ (1 : ℝ)) e).card : ℝ) /
          (2 : ℝ) ^ n := div_le_div_of_nonneg_right hcard hden.le
    _ = finiteRademacherUpperTailProbability (fun _ : Fin n ↦ (1 : ℝ)) ((n : ℝ) / 2) := by
      unfold finiteRademacherUpperTailProbability
      congr 1
      · rw [Finset.card_filter]
        push_cast
        simp
        apply congrArg Finset.card
        ext e
        simp
      · simp
    _ ≤ Real.exp (-(((n : ℝ) / 2) ^ 2) /
          (2 * finiteRademacherVariance (fun _ : Fin n ↦ (1 : ℝ)))) := by
      apply finiteRademacherUpperTailProbability_le
      · positivity
      · rw [finiteRademacherVariance_ones]
        exact_mod_cast hn
    _ = Real.exp (-(n : ℝ) / 8) := by
      rw [finiteRademacherVariance_ones]
      congr 1
      have hnR : (0 : ℝ) < n := by exact_mod_cast hn
      field_simp
      ring

abbrev VerticallyUnbalancedAxisPath (n : ℕ) :=
  {p : AxisGoodPath n // 4 * (p.1.1ᶜ).card < n}

lemma card_verticallyUnbalancedAxisPath_le (n : ℕ) :
    Fintype.card (VerticallyUnbalancedAxisPath n) ≤
      (verticallyUnbalancedSchedules n).card * 2 ^ n := by
  let f : VerticallyUnbalancedAxisPath n →
      (verticallyUnbalancedSchedules n) × (Fin n → Bool) := fun p ↦
    (⟨p.1.1.1, by simpa [verticallyUnbalancedSchedules] using p.property⟩, p.1.1.2)
  have hf : Function.Injective f := by
    intro p q h
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · exact congrArg (fun z ↦ z.1.1) h
    · exact congrArg (fun z ↦ z.2) h
  have hc := Fintype.card_le_of_injective f hf
  simpa [Fintype.card_prod, Fintype.card_coe, Fintype.card_fun] using hc

/-- Under full quadrant conditioning, the schedules excluded by the one-coordinate comparison
still have exponentially small probability. -/
theorem verticallyUnbalancedAxisPath_density_le (n : ℕ) (hn : 1 ≤ n) :
    (Fintype.card (VerticallyUnbalancedAxisPath n) : ℝ) /
        Fintype.card (AxisGoodPath n) ≤
      16 * (n + 1 : ℝ) * Real.exp (-(n : ℝ) / 8) := by
  have hbadNat := card_verticallyUnbalancedAxisPath_le n
  have hbad : (Fintype.card (VerticallyUnbalancedAxisPath n) : ℝ) ≤
      (verticallyUnbalancedSchedules n).card * (2 : ℝ) ^ n := by
    exact_mod_cast hbadNat
  have hgood : (0 : ℝ) < Fintype.card (AxisGoodPath n) := by
    exact_mod_cast card_axisGoodPath_pos n
  have hpow : (0 : ℝ) < (4 : ℝ) ^ n := by positivity
  have hraw :
      (Fintype.card (VerticallyUnbalancedAxisPath n) : ℝ) / (4 : ℝ) ^ n ≤
        Real.exp (-(n : ℝ) / 8) := by
    calc
      _ ≤ ((verticallyUnbalancedSchedules n).card * (2 : ℝ) ^ n) /
          (4 : ℝ) ^ n := div_le_div_of_nonneg_right hbad hpow.le
      _ = ((verticallyUnbalancedSchedules n).card : ℝ) / (2 : ℝ) ^ n := by
        rw [show (4 : ℝ) ^ n = (2 : ℝ) ^ n * (2 : ℝ) ^ n by
          rw [← mul_pow]; norm_num]
        field_simp
      _ ≤ _ := verticallyUnbalancedSchedules_density_le n hn
  have hsurv := card_axisGoodPath_ratio_lower n
  have hsurv' : (1 / (16 * (n + 1 : ℝ))) * (4 : ℝ) ^ n ≤
      Fintype.card (AxisGoodPath n) := (le_div_iff₀ hpow).1 hsurv
  have hscale : (4 : ℝ) ^ n ≤
      16 * (n + 1 : ℝ) * Fintype.card (AxisGoodPath n) := by
    have hpos : 0 ≤ (16 * (n + 1 : ℝ)) := by positivity
    calc
      (4 : ℝ) ^ n = (16 * (n + 1 : ℝ)) *
          ((1 / (16 * (n + 1 : ℝ))) * (4 : ℝ) ^ n) := by field_simp
      _ ≤ (16 * (n + 1 : ℝ)) * Fintype.card (AxisGoodPath n) :=
        mul_le_mul_of_nonneg_left hsurv' hpos
  apply (div_le_iff₀ hgood).2
  calc
    (Fintype.card (VerticallyUnbalancedAxisPath n) : ℝ) ≤
        Real.exp (-(n : ℝ) / 8) * (4 : ℝ) ^ n :=
      (div_le_iff₀ hpow).1 hraw
    _ ≤ Real.exp (-(n : ℝ) / 8) *
        (16 * (n + 1 : ℝ) * Fintype.card (AxisGoodPath n)) :=
      mul_le_mul_of_nonneg_left hscale (Real.exp_pos _).le
    _ = (16 * (n + 1 : ℝ) * Real.exp (-(n : ℝ) / 8)) *
        Fintype.card (AxisGoodPath n) := by ring

end Erdos521
