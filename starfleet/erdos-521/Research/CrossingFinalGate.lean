import Research.IntegratedCrossings
import Research.FlexibleUpperReduction
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic

open Filter MeasureTheory
open scoped Topology

namespace Erdos521

/-- The largest convenient rational one-sided target supplied by `π < 22/7`. -/
def RightUpperSevenTwentyTwo : Prop :=
  ∀ᵐ ω ∂rademacherMeasure,
    ∀ᶠ n : ℕ in atTop,
      (rightRootCount ω n : ℝ) / Real.log (n : ℝ) ≤ (7 : ℝ) / 22

lemma local_seven_elevenths_of_right_seven_twenty_two (h : RightUpperSevenTwentyTwo) :
    ∀ᵐ ω ∂rademacherMeasure,
      ∀ᶠ n : ℕ in atTop,
        (innerRootCount ω n : ℝ) / Real.log (n : ℝ) ≤ (7 : ℝ) / 11 := by
  have hleft := left_eventual_upper_of_right_eventual_upper h
  filter_upwards [h, hleft] with ω hright hleftω
  filter_upwards [hright, hleftω] with n hr hl
  rw [innerRootCount_eq_left_add_right]
  push_cast
  rw [add_div]
  linarith

lemma seven_elevenths_lt_two_div_pi : (7 : ℝ) / 11 < 2 / Real.pi := by
  have hp := Real.pi_pos
  apply (div_lt_div_iff₀ (by norm_num : (0 : ℝ) < 11) hp).2
  have hpi := Real.pi_lt_d20
  norm_num at hpi ⊢
  linarith

theorem erdos_521_negative_of_right_seven_twenty_two (h : RightUpperSevenTwentyTwo) : ¬ Claim :=
  erdos_521_negative_of_eventual_local_upper seven_elevenths_lt_two_div_pi
    (local_seven_elevenths_of_right_seven_twenty_two h)

/-- The remaining crossing gate: an eventual `0.3` upper bound for integrated-walk weak crossings. -/
def IntegratedCrossingUpperThreeTenths : Prop :=
  ∀ᵐ ω ∂rademacherMeasure,
    ∀ᶠ N : ℕ in atTop,
      (integratedCrossingCount ω N : ℝ) / Real.log ((N + 2 : ℕ) : ℝ) ≤ (3 : ℝ) / 10

lemma right_seven_twenty_two_of_crossing_three_tenths
    (h : IntegratedCrossingUpperThreeTenths) : RightUpperSevenTwentyTwo := by
  have hlog : ∀ᶠ n : ℕ in atTop, (165 : ℝ) ≤ Real.log (n : ℝ) := by
    have ht : Tendsto (fun n : ℕ ↦ Real.log (n : ℝ)) atTop atTop :=
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    exact ht.eventually (eventually_ge_atTop 165)
  obtain ⟨L, hL⟩ := eventually_atTop.1 hlog
  filter_upwards [h] with ω hω
  obtain ⟨K, hK⟩ := eventually_atTop.1 hω
  apply eventually_atTop.2
  refine ⟨max (K + 2) L, ?_⟩
  intro n hn
  let N := n - 2
  have hn2 : n = N + 2 := by
    dsimp [N]
    have : 2 ≤ n := le_trans (by omega : 2 ≤ K + 2) (le_trans (le_max_left _ _) hn)
    omega
  have hNK : K ≤ N := by
    dsimp [N]
    have := le_trans (le_max_left (K + 2) L) hn
    omega
  have hln : (165 : ℝ) ≤ Real.log (n : ℝ) := hL n (le_trans (le_max_right _ _) hn)
  have hlogpos : 0 < Real.log (n : ℝ) := lt_of_lt_of_le (by norm_num) hln
  have hcross := hK N hNK
  rw [← hn2] at hcross
  have hroot := rightRootCount_le_integratedCrossingCount_add_three ω N
  rw [← hn2] at hroot
  have hrootR : (rightRootCount ω n : ℝ) ≤ (integratedCrossingCount ω N : ℝ) + 3 := by
    exact_mod_cast hroot
  have hthree : (3 : ℝ) / Real.log (n : ℝ) ≤ 1 / 55 := by
    apply (div_le_iff₀ hlogpos).2
    nlinarith
  calc
    (rightRootCount ω n : ℝ) / Real.log (n : ℝ) ≤
        ((integratedCrossingCount ω N : ℝ) + 3) / Real.log (n : ℝ) :=
      div_le_div_of_nonneg_right hrootR (le_of_lt hlogpos)
    _ = (integratedCrossingCount ω N : ℝ) / Real.log (n : ℝ) +
        3 / Real.log (n : ℝ) := by ring
    _ ≤ (3 : ℝ) / 10 + 1 / 55 := add_le_add hcross hthree
    _ = (7 : ℝ) / 22 := by norm_num

/-- It is enough to prove the measurable integrated weak-crossing process has eventual rate `0.3`. -/
theorem erdos_521_negative_of_crossing_three_tenths
    (h : IntegratedCrossingUpperThreeTenths) : ¬ Claim :=
  erdos_521_negative_of_right_seven_twenty_two
    (right_seven_twenty_two_of_crossing_three_tenths h)

end Erdos521
