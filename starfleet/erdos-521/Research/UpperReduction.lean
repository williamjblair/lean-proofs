import Research.RademacherBallot
import Research.Reduction
import Mathlib.Tactic

open Filter MeasureTheory
open scoped Topology

namespace Erdos521

/-- A deliberately weaker analytic input than Do's exact local strong law: eventually the number
of roots in `[-1,1]` is at most `3/(2π)` times `log n`, leaving a fixed gap below `2/π`. -/
def LocalUpperGap : Prop :=
  ∀ᵐ ω ∂rademacherMeasure,
    ∀ᶠ n : ℕ in atTop,
      (innerRootCount ω n : ℝ) / Real.log (n : ℝ) ≤ (3 : ℝ) / (2 * Real.pi)

/-- The exact local limit `1/π` is stronger than the upper-gap statement. -/
lemma localUpperGap_of_localStrongLaw (h : LocalStrongLaw) : LocalUpperGap := by
  filter_upwards [h] with ω hω
  have hlt : (1 : ℝ) / Real.pi < (3 : ℝ) / (2 * Real.pi) := by
    have hp := Real.pi_pos
    apply (div_lt_div_iff₀ hp (mul_pos (by norm_num) hp)).2
    nlinarith
  exact hω.eventually (Iic_mem_nhds hlt)

/-- The weak eventual upper gap, together with the unconditional recurrent cone records, already
refutes the proposed total-root limit. -/
theorem erdos_521_negative_of_localUpperGap (hlocal : LocalUpperGap) : ¬ Claim := by
  intro hclaim
  have hboth : ∀ᵐ ω ∂rademacherMeasure,
      Tendsto (fun n : ℕ ↦ (realRootCount ω n : ℝ) / Real.log (n : ℝ))
          atTop (𝓝 ((2 : ℝ) / Real.pi)) ∧
      (∀ᶠ n : ℕ in atTop,
        (innerRootCount ω n : ℝ) / Real.log (n : ℝ) ≤ (3 : ℝ) / (2 * Real.pi)) :=
    hclaim.and hlocal
  obtain ⟨ω, hωrec, htotal, hupper⟩ :=
    Measure.exists_mem_of_measure_ne_zero_of_ae positive_infinitelyOftenConeRecords.ne'
      (ae_restrict_of_ae hboth)
  have hthreshold : (3 : ℝ) / (2 * Real.pi) < (2 : ℝ) / Real.pi := by
    have hp := Real.pi_pos
    apply (div_lt_div_iff₀ (mul_pos (by norm_num) hp) hp).2
    nlinarith
  have hlower : ∀ᶠ n : ℕ in atTop,
      (3 : ℝ) / (2 * Real.pi) <
        (realRootCount ω n : ℝ) / Real.log (n : ℝ) :=
    htotal.eventually (Ioi_mem_nhds hthreshold)
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hupper.and hlower)
  obtain ⟨m, hmN, hmrec⟩ := hωrec N
  have hmdeg : N ≤ 2 * m + 1 := by omega
  have hinner_m := (hN (2 * m + 1) hmdeg).1
  have htotal_m := (hN (2 * m + 1) hmdeg).2
  rw [← coneRecord_innerRootCount_eq hmrec] at htotal_m
  linarith

end Erdos521
