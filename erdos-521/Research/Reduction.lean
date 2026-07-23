import Research.RademacherRecords
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.Tactic

open Filter MeasureTheory
open scoped Topology

namespace Erdos521

/-- Number of distinct real roots in the closed unit interval, written using `|x| ≤ 1`. -/
noncomputable def innerRootCount (ω : ℕ → Bool) (n : ℕ) : ℕ :=
  Set.ncard (((littlewoodPolynomial ω n).rootSet ℝ) ∩ {x : ℝ | |x| ≤ 1})

lemma root_eval_eq_zero {p : Polynomial ℝ} {x : ℝ} (hx : x ∈ p.rootSet ℝ) :
    p.eval x = 0 := by
  rw [Polynomial.mem_rootSet] at hx
  simpa [Polynomial.aeval_def] using hx.2

/-- If a polynomial has no exterior roots, its total and inner real-root counts agree. -/
lemma innerRootCount_eq_realRootCount_of_no_exterior (ω : ℕ → Bool) (n : ℕ)
    (hno : ∀ x : ℝ, 1 < |x| → (littlewoodPolynomial ω n).eval x ≠ 0) :
    innerRootCount ω n = realRootCount ω n := by
  apply congrArg Set.ncard
  apply Set.Subset.antisymm Set.inter_subset_left
  intro x hx
  refine ⟨hx, ?_⟩
  by_contra hle
  have hlt : 1 < |x| := lt_of_not_ge hle
  exact hno x hlt (root_eval_eq_zero hx)

/-- At every paired cone-record time, the total root count equals the count in `[-1,1]`. -/
lemma coneRecord_innerRootCount_eq {ω : ℕ → Bool} {m : ℕ}
    (hrec : IsConeRecord (rademacherIncrement ω) (m + 1)) :
    innerRootCount ω (2 * m + 1) = realRootCount ω (2 * m + 1) := by
  apply innerRootCount_eq_realRootCount_of_no_exterior
  intro x hx
  exact coneRecord_no_exterior_root hrec hx

/-- A path has cone records arbitrarily far out. -/
def InfinitelyOftenConeRecords (ω : ℕ → Bool) : Prop :=
  ∀ N : ℕ, ∃ m ≥ N, IsConeRecord (rademacherIncrement ω) (m + 1)

/-- The already-known local strong law, isolated as the analytic input to the new reduction. -/
def LocalStrongLaw : Prop :=
  ∀ᵐ ω ∂rademacherMeasure,
    Tendsto (fun n : ℕ ↦ (innerRootCount ω n : ℝ) / Real.log (n : ℝ))
      atTop (𝓝 ((1 : ℝ) / Real.pi))

/-- Abstract final reduction: the local strong law plus a positive-measure set of arbitrarily
large cone records contradicts the proposed total-root strong law. -/
lemma negative_of_localStrongLaw_of_coneRecords
    (hlocal : LocalStrongLaw)
    (hrecords : 0 < rademacherMeasure {ω | InfinitelyOftenConeRecords ω}) :
    ¬ Claim := by
  intro hclaim
  have hboth : ∀ᵐ ω ∂rademacherMeasure,
      Tendsto (fun n : ℕ ↦ (realRootCount ω n : ℝ) / Real.log (n : ℝ))
          atTop (𝓝 ((2 : ℝ) / Real.pi)) ∧
      Tendsto (fun n : ℕ ↦ (innerRootCount ω n : ℝ) / Real.log (n : ℝ))
          atTop (𝓝 ((1 : ℝ) / Real.pi)) := hclaim.and hlocal
  obtain ⟨ω, hωrec, htotal, hinner⟩ :=
    Measure.exists_mem_of_measure_ne_zero_of_ae hrecords.ne'
      (ae_restrict_of_ae hboth)
  have hdiff : Tendsto
      (fun n : ℕ ↦ (realRootCount ω n : ℝ) / Real.log (n : ℝ) -
        (innerRootCount ω n : ℝ) / Real.log (n : ℝ))
      atTop (𝓝 ((1 : ℝ) / Real.pi)) := by
    convert htotal.sub hinner using 1
    congr 1
    ring
  have hpi : 0 < (1 : ℝ) / Real.pi := div_pos one_pos Real.pi_pos
  have hevent : ∀ᶠ n : ℕ in atTop,
      0 < (realRootCount ω n : ℝ) / Real.log (n : ℝ) -
        (innerRootCount ω n : ℝ) / Real.log (n : ℝ) :=
    hdiff.eventually (Ioi_mem_nhds hpi)
  obtain ⟨N, hN⟩ := (eventually_atTop.1 hevent)
  obtain ⟨m, hmN, hmrec⟩ := hωrec N
  have hnN : N ≤ 2 * m + 1 := by omega
  have hpos := hN (2 * m + 1) hnN
  rw [← coneRecord_innerRootCount_eq hmrec] at hpos
  linarith

end Erdos521
