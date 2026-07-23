import Research.RecordProbability
import Research.DivergentTail
import Research.Reduction
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

open Filter MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

namespace Erdos521

local instance fairCoin_isProbabilityMeasure' : IsProbabilityMeasure fairCoin := by
  unfold fairCoin
  infer_instance

local instance rademacherMeasure_isProbabilityMeasure' :
    IsProbabilityMeasure rademacherMeasure := by
  unfold rademacherMeasure
  infer_instance

/-- Real-valued marginal mass of the time-`n` cone-record event. -/
noncomputable def coneRecordProbability (n : ℕ) : ℝ :=
  rademacherMeasure.real (coneRecordEvent n)

lemma coneRecordProbability_nonneg (n : ℕ) : 0 ≤ coneRecordProbability n :=
  measureReal_nonneg

lemma coneRecordProbability_zero : coneRecordProbability 0 = 1 := by
  simp [coneRecordProbability, coneRecordEvent, IsConeRecord]

lemma measureReal_inter_coneRecordEvent {i j : ℕ} (hij : i < j) :
    rademacherMeasure.real (coneRecordEvent i ∩ coneRecordEvent j) =
      coneRecordProbability i * coneRecordProbability (j - i) := by
  have hpos : 0 < j - i := by omega
  have hadd : i + (j - i) = j := by omega
  have h := measure_inter_coneRecordEvent i (j - i) hpos
  rw [hadd] at h
  change (rademacherMeasure (coneRecordEvent i ∩ coneRecordEvent j)).toReal =
    (rademacherMeasure (coneRecordEvent i)).toReal *
      (rademacherMeasure (coneRecordEvent (j - i))).toReal
  rw [h, ENNReal.toReal_mul]

lemma measureReal_inter_coneRecordEvent_self (i : ℕ) :
    rademacherMeasure.real (coneRecordEvent i ∩ coneRecordEvent i) =
      coneRecordProbability i := by
  simp [coneRecordProbability]

/-- A symmetric double sum splits into its diagonal plus twice its strict upper triangle. -/
lemma sum_square_eq_diag_add_two_upper {s : Finset ℕ} {f : ℕ → ℕ → ℝ}
    (hsymm : ∀ i ∈ s, ∀ j ∈ s, f i j = f j i) :
    (∑ i ∈ s, ∑ j ∈ s, f i j) =
      (∑ i ∈ s, f i i) + 2 * (∑ i ∈ s, ∑ j ∈ s.filter (i < ·), f i j) := by
  classical
  let P := s ×ˢ s
  let D := P.filter (fun p ↦ p.1 = p.2)
  let U := P.filter (fun p ↦ p.1 < p.2)
  let L := P.filter (fun p ↦ p.2 < p.1)
  have hsplit : (∑ p ∈ P, f p.1 p.2) =
      (∑ p ∈ D, f p.1 p.2) + (∑ p ∈ U, f p.1 p.2) +
        (∑ p ∈ L, f p.1 p.2) := by
    calc
      (∑ p ∈ P, f p.1 p.2) = P.sum (fun p ↦
          ((if p.1 = p.2 then f p.1 p.2 else 0) +
            (if p.1 < p.2 then f p.1 p.2 else 0)) +
              (if p.2 < p.1 then f p.1 p.2 else 0)) := by
        apply Finset.sum_congr rfl
        intro p hp
        rcases lt_trichotomy p.1 p.2 with hlt | heq | hgt
        · simp [hlt, hlt.ne, hlt.not_gt]
        · simp [heq]
        · simp [hgt, hgt.ne', hgt.not_gt]
      _ = (∑ p ∈ D, f p.1 p.2) + (∑ p ∈ U, f p.1 p.2) +
          (∑ p ∈ L, f p.1 p.2) := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
        simp only [D, U, L, Finset.sum_filter]
  have hdiag : (∑ p ∈ D, f p.1 p.2) = ∑ i ∈ s, f i i := by
    refine Finset.sum_bij (fun p _ ↦ p.1) ?_ ?_ ?_ ?_
    · intro p hp
      have hp' : p ∈ P ∧ p.1 = p.2 := by simpa [D] using hp
      exact (Finset.mem_product.mp hp'.1).1
    · intro p₁ hp₁ p₂ hp₂ heq
      have h1 : p₁ ∈ P ∧ p₁.1 = p₁.2 := by simpa [D] using hp₁
      have h2 : p₂ ∈ P ∧ p₂.1 = p₂.2 := by simpa [D] using hp₂
      apply Prod.ext
      · exact heq
      · simpa [h1.2, h2.2] using heq
    · intro i hi
      refine ⟨(i, i), ?_, rfl⟩
      simp [D, P, hi]
    · intro p hp
      have hp' : p ∈ P ∧ p.1 = p.2 := by simpa [D] using hp
      simp [hp'.2]
  have hlower : (∑ p ∈ L, f p.1 p.2) = ∑ p ∈ U, f p.1 p.2 := by
    refine Finset.sum_bij (fun p _ ↦ (p.2, p.1)) ?_ ?_ ?_ ?_
    · intro p hp
      rcases Finset.mem_filter.mp hp with ⟨hpP, hplt⟩
      rcases Finset.mem_product.mp hpP with ⟨hp1, hp2⟩
      simp [U, P, hp1, hp2, hplt]
    · intro p₁ hp₁ p₂ hp₂ heq
      exact Prod.ext (congrArg Prod.snd heq) (congrArg Prod.fst heq)
    · intro p hp
      rcases Finset.mem_filter.mp hp with ⟨hpP, hplt⟩
      rcases Finset.mem_product.mp hpP with ⟨hp1, hp2⟩
      refine ⟨(p.2, p.1), ?_, by simp⟩
      simp [L, P, hp1, hp2, hplt]
    · intro p hp
      rcases Finset.mem_filter.mp hp with ⟨hpP, _⟩
      rcases Finset.mem_product.mp hpP with ⟨hp1, hp2⟩
      simpa using hsymm p.1 hp1 p.2 hp2
  have hupper : (∑ p ∈ U, f p.1 p.2) =
      ∑ i ∈ s, ∑ j ∈ s.filter (i < ·), f i j := by
    simpa only [U, P, Finset.sum_filter] using
      (Finset.sum_product' s s (fun i j ↦ if i < j then f i j else 0))
  rw [← Finset.sum_product', hsplit, hdiag, hlower, hupper]
  ring

/-- Positive lags from one row of an interval inject into the full lag range. -/
lemma sum_positive_lags_le_partialSum (q : ℕ → ℝ) (hq : ∀ n, 0 ≤ q n)
    (K N i : ℕ) :
    (∑ j ∈ (Finset.Icc K N).filter (i < ·), q (j - i)) ≤
      ∑ d ∈ Finset.range (N + 1), q d := by
  classical
  let u := (Finset.Icc K N).filter (i < ·)
  let v := u.image (fun j ↦ j - i)
  have hinj : Set.InjOn (fun j ↦ j - i) (u : Set ℕ) := by
    intro x hx y hy hxy
    have hxlt : i < x := (Finset.mem_filter.mp hx).2
    have hylt : i < y := (Finset.mem_filter.mp hy).2
    change x - i = y - i at hxy
    omega
  have hsum : (∑ d ∈ v, q d) = ∑ j ∈ u, q (j - i) :=
    Finset.sum_image hinj
  have hsub : v ⊆ Finset.range (N + 1) := by
    intro d hd
    rcases Finset.mem_image.mp hd with ⟨j, hju, rfl⟩
    have hjIcc := (Finset.mem_filter.mp hju).1
    have hjN := (Finset.mem_Icc.mp hjIcc).2
    simp only [Finset.mem_range]
    omega
  change (∑ j ∈ u, q (j - i)) ≤ ∑ d ∈ Finset.range (N + 1), q d
  rw [← hsum]
  exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun d hd hdv ↦ hq d)

lemma sum_upper_record_products_le (q : ℕ → ℝ) (hq : ∀ n, 0 ≤ q n)
    (K N : ℕ) :
    let s := Finset.Icc K N
    let S := ∑ i ∈ s, q i
    let T := ∑ d ∈ Finset.range (N + 1), q d
    (∑ i ∈ s, ∑ j ∈ s.filter (i < ·), q i * q (j - i)) ≤ S * T := by
  dsimp only
  let s := Finset.Icc K N
  let T := ∑ d ∈ Finset.range (N + 1), q d
  calc
    (∑ i ∈ s, ∑ j ∈ s.filter (i < ·), q i * q (j - i)) =
        ∑ i ∈ s, q i * (∑ j ∈ s.filter (i < ·), q (j - i)) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mul_sum]
    _ ≤ ∑ i ∈ s, q i * T := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_left
        (sum_positive_lags_le_partialSum q hq K N i) (hq i)
    _ = (∑ i ∈ s, q i) * T := by rw [Finset.sum_mul]

/-- The exact two-time law F-010 implies the aggregate correlation estimate needed by F-008. -/
lemma coneRecord_correlation_bound (K N : ℕ) (hKN : K ≤ N) :
    let s := Finset.Icc K N
    let S := ∑ i ∈ s, coneRecordProbability i
    let T := ∑ i ∈ Finset.range (N + 1), coneRecordProbability i
    (∑ i ∈ s, ∑ j ∈ s,
      rademacherMeasure.real (coneRecordEvent i ∩ coneRecordEvent j)) ≤
        S + 2 * S * T := by
  dsimp only
  let s := Finset.Icc K N
  let S := ∑ i ∈ s, coneRecordProbability i
  let T := ∑ i ∈ Finset.range (N + 1), coneRecordProbability i
  let f := fun i j ↦ rademacherMeasure.real (coneRecordEvent i ∩ coneRecordEvent j)
  have hsymm : ∀ i ∈ s, ∀ j ∈ s, f i j = f j i := by
    intro i hi j hj
    simp only [f, inter_comm]
  have hsplit := sum_square_eq_diag_add_two_upper (s := s) hsymm
  have hdiag : (∑ i ∈ s, f i i) = S := by
    apply Finset.sum_congr rfl
    intro i hi
    exact measureReal_inter_coneRecordEvent_self i
  have hupper : (∑ i ∈ s, ∑ j ∈ s.filter (i < ·), f i j) =
      ∑ i ∈ s, ∑ j ∈ s.filter (i < ·),
        coneRecordProbability i * coneRecordProbability (j - i) := by
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    exact measureReal_inter_coneRecordEvent (Finset.mem_filter.mp hj).2
  have hub : (∑ i ∈ s, ∑ j ∈ s.filter (i < ·),
      coneRecordProbability i * coneRecordProbability (j - i)) ≤ S * T := by
    exact sum_upper_record_products_le coneRecordProbability coneRecordProbability_nonneg K N
  change (∑ i ∈ s, ∑ j ∈ s, f i j) ≤ S + 2 * S * T
  rw [hsplit, hdiag, hupper]
  nlinarith

/-- Divergence of the concrete Rademacher record masses implies positive-measure recurrence. -/
lemma positive_eventLimsup_coneRecord_of_divergence
    (hdiv : Tendsto
      (fun N ↦ ∑ i ∈ Finset.range (N + 1), coneRecordProbability i) atTop atTop) :
    0 < rademacherMeasure (eventLimsup coneRecordEvent) := by
  apply positive_limsup_of_record_correlation rademacherMeasure
    measurableSet_coneRecordEvent coneRecordProbability coneRecordProbability_nonneg
  · intro n
    rfl
  · exact tailLarge_of_partialSums_tendsto_atTop coneRecordProbability
      coneRecordProbability_nonneg hdiv
  · exact coneRecord_correlation_bound

lemma eventLimsup_coneRecord_subset_infinitelyOften :
    eventLimsup coneRecordEvent ⊆ {ω | InfinitelyOftenConeRecords ω} := by
  intro ω hω N
  have htail := Set.mem_iInter.mp hω (N + 1)
  simp only [eventTail, Set.mem_iUnion] at htail
  obtain ⟨n, hn, hrec⟩ := htail
  refine ⟨n - 1, by omega, ?_⟩
  have hnpos : 0 < n := by omega
  have hnsub : n - 1 + 1 = n := by omega
  simpa only [coneRecordEvent, Set.mem_setOf_eq, hnsub] using hrec

lemma positive_infinitelyOftenConeRecords_of_divergence
    (hdiv : Tendsto
      (fun N ↦ ∑ i ∈ Finset.range (N + 1), coneRecordProbability i) atTop atTop) :
    0 < rademacherMeasure {ω | InfinitelyOftenConeRecords ω} := by
  exact (positive_eventLimsup_coneRecord_of_divergence hdiv).trans_le
    (measure_mono eventLimsup_coneRecord_subset_infinitelyOften)

end Erdos521
