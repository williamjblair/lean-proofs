import Research.SecondMoment
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Tactic

open MeasureTheory Set Filter
open scoped BigOperators ENNReal

namespace Erdos521

section KochenStone

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]

/-- Union of all events from time `K` onward. -/
def eventTail (A : ℕ → Set Ω) (K : ℕ) : Set Ω :=
  ⋃ n : ℕ, ⋃ _h : K ≤ n, A n

/-- Event that infinitely many of the events `A n` occur. -/
def eventLimsup (A : ℕ → Set Ω) : Set Ω :=
  ⋂ K : ℕ, eventTail A K

lemma measurableSet_eventTail {A : ℕ → Set Ω} (hA : ∀ n, MeasurableSet (A n)) (K : ℕ) :
    MeasurableSet (eventTail A K) := by
  apply MeasurableSet.iUnion
  intro n
  apply MeasurableSet.iUnion
  intro h
  exact hA n

lemma eventTail_antitone (A : ℕ → Set Ω) : Antitone (eventTail A) := by
  intro K L hKL x hx
  simp only [eventTail, Set.mem_iUnion] at hx ⊢
  obtain ⟨n, hn, hxn⟩ := hx
  exact ⟨n, hKL.trans hn, hxn⟩

lemma eventUnion_Icc_subset_tail (A : ℕ → Set Ω) {K N : ℕ} :
    eventUnion A (Finset.Icc K N) ⊆ eventTail A K := by
  intro x hx
  simp only [eventUnion, Set.mem_iUnion] at hx
  obtain ⟨n, hnIcc, hxn⟩ := hx
  have hKn : K ≤ n := (Finset.mem_Icc.mp hnIcc).1
  exact Set.mem_iUnion.mpr ⟨n, Set.mem_iUnion.mpr ⟨hKn, hxn⟩⟩

/-- A convenient Kochen--Stone criterion.  If every tail contains a finite block whose sum of
pair intersections is at most `C` times the squared first moment, then infinitely many events
occur on a set of positive measure. -/
lemma kochenStone_of_finite_blocks {A : ℕ → Set Ω} (hA : ∀ n, MeasurableSet (A n))
    {C : ℝ} (hC : 0 < C)
    (hblock : ∀ K : ℕ, ∃ N ≥ K,
      let s := Finset.Icc K N
      let S := ∑ i ∈ s, μ.real (A i)
      let D := ∑ i ∈ s, ∑ j ∈ s, μ.real (A i ∩ A j)
      0 < S ∧ D ≤ C * S ^ 2) :
    0 < μ (eventLimsup A) := by
  have htailReal (K : ℕ) : 1 / C ≤ μ.real (eventTail A K) := by
    obtain ⟨N, hKN, hS, hD⟩ := hblock K
    let s := Finset.Icc K N
    let S := ∑ i ∈ s, μ.real (A i)
    let D := ∑ i ∈ s, ∑ j ∈ s, μ.real (A i ∩ A j)
    change 0 < S at hS
    change D ≤ C * S ^ 2 at hD
    have hsecond : S ^ 2 ≤ μ.real (eventUnion A s) * D := by
      exact finite_event_second_moment μ s (fun i hi ↦ hA i)
    have hmono : μ.real (eventUnion A s) ≤ μ.real (eventTail A K) :=
      measureReal_mono (eventUnion_Icc_subset_tail A)
    have hD0 : 0 ≤ D := by
      dsimp [D]
      positivity
    have htail0 : 0 ≤ μ.real (eventTail A K) := measureReal_nonneg
    have hsquare : 0 < S ^ 2 := sq_pos_of_pos hS
    have hchain : S ^ 2 ≤ (μ.real (eventTail A K) * C) * S ^ 2 :=
      calc
        S ^ 2 ≤ μ.real (eventUnion A s) * D := hsecond
        _ ≤ μ.real (eventTail A K) * D := mul_le_mul_of_nonneg_right hmono hD0
        _ ≤ μ.real (eventTail A K) * (C * S ^ 2) :=
          mul_le_mul_of_nonneg_left hD htail0
        _ = (μ.real (eventTail A K) * C) * S ^ 2 := by ring
    apply (div_le_iff₀ hC).2
    nlinarith
  have htailENN (K : ℕ) : ENNReal.ofReal (1 / C) ≤ μ (eventTail A K) := by
    apply (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top μ _)).2
    simpa only [measureReal_def] using htailReal K
  have hinter : μ (eventLimsup A) = ⨅ K : ℕ, μ (eventTail A K) := by
    exact (eventTail_antitone A).measure_iInter
      (fun K ↦ (measurableSet_eventTail hA K).nullMeasurableSet)
      ⟨0, measure_ne_top μ _⟩
  rw [hinter]
  exact (ENNReal.ofReal_pos.mpr (div_pos one_pos hC)).trans_le (le_iInf htailENN)

end KochenStone

end Erdos521
