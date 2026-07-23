import Mathlib
import Research.Statement

namespace Erdos254.PhaseEscape

open scoped BigOperators

/-- A representative of a real number modulo one in `[-1/2,1/2]`. -/
noncomputable def centeredFraction (x : ℝ) : ℝ :=
  if Int.fract x ≤ 1 / 2 then Int.fract x else Int.fract x - 1

lemma centeredFraction_nonneg_iff (x : ℝ) :
    0 ≤ centeredFraction x ↔ Int.fract x ≤ 1 / 2 := by
  rw [centeredFraction]
  split_ifs with h
  · exact ⟨fun _ => h, fun _ => Int.fract_nonneg x⟩
  · constructor
    · intro hx
      have hlt := Int.fract_lt_one x
      linarith
    · exact fun hx => (h hx).elim

lemma abs_centeredFraction (x : ℝ) :
    |centeredFraction x| = nearestIntegerDistance x := by
  rw [centeredFraction, nearestIntegerDistance]
  split_ifs with h
  · rw [abs_of_nonneg (Int.fract_nonneg x), min_eq_left (by linarith)]
  · have hhalf : 1 / 2 < Int.fract x := lt_of_not_ge h
    have hnonpos : Int.fract x - 1 ≤ 0 := (Int.fract_lt_one x).le |> sub_nonpos.mpr
    rw [abs_of_nonpos hnonpos, min_eq_right (by linarith)]
    ring

lemma centeredFraction_le_half (x : ℝ) : centeredFraction x ≤ 1 / 2 := by
  rw [centeredFraction]
  split_ifs with h
  · exact h
  · have := Int.fract_lt_one x
    linarith

lemma neg_centeredFraction_le_half (x : ℝ) : -centeredFraction x ≤ 1 / 2 := by
  rw [centeredFraction]
  split_ifs with h
  · have := Int.fract_nonneg x
    linarith
  · have hhalf : 1 / 2 < Int.fract x := lt_of_not_ge h
    linarith

/-- If bounded nonnegative weights have total at least `1/4`, some subfamily
has total between `1/4` and `3/4`. -/
lemma exists_subset_sum_quarter {α : Type*} [DecidableEq α]
    (s : Finset α) (w : α → ℝ)
    (hw0 : ∀ a ∈ s, 0 ≤ w a) (hw : ∀ a ∈ s, w a ≤ 1 / 2)
    (hs : 1 / 4 ≤ ∑ a ∈ s, w a) :
    ∃ t : Finset α, t ⊆ s ∧
      1 / 4 ≤ ∑ a ∈ t, w a ∧ ∑ a ∈ t, w a ≤ 3 / 4 := by
  classical
  induction s using Finset.induction with
  | empty =>
      exfalso
      norm_num at hs
  | @insert a s ha ih =>
      by_cases hrest : 1 / 4 ≤ ∑ x ∈ s, w x
      · obtain ⟨t, hts, hlo, hhi⟩ := ih
          (fun x hx => hw0 x (Finset.mem_insert_of_mem hx))
          (fun x hx => hw x (Finset.mem_insert_of_mem hx)) hrest
        exact ⟨t, hts.trans (Finset.subset_insert a s), hlo, hhi⟩
      · refine ⟨insert a s, Finset.Subset.rfl, ?_, ?_⟩
        · exact hs
        · rw [Finset.sum_insert ha]
          have ha' := hw a (Finset.mem_insert_self a s)
          linarith

/-- A finite family with total nearest-integer mass at least `1/2` contains a
subfamily whose sum of centered representatives stays a definite distance
from every integer. -/
theorem finite_phase_escape {α : Type*} [DecidableEq α]
    (s : Finset α) (f : α → ℝ)
    (hs : 1 / 2 ≤ ∑ a ∈ s, nearestIntegerDistance (f a)) :
    ∃ t : Finset α, t ⊆ s ∧
      ((1 / 4 ≤ ∑ a ∈ t, centeredFraction (f a) ∧
          ∑ a ∈ t, centeredFraction (f a) ≤ 3 / 4) ∨
       (-3 / 4 ≤ ∑ a ∈ t, centeredFraction (f a) ∧
          ∑ a ∈ t, centeredFraction (f a) ≤ -1 / 4)) := by
  classical
  let p := s.filter (fun a => 0 ≤ centeredFraction (f a))
  let m := s.filter (fun a => centeredFraction (f a) < 0)
  have hsplit : ∑ a ∈ s, nearestIntegerDistance (f a) =
      (∑ a ∈ p, centeredFraction (f a)) +
      (∑ a ∈ m, -centeredFraction (f a)) := by
    change (∑ a ∈ s, nearestIntegerDistance (f a)) =
      (∑ a ∈ s.filter (fun a => 0 ≤ centeredFraction (f a)), centeredFraction (f a)) +
      (∑ a ∈ s.filter (fun a => centeredFraction (f a) < 0), -centeredFraction (f a))
    rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro a ha
    rw [← abs_centeredFraction]
    by_cases h : 0 ≤ centeredFraction (f a)
    · simp [h, not_lt_of_ge h, abs_of_nonneg h]
    · have hlt : centeredFraction (f a) < 0 := lt_of_not_ge h
      simp [h, hlt, abs_of_neg hlt]
  by_cases hp : 1 / 4 ≤ ∑ a ∈ p, centeredFraction (f a)
  · obtain ⟨t, htp, hlo, hhi⟩ := exists_subset_sum_quarter p
      (fun a => centeredFraction (f a))
      (by intro a ha; exact (Finset.mem_filter.mp ha).2)
      (by intro a ha; exact centeredFraction_le_half (f a)) hp
    exact ⟨t, htp.trans (Finset.filter_subset _ _), Or.inl ⟨hlo, hhi⟩⟩
  · have hm : 1 / 4 ≤ ∑ a ∈ m, -centeredFraction (f a) := by
      rw [hsplit] at hs
      linarith
    obtain ⟨t, htm, hlo, hhi⟩ := exists_subset_sum_quarter m
      (fun a => -centeredFraction (f a))
      (by intro a ha; exact (Finset.mem_filter.mp ha).2.le |> neg_nonneg.mpr)
      (by intro a ha; exact neg_centeredFraction_le_half (f a)) hm
    refine ⟨t, htm.trans (Finset.filter_subset _ _), Or.inr ?_⟩
    simp only [Finset.sum_neg_distrib] at hlo hhi
    constructor <;> linarith

/-- Divergence of a phase series produces a definite subset-sum escape using
members beyond every prescribed cutoff. -/
theorem tail_phase_escape (A : Set ℕ) (θ : ℝ)
    (hdiv : Filter.Tendsto (phasePartialSum A θ)
      (Filter.atTop : Filter ℕ) Filter.atTop)
    (N : ℕ) :
    ∃ s : Finset ℕ,
      (∀ n ∈ s, n ∈ A ∧ N ≤ n) ∧
      ((1 / 4 ≤ ∑ n ∈ s, centeredFraction (θ * (n : ℝ)) ∧
          ∑ n ∈ s, centeredFraction (θ * (n : ℝ)) ≤ 3 / 4) ∨
       (-3 / 4 ≤ ∑ n ∈ s, centeredFraction (θ * (n : ℝ)) ∧
          ∑ n ∈ s, centeredFraction (θ * (n : ℝ)) ≤ -1 / 4)) := by
  classical
  let P : ℕ → Finset ℕ := fun M =>
    (Finset.Icc 1 M).filter (fun n => n ∈ A)
  let base := phasePartialSum A θ (N - 1)
  have hev := Filter.tendsto_atTop.mp hdiv (base + 1 / 2)
  have hevN : ∀ᶠ M : ℕ in Filter.atTop,
      N ≤ M ∧ base + 1 / 2 ≤ phasePartialSum A θ M :=
    (Filter.eventually_ge_atTop N).and hev
  obtain ⟨M, hNM, hM⟩ := hevN.exists
  have hsub : P (N - 1) ⊆ P M := by
    intro n hn
    change n ∈ (Finset.Icc 1 (N - 1)).filter (fun n => n ∈ A) at hn
    change n ∈ (Finset.Icc 1 M).filter (fun n => n ∈ A)
    rw [Finset.mem_filter, Finset.mem_Icc] at hn ⊢
    exact ⟨⟨hn.1.1, by omega⟩, hn.2⟩
  let s := P M \ P (N - 1)
  have hmass : 1 / 2 ≤
      ∑ n ∈ s, nearestIntegerDistance (θ * (n : ℝ)) := by
    have hdiff := Finset.sum_sdiff_eq_sub (f := fun n : ℕ =>
      nearestIntegerDistance (θ * (n : ℝ))) hsub
    change (∑ n ∈ P M \ P (N - 1),
      nearestIntegerDistance (θ * (n : ℝ))) = _ at hdiff
    have hPM : (∑ n ∈ P M, nearestIntegerDistance (θ * (n : ℝ))) =
        phasePartialSum A θ M := by rfl
    have hP0 : (∑ n ∈ P (N - 1), nearestIntegerDistance (θ * (n : ℝ))) =
        base := by rfl
    change 1 / 2 ≤ ∑ n ∈ P M \ P (N - 1),
      nearestIntegerDistance (θ * (n : ℝ))
    rw [hdiff, hPM, hP0]
    linarith
  obtain ⟨t, hts, ht⟩ := finite_phase_escape s
    (fun n => θ * (n : ℝ)) hmass
  refine ⟨t, ?_, ht⟩
  intro n hn
  have hns : n ∈ s := hts hn
  have hnM : n ∈ P M := (Finset.mem_sdiff.mp hns).1
  have hn0 : n ∉ P (N - 1) := (Finset.mem_sdiff.mp hns).2
  change n ∈ (Finset.Icc 1 M).filter (fun n => n ∈ A) at hnM
  rw [Finset.mem_filter, Finset.mem_Icc] at hnM
  have hnA := hnM.2
  refine ⟨hnA, ?_⟩
  by_contra hnot
  have hnle : n ≤ N - 1 := by omega
  apply hn0
  change n ∈ (Finset.Icc 1 (N - 1)).filter (fun n => n ∈ A)
  rw [Finset.mem_filter, Finset.mem_Icc]
  exact ⟨⟨hnM.1.1, hnle⟩, hnA⟩

end Erdos254.PhaseEscape
