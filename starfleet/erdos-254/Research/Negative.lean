import Research.Statement

namespace Erdos254

open Filter
open scoped BigOperators

lemma nearestIntegerDistance_nonneg (x : ℝ) :
    0 ≤ nearestIntegerDistance x := by
  apply le_min
  · exact Int.fract_nonneg x
  · exact sub_nonneg.mpr (Int.fract_lt_one x).le

lemma nearestIntegerDistance_le_half (x : ℝ) :
    nearestIntegerDistance x ≤ 1 / 2 := by
  by_cases h : Int.fract x ≤ (1 : ℝ) / 2
  · exact (min_le_left _ _).trans h
  · exact (min_le_right _ _).trans (by linarith)

lemma nearestIntegerDistance_intCast (z : ℤ) :
    nearestIntegerDistance (z : ℝ) = 0 := by
  simp [nearestIntegerDistance, Int.fract]

lemma nearestIntegerDistance_natCast (n : ℕ) :
    nearestIntegerDistance (n : ℝ) = 0 := by
  simp [nearestIntegerDistance, Int.fract]

lemma phasePartialSum_monotone (A : Set ℕ) (θ : ℝ) :
    Monotone (phasePartialSum A θ) := by
  intro M N hMN
  classical
  simp only [phasePartialSum]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro n hn
    simp only [Finset.mem_filter, Finset.mem_Icc] at hn ⊢
    exact ⟨⟨hn.1.1, hn.1.2.trans hMN⟩, hn.2⟩
  · intro n _ _
    exact nearestIntegerDistance_nonneg _

lemma phasePartialSum_tendsto_iff_unbounded (A : Set ℕ) (θ : ℝ) :
    Tendsto (phasePartialSum A θ) atTop atTop ↔
      ∀ B : ℝ, ∃ N : ℕ, B ≤ phasePartialSum A θ N :=
  (phasePartialSum_monotone A θ).tendsto_atTop_atTop_iff

/-- A set contained in one proper divisibility class cannot satisfy the phase
hypothesis: the rational phase `1/q` annihilates every term. -/
theorem rational_phase_obstruction (A : Set ℕ) (q : ℕ) (hq : 2 ≤ q)
    (hdiv : ∀ n ∈ A, q ∣ n) :
    ¬ (∀ θ : ℝ, θ ∈ Set.Ioo 0 1 →
      Tendsto (phasePartialSum A θ) atTop atTop) := by
  intro hphase
  let θ : ℝ := 1 / (q : ℝ)
  have hqpos : (0 : ℝ) < (q : ℝ) := by positivity
  have hθpos : (0 : ℝ) < θ := by
    dsimp [θ]
    positivity
  have hθlt : θ < (1 : ℝ) := by
    dsimp [θ]
    rw [div_lt_one hqpos]
    exact_mod_cast (show 1 < q from lt_of_lt_of_le Nat.one_lt_two hq)
  have htend : Tendsto (phasePartialSum A θ) atTop atTop :=
    hphase θ ⟨hθpos, hθlt⟩
  have hzero : phasePartialSum A θ = fun _ => 0 := by
    funext N
    classical
    simp only [phasePartialSum]
    apply Finset.sum_eq_zero
    intro n hn
    have hnA : n ∈ A := (Finset.mem_filter.mp hn).2
    obtain ⟨k, rfl⟩ := hdiv n hnA
    simp [θ, nearestIntegerDistance, Int.fract, hqpos.ne']
  rw [hzero] at htend
  exact not_tendsto_const_atTop (0 : ℝ) atTop htend

/-- Even finitely many exceptions do not remove the rational obstruction. -/
theorem eventual_rational_phase_obstruction (A : Set ℕ) (q : ℕ) (hq : 2 ≤ q)
    (hevent : ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → n ∈ A → q ∣ n) :
    ¬ (∀ θ : ℝ, θ ∈ Set.Ioo 0 1 →
      Tendsto (phasePartialSum A θ) atTop atTop) := by
  intro hphase
  obtain ⟨N₀, hdiv⟩ := hevent
  let θ : ℝ := 1 / (q : ℝ)
  have hqpos : (0 : ℝ) < (q : ℝ) := by positivity
  have hθpos : (0 : ℝ) < θ := by
    dsimp [θ]
    positivity
  have hθlt : θ < (1 : ℝ) := by
    dsimp [θ]
    rw [div_lt_one hqpos]
    exact_mod_cast (show 1 < q from lt_of_lt_of_le Nat.one_lt_two hq)
  have htend : Tendsto (phasePartialSum A θ) atTop atTop :=
    hphase θ ⟨hθpos, hθlt⟩
  have heq : ∀ N : ℕ, N₀ ≤ N →
      phasePartialSum A θ N = phasePartialSum A θ N₀ := by
    intro N hN
    classical
    simp only [phasePartialSum]
    symm
    apply Finset.sum_subset
    · intro n hn
      simp only [Finset.mem_filter, Finset.mem_Icc] at hn ⊢
      exact ⟨⟨hn.1.1, hn.1.2.trans hN⟩, hn.2⟩
    · intro n hnN hn0
      simp only [Finset.mem_filter, Finset.mem_Icc] at hnN
      have hnle : N₀ ≤ n := by
        by_contra hnot
        have hnlt : n < N₀ := Nat.lt_of_not_ge hnot
        apply hn0
        simp only [Finset.mem_filter, Finset.mem_Icc]
        exact ⟨⟨hnN.1.1, hnlt.le⟩, hnN.2⟩
      obtain ⟨k, rfl⟩ := hdiv n hnle hnN.2
      simp [θ, nearestIntegerDistance, Int.fract, hqpos.ne']
  have hconst : Tendsto (fun _ : ℕ => phasePartialSum A θ N₀) atTop atTop := by
    apply htend.congr'
    filter_upwards [eventually_atTop.2 ⟨N₀, fun N hN => heq N hN⟩] with N hN
    exact hN
  exact not_tendsto_const_atTop (phasePartialSum A θ N₀) atTop hconst

/-- The phase hypothesis forces nonmultiples of every `q ≥ 2` arbitrarily far
out in the set. -/
theorem phase_implies_tail_nonmultiple (A : Set ℕ)
    (hphase : ∀ θ : ℝ, θ ∈ Set.Ioo 0 1 →
      Tendsto (phasePartialSum A θ) atTop atTop)
    (q : ℕ) (hq : 2 ≤ q) (N : ℕ) :
    ∃ n : ℕ, N ≤ n ∧ n ∈ A ∧ ¬ q ∣ n := by
  by_contra hnone
  have hdiv : ∀ n : ℕ, N ≤ n → n ∈ A → q ∣ n := by
    intro n hn hnA
    by_contra hndiv
    exact hnone ⟨n, hn, hnA, hndiv⟩
  exact (eventual_rational_phase_obstruction A q hq ⟨N, hdiv⟩) hphase

/-- Quantitative finite form of tail aperiodicity. -/
theorem phase_implies_many_nonmultiples (A : Set ℕ)
    (hphase : ∀ θ : ℝ, θ ∈ Set.Ioo 0 1 →
      Tendsto (phasePartialSum A θ) atTop atTop)
    (q : ℕ) (hq : 2 ≤ q) (K : ℕ) :
    ∃ s : Finset ℕ, s.card = K ∧ (↑s : Set ℕ) ⊆ A ∧
      ∀ n ∈ s, ¬ q ∣ n := by
  let E : Set ℕ := {n | n ∈ A ∧ ¬ q ∣ n}
  have hE : E.Infinite := by
    intro hfinite
    obtain ⟨M, hM⟩ := hfinite.exists_le
    obtain ⟨n, hnM, hnA, hnq⟩ :=
      phase_implies_tail_nonmultiple A hphase q hq (M + 1)
    have hnle : n ≤ M := hM n ⟨hnA, hnq⟩
    omega
  obtain ⟨s, hsE, hscard⟩ := hE.exists_subset_card_eq K
  refine ⟨s, hscard, ?_, ?_⟩
  · intro n hn
    exact (hsE hn).1
  · intro n hn
    exact (hsE hn).2

end Erdos254
