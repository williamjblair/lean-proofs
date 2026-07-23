import Mathlib
import Research.GrowthPartition
import Research.GrowingReservation
import Research.ReserveGrowth

namespace Erdos254.CanonicalCountableReserve

open Filter
open scoped BigOperators
open Erdos254.GrowthPartition Erdos254.GrowingReservation Erdos254.ReserveGrowth

noncomputable section

lemma tendsto_shift_index (J : ℕ) : Tendsto (fun n : ℕ => J + n) atTop atTop := by
  rw [tendsto_atTop]
  intro b
  filter_upwards [eventually_ge_atTop b] with n hn
  omega

lemma divergent_shell_sums_shift
    (f : ℕ → ℝ)
    (h : Tendsto (fun N => ∑ j ∈ Finset.range N, f j) atTop atTop)
    (J : ℕ) :
    Tendsto (fun N => ∑ j ∈ Finset.range N, f (J + j)) atTop atTop := by
  rw [tendsto_atTop]
  intro b
  have ht := tendsto_atTop.1 h
    (b + ∑ j ∈ Finset.range J, f j)
  filter_upwards [(tendsto_shift_index J).eventually ht] with N hN
  rw [Finset.sum_range_add] at hN
  linarith

/-- Canonical dyadic-shell version of F-052/F-053 allowing arbitrary finite
initial shells: after a cutoff one can choose growing shell reserves which are
syndetic and preserve a prescribed countable family of divergent shell sums. -/
theorem exists_eventual_syndetic_reserve_preserving_countable_divergence
    (A : Set ℕ) (w : ℕ → ℕ → ℝ)
    (hw : ∀ i j n, n ∈ powerShell A j → 0 ≤ w i n)
    (hcard : Tendsto (fun j => (powerShell A j).card) atTop atTop)
    (hdiv : ∀ i : ℕ, Tendsto
      (fun N => ∑ j ∈ Finset.range N,
        ∑ n ∈ powerShell A j, w i n) atTop atTop) :
    ∃ R : ℕ → Finset ℕ,
      (∀ j, R j ⊆ powerShell A j) ∧
      Tendsto (fun j => (R j).card) atTop atTop ∧
      (∀ i : ℕ, ∃ J : ℕ, Tendsto
        (fun N => ∑ j ∈ Finset.range N,
          ((∑ n ∈ powerShell A (J + j), w i n) -
            ∑ n ∈ R (J + j), w i n)) atTop atTop) ∧
      (∃ K : ℕ, ∀ n : ℕ, ∃ t : Finset ℕ,
        (∀ b ∈ t, b ∈ reserveSet R) ∧
        (∑ b ∈ t, b) ≤ n ∧ n ≤ (∑ b ∈ t, b) + K) := by
  classical
  have hfour : ∀ᶠ j : ℕ in atTop, 4 ≤ (powerShell A j).card :=
    tendsto_atTop.1 hcard 4
  obtain ⟨J, hJ⟩ := eventually_atTop.1 hfour
  let S : ℕ → Finset ℕ := fun j => powerShell A (J + j)
  have hSfour : ∀ j, 4 ≤ (S j).card := by
    intro j
    exact hJ (J + j) (by omega)
  have hScard : Tendsto (fun j => (S j).card) atTop atTop := by
    exact hcard.comp (tendsto_shift_index J)
  have hSdiv : ∀ i : ℕ, Tendsto
      (fun N => ∑ j ∈ Finset.range N, ∑ n ∈ S j, w i n) atTop atTop := by
    intro i
    exact divergent_shell_sums_shift
      (fun j => ∑ n ∈ powerShell A j, w i n) (hdiv i) J
  obtain ⟨R', hR'sub, hR'card, hR'keep⟩ :=
    exists_growing_reserves_preserving_countable_divergence S w
      (fun i j n hn => hw i (J + j) n hn) hSfour hScard hSdiv
  let R : ℕ → Finset ℕ := fun j => if hj : J ≤ j then R' (j - J) else ∅
  have hRsub : ∀ j, R j ⊆ powerShell A j := by
    intro j
    by_cases hj : J ≤ j
    · simp only [R, dif_pos hj]
      have hs := hR'sub (j - J)
      simpa [S, Nat.add_sub_of_le hj] using hs
    · simp [R, hj]
  have hRcard : Tendsto (fun j => (R j).card) atTop atTop := by
    rw [tendsto_atTop]
    intro b
    obtain ⟨K, hK⟩ := eventually_atTop.1 (tendsto_atTop.1 hR'card b)
    filter_upwards [eventually_ge_atTop (J + K)] with j hj
    have hJj : J ≤ j := by omega
    have hKj : K ≤ j - J := by omega
    simpa [R, hJj] using hK (j - J) hKj
  refine ⟨R, hRsub, hRcard, ?_, ?_⟩
  · intro i
    refine ⟨J, ?_⟩
    simpa [S, R] using hR'keep i
  · exact growing_shell_reserves_are_syndetic A R hRsub hRcard

end

end Erdos254.CanonicalCountableReserve
