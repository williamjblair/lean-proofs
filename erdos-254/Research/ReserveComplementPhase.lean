import Mathlib
import Research.GrowthPartition
import Research.PhaseShellDecomposition
import Research.CanonicalCountableReserve
import Research.CountablePhaseSyndeticReserve
import Research.Negative

namespace Erdos254.ReserveComplementPhase

open Filter
open scoped BigOperators
open Erdos254.GrowthPartition Erdos254.PhaseShellDecomposition
open Erdos254.ReserveGrowth Erdos254.CountablePhaseSyndeticReserve

noncomputable section

lemma powerShell_reserve_complement {A : Set ℕ} {R : ℕ → Finset ℕ}
    (hsub : ∀ j, R j ⊆ powerShell A j) (k : ℕ) :
    powerShell A k \ R k = powerShell (A \ reserveSet R) k := by
  classical
  ext n
  constructor
  · intro hn
    have hdata := Finset.mem_sdiff.mp hn
    have hnA := hdata.1
    simp only [powerShell, Finset.mem_filter] at hnA ⊢
    refine ⟨hnA.1, hnA.2, ?_⟩
    intro hnB
    obtain ⟨l, hnl⟩ := hnB
    have hnAl := hsub l hnl
    have hkl : k = l := powerShell_index_unique A hdata.1 hnAl
    subst l
    exact hdata.2 hnl
  · intro hn
    simp only [powerShell, Finset.mem_filter] at hn
    have hnA : n ∈ powerShell A k := by
      simp only [powerShell, Finset.mem_filter]
      exact ⟨hn.1, hn.2.1⟩
    apply Finset.mem_sdiff.mpr
    refine ⟨hnA, ?_⟩
    intro hnR
    exact hn.2.2 ⟨k, hnR⟩

lemma shell_sum_sub_reserve {A : Set ℕ} {R : ℕ → Finset ℕ}
    (hsub : ∀ j, R j ⊆ powerShell A j) (f : ℕ → ℝ) (k : ℕ) :
    (∑ n ∈ powerShell A k, f n) - ∑ n ∈ R k, f n =
      ∑ n ∈ powerShell (A \ reserveSet R) k, f n := by
  classical
  have hs := Finset.sum_sdiff (hsub k) (f := f)
  rw [powerShell_reserve_complement hsub k] at hs
  linarith

lemma shifted_shell_sum_le_phasePartialSum
    (C : Set ℕ) (θ : ℝ) (J N : ℕ) :
    (∑ j ∈ Finset.range N, ∑ n ∈ powerShell C (J + j),
      nearestIntegerDistance (θ * (n : ℝ))) ≤
      phasePartialSum C θ (2 ^ (J + N)) := by
  classical
  let f : ℕ → ℝ := fun n => nearestIntegerDistance (θ * (n : ℝ))
  let g : ℕ → ℝ := fun j => ∑ n ∈ powerShell C j, f n
  have hprefixNonneg : 0 ≤ ∑ j ∈ Finset.range J, g j := by
    apply Finset.sum_nonneg
    intro j hj
    exact Finset.sum_nonneg fun n hn => nearestIntegerDistance_nonneg _
  have hshiftTotal : (∑ j ∈ Finset.range N, g (J + j)) ≤
      ∑ j ∈ Finset.range (J + N), g j := by
    rw [Finset.sum_range_add]
    linarith
  have hprefixSubset : powerShellPrefix C (J + N) ⊆
      (Finset.Icc 1 (2 ^ (J + N))).filter (fun n => n ∈ C) := by
    intro n hn
    simp only [powerShellPrefix, Finset.mem_filter, Finset.mem_Ioc,
      Finset.mem_Icc] at hn ⊢
    exact ⟨⟨hn.1.1.le, hn.1.2⟩, hn.2⟩
  have hsumle : (∑ n ∈ powerShellPrefix C (J + N), f n) ≤
      ∑ n ∈ (Finset.Icc 1 (2 ^ (J + N))).filter (fun n => n ∈ C), f n :=
    Finset.sum_le_sum_of_subset_of_nonneg hprefixSubset
      (fun n hnBig hnSmall => nearestIntegerDistance_nonneg _)
  change (∑ j ∈ Finset.range N, g (J + j)) ≤ _
  calc
    (∑ j ∈ Finset.range N, g (J + j)) ≤
        ∑ j ∈ Finset.range (J + N), g j := hshiftTotal
    _ = ∑ n ∈ powerShellPrefix C (J + N), f n :=
      sum_powerShells_eq_prefix C f (J + N)
    _ ≤ _ := by simpa [phasePartialSum, f] using hsumle

/-- Divergence of the shell-by-shell remainder after deleting reserves is
exactly canonical phase divergence on the set-theoretic complement. -/
theorem complement_phase_diverges_of_shell_remainder
    (A : Set ℕ) (R : ℕ → Finset ℕ)
    (hsub : ∀ j, R j ⊆ powerShell A j)
    (θ : ℝ) (J : ℕ)
    (hrem : Tendsto
      (fun N => ∑ j ∈ Finset.range N,
        ((∑ n ∈ powerShell A (J + j),
            nearestIntegerDistance (θ * (n : ℝ))) -
          ∑ n ∈ R (J + j),
            nearestIntegerDistance (θ * (n : ℝ)))) atTop atTop) :
    Tendsto (phasePartialSum (A \ reserveSet R) θ) atTop atTop := by
  rw [phasePartialSum_tendsto_iff_unbounded]
  intro b
  have hb := tendsto_atTop.1 hrem b
  obtain ⟨N, hN⟩ := hb.exists
  have heq : (∑ j ∈ Finset.range N,
        ((∑ n ∈ powerShell A (J + j),
            nearestIntegerDistance (θ * (n : ℝ))) -
          ∑ n ∈ R (J + j),
            nearestIntegerDistance (θ * (n : ℝ)))) =
      ∑ j ∈ Finset.range N,
        ∑ n ∈ powerShell (A \ reserveSet R) (J + j),
          nearestIntegerDistance (θ * (n : ℝ)) := by
    apply Finset.sum_congr rfl
    intro j hj
    exact shell_sum_sub_reserve hsub
      (fun n => nearestIntegerDistance (θ * (n : ℝ))) (J + j)
  rw [heq] at hN
  refine ⟨2 ^ (J + N), hN.trans ?_⟩
  exact shifted_shell_sum_le_phasePartialSum (A \ reserveSet R) θ J N

/-- Fully canonical specialization: for any prescribed countable phase list,
one can reserve a syndetic growth class and the actual set-theoretic complement
still satisfies canonical phase divergence at every listed phase. -/
theorem exists_syndetic_reserve_with_phase_divergent_complement
    (A : Set ℕ)
    (hdyadic : Tendsto (Erdos254.dyadicIncrement A) atTop atTop)
    (hphase : ∀ θ : ℝ, θ ∈ Set.Ioo 0 1 →
      Tendsto (phasePartialSum A θ) atTop atTop)
    (θ : ℕ → ℝ) (hθ : ∀ i, θ i ∈ Set.Ioo 0 1) :
    ∃ R : ℕ → Finset ℕ,
      (∀ j, R j ⊆ powerShell A j) ∧
      Tendsto (fun j => (R j).card) atTop atTop ∧
      (∀ i : ℕ, Tendsto
        (phasePartialSum (A \ reserveSet R) (θ i)) atTop atTop) ∧
      (∃ K : ℕ, ∀ n : ℕ, ∃ t : Finset ℕ,
        (∀ b ∈ t, b ∈ reserveSet R) ∧
        (∑ b ∈ t, b) ≤ n ∧ n ≤ (∑ b ∈ t, b) + K) := by
  obtain ⟨R, hRsub, hRcard, hRphase, hRsynd⟩ :=
    exists_syndetic_reserve_protecting_countable_phases
      A hdyadic hphase θ hθ
  refine ⟨R, hRsub, hRcard, ?_, hRsynd⟩
  intro i
  obtain ⟨J, hJ⟩ := hRphase i
  exact complement_phase_diverges_of_shell_remainder A R hRsub (θ i) J hJ

end

end Erdos254.ReserveComplementPhase
