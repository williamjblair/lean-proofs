import Mathlib
import Research.GrowthPartition
import Research.CanonicalCountableReserve
import Research.PhaseShellDecomposition
import Research.Negative

namespace Erdos254.CountablePhaseSyndeticReserve

open Filter
open scoped BigOperators
open Erdos254.GrowthPartition
open Erdos254.CanonicalCountableReserve Erdos254.PhaseShellDecomposition
open Erdos254.ReserveGrowth

noncomputable section

/-- For any prescribed countable list of phases, the canonical hypotheses
produce a growing syndetic dyadic reserve while all listed phase series remain
divergent on the shell complements. -/
theorem exists_syndetic_reserve_protecting_countable_phases
    (A : Set ℕ)
    (hdyadic : Tendsto (Erdos254.dyadicIncrement A) atTop atTop)
    (hphase : ∀ θ : ℝ, θ ∈ Set.Ioo 0 1 →
      Tendsto (phasePartialSum A θ) atTop atTop)
    (θ : ℕ → ℝ) (hθ : ∀ i, θ i ∈ Set.Ioo 0 1) :
    ∃ R : ℕ → Finset ℕ,
      (∀ j, R j ⊆ powerShell A j) ∧
      Tendsto (fun j => (R j).card) atTop atTop ∧
      (∀ i : ℕ, ∃ J : ℕ, Tendsto
        (fun N => ∑ j ∈ Finset.range N,
          ((∑ n ∈ powerShell A (J + j),
              nearestIntegerDistance (θ i * (n : ℝ))) -
            ∑ n ∈ R (J + j),
              nearestIntegerDistance (θ i * (n : ℝ)))) atTop atTop) ∧
      (∃ K : ℕ, ∀ n : ℕ, ∃ t : Finset ℕ,
        (∀ b ∈ t, b ∈ reserveSet R) ∧
        (∑ b ∈ t, b) ≤ n ∧ n ≤ (∑ b ∈ t, b) + K) := by
  have hpow : Tendsto (fun j : ℕ => 2 ^ j) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (r := (2 : ℕ)) (by decide)
  have hcard : Tendsto (fun j => (powerShell A j).card) atTop atTop := by
    have hd := hdyadic.comp hpow
    change Tendsto (fun j => Erdos254.dyadicIncrement A (2 ^ j)) atTop atTop at hd
    have heq : (fun j => (powerShell A j).card) =
        (fun j => Erdos254.dyadicIncrement A (2 ^ j)) := by
      funext j
      rw [show Erdos254.dyadicIncrement A (2 ^ j) =
        Erdos254.GrowthPartition.dyadicIncrement A (2 ^ j) by rfl]
      rw [Erdos254.GrowthPartition.dyadicIncrement_eq_shellCard]
      simp [powerShell, Erdos254.GrowthPartition.shellCount, pow_succ, mul_comm]
    rw [heq]
    exact hd
  apply exists_eventual_syndetic_reserve_preserving_countable_divergence
    A (fun i n => nearestIntegerDistance (θ i * (n : ℝ)))
  · intro i j n hn
    exact nearestIntegerDistance_nonneg _
  · exact hcard
  · intro i
    exact phase_divergence_implies_powerShell_divergence A (θ i)
      (hphase (θ i) (hθ i))

end

end Erdos254.CountablePhaseSyndeticReserve
