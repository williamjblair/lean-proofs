import Mathlib
import Research.GrowthPartition
import Research.Negative

namespace Erdos254.PhaseShellDecomposition

open Filter
open scoped BigOperators
open Erdos254.GrowthPartition

noncomputable section

/-- Members of `A` strictly above one and at most `2^K`. -/
def powerShellPrefix (A : Set ℕ) (K : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Ioc 1 (2 ^ K)).filter (fun n => n ∈ A)

lemma powerShellPrefix_succ (A : Set ℕ) (K : ℕ) :
    powerShellPrefix A (K + 1) =
      powerShellPrefix A K ∪ powerShell A K := by
  classical
  ext n
  simp only [powerShellPrefix, powerShell, Finset.mem_filter, Finset.mem_Ioc,
    Finset.mem_union]
  constructor
  · rintro ⟨⟨h1, hu⟩, hnA⟩
    by_cases hn : n ≤ 2 ^ K
    · exact Or.inl ⟨⟨h1, hn⟩, hnA⟩
    · exact Or.inr ⟨⟨Nat.lt_of_not_ge hn, by simpa [pow_succ] using hu⟩, hnA⟩
  · rintro (⟨⟨h1, hu⟩, hnA⟩ | ⟨⟨hl, hu⟩, hnA⟩)
    · exact ⟨⟨h1, hu.trans (Nat.pow_le_pow_right (by decide) (by omega))⟩, hnA⟩
    · exact ⟨⟨(Nat.one_le_two_pow.trans_lt hl), by simpa [pow_succ] using hu⟩, hnA⟩

lemma powerShellPrefix_disjoint (A : Set ℕ) (K : ℕ) :
    Disjoint (powerShellPrefix A K) (powerShell A K) := by
  classical
  rw [Finset.disjoint_left]
  intro n hnP hnS
  simp only [powerShellPrefix, powerShell, Finset.mem_filter, Finset.mem_Ioc] at hnP hnS
  omega

lemma sum_powerShells_eq_prefix (A : Set ℕ) (f : ℕ → ℝ) (K : ℕ) :
    (∑ j ∈ Finset.range K, ∑ n ∈ powerShell A j, f n) =
      ∑ n ∈ powerShellPrefix A K, f n := by
  classical
  induction K with
  | zero => simp [powerShellPrefix]
  | succ K ih =>
      rw [Finset.sum_range_succ, ih]
      rw [show K + 1 = Nat.succ K by omega, powerShellPrefix_succ]
      exact (Finset.sum_union (powerShellPrefix_disjoint A K)).symm

lemma phasePartialSum_power_le_shells_add_one (A : Set ℕ) (θ : ℝ) (K : ℕ) :
    phasePartialSum A θ (2 ^ K) ≤
      nearestIntegerDistance θ +
        ∑ j ∈ Finset.range K, ∑ n ∈ powerShell A j,
          nearestIntegerDistance (θ * (n : ℝ)) := by
  classical
  let w : ℕ → ℝ := fun n => nearestIntegerDistance (θ * (n : ℝ))
  let P := (Finset.Icc 1 (2 ^ K)).filter (fun n => n ∈ A)
  have hsub : P ⊆ insert 1 (powerShellPrefix A K) := by
    intro n hn
    have hn' := Finset.mem_filter.mp hn
    have hI := Finset.mem_Icc.mp hn'.1
    by_cases hn1 : n = 1
    · subst n
      simp
    · have hgt : 1 < n := by omega
      simp only [Finset.mem_insert]
      exact Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨hgt, hI.2⟩, hn'.2⟩)
  have hnonneg : ∀ n ∈ insert 1 (powerShellPrefix A K), 0 ≤ w n := by
    intro n hn
    exact nearestIntegerDistance_nonneg _
  have hle : (∑ n ∈ P, w n) ≤ ∑ n ∈ insert 1 (powerShellPrefix A K), w n :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun n hnBig hnSmall => hnonneg n hnBig)
  have h1not : 1 ∉ powerShellPrefix A K := by
    simp [powerShellPrefix]
  rw [Finset.sum_insert h1not, ← sum_powerShells_eq_prefix] at hle
  simpa [phasePartialSum, P, w] using hle

/-- Canonical phase divergence implies divergence of the corresponding sums
when regrouped by dyadic power shells. -/
theorem phase_divergence_implies_powerShell_divergence
    (A : Set ℕ) (θ : ℝ)
    (hphase : Tendsto (phasePartialSum A θ) atTop atTop) :
    Tendsto
      (fun K => ∑ j ∈ Finset.range K, ∑ n ∈ powerShell A j,
        nearestIntegerDistance (θ * (n : ℝ))) atTop atTop := by
  have hpow : Tendsto (fun K => phasePartialSum A θ (2 ^ K)) atTop atTop :=
    hphase.comp (tendsto_pow_atTop_atTop_of_one_lt (r := (2 : ℕ)) (by decide))
  rw [tendsto_atTop]
  intro b
  have hp := tendsto_atTop.1 hpow (b + nearestIntegerDistance θ)
  filter_upwards [hp] with K hK
  have hle := phasePartialSum_power_le_shells_add_one A θ K
  linarith

end

end Erdos254.PhaseShellDecomposition
