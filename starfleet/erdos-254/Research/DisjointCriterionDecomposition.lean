import Mathlib
import Research.Statement
import Research.GrowthPartition
import Research.InfiniteCoinCover
import Research.FourSyndeticClasses
import Research.ReserveGrowth
import Research.UniversalCorrectionPartition

namespace Erdos254.DisjointCriterionDecomposition

open Filter
open scoped BigOperators
open Erdos254
open Erdos254.GrowthPartition Erdos254.InfiniteCoinCover
open Erdos254.FourSyndeticClasses Erdos254.ReserveGrowth
open Erdos254.UniversalCorrectionPartition

noncomputable section

lemma powerShell_reserveSet_eq
    {A : Set ℕ} {R : ℕ → Finset ℕ}
    (hsub : ∀ j, R j ⊆ powerShell A j) (j : ℕ) :
    powerShell (reserveSet R) j = R j := by
  classical
  ext n
  constructor
  · intro hn
    have hnD := (Finset.mem_filter.mp hn).2
    obtain ⟨k, hnk⟩ := hnD
    have hnkA := hsub k hnk
    have hnjA : n ∈ powerShell A j := by
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hn).1,
        (Finset.mem_filter.mp hnkA).2⟩
    have hjk := powerShell_index_unique A hnjA hnkA
    simpa [hjk] using hnk
  · intro hn
    have hnA := hsub j hn
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hnA).1, ⟨j, hn⟩⟩

lemma reserveSet_subset
    {A : Set ℕ} {R : ℕ → Finset ℕ}
    (hsub : ∀ j, R j ⊆ powerShell A j) :
    reserveSet R ⊆ A := by
  classical
  intro n hn
  obtain ⟨j, hnj⟩ := hn
  exact (Finset.mem_filter.mp (hsub j hnj)).2

/-- Exact Bergelson--Simmons-style disjoint decomposition: three disjoint
classes have syndetic distinct subset sums, while the disjoint remainder
retains every phase divergence. -/
theorem exists_three_syndetic_classes_and_universal_correction
    (A : Set ℕ)
    (hdyadic : Tendsto (Erdos254.dyadicIncrement A) atTop atTop)
    (hphase : ∀ θ : ℝ, θ ∈ Set.Ioo 0 1 →
      Tendsto (phasePartialSum A θ) atTop atTop) :
    ∃ B : Fin 3 → Set ℕ, ∃ C : Set ℕ,
      (∀ i, B i ⊆ A) ∧ C ⊆ A ∧
      Pairwise (fun i j => Disjoint (B i) (B j)) ∧
      (∀ i, Disjoint (B i) C) ∧
      (A = C ∪ ⋃ i, B i) ∧
      (∀ i, ∃ K : ℕ, ∀ n : ℕ, ∃ t : Finset ℕ,
        (∀ b ∈ t, b ∈ B i) ∧
        (∑ b ∈ t, b) ≤ n ∧ n ≤ (∑ b ∈ t, b) + K) ∧
      (∀ θ : ℝ, θ ∈ Set.Ioo 0 1 →
        Tendsto (phasePartialSum C θ) atTop atTop) := by
  classical
  obtain ⟨R, hRsubSeed, hRcard, hCbasePhase, hRsynd⟩ :=
    exists_universally_phase_protected_growing_reserve A hdyadic hphase
  have hSeedA : seedReserve A ⊆ A := fun n hn => hn.1
  have hRsubA : ∀ j, R j ⊆ powerShell A j := by
    intro j n hn
    have hnSeed := hRsubSeed j hn
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hnSeed).1,
      hSeedA (Finset.mem_filter.mp hnSeed).2⟩
  let D : Set ℕ := reserveSet R
  have hDA : D ⊆ A := reserveSet_subset hRsubA
  have hDcard : Tendsto (fun j => (powerShell D j).card) atTop atTop := by
    simpa only [D, powerShell_reserveSet_eq hRsubA] using hRcard
  have hshell : ∀ᶠ j : ℕ in atTop, 16 ≤ (powerShell D j).card :=
    tendsto_atTop.1 hDcard 16
  let B : Fin 3 → Set ℕ := fun i => colorClass D i.val
  let U : Set ℕ := ⋃ i, B i
  let C : Set ℕ := A \ U
  have hBiD : ∀ i, B i ⊆ D := by
    intro i n hn
    obtain ⟨j, hnj⟩ := hn
    exact (Finset.mem_filter.mp
      (balancedPart_subset (powerShell D j) i.val hnj)).2
  have hBiA : ∀ i, B i ⊆ A := fun i => (hBiD i).trans hDA
  have hpair : Pairwise (fun i j => Disjoint (B i) (B j)) := by
    intro i j hij
    apply colorClass_pairwise_disjoint D
    intro hv
    apply hij
    exact Fin.ext hv
  have hdisC : ∀ i, Disjoint (B i) C := by
    intro i
    rw [Set.disjoint_left]
    intro n hnB hnC
    exact hnC.2 (Set.mem_iUnion.mpr ⟨i, hnB⟩)
  have hcover : A = C ∪ U := by
    apply Set.Subset.antisymm
    · intro n hnA
      by_cases hnU : n ∈ U
      · exact Or.inr hnU
      · exact Or.inl ⟨hnA, hnU⟩
    · intro n hn
      rcases hn with hnC | hnU
      · exact hnC.1
      · obtain ⟨i, hnBi⟩ := Set.mem_iUnion.mp hnU
        exact hBiA i hnBi
  have hsynd : ∀ i, ∃ K : ℕ, ∀ n : ℕ, ∃ t : Finset ℕ,
      (∀ b ∈ t, b ∈ B i) ∧
      (∑ b ∈ t, b) ≤ n ∧ n ≤ (∑ b ∈ t, b) + K := by
    intro i
    obtain ⟨N₀, hgrowth⟩ :=
      colorClass_eventual_growth D i.val (by omega) hshell
    refine ⟨N₀, ?_⟩
    apply infinite_prefix_growth_gives_syndetic_subsetSums
    · exact colorClass_infinite D i.val (by omega) hshell
    · intro b hbB hb1
      by_cases hbN : N₀ ≤ b
      · rw [smallerCoins_colorClass_eq_prefixFinset]
        exact (hgrowth b hbN hbB).trans (Nat.le_add_right _ _)
      · exact (Nat.le_of_lt (Nat.lt_of_not_ge hbN)).trans
          (Nat.le_add_left N₀ _)
  have hbaseSub : A \ D ⊆ C := by
    intro n hn
    refine ⟨hn.1, ?_⟩
    intro hnU
    obtain ⟨i, hnBi⟩ := Set.mem_iUnion.mp hnU
    exact hn.2 (hBiD i hnBi)
  have hCphase : ∀ θ : ℝ, θ ∈ Set.Ioo 0 1 →
      Tendsto (phasePartialSum C θ) atTop atTop := by
    intro θ hθ
    exact phase_divergence_mono_set hbaseSub θ (hCbasePhase θ hθ)
  refine ⟨B, C, hBiA, ?_, hpair, hdisC, ?_, hsynd, hCphase⟩
  · intro n hn
    exact hn.1
  · simpa only [U] using hcover

end

end Erdos254.DisjointCriterionDecomposition
