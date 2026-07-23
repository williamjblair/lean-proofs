import Mathlib
import Research.GrowthPartition
import Research.InfiniteCoinCover

namespace Erdos254.FourSyndeticClasses

open scoped BigOperators
open Erdos254.GrowthPartition Erdos254.InfiniteCoinCover

noncomputable section

lemma colorClass_elements_gt_one (A : Set ℕ) (c : ℕ) {n : ℕ}
    (hn : n ∈ colorClass A c) : 1 < n := by
  classical
  obtain ⟨j, hj⟩ := hn
  have hjs := balancedPart_subset (powerShell A j) c hj
  have hlo := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hjs).1).1
  have hp : 1 ≤ 2 ^ j := Nat.one_le_two_pow
  omega

lemma colorClass_infinite (A : Set ℕ) (c : ℕ) (hc : c < 4)
    (hshell : ∀ᶠ j : ℕ in Filter.atTop, 16 ≤ (powerShell A j).card) :
    (colorClass A c).Infinite := by
  classical
  apply Set.infinite_of_forall_exists_gt
  intro x
  have hp : ∀ᶠ j : ℕ in Filter.atTop, x < 2 ^ j :=
    (tendsto_pow_atTop_atTop_of_one_lt (r := (2 : ℕ)) (by decide)).eventually
      (Filter.eventually_gt_atTop x)
  obtain ⟨j, hcard, hxj⟩ := (hshell.and hp).exists
  have hpartcard : 4 ≤ (balancedPart (powerShell A j) c).card := by
    exact balancedPart_card_ge (powerShell A j) c 4 hc (by omega)
  have hne : (balancedPart (powerShell A j) c).Nonempty :=
    Finset.card_pos.mp (by omega)
  obtain ⟨n, hn⟩ := hne
  refine ⟨n, ⟨j, hn⟩, ?_⟩
  have hns := balancedPart_subset (powerShell A j) c hn
  have hjn := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hns).1).1
  omega

lemma smallerCoins_colorClass_eq_prefixFinset (A : Set ℕ) (c b : ℕ) :
    smallerCoins (colorClass A c) b = prefixFinset (colorClass A c) b := by
  classical
  ext x
  simp only [smallerCoins, prefixFinset, Finset.mem_filter, Finset.mem_Ico,
    Finset.mem_Iio]
  constructor
  · rintro ⟨⟨hx1, hxb⟩, hxC⟩
    exact ⟨hxb, hxC⟩
  · rintro ⟨hxb, hxC⟩
    exact ⟨⟨(colorClass_elements_gt_one A c hxC).le, hxb⟩, hxC⟩

/-- The dyadic hypothesis yields four pairwise-disjoint classes covering
`A \ {0,1}`, and each class has syndetic distinct subset sums. -/
theorem dyadic_produces_four_syndetic_classes (A : Set ℕ)
    (hdyadic : Filter.Tendsto (dyadicIncrement A) Filter.atTop Filter.atTop) :
    ∃ B : Fin 4 → Set ℕ,
      (∀ i, B i ⊆ A) ∧
      Pairwise (fun i j => Disjoint (B i) (B j)) ∧
      (∀ n ∈ A, 1 < n → ∃ i, n ∈ B i) ∧
      (∀ i, ∃ K : ℕ, ∀ n : ℕ, ∃ t : Finset ℕ,
        (∀ b ∈ t, b ∈ B i) ∧
        (∑ b ∈ t, b) ≤ n ∧ n ≤ (∑ b ∈ t, b) + K) := by
  classical
  let B : Fin 4 → Set ℕ := fun i => colorClass A i.val
  have hshell := dyadic_tendsto_powerShells A hdyadic
  refine ⟨B, ?_, ?_, ?_, ?_⟩
  · intro i n hn
    obtain ⟨j, hnj⟩ := hn
    have hns := balancedPart_subset (powerShell A j) i.val hnj
    exact (Finset.mem_filter.mp hns).2
  · intro i j hij
    apply colorClass_pairwise_disjoint A
    intro hv
    apply hij
    exact Fin.ext hv
  · intro n hnA hn
    obtain ⟨c, hc, hnc⟩ := mem_some_colorClass A hnA hn
    exact ⟨⟨c, hc⟩, hnc⟩
  · intro i
    obtain ⟨N₀, hgrowth⟩ := colorClass_eventual_growth A i.val i.isLt hshell
    refine ⟨N₀, ?_⟩
    apply infinite_prefix_growth_gives_syndetic_subsetSums
    · exact colorClass_infinite A i.val i.isLt hshell
    · intro b hbB hb1
      by_cases hbN : N₀ ≤ b
      · rw [smallerCoins_colorClass_eq_prefixFinset]
        exact (hgrowth b hbN hbB).trans (Nat.le_add_right _ _)
      · have : b ≤ N₀ := Nat.le_of_lt (Nat.lt_of_not_ge hbN)
        exact this.trans (Nat.le_add_left N₀ _)

end

end Erdos254.FourSyndeticClasses
