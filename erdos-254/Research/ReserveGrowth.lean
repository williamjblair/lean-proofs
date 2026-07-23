import Mathlib
import Research.GrowthPartition
import Research.InfiniteCoinCover

namespace Erdos254.ReserveGrowth

open Filter
open scoped BigOperators
open Erdos254.GrowthPartition Erdos254.InfiniteCoinCover

noncomputable section

/-- The set obtained by taking prescribed reserves from every power shell. -/
def reserveSet (R : ℕ → Finset ℕ) : Set ℕ :=
  {n | ∃ j, n ∈ R j}

lemma reserveSet_elements_gt_one {A : Set ℕ} {R : ℕ → Finset ℕ}
    (hsub : ∀ j, R j ⊆ powerShell A j) {n : ℕ}
    (hn : n ∈ reserveSet R) : 1 < n := by
  classical
  obtain ⟨j, hnj⟩ := hn
  have hns := hsub j hnj
  have hlo := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hns).1).1
  have hp : 1 ≤ 2 ^ j := Nat.one_le_two_pow
  omega

lemma reserveSet_subset {A : Set ℕ} {R : ℕ → Finset ℕ}
    (hsub : ∀ j, R j ⊆ powerShell A j) : reserveSet R ⊆ A := by
  classical
  intro n hn
  obtain ⟨j, hnj⟩ := hn
  exact (Finset.mem_filter.mp (hsub j hnj)).2

lemma previous_reserve_covers_next {A : Set ℕ} {R : ℕ → Finset ℕ}
    (hsub : ∀ j, R j ⊆ powerShell A j) (j n : ℕ)
    (hcard : 4 ≤ (R j).card) (hn : n ∈ powerShell A (j + 1)) :
    n ≤ ∑ m ∈ R j, m := by
  classical
  have hlower : ∀ m ∈ R j, 2 ^ j + 1 ≤ m := by
    intro m hm
    have hms := hsub j hm
    simp only [powerShell, Finset.mem_filter, Finset.mem_Ioc] at hms
    omega
  have hsum : (2 ^ j + 1) * (R j).card ≤ ∑ m ∈ R j, m := by
    simpa [nsmul_eq_mul, mul_comm] using
      (Finset.card_nsmul_le_sum (R j) (fun m => m) (2 ^ j + 1) hlower)
  have hnupper : n ≤ 2 ^ (j + 2) := by
    simp only [powerShell, Finset.mem_filter, Finset.mem_Ioc] at hn
    simpa [Nat.add_assoc] using hn.1.2
  calc
    n ≤ 2 ^ (j + 2) := hnupper
    _ ≤ (2 ^ j + 1) * (R j).card := by
      rw [show 2 ^ (j + 2) = 4 * 2 ^ j by ring]
      calc
        4 * 2 ^ j ≤ (2 ^ j + 1) * 4 := by omega
        _ ≤ (2 ^ j + 1) * (R j).card := Nat.mul_le_mul_left _ hcard
    _ ≤ _ := hsum

lemma reserve_subset_prefix {A : Set ℕ} {R : ℕ → Finset ℕ}
    (hsub : ∀ j, R j ⊆ powerShell A j) (j n : ℕ)
    (hn : n ∈ powerShell A (j + 1)) :
    R j ⊆ smallerCoins (reserveSet R) n := by
  classical
  intro m hm
  have hms := hsub j hm
  simp only [powerShell, Finset.mem_filter, Finset.mem_Ioc] at hms hn
  simp only [smallerCoins, Finset.mem_filter, Finset.mem_Ico]
  exact ⟨⟨by omega, by omega⟩, ⟨j, hm⟩⟩

lemma reserveSet_infinite {A : Set ℕ} {R : ℕ → Finset ℕ}
    (hsub : ∀ j, R j ⊆ powerShell A j)
    (hcard : Tendsto (fun j => (R j).card) atTop atTop) :
    (reserveSet R).Infinite := by
  classical
  apply Set.infinite_of_forall_exists_gt
  intro x
  have hp : ∀ᶠ j : ℕ in atTop, x < 2 ^ j :=
    (tendsto_pow_atTop_atTop_of_one_lt (r := (2 : ℕ)) (by decide)).eventually
      (eventually_gt_atTop x)
  have hc : ∀ᶠ j : ℕ in atTop, 1 ≤ (R j).card :=
    (tendsto_atTop.1 hcard 1)
  obtain ⟨j, hxj, hcj⟩ := (hp.and hc).exists
  have hne : (R j).Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨n, hn⟩ := hne
  refine ⟨n, ⟨j, hn⟩, ?_⟩
  have hns := hsub j hn
  have hjn := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hns).1).1
  omega

/-- Growing reserves in consecutive dyadic shells themselves satisfy the
Burr--Erdős prefix condition and have syndetic distinct subset sums. -/
theorem growing_shell_reserves_are_syndetic
    (A : Set ℕ) (R : ℕ → Finset ℕ)
    (hsub : ∀ j, R j ⊆ powerShell A j)
    (hcard : Tendsto (fun j => (R j).card) atTop atTop) :
    ∃ K : ℕ, ∀ n : ℕ, ∃ t : Finset ℕ,
      (∀ b ∈ t, b ∈ reserveSet R) ∧
      (∑ b ∈ t, b) ≤ n ∧ n ≤ (∑ b ∈ t, b) + K := by
  classical
  have hfour : ∀ᶠ j : ℕ in atTop, 4 ≤ (R j).card := tendsto_atTop.1 hcard 4
  obtain ⟨J, hJ⟩ := eventually_atTop.1 hfour
  let N₀ := 2 ^ (J + 1) + 1
  have hgrowth : ∀ b ∈ reserveSet R, 1 ≤ b →
      b ≤ (∑ x ∈ smallerCoins (reserveSet R) b, x) + N₀ := by
    intro b hbB hb1
    by_cases hbN : N₀ ≤ b
    · obtain ⟨k, hbk⟩ := hbB
      have hbkshell := hsub k hbk
      have hkgt : J < k := by
        by_contra hnot
        have hkle : k ≤ J := Nat.le_of_not_gt hnot
        have hbupper : b ≤ 2 ^ (k + 1) :=
          (Finset.mem_Ioc.mp (Finset.mem_filter.mp hbkshell).1).2
        have hp : 2 ^ (k + 1) ≤ 2 ^ (J + 1) :=
          Nat.pow_le_pow_right (by decide) (by omega)
        have hbJ : b ≤ 2 ^ (J + 1) := hbupper.trans hp
        dsimp [N₀] at hbN
        omega
      let j := k - 1
      have hjk : j + 1 = k := Nat.sub_add_cancel (by omega)
      have hcj : 4 ≤ (R j).card := hJ j (by omega)
      have hcover := previous_reserve_covers_next hsub j b hcj (by rwa [hjk])
      have hsumle : (∑ x ∈ R j, x) ≤
          ∑ x ∈ smallerCoins (reserveSet R) b, x :=
        Finset.sum_le_sum_of_subset (reserve_subset_prefix hsub j b (by rwa [hjk]))
      exact hcover.trans (hsumle.trans (Nat.le_add_right _ _))
    · have hbsmall : b ≤ N₀ := Nat.le_of_lt (Nat.lt_of_not_ge hbN)
      exact hbsmall.trans (Nat.le_add_left N₀ _)
  exact ⟨N₀, infinite_prefix_growth_gives_syndetic_subsetSums
    (reserveSet R) N₀ (reserveSet_infinite hsub hcard) hgrowth⟩

end

end Erdos254.ReserveGrowth
