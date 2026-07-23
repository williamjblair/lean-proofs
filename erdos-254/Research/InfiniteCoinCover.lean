import Mathlib
import Research.FiniteCoinCover

namespace Erdos254.InfiniteCoinCover

open scoped BigOperators
open Erdos254.FiniteCoinCover

noncomputable section

/-- Positive members of `B` not exceeding `M`. -/
def coinsUpTo (B : Set ℕ) (M : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Icc 1 M).filter (fun b => b ∈ B)

/-- Positive members of `B` strictly smaller than `b`. -/
def smallerCoins (B : Set ℕ) (b : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Ico 1 b).filter (fun x => x ∈ B)

lemma coinsUpTo_filter_lt {B : Set ℕ} {M b : ℕ} (hbM : b ≤ M) :
    (coinsUpTo B M).filter (fun x => x < b) = smallerCoins B b := by
  classical
  ext x
  constructor
  · intro hx
    have hxOuter := Finset.mem_filter.mp hx
    have hxCoin := Finset.mem_filter.mp hxOuter.1
    exact Finset.mem_filter.mpr ⟨
      Finset.mem_Ico.mpr ⟨(Finset.mem_Icc.mp hxCoin.1).1, hxOuter.2⟩,
      hxCoin.2⟩
  · intro hx
    have hxSmall := Finset.mem_filter.mp hx
    have hxIco := Finset.mem_Ico.mp hxSmall.1
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hxIco.1, ?_⟩,
      hxSmall.2⟩, hxIco.2⟩
    exact hxIco.2.le.trans hbM

/-- An infinite set of positive natural numbers has unbounded finite-prefix
sum. -/
lemma infinite_prefixSum_unbounded {B : Set ℕ} (hB : B.Infinite) :
    ∀ n : ℕ, ∃ M : ℕ, n ≤ ∑ b ∈ coinsUpTo B M, b := by
  intro n
  obtain ⟨b, hbB, hnb⟩ := hB.exists_gt n
  refine ⟨b, ?_⟩
  have hbmem : b ∈ coinsUpTo B b := by
    simp only [coinsUpTo, Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨by omega, le_rfl⟩, hbB⟩
  calc
    n ≤ b := Nat.le_of_lt hnb
    _ = ∑ x ∈ ({b} : Finset ℕ), x := by simp
    _ ≤ ∑ x ∈ coinsUpTo B b, x :=
      Finset.sum_le_sum_of_subset (by simpa using hbmem)

/-- The Burr--Erdős prefix-growth condition implies that the distinct subset
sums are syndetic (in the one-sided, downward-gap formulation). -/
theorem infinite_prefix_growth_gives_syndetic_subsetSums
    (B : Set ℕ) (K : ℕ) (hB : B.Infinite)
    (hgrowth : ∀ b ∈ B, 1 ≤ b →
      b ≤ (∑ x ∈ smallerCoins B b, x) + K) :
    ∀ n : ℕ, ∃ t : Finset ℕ,
      (∀ b ∈ t, b ∈ B) ∧
      (∑ b ∈ t, b) ≤ n ∧ n ≤ (∑ b ∈ t, b) + K := by
  classical
  intro n
  obtain ⟨M, hnM⟩ := infinite_prefixSum_unbounded hB n
  let s := coinsUpTo B M
  have hfiniteGrowth : ∀ b ∈ s,
      b ≤ (∑ x ∈ s.filter (fun x => x < b), x) + K := by
    intro b hb
    have hbdata : 1 ≤ b ∧ b ≤ M ∧ b ∈ B := by
      simpa [s, coinsUpTo, and_assoc] using hb
    rw [coinsUpTo_filter_lt hbdata.2.1]
    exact hgrowth b hbdata.2.2 hbdata.1
  obtain ⟨t, hts, htlo, hthi⟩ :=
    finite_prefix_bound_gives_bounded_gaps s K hfiniteGrowth n hnM
  refine ⟨t, ?_, htlo, hthi⟩
  intro b hbt
  have hbs : b ∈ s := hts hbt
  change b ∈ coinsUpTo B M at hbs
  exact (Finset.mem_filter.mp hbs).2

end

end Erdos254.InfiniteCoinCover
