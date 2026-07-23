import Mathlib

namespace Erdos254.FiniteCoinCover

open scoped BigOperators

/-- The subset sums of `s` have no downward gap larger than `K` throughout
`[0, sum s]`. -/
def HasSubsetSumGapsAtMost (s : Finset ℕ) (K : ℕ) : Prop :=
  ∀ n : ℕ, n ≤ ∑ a ∈ s, a →
    ∃ t : Finset ℕ, t ⊆ s ∧ (∑ a ∈ t, a) ≤ n ∧ n ≤ (∑ a ∈ t, a) + K

lemma empty_hasSubsetSumGapsAtMost (K : ℕ) :
    HasSubsetSumGapsAtMost ∅ K := by
  intro n hn
  refine ⟨∅, by simp, by simp, ?_⟩
  simp at hn ⊢
  omega

/-- Adjoining a coin no larger than the old total plus `K` preserves the
`K`-gap property. -/
lemma insert_hasSubsetSumGapsAtMost {s : Finset ℕ} {a K : ℕ} (ha : a ∉ s)
    (hs : HasSubsetSumGapsAtMost s K)
    (haBound : a ≤ (∑ x ∈ s, x) + K) :
    HasSubsetSumGapsAtMost (insert a s) K := by
  intro n hn
  rw [Finset.sum_insert ha] at hn
  by_cases hnold : n ≤ ∑ x ∈ s, x
  · obtain ⟨t, hts, htlo, hthi⟩ := hs n hnold
    exact ⟨t, hts.trans (Finset.subset_insert a s), htlo, hthi⟩
  by_cases han : a ≤ n
  · have htarget : n - a ≤ ∑ x ∈ s, x := by omega
    obtain ⟨t, hts, htlo, hthi⟩ := hs (n - a) htarget
    refine ⟨insert a t, ?_, ?_, ?_⟩
    · exact Finset.insert_subset (Finset.mem_insert_self _ _) <|
        hts.trans (Finset.subset_insert a s)
    · rw [Finset.sum_insert (fun hat => ha (hts hat))]
      omega
    · rw [Finset.sum_insert (fun hat => ha (hts hat))]
      omega
  · refine ⟨s, Finset.subset_insert a s, Nat.le_of_not_ge hnold, ?_⟩
    omega

/-- If every coin is at most `K` plus the sum of the smaller coins, then all
subset-sum gaps up to the total are at most `K`. -/
theorem finite_prefix_bound_gives_bounded_gaps (s : Finset ℕ) (K : ℕ)
    (hgrowth : ∀ a ∈ s, a ≤ (∑ x ∈ s.filter (fun x => x < a), x) + K) :
    HasSubsetSumGapsAtMost s K := by
  classical
  induction s using Finset.strongInductionOn
  rename_i s ih
  by_cases hs0 : s = ∅
  · subst s
    exact empty_hasSubsetSumGapsAtMost K
  · let a := s.max' (Finset.nonempty_iff_ne_empty.mpr hs0)
    let r := s.erase a
    have haS : a ∈ s := Finset.max'_mem s _
    have har : a ∉ r := by simp [r]
    have hrs : r ⊂ s := Finset.erase_ssubset haS
    have hless : ∀ x ∈ r, x < a := by
      intro x hxr
      have hxS : x ∈ s := (Finset.mem_erase.mp hxr).2
      have hxle : x ≤ a := Finset.le_max' s x hxS
      have hxne : x ≠ a := (Finset.mem_erase.mp hxr).1
      omega
    have hfilter : s.filter (fun x => x < a) = r := by
      ext x
      simp only [Finset.mem_filter]
      change (x ∈ s ∧ x < a) ↔ x ∈ s.erase a
      rw [Finset.mem_erase]
      constructor
      · rintro ⟨hxS, hxa⟩
        exact ⟨by omega, hxS⟩
      · rintro ⟨hxa, hxS⟩
        have hxr : x ∈ r := by
          change x ∈ s.erase a
          exact Finset.mem_erase.mpr ⟨hxa, hxS⟩
        exact ⟨hxS, hless x hxr⟩
    have haBound : a ≤ (∑ x ∈ r, x) + K := by
      rw [← hfilter]
      exact hgrowth a haS
    have hgrowthR : ∀ b ∈ r,
        b ≤ (∑ x ∈ r.filter (fun x => x < b), x) + K := by
      intro b hb
      have hbS : b ∈ s := (Finset.mem_erase.mp hb).2
      have hfilters : r.filter (fun x => x < b) = s.filter (fun x => x < b) := by
        ext x
        simp only [Finset.mem_filter]
        change (x ∈ s.erase a ∧ x < b) ↔ (x ∈ s ∧ x < b)
        rw [Finset.mem_erase]
        constructor
        · rintro ⟨⟨hxa, hxS⟩, hxb⟩
          exact ⟨hxS, hxb⟩
        · rintro ⟨hxS, hxb⟩
          exact ⟨⟨by
            have hba : b < a := hless b hb
            omega, hxS⟩, hxb⟩
      rw [hfilters]
      exact hgrowth b hbS
    have hcoverR : HasSubsetSumGapsAtMost r K := ih r hrs hgrowthR
    have hins := insert_hasSubsetSumGapsAtMost har hcoverR haBound
    simpa [r, Finset.insert_erase haS] using hins

end Erdos254.FiniteCoinCover
