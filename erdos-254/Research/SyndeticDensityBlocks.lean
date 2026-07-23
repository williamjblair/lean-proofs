import Mathlib

namespace Erdos254.SyndeticDensityBlocks

noncomputable section

attribute [local instance] Classical.propDecidable

/-- A backward-gap bound supplies at least one point in each disjoint block of
length `K+1`. -/
theorem card_filter_range_mul_lower
    (S : Set ℕ) (K m : ℕ)
    (hS : ∀ n : ℕ, ∃ s : ℕ, s ∈ S ∧ s ≤ n ∧ n ≤ s + K) :
    m ≤ ((Finset.range (m * (K + 1))).filter (fun n => n ∈ S)).card := by
  let Q := K + 1
  have hex : ∀ i : Fin m, ∃ s : ℕ,
      s ∈ S ∧ i.val * Q ≤ s ∧ s < (i.val + 1) * Q := by
    intro i
    obtain ⟨s, hsS, hslow, hshigh⟩ := hS ((i.val + 1) * Q - 1)
    refine ⟨s, hsS, ?_, ?_⟩
    · dsimp [Q] at hslow hshigh ⊢
      have hpos : 0 < (i.val + 1) * (K + 1) := by positivity
      have heq : (i.val + 1) * (K + 1) =
          i.val * (K + 1) + (K + 1) := by ring
      omega
    · dsimp [Q] at hslow hshigh ⊢
      have hpos : 0 < (i.val + 1) * (K + 1) := by positivity
      omega
  choose s hsS hslo hshi using hex
  have hinj : Function.Injective s := by
    intro i j hij
    apply Fin.ext
    by_contra hne
    rcases lt_or_gt_of_ne hne with hijlt | hjilt
    · have hblocks : (i.val + 1) * Q ≤ j.val * Q :=
        Nat.mul_le_mul_right Q (by omega)
      have hslt : s i < s j := (hshi i).trans_le (hblocks.trans (hslo j))
      exact (ne_of_lt hslt) hij
    · have hblocks : (j.val + 1) * Q ≤ i.val * Q :=
        Nat.mul_le_mul_right Q (by omega)
      have hslt : s j < s i := (hshi j).trans_le (hblocks.trans (hslo i))
      exact (ne_of_gt hslt) hij
  have hmem : ∀ i, s i ∈
      (Finset.range (m * (K + 1))).filter (fun n => n ∈ S) := by
    intro i
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_range.mpr ?_, hsS i⟩
    have hi : i.val + 1 ≤ m := i.isLt
    have htop : (i.val + 1) * Q ≤ m * Q := Nat.mul_le_mul_right Q hi
    simpa [Q] using (hshi i).trans_le htop
  let emb : Fin m ↪ {n // n ∈
      (Finset.range (m * (K + 1))).filter (fun n => n ∈ S)} :=
    ⟨fun i => ⟨s i, hmem i⟩, fun i j h => hinj (congrArg Subtype.val h)⟩
  simpa using Fintype.card_le_of_injective emb emb.injective

end

end Erdos254.SyndeticDensityBlocks
