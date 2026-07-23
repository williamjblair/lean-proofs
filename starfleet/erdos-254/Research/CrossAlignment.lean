import Mathlib

namespace Erdos254.CrossAlignment

open scoped BigOperators

noncomputable section

attribute [local instance] Classical.propDecidable

/-- Two finite subsets of `[0,L)` have a common exact-sum fiber of size at
least their product divided by `2L`. -/
theorem exists_large_exact_sum_fiber
    (A B : Finset ℕ) (L : ℕ) (hL : 0 < L)
    (hA : ∀ x ∈ A, x < L) (hB : ∀ y ∈ B, y < L) :
    ∃ r : ℕ, r < 2 * L ∧ ∃ C : Finset ℕ,
      A.card * B.card ≤ (2 * L) * C.card ∧
      (∀ x ∈ C, x ∈ A ∧ ∃ y ∈ B, x + y = r) := by
  let pairs := A.product B
  let D : ℕ → Finset (ℕ × ℕ) := fun r =>
    pairs.filter (fun p => p.1 + p.2 = r)
  have hsum : ∑ r ∈ Finset.range (2 * L), (D r).card = pairs.card := by
    dsimp [D]
    simp_rw [Finset.card_filter]
    rw [Finset.sum_comm]
    calc
      (∑ x ∈ pairs, ∑ r ∈ Finset.range (2 * L),
          if x.1 + x.2 = r then 1 else 0) = ∑ _x ∈ pairs, 1 := by
        apply Finset.sum_congr rfl
        intro p hp
        have hp' := Finset.mem_product.mp hp
        have hplt : p.1 + p.2 < 2 * L := by
          have hx := hA p.1 hp'.1
          have hy := hB p.2 hp'.2
          omega
        simp [hplt]
      _ = pairs.card := by simp
  have hrange : (Finset.range (2 * L)).Nonempty := by
    simp [hL.ne']
  obtain ⟨r, hrRange, hrmax⟩ :=
    Finset.exists_max_image (Finset.range (2 * L)) (fun r => (D r).card) hrange
  have hlargeD : A.card * B.card ≤ (2 * L) * (D r).card := by
    have havg := Finset.sum_le_card_nsmul (Finset.range (2 * L))
      (fun q => (D q).card) ((D r).card) hrmax
    rw [hsum] at havg
    dsimp [pairs] at havg
    simp only [Finset.card_product, Finset.card_range, nsmul_eq_mul] at havg
    exact havg
  have hfstinj : Set.InjOn Prod.fst (D r : Set (ℕ × ℕ)) := by
    intro p hp q hq hpq
    have hpD := Finset.mem_filter.mp hp
    have hqD := Finset.mem_filter.mp hq
    apply Prod.ext
    · exact hpq
    · have hpsum := hpD.2
      have hqsum := hqD.2
      omega
  let C : Finset ℕ := (D r).image Prod.fst
  have hcardC : C.card = (D r).card := Finset.card_image_iff.mpr hfstinj
  refine ⟨r, Finset.mem_range.mp hrRange, C, ?_, ?_⟩
  · rwa [hcardC]
  · intro x hx
    rw [Finset.mem_image] at hx
    obtain ⟨p, hpD, rfl⟩ := hx
    have hp := Finset.mem_filter.mp hpD
    have hpPair := Finset.mem_product.mp hp.1
    exact ⟨hpPair.1, p.2, hpPair.2, hp.2⟩

end

end Erdos254.CrossAlignment
