import Mathlib

namespace Erdos254.DenseChunk

open scoped BigOperators

noncomputable section

attribute [local instance] Classical.propDecidable

/-- Partition a finite subset of `[0,mR)` into `R` consecutive chunks and
choose one whose translated copy has at least the average cardinality. -/
theorem exists_dense_chunk
    (C : Finset ℕ) (m R : ℕ) (hm : 0 < m) (hR : 0 < R)
    (hC : ∀ x ∈ C, x < m * R) :
    ∃ c : ℕ, c < R ∧ ∃ B : Finset ℕ,
      C.card ≤ R * B.card ∧
      ∀ x ∈ B, x < m ∧ c * m + x ∈ C := by
  let D : ℕ → Finset ℕ := fun c =>
    C.filter (fun x => c * m ≤ x ∧ x < (c + 1) * m)
  have hsum : ∑ c ∈ Finset.range R, (D c).card = C.card := by
    dsimp [D]
    simp_rw [Finset.card_filter]
    rw [Finset.sum_comm]
    calc
      (∑ x ∈ C, ∑ c ∈ Finset.range R,
          if c * m ≤ x ∧ x < (c + 1) * m then 1 else 0) =
          ∑ _x ∈ C, 1 := by
        apply Finset.sum_congr rfl
        intro x hx
        have hxlt := hC x hx
        let c := x / m
        have hcR : c < R := by
          dsimp [c]
          exact (Nat.div_lt_iff_lt_mul hm).2 (by simpa [Nat.mul_comm] using hxlt)
        have hclo : c * m ≤ x := Nat.div_mul_le_self x m
        have hchi : x < (c + 1) * m := by
          dsimp [c]
          simpa [Nat.mul_comm] using Nat.lt_mul_div_succ x hm
        rw [Finset.sum_eq_single c]
        · simp [hcR, hclo, hchi]
        · intro b hb hbc
          have hfalse : ¬(b * m ≤ x ∧ x < (b + 1) * m) := by
            rintro ⟨hblo, hbhi⟩
            apply hbc
            dsimp [c]
            exact (Nat.div_eq_of_lt_le hblo hbhi).symm
          simp [hfalse]
        · intro hcnot
          exact (hcnot (Finset.mem_range.mpr hcR)).elim
      _ = C.card := by simp
  have hrange : (Finset.range R).Nonempty := by simp [hR.ne']
  obtain ⟨c, hcRange, hcmax⟩ :=
    Finset.exists_max_image (Finset.range R) (fun c => (D c).card) hrange
  have hlarge : C.card ≤ R * (D c).card := by
    have havg := Finset.sum_le_card_nsmul (Finset.range R)
      (fun b => (D b).card) ((D c).card) hcmax
    rw [hsum] at havg
    simpa using havg
  let B : Finset ℕ := (D c).image (fun x => x - c * m)
  have hinj : Set.InjOn (fun x : ℕ => x - c * m) (D c : Set ℕ) := by
    intro x hx y hy hxy
    have hxlo := (Finset.mem_filter.mp hx).2.1
    have hylo := (Finset.mem_filter.mp hy).2.1
    change x - c * m = y - c * m at hxy
    calc
      x = (x - c * m) + c * m := (Nat.sub_add_cancel hxlo).symm
      _ = (y - c * m) + c * m := by rw [hxy]
      _ = y := Nat.sub_add_cancel hylo
  have hcardB : B.card = (D c).card := Finset.card_image_iff.mpr hinj
  refine ⟨c, Finset.mem_range.mp hcRange, B, ?_, ?_⟩
  · rwa [hcardB]
  · intro x hx
    rw [Finset.mem_image] at hx
    obtain ⟨z, hzD, rfl⟩ := hx
    have hz := Finset.mem_filter.mp hzD
    refine ⟨?_, ?_⟩
    · have hzlo := hz.2.1
      rw [Nat.sub_lt_iff_lt_add' hzlo]
      simpa [add_mul, Nat.add_comm] using hz.2.2
    · have hzlo := hz.2.1
      rw [Nat.add_sub_of_le hzlo]
      exact hz.1

end

end Erdos254.DenseChunk
