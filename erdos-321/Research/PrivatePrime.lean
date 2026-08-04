import Research.Structural
import Mathlib.NumberTheory.Padics.PadicNorm

namespace Erdos321

/-- If `p` divides a new nonzero denominator `x` but divides no denominator in
`A`, then adjoining `x` preserves distinct reciprocal subset sums. -/
theorem valid_insert_of_private_prime {A : Finset ℕ} {x p : ℕ}
    (hp : p.Prime) (hx0 : x ≠ 0) (hpx : p ∣ x)
    (hprivate : ∀ a ∈ A, ¬ p ∣ a) (hA : Valid A) :
    Valid (insert x A) := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  have hNormInvOfPrivate (a : ℕ) (ha : a ∈ A) :
      padicNorm p ((a : ℚ)⁻¹) = 1 := by
    have hnorm : padicNorm p (a : ℚ) = 1 :=
      (padicNorm.nat_eq_one_iff a).mpr (hprivate a ha)
    rw [show ((a : ℚ)⁻¹) = (1 : ℚ) / a by simp, padicNorm.div,
      padicNorm.one, hnorm]
    norm_num
  have hNormInvX : 1 < padicNorm p ((x : ℚ)⁻¹) := by
    have hxq : (x : ℚ) ≠ 0 := by exact_mod_cast hx0
    have hpos : 0 < padicNorm p (x : ℚ) :=
      lt_of_le_of_ne (padicNorm.nonneg _) (Ne.symm (padicNorm.nonzero hxq))
    have hlt : padicNorm p (x : ℚ) < 1 :=
      (padicNorm.nat_lt_one_iff x).mpr hpx
    rw [show ((x : ℚ)⁻¹) = (1 : ℚ) / x by simp, padicNorm.div,
      padicNorm.one, one_div]
    exact (one_lt_inv₀ hpos).mpr hlt
  have subset_A_of_subset_insert_of_not_mem (U : Finset ℕ)
      (hU : U ⊆ insert x A) (hxU : x ∉ U) : U ⊆ A := by
    intro a ha
    rcases Finset.mem_insert.mp (hU ha) with rfl | haA
    · exact (hxU ha).elim
    · exact haA
  have norm_subset_le_one (U : Finset ℕ) (hU : U ⊆ A) :
      padicNorm p (reciprocalSubsetSum U) ≤ 1 := by
    apply padicNorm.sum_le'
    · intro a ha
      rw [hNormInvOfPrivate a (hU ha)]
    · norm_num
  rw [valid_iff_no_disjoint_collision]
  intro hCollision
  obtain ⟨S, hS, T, hT, hDisjoint, hNonempty, hEq⟩ := hCollision
  have hSins : S ⊆ insert x A := Finset.mem_powerset.mp hS
  have hTins : T ⊆ insert x A := Finset.mem_powerset.mp hT
  have impossible (X Y : Finset ℕ)
      (hXins : X ⊆ insert x A) (hYins : Y ⊆ insert x A)
      (hXY : Disjoint X Y) (hxX : x ∈ X)
      (hSum : reciprocalSubsetSum X = reciprocalSubsetSum Y) : False := by
    have hxY : x ∉ Y := Finset.disjoint_left.mp hXY hxX
    have hYA : Y ⊆ A := subset_A_of_subset_insert_of_not_mem Y hYins hxY
    have hXeraseA : X.erase x ⊆ A := by
      intro a ha
      have hax : a ≠ x := (Finset.mem_erase.mp ha).1
      rcases Finset.mem_insert.mp (hXins (Finset.mem_erase.mp ha).2) with h | haA
      · exact (hax h).elim
      · exact haA
    have hNormY := norm_subset_le_one Y hYA
    have hNormErase := norm_subset_le_one (X.erase x) hXeraseA
    have hDecomp : reciprocalSubsetSum (X.erase x) + ((x : ℚ)⁻¹) =
        reciprocalSubsetSum X := by
      simpa [reciprocalSubsetSum] using
        (Finset.sum_erase_add X (fun n : ℕ => ((n : ℚ)⁻¹)) hxX)
    have hIsolate : ((x : ℚ)⁻¹) =
        reciprocalSubsetSum Y - reciprocalSubsetSum (X.erase x) := by
      linarith
    have hNormRhs : padicNorm p
        (reciprocalSubsetSum Y - reciprocalSubsetSum (X.erase x)) ≤ 1 :=
      padicNorm.sub.trans (max_le hNormY hNormErase)
    rw [← hIsolate] at hNormRhs
    exact (not_le_of_gt hNormInvX) hNormRhs
  by_cases hxS : x ∈ S
  · exact impossible S T hSins hTins hDisjoint hxS hEq
  by_cases hxT : x ∈ T
  · exact impossible T S hTins hSins hDisjoint.symm hxT hEq.symm
  have hSA : S ⊆ A := subset_A_of_subset_insert_of_not_mem S hSins hxS
  have hTA : T ⊆ A := subset_A_of_subset_insert_of_not_mem T hTins hxT
  have hST : S = T := hA S (Finset.mem_powerset.mpr hSA)
    T (Finset.mem_powerset.mpr hTA) hEq
  subst T
  have hEmpty : S = ∅ := by
    have hInter : S ∩ S = ∅ := Finset.disjoint_iff_inter_eq_empty.mp hDisjoint
    simpa using hInter
  simp [hEmpty] at hNonempty

/-- A prime larger than every old denominator has itself as a private prime. -/
theorem valid_insert_prime_above {A : Finset ℕ} {p : ℕ} (hp : p.Prime)
    (hAinterval : A ⊆ Finset.Icc 1 (p - 1)) (hA : Valid A) :
    Valid (insert p A) := by
  apply valid_insert_of_private_prime hp hp.ne_zero (dvd_refl p) ?_ hA
  intro a ha
  have haIcc := Finset.mem_Icc.mp (hAinterval ha)
  exact Nat.not_dvd_of_pos_of_lt haIcc.1 (Nat.lt_of_le_pred hp.pos haIcc.2)

/-- Enlarging the ambient interval by one can increase the extremal size by at
most one. -/
theorem extremalSize_succ_le (N : ℕ) :
    extremalSize (N + 1) ≤ extremalSize N + 1 := by
  obtain ⟨A, hA, hcard⟩ := exists_extremizer (N + 1)
  let B := A.erase (N + 1)
  have hBsub : B ⊆ Finset.Icc 1 N := by
    intro a ha
    have haA : a ∈ A := (Finset.mem_erase.mp ha).2
    have haNe : a ≠ N + 1 := (Finset.mem_erase.mp ha).1
    have haIcc := Finset.mem_Icc.mp (hA.1 haA)
    exact Finset.mem_Icc.mpr ⟨haIcc.1, by omega⟩
  have hBvalid : Valid B := hA.2.mono (Finset.erase_subset _ _)
  have hBbound : B.card ≤ extremalSize N :=
    card_le_extremalSize ⟨hBsub, hBvalid⟩
  have hCardStep : A.card ≤ B.card + 1 := by
    by_cases hmem : N + 1 ∈ A
    · rw [Finset.card_erase_add_one hmem]
    · simp [B, Finset.erase_eq_self.mpr hmem]
  omega

/-- At every prime endpoint the extremal function jumps by exactly one. -/
theorem extremalSize_at_prime {p : ℕ} (hp : p.Prime) :
    extremalSize p = extremalSize (p - 1) + 1 := by
  apply Nat.le_antisymm
  · have h := extremalSize_succ_le (p - 1)
    rwa [Nat.sub_add_cancel hp.one_le] at h
  · obtain ⟨A, hA, hcard⟩ := exists_extremizer (p - 1)
    have hpNotMem : p ∉ A := by
      intro hpA
      have hpLe := (Finset.mem_Icc.mp (hA.1 hpA)).2
      have hpPos := hp.pos
      omega
    have hInsertSub : insert p A ⊆ Finset.Icc 1 p := by
      intro a ha
      rcases Finset.mem_insert.mp ha with rfl | haA
      · exact Finset.mem_Icc.mpr ⟨hp.one_le, le_rfl⟩
      · have haIcc := Finset.mem_Icc.mp (hA.1 haA)
        exact Finset.mem_Icc.mpr ⟨haIcc.1, haIcc.2.trans (Nat.sub_le p 1)⟩
    have hInsertValid : Valid (insert p A) :=
      valid_insert_prime_above hp hA.1 hA.2
    have hBound := card_le_extremalSize
      (N := p) (A := insert p A) ⟨hInsertSub, hInsertValid⟩
    simp [hpNotMem, hcard] at hBound
    exact hBound

end Erdos321
