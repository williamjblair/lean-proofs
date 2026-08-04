import Research.Structural
import Research.PrivatePrime
import Mathlib.NumberTheory.Padics.PadicNorm

namespace Erdos321

private theorem padicNorm_inv_nat_eq_zpow {p n : ℕ} [Fact p.Prime] (hn : n ≠ 0) :
    padicNorm p ((n : ℚ)⁻¹) = (p : ℚ) ^ (padicValNat p n : ℤ) := by
  have hnq : (n : ℚ) ≠ 0 := by exact_mod_cast hn
  rw [show ((n : ℚ)⁻¹) = (1 : ℚ) / n by simp, padicNorm.div,
    padicNorm.one, padicNorm.eq_zpow_of_nonzero hnq, one_div]
  rw [← zpow_neg]
  congr 1
  simp [padicValRat.of_nat]

private theorem padicNorm_inv_nat_lt_of_padicValNat_lt
    {p a x : ℕ} [Fact p.Prime] (ha : a ≠ 0) (hx : x ≠ 0)
    (hval : padicValNat p a < padicValNat p x) :
    padicNorm p ((a : ℚ)⁻¹) < padicNorm p ((x : ℚ)⁻¹) := by
  rw [padicNorm_inv_nat_eq_zpow ha, padicNorm_inv_nat_eq_zpow hx,
    zpow_lt_zpow_iff_right₀]
  · exact_mod_cast hval
  · exact_mod_cast (Fact.out : Nat.Prime p).one_lt

/-- A new denominator whose `p`-adic exponent strictly exceeds every old one
can be adjoined to a valid set. -/
theorem valid_insert_of_padicValNat_dominance {A : Finset ℕ} {x p : ℕ}
    (hp : p.Prime) (hx0 : x ≠ 0)
    (hdominates : ∀ a ∈ A, padicValNat p a < padicValNat p x)
    (hA : Valid A) : Valid (insert x A) := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  let t : ℚ := padicNorm p ((x : ℚ)⁻¹)
  have htpos : 0 < t := by
    have hxq : ((x : ℚ)⁻¹) ≠ 0 := inv_ne_zero (by exact_mod_cast hx0)
    exact lt_of_le_of_ne (padicNorm.nonneg _) (Ne.symm (padicNorm.nonzero hxq))
  have hOldNorm (a : ℕ) (ha : a ∈ A) : padicNorm p ((a : ℚ)⁻¹) < t := by
    have ha0 : a ≠ 0 := fun h => hA.zero_not_mem (h ▸ ha)
    exact padicNorm_inv_nat_lt_of_padicValNat_lt ha0 hx0 (hdominates a ha)
  have subset_A_of_subset_insert_of_not_mem (U : Finset ℕ)
      (hU : U ⊆ insert x A) (hxU : x ∉ U) : U ⊆ A := by
    intro a ha
    rcases Finset.mem_insert.mp (hU ha) with rfl | haA
    · exact (hxU ha).elim
    · exact haA
  have norm_subset_lt (U : Finset ℕ) (hU : U ⊆ A) :
      padicNorm p (reciprocalSubsetSum U) < t := by
    apply padicNorm.sum_lt'
    · intro a ha
      exact hOldNorm a (hU ha)
    · exact htpos
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
    have hNormY := norm_subset_lt Y hYA
    have hNormErase := norm_subset_lt (X.erase x) hXeraseA
    have hDecomp : reciprocalSubsetSum (X.erase x) + ((x : ℚ)⁻¹) =
        reciprocalSubsetSum X := by
      simpa [reciprocalSubsetSum] using
        (Finset.sum_erase_add X (fun n : ℕ => ((n : ℚ)⁻¹)) hxX)
    have hIsolate : ((x : ℚ)⁻¹) =
        reciprocalSubsetSum Y - reciprocalSubsetSum (X.erase x) := by
      linarith
    have hNormRhs : padicNorm p
        (reciprocalSubsetSum Y - reciprocalSubsetSum (X.erase x)) < t :=
      lt_of_le_of_lt padicNorm.sub (max_lt hNormY hNormErase)
    rw [← hIsolate] at hNormRhs
    exact (lt_irrefl t) hNormRhs
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

/-- Divisibility by a private prime-power threshold is a convenient sufficient
form of strict valuation dominance. -/
theorem valid_insert_of_private_prime_power {A : Finset ℕ} {x p k : ℕ}
    (hp : p.Prime) (hx0 : x ≠ 0) (hpkx : p ^ k ∣ x)
    (hprivate : ∀ a ∈ A, ¬ p ^ k ∣ a) (hA : Valid A) :
    Valid (insert x A) := by
  letI : Fact p.Prime := ⟨hp⟩
  apply valid_insert_of_padicValNat_dominance hp hx0 ?_ hA
  intro a ha
  have ha0 : a ≠ 0 := fun h => hA.zero_not_mem (h ▸ ha)
  have haValLt : padicValNat p a < k := by
    apply lt_of_not_ge
    intro hk
    exact hprivate a ha ((padicValNat_dvd_iff_le ha0).mpr hk)
  have hxVal : k ≤ padicValNat p x := (padicValNat_dvd_iff_le hx0).mp hpkx
  exact haValLt.trans_le hxVal

/-- Every prime-power endpoint is forced and causes an exact unit jump. -/
theorem extremalSize_at_prime_pow {p k : ℕ} (hp : p.Prime) :
    extremalSize (p ^ k) = extremalSize (p ^ k - 1) + 1 := by
  have hpowPos : 0 < p ^ k := pow_pos hp.pos k
  apply Nat.le_antisymm
  · have h := extremalSize_succ_le (p ^ k - 1)
    rwa [Nat.sub_add_cancel hpowPos] at h
  · obtain ⟨A, hA, hcard⟩ := exists_extremizer (p ^ k - 1)
    have hPowNotMem : p ^ k ∉ A := by
      intro hpA
      have hpLe := (Finset.mem_Icc.mp (hA.1 hpA)).2
      omega
    have hPrivate : ∀ a ∈ A, ¬ p ^ k ∣ a := by
      intro a ha
      have haIcc := Finset.mem_Icc.mp (hA.1 ha)
      exact Nat.not_dvd_of_pos_of_lt haIcc.1
        (Nat.lt_of_le_pred hpowPos haIcc.2)
    have hInsertSub : insert (p ^ k) A ⊆ Finset.Icc 1 (p ^ k) := by
      intro a ha
      rcases Finset.mem_insert.mp ha with rfl | haA
      · exact Finset.mem_Icc.mpr ⟨hpowPos, le_rfl⟩
      · have haIcc := Finset.mem_Icc.mp (hA.1 haA)
        exact Finset.mem_Icc.mpr ⟨haIcc.1, haIcc.2.trans (Nat.sub_le _ _ )⟩
    have hInsertValid : Valid (insert (p ^ k) A) :=
      valid_insert_of_private_prime_power hp (ne_of_gt hpowPos) (dvd_refl _)
        hPrivate hA.2
    have hBound := card_le_extremalSize
      (N := p ^ k) (A := insert (p ^ k) A) ⟨hInsertSub, hInsertValid⟩
    simp [hPowNotMem, hcard] at hBound
    exact hBound

end Erdos321
