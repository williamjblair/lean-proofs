import Research.SubsetSums

/-! # Exact-doubling denominators for the lower bound -/

namespace Research

/-- A positive denominator which has no signed representation by earlier
reciprocals. Denominator `d` corresponds to zero-based index `d-1`. -/
def GoodDenominator (d : ℕ) : Prop :=
  0 < d ∧ NoSignedReciprocalRepresentation (d - 1)

noncomputable instance goodDenominatorDecidable (d : ℕ) :
    Decidable (GoodDenominator d) := Classical.propDecidable _

/-- Good denominators up to `N`. -/
noncomputable def goodDenominators (N : ℕ) : Finset ℕ :=
  (Finset.Icc 1 N).filter GoodDenominator

/-- The subset-sum support cannot shrink when a denominator is adjoined. -/
theorem S_le_succ (N : ℕ) : S N ≤ S (N + 1) := by
  change (reciprocalSubsetSums N).card ≤ (reciprocalSubsetSums (N + 1)).card
  rw [reciprocalSubsetSums_succ]
  exact Finset.card_le_card Finset.subset_union_left

/-- A good denominator produces exact doubling at the corresponding step. -/
theorem S_eq_two_mul_of_good {d : ℕ} (hd : GoodDenominator d) :
    S d = 2 * S (d - 1) := by
  have hdpos : 0 < d := hd.1
  have hsucc : d - 1 + 1 = d := by omega
  have hiff := (S_succ_eq_two_mul_iff (d - 1)).mpr hd.2
  rwa [hsucc] at hiff

/-- Adding `N+1` either leaves the good-denominator count unchanged or adds
exactly that new endpoint. -/
theorem goodDenominators_succ (N : ℕ) :
    goodDenominators (N + 1) =
      if GoodDenominator (N + 1) then
        insert (N + 1) (goodDenominators N)
      else goodDenominators N := by
  ext d
  by_cases hgood : GoodDenominator (N + 1)
  · simp only [goodDenominators, Finset.mem_filter, Finset.mem_Icc,
      Finset.mem_insert, if_pos hgood]
    constructor
    · rintro ⟨hd, hgd⟩
      by_cases heq : d = N + 1
      · exact Or.inl heq
      · right
        exact ⟨⟨hd.1, by omega⟩, hgd⟩
    · rintro (rfl | hd)
      · exact ⟨⟨by omega, le_rfl⟩, hgood⟩
      · exact ⟨⟨hd.1.1, le_trans hd.1.2 (by omega)⟩, hd.2⟩
  · simp only [goodDenominators, Finset.mem_filter, Finset.mem_Icc,
      if_neg hgood]
    constructor
    · rintro ⟨hd, hgd⟩
      have hne : d ≠ N + 1 := by
        intro heq
        subst d
        exact hgood hgd
      exact ⟨⟨hd.1, by omega⟩, hgd⟩
    · rintro ⟨hd, hgd⟩
      exact ⟨⟨hd.1, le_trans hd.2 (by omega)⟩, hgd⟩

/-- Every good denominator contributes an independent factor two to the
number of distinct subset sums. -/
theorem two_pow_card_good_le_S (N : ℕ) :
    2 ^ (goodDenominators N).card ≤ S N := by
  induction N with
  | zero => simp [goodDenominators, S_zero]
  | succ N ih =>
      rw [goodDenominators_succ]
      by_cases hgood : GoodDenominator (N + 1)
      · rw [if_pos hgood]
        have hnotmem : N + 1 ∉ goodDenominators N := by
          simp [goodDenominators]
        rw [Finset.card_insert_of_notMem hnotmem, pow_succ,
          S_eq_two_mul_of_good hgood]
        simpa [Nat.mul_comm] using Nat.mul_le_mul_left 2 ih
      · rw [if_neg hgood]
        exact le_trans ih (S_le_succ N)

/-- Logarithmic form: `log S(N)` is at least `log 2` times the number of good
denominators. -/
theorem card_good_mul_log_two_le_logS (N : ℕ) :
    ((goodDenominators N).card : ℝ) * Real.log 2 ≤ logS N := by
  have hpowposNat : 0 < (2 : ℕ) ^ (goodDenominators N).card := by positivity
  have hpowpos : (0 : ℝ) < (((2 : ℕ) ^ (goodDenominators N).card : ℕ) : ℝ) := by
    exact_mod_cast hpowposNat
  have hSposNat : 0 < S N := lt_of_lt_of_le hpowposNat (two_pow_card_good_le_S N)
  have hSpos : (0 : ℝ) < S N := by exact_mod_cast hSposNat
  have hcast : (((2 : ℕ) ^ (goodDenominators N).card : ℕ) : ℝ) ≤ (S N : ℝ) := by
    exact_mod_cast two_pow_card_good_le_S N
  norm_num only [Nat.cast_pow, Nat.cast_ofNat] at hcast hpowpos
  have hlog := Real.log_le_log hpowpos hcast
  norm_num only [Nat.cast_pow, Nat.cast_ofNat] at hlog
  rw [Real.log_pow] at hlog
  simpa [logS] using hlog

end Research
