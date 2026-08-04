import Research.MultiplicativeScaleDensity
import Research.ShiftedCorrection

namespace Erdos123

private theorem smooth3_pos {a b c x : ℕ}
    (ha : 1 < a) (hb : 1 < b) (hc : 1 < c) (hx : x ∈ Smooth3 a b c) :
    0 < x := by
  rcases hx with ⟨i, j, k, rfl⟩
  positivity

private theorem correctionSet_sum_pos {a b c r : ℕ}
    (hb : 1 < b) (hc : 1 < c) (hr : 0 < r) :
    0 < (correctionSet a b c r).sum id := by
  have hmem : correctionTerm a b c r 0 ∈ correctionSet a b c r := by
    apply Finset.mem_image.mpr
    exact ⟨0, Finset.mem_range.mpr hr, rfl⟩
  have hterm : 0 < correctionTerm a b c r 0 := by
    simp [correctionTerm, pow_pos (by omega : 0 < b), pow_pos (by omega : 0 < c)]
  exact hterm.trans_le (by
    simpa only [id_eq] using Finset.single_le_sum (fun z _hz => Nat.zero_le z) hmem)

/-- For each fixed nonzero residue modulo `a`, every sufficiently large target
in that residue reduces to a smaller target by an F-010 correction. The smaller
target loses at most the explicit factor `a*(S+1)`, where `S` is the unshifted
correction-gadget sum. -/
theorem eventually_reduce_nonzero_residue
    {a b c r : ℕ}
    (ha : 1 < a) (hb : 1 < b) (hc : 1 < c)
    (hab : Nat.Coprime a b) (hac : Nat.Coprime a c) (hbc : Nat.Coprime b c)
    (hr : 0 < r) :
    let S := (correctionSet a b c r).sum id
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → n ≡ r [MOD a] →
      ∃ m : ℕ, m < n ∧ n ≤ a * (S + 1) * m ∧
        (IsRepresentable (Smooth3 a b c) m → IsRepresentable (Smooth3 a b c) n) := by
  dsimp only
  let S : ℕ := (correctionSet a b c r).sum id
  have hS : 0 < S := correctionSet_sum_pos hb hc hr
  have hφ : 0 < a.totient := Nat.totient_pos.mpr (by omega)
  let B₀ : ℕ := b ^ a.totient
  let C₀ : ℕ := c ^ a.totient
  have hB₀ : 1 < B₀ := Nat.one_lt_pow (by omega) hb
  have hC₀ : 1 < C₀ := Nat.one_lt_pow (by omega) hc
  have hBC : Nat.Coprime B₀ C₀ := hbc.pow _ _
  let ρ : ℝ := ((S + a : ℕ) : ℝ) / ((S + 1 : ℕ) : ℝ)
  have hρ : 1 < ρ := by
    dsimp [ρ]
    rw [one_lt_div (by positivity : (0 : ℝ) < (S + 1 : ℕ))]
    exact_mod_cast (show S + 1 < S + a by omega)
  rcases smooth2_eventually_multiplicatively_leftDense hB₀ hC₀ hBC hρ with
    ⟨Y, hY⟩
  rcases exists_nat_ge (Y * (S + 1 : ℕ)) with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn hnmod
  have hnCast : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hxY : Y ≤ (n : ℝ) / (S + 1 : ℕ) := by
    have hden : (0 : ℝ) < (S + 1 : ℕ) := by positivity
    apply (le_div_iff₀ hden).mpr
    exact hN.trans hnCast
  rcases hY ((n : ℝ) / (S + 1 : ℕ)) hxY with ⟨u, v, hwLower, hwUpper⟩
  let w : ℕ := correctionMultiplier a b c u v
  have hwCast : (w : ℝ) = (B₀ : ℝ) ^ u * (C₀ : ℝ) ^ v := by
    simp [w, B₀, C₀, correctionMultiplier, pow_mul]
  have hfrac : ((n : ℝ) / (S + 1 : ℕ)) / ρ = (n : ℝ) / (S + a : ℕ) := by
    dsimp [ρ]
    field_simp
    <;> ring
  rw [← hwCast, hfrac] at hwLower
  rw [← hwCast] at hwUpper
  have hCritReal : (n : ℝ) < (w : ℝ) * (S + a : ℕ) :=
    (div_lt_iff₀ (by positivity : (0 : ℝ) < (S + a : ℕ))).mp hwLower
  have hUpperReal : (w : ℝ) * (S + 1 : ℕ) ≤ (n : ℝ) :=
    (le_div_iff₀ (by positivity : (0 : ℝ) < (S + 1 : ℕ))).mp hwUpper
  have hCrit : n < w * (S + a) := by exact_mod_cast hCritReal
  have hUpper : w * (S + 1) ≤ n := by exact_mod_cast hUpperReal

  let t : Finset ℕ := shiftedCorrectionSet a b c r u v
  let B : ℕ := t.sum id
  have hB : B = w * S := by
    dsimp [B, t, w, S]
    exact shiftedCorrectionSet_sum ha hb hc
  have hBLe : B ≤ n := by
    rw [hB]
    nlinarith
  have hBmod : B ≡ r [MOD a] := by
    dsimp [B, t]
    exact shiftedCorrectionSet_sum_modEq ha hb hc hab hac hbc
  have hsubmod : n - B ≡ 0 [MOD a] := by
    simpa using hnmod.sub hBLe (le_refl r) hBmod
  have hdiv : a ∣ n - B := Nat.modEq_zero_iff_dvd.mp hsubmod
  let m : ℕ := (n - B) / a
  have ham : a * m = n - B := Nat.mul_div_cancel' hdiv
  have hnEq : n = a * m + B := by
    rw [ham]
    omega
  have hmLtW : m < w := by
    have h' : a * m + w * S < w * (S + a) := by simpa [hnEq, hB] using hCrit
    have h'' : w * S + a * m < w * S + a * w := by
      simpa [mul_add, mul_comm, mul_left_comm, add_comm, add_left_comm] using h'
    have hamlt : a * m < a * w := (Nat.add_lt_add_iff_left).mp h''
    exact (Nat.mul_lt_mul_left (by omega : 0 < a)).mp hamlt
  have hwLeAm : w ≤ a * m := by
    have h' : w * (S + 1) ≤ a * m + w * S := by simpa [hnEq, hB] using hUpper
    have h'' : w * S + w ≤ w * S + a * m := by
      simpa [mul_add, add_comm, add_left_comm] using h'
    exact (Nat.add_le_add_iff_left).mp h''
  have hnBound : n ≤ a * (S + 1) * m := by
    rw [hnEq, hB]
    calc
      a * m + w * S ≤ a * m + (a * m) * S := Nat.add_le_add_left (Nat.mul_le_mul_right S hwLeAm) _
      _ = a * (S + 1) * m := by ring
  have hwPos : 0 < w := correctionMultiplier_pos hb hc
  have hnPos : 0 < n := (Nat.mul_pos hwPos (by omega)).trans_le hUpper
  have hmPos : 0 < m := by
    by_contra hm0
    have hmEq : m = 0 := Nat.eq_zero_of_not_pos hm0
    rw [hmEq] at hnBound
    simp only [mul_zero] at hnBound
    omega
  have hmLtN : m < n := by
    have hmLtAm : m < a * m := by
      simpa using Nat.mul_lt_mul_of_pos_right ha hmPos
    have hamLe : a * m ≤ n := by
      rw [hnEq]
      exact Nat.le_add_right _ _
    exact hmLtAm.trans_le hamLe

  refine ⟨m, hmLtN, hnBound, ?_⟩
  rintro ⟨s, hsA, hsPrimitive, hsSum⟩
  have hsPos : ∀ x ∈ s, 0 < x := fun x hx => smooth3_pos ha hb hc (hsA x hx)
  have htPrimitive : IsPrimitive t := by
    dsimp [t]
    exact shiftedCorrectionSet_isPrimitive ha hb hc hab hac hbc
  have htCoprime : ∀ y ∈ t, Nat.Coprime a y := by
    intro y hy
    exact shiftedCorrectionSet_coprime hab hac hy
  have hsep : ∀ x ∈ s, ∀ y ∈ t, x < y := by
    intro x hx y hy
    have hxLe : x ≤ m := by
      rw [← hsSum]
      simpa only [id_eq] using Finset.single_le_sum (fun z _hz => Nat.zero_le z) hx
    have hwLe : w ≤ y := correctionMultiplier_le_of_mem_shifted hb hc hy
    exact hxLe.trans_lt (hmLtW.trans_le hwLe)
  refine ⟨scaleFinset a s ∪ t, ?_,
    isPrimitive_scaleFinset_union ha hsPos hsPrimitive htPrimitive htCoprime hsep, ?_⟩
  · intro y hy
    rcases Finset.mem_union.mp hy with hyOld | hyCorr
    · rcases Finset.mem_image.mp hyOld with ⟨x, hx, rfl⟩
      rcases hsA x hx with ⟨i, j, k, rfl⟩
      refine ⟨i + 1, j, k, ?_⟩
      simp [pow_succ, mul_assoc, mul_comm, mul_left_comm]
    · exact shiftedCorrectionSet_subset_smooth3 hyCorr
  · rw [sum_scaleFinset_union ha htCoprime, hsSum]
    change a * m + B = n
    exact hnEq.symm

end Erdos123
