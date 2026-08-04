import Research.ResidueReduction

namespace Erdos123

private theorem representable_scale_base {a b c m : ℕ}
    (ha : 1 < a) (hb : 1 < b) (hc : 1 < c)
    (hrep : IsRepresentable (Smooth3 a b c) m) :
    IsRepresentable (Smooth3 a b c) (a * m) := by
  rcases hrep with ⟨s, hsA, hsPrimitive, hsSum⟩
  have hsPos : ∀ x ∈ s, 0 < x := by
    intro x hx
    rcases hsA x hx with ⟨i, j, k, rfl⟩
    positivity
  have htPrimitive : IsPrimitive (∅ : Finset ℕ) := by simp [IsPrimitive]
  have htCoprime : ∀ y ∈ (∅ : Finset ℕ), Nat.Coprime a y := by simp
  have hsep : ∀ x ∈ s, ∀ y ∈ (∅ : Finset ℕ), x < y := by simp
  refine ⟨scaleFinset a s, ?_, ?_, ?_⟩
  · intro y hy
    rcases Finset.mem_image.mp hy with ⟨x, hx, rfl⟩
    rcases hsA x hx with ⟨i, j, k, rfl⟩
    refine ⟨i + 1, j, k, ?_⟩
    simp [pow_succ, mul_assoc, mul_comm, mul_left_comm]
  · simpa using isPrimitive_scaleFinset_union ha hsPos hsPrimitive
      htPrimitive htCoprime hsep
  · have hsum := sum_scaleFinset_union (s := s) (t := ∅) ha htCoprime
    simp only [Finset.union_empty, Finset.sum_empty, add_zero] at hsum
    rw [hsum, hsSum]

/-- The general conjecture has a finite seed gate. For every fixed coprime
triple there are explicit-in-principle constants `N,C` such that representing
the finite interval `[N,CN]` implies d-completeness. This isolates the sole
remaining global obstruction after F-011. -/
theorem finite_seed_gate
    {a b c : ℕ}
    (ha : 1 < a) (hb : 1 < b) (hc : 1 < c)
    (hab : Nat.Coprime a b) (hac : Nat.Coprime a c) (hbc : Nat.Coprime b c) :
    ∃ N C : ℕ, 0 < N ∧ 1 < C ∧
      ((∀ n : ℕ, N ≤ n → n ≤ C * N → IsRepresentable (Smooth3 a b c) n) →
        IsDComplete (Smooth3 a b c)) := by
  classical
  have hall : ∀ r : ℕ, ∃ Nr : ℕ, 0 < r →
      ∀ n : ℕ, Nr ≤ n → n ≡ r [MOD a] →
        ∃ m : ℕ, m < n ∧
          n ≤ a * ((correctionSet a b c r).sum id + 1) * m ∧
          (IsRepresentable (Smooth3 a b c) m → IsRepresentable (Smooth3 a b c) n) := by
    intro r
    by_cases hr : 0 < r
    · rcases eventually_reduce_nonzero_residue ha hb hc hab hac hbc hr with ⟨N, hN⟩
      exact ⟨N, fun _hr => hN⟩
    · exact ⟨0, fun h => False.elim (hr h)⟩
  choose Nr hNr using hall
  let N : ℕ := 1 + ∑ r ∈ Finset.range a, Nr r
  let Cr : ℕ → ℕ := fun r => a * ((correctionSet a b c r).sum id + 1)
  let C : ℕ := a + ∑ r ∈ Finset.range a, Cr r
  have hNpos : 0 < N := by simp [N]
  have hCgeA : a ≤ C := by simp [C]
  have hCpos : 0 < C := (by omega : 0 < a).trans_le hCgeA
  have hCone : 1 < C := ha.trans_le hCgeA
  have hNrLeN : ∀ r < a, Nr r ≤ N := by
    intro r hr
    have hle : Nr r ≤ ∑ z ∈ Finset.range a, Nr z := by
      exact Finset.single_le_sum (fun z _hz => Nat.zero_le (Nr z)) (Finset.mem_range.mpr hr)
    dsimp [N]
    omega
  have hCrLeC : ∀ r < a, Cr r ≤ C := by
    intro r hr
    have hle : Cr r ≤ ∑ z ∈ Finset.range a, Cr z := by
      exact Finset.single_le_sum (fun z _hz => Nat.zero_le (Cr z)) (Finset.mem_range.mpr hr)
    dsimp [C]
    omega

  have hreduce : ∀ n : ℕ, C * N < n →
      ∃ m : ℕ, N ≤ m ∧ m < n ∧
        (IsRepresentable (Smooth3 a b c) m → IsRepresentable (Smooth3 a b c) n) := by
    intro n hnLarge
    let r : ℕ := n % a
    have hrlt : r < a := Nat.mod_lt n (by omega)
    by_cases hr0 : r = 0
    · have hdiv : a ∣ n := by
        apply Nat.dvd_of_mod_eq_zero
        exact hr0
      let m : ℕ := n / a
      have ham : a * m = n := Nat.mul_div_cancel' hdiv
      have hNm : N ≤ m := by
        apply (Nat.le_div_iff_mul_le (by omega : 0 < a)).mpr
        have haNle : a * N ≤ C * N := Nat.mul_le_mul_right N hCgeA
        simpa [mul_comm] using haNle.trans (Nat.le_of_lt hnLarge)
      have hmPos : 0 < m := hNpos.trans_le hNm
      have hmLt : m < n := by
        rw [← ham]
        simpa using Nat.mul_lt_mul_of_pos_right ha hmPos
      refine ⟨m, hNm, hmLt, ?_⟩
      intro hmRep
      rw [← ham]
      exact representable_scale_base ha hb hc hmRep
    · have hrpos : 0 < r := by omega
      have hNn : N ≤ n :=
        (Nat.le_mul_of_pos_left N hCpos).trans (Nat.le_of_lt hnLarge)
      have hnNr : Nr r ≤ n := (hNrLeN r hrlt).trans hNn
      have hnmod : n ≡ r [MOD a] := (Nat.mod_modEq n a).symm
      rcases hNr r hrpos n hnNr hnmod with ⟨m, hmLt, hnm, hlift⟩
      have hnmC : n ≤ C * m := by
        have hCr := hCrLeC r hrlt
        exact hnm.trans (Nat.mul_le_mul_right m hCr)
      have hNm : N ≤ m := by
        have hmul : C * N < C * m := hnLarge.trans_le hnmC
        exact (Nat.mul_lt_mul_left hCpos).mp hmul |>.le
      exact ⟨m, hNm, hmLt, hlift⟩

  refine ⟨N, C, hNpos, hCone, ?_⟩
  intro hseed
  refine ⟨N, ?_⟩
  intro n hn
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases hnSeed : n ≤ C * N
      · exact hseed n hn hnSeed
      · rcases hreduce n (lt_of_not_ge hnSeed) with ⟨m, hmN, hmn, hlift⟩
        exact hlift (ih m hmn hmN)

/-- Flexible form of the finite seed gate: once the reduction constants are
fixed, a represented block may start at any larger threshold, not only at the
particular threshold used to define the constants. -/
theorem flexible_finite_seed_gate
    {a b c : ℕ}
    (ha : 1 < a) (hb : 1 < b) (hc : 1 < c)
    (hab : Nat.Coprime a b) (hac : Nat.Coprime a c) (hbc : Nat.Coprime b c) :
    ∃ N₀ C : ℕ, 0 < N₀ ∧ 1 < C ∧
      ∀ N : ℕ, N₀ ≤ N →
        ((∀ n : ℕ, N ≤ n → n ≤ C * N →
            IsRepresentable (Smooth3 a b c) n) →
          IsDComplete (Smooth3 a b c)) := by
  classical
  have hall : ∀ r : ℕ, ∃ Nr : ℕ, 0 < r →
      ∀ n : ℕ, Nr ≤ n → n ≡ r [MOD a] →
        ∃ m : ℕ, m < n ∧
          n ≤ a * ((correctionSet a b c r).sum id + 1) * m ∧
          (IsRepresentable (Smooth3 a b c) m →
            IsRepresentable (Smooth3 a b c) n) := by
    intro r
    by_cases hr : 0 < r
    · rcases eventually_reduce_nonzero_residue ha hb hc hab hac hbc hr with ⟨N, hN⟩
      exact ⟨N, fun _hr => hN⟩
    · exact ⟨0, fun h => False.elim (hr h)⟩
  choose Nr hNr using hall
  let N₀ : ℕ := 1 + ∑ r ∈ Finset.range a, Nr r
  let Cr : ℕ → ℕ := fun r => a * ((correctionSet a b c r).sum id + 1)
  let C : ℕ := a + ∑ r ∈ Finset.range a, Cr r
  have hN₀pos : 0 < N₀ := by simp [N₀]
  have hCgeA : a ≤ C := by simp [C]
  have hCpos : 0 < C := (by omega : 0 < a).trans_le hCgeA
  have hCone : 1 < C := ha.trans_le hCgeA
  have hNrLe : ∀ r < a, Nr r ≤ N₀ := by
    intro r hr
    have hle : Nr r ≤ ∑ z ∈ Finset.range a, Nr z := by
      exact Finset.single_le_sum (fun z _hz => Nat.zero_le (Nr z))
        (Finset.mem_range.mpr hr)
    dsimp [N₀]
    omega
  have hCrLe : ∀ r < a, Cr r ≤ C := by
    intro r hr
    have hle : Cr r ≤ ∑ z ∈ Finset.range a, Cr z := by
      exact Finset.single_le_sum (fun z _hz => Nat.zero_le (Cr z))
        (Finset.mem_range.mpr hr)
    dsimp [C]
    omega
  refine ⟨N₀, C, hN₀pos, hCone, ?_⟩
  intro N hN₀N hseed
  have hreduce : ∀ n : ℕ, C * N < n →
      ∃ m : ℕ, N ≤ m ∧ m < n ∧
        (IsRepresentable (Smooth3 a b c) m →
          IsRepresentable (Smooth3 a b c) n) := by
    intro n hnLarge
    let r : ℕ := n % a
    have hrlt : r < a := Nat.mod_lt n (by omega)
    by_cases hr0 : r = 0
    · have hdiv : a ∣ n := by
        apply Nat.dvd_of_mod_eq_zero
        exact hr0
      let m : ℕ := n / a
      have ham : a * m = n := Nat.mul_div_cancel' hdiv
      have hNm : N ≤ m := by
        apply (Nat.le_div_iff_mul_le (by omega : 0 < a)).mpr
        have haNle : a * N ≤ C * N := Nat.mul_le_mul_right N hCgeA
        simpa [mul_comm] using haNle.trans (Nat.le_of_lt hnLarge)
      have hNpos : 0 < N := hN₀pos.trans_le hN₀N
      have hmPos : 0 < m := hNpos.trans_le hNm
      have hmLt : m < n := by
        rw [← ham]
        simpa using Nat.mul_lt_mul_of_pos_right ha hmPos
      refine ⟨m, hNm, hmLt, ?_⟩
      intro hmRep
      rw [← ham]
      exact representable_scale_base ha hb hc hmRep
    · have hrpos : 0 < r := by omega
      have hNn : N ≤ n :=
        (Nat.le_mul_of_pos_left N hCpos).trans (Nat.le_of_lt hnLarge)
      have hnNr : Nr r ≤ n := (hNrLe r hrlt).trans (hN₀N.trans hNn)
      have hnmod : n ≡ r [MOD a] := (Nat.mod_modEq n a).symm
      rcases hNr r hrpos n hnNr hnmod with ⟨m, hmLt, hnm, hlift⟩
      have hnmC : n ≤ C * m := by
        exact hnm.trans (Nat.mul_le_mul_right m (hCrLe r hrlt))
      have hNm : N ≤ m := by
        have hmul : C * N < C * m := hnLarge.trans_le hnmC
        exact (Nat.mul_lt_mul_left hCpos).mp hmul |>.le
      exact ⟨m, hNm, hmLt, hlift⟩
  refine ⟨N, ?_⟩
  intro n hn
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases hnSeed : n ≤ C * N
      · exact hseed n hn hnSeed
      · rcases hreduce n (lt_of_not_ge hnSeed) with ⟨m, hmN, hmn, hlift⟩
        exact hlift (ih m hmn hmN)

end Erdos123
