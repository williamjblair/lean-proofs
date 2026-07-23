import Research.UpperFiberHypergraphs

namespace Erdos796

/-- Encoding by a prime above the `N⁴` threshold and a cofactor through `N²`. -/
def HasLargePrimeEncoding (N M d : ℕ) : Prop :=
  ∃ z : ℕ × ℕ, z.1 ∈ Nat.primesLE M ∧
    z.2 ≤ N ^ 2 ∧ d = z.1 * z.2

/-- Encoding by two bounded factors. -/
def HasBalancedEncoding (N d : ℕ) : Prop :=
  ∃ z : ℕ × ℕ, z.1 ≤ N ^ 4 ∧ z.2 ≤ N ^ 3 ∧ d = z.1 * z.2

/-- The sixth-power factorization lemma in finite-encoding form. -/
theorem largePrimeEncoding_or_balanced {N M d : ℕ}
    (hN : 1 < N) (hdpos : 0 < d) (hdM : d ≤ M) (hMN : M ≤ N ^ 6) :
    HasLargePrimeEncoding N M d ∨ HasBalancedEncoding N d := by
  rcases sixthPower_factorization hN hdpos (hdM.trans hMN) with hlarge | hbal
  · rcases hlarge with ⟨p, t, hp, hpN, hpt, ht⟩
    left
    refine ⟨(p, t), ?_, ht, hpt⟩
    rw [Nat.mem_primesLE]
    refine ⟨?_, hp⟩
    have htpos : 0 < t := by
      apply Nat.pos_of_mul_pos_left (a := p)
      rw [← hpt]
      exact hdpos
    calc
      p ≤ p * t := Nat.le_mul_of_pos_right p htpos
      _ = d := hpt.symm
      _ ≤ M := hdM
  · rcases hbal with ⟨u, v, huv, hu, hv⟩
    exact Or.inr ⟨(u, v), hu, hv, huv⟩

/-- A self-compatible core through `N⁶` has at most the prime baseline plus an
explicit `O(N⁵)` error.  This power saving is enough to bound all finite
variational constants uniformly. -/
theorem selfCompatible_card_le_of_le_sixthPower
    {N M : ℕ} (hN : 1 < N) (hMN : M ≤ N ^ 6) (S : Finset ℕ)
    (hS : S ⊆ Finset.Icc 1 M)
    (hcompat : CrossCompatible S S) :
    (S.card : ℝ) ≤
      (Nat.primeCounting M : ℝ) +
        (N ^ 2 + 1 : ℕ) * Real.sqrt (Nat.primeCounting M) +
      ((N ^ 4 + 1 : ℕ) +
        (N ^ 3 + 1 : ℕ) * Real.sqrt (N ^ 4 + 1 : ℕ)) := by
  classical
  let L := S.filter (HasLargePrimeEncoding N M)
  let B := S.filter fun d => ¬HasLargePrimeEncoding N M d
  have hpart : L.card + B.card = S.card := by
    dsimp [L, B]
    exact Finset.card_filter_add_card_filter_not
      (s := S) (HasLargePrimeEncoding N M)
  let wL : ↥L → ℕ × ℕ := fun z => Classical.choose
    (Finset.mem_filter.mp z.property).2
  have hwL : ∀ z : ↥L,
      (wL z).1 ∈ Nat.primesLE M ∧
      (wL z).2 ≤ N ^ 2 ∧ z.1 = (wL z).1 * (wL z).2 := by
    intro z
    exact Classical.choose_spec (Finset.mem_filter.mp z.property).2
  let encL : ↥L → ↥(Nat.primesLE M) × Fin (N ^ 2 + 1) := fun z =>
    (⟨(wL z).1, (hwL z).1⟩,
      ⟨(wL z).2, by have := (hwL z).2.1; omega⟩)
  have hLmem : ∀ z : ↥L, z.1 ∈ S := by
    intro z
    exact (Finset.mem_filter.mp z.property).1
  have hLrecon : ∀ z : ↥L,
      ((encL z).1 : ℕ) * ((encL z).2 : ℕ) = z.1 := by
    intro z
    exact (hwL z).2.2.symm
  have hL := factorEncoding_card_le
    (X := ↥(Nat.primesLE M)) (Y := Fin (N ^ 2 + 1))
    S hcompat (fun z : ↥L => z.1) Subtype.val_injective hLmem
    encL (fun z => z.1) (fun z => z.1) hLrecon
  have hL' : (L.card : ℝ) ≤
      (Nat.primeCounting M : ℝ) +
        (N ^ 2 + 1 : ℕ) * Real.sqrt (Nat.primeCounting M) := by
    simpa [Nat.primesLE_card_eq_primeCounting] using hL
  have hBbal : ∀ z : ↥B, HasBalancedEncoding N z.1 := by
    intro z
    have hz := Finset.mem_filter.mp z.property
    have hzI := Finset.mem_Icc.mp (hS hz.1)
    rcases largePrimeEncoding_or_balanced hN hzI.1 hzI.2 hMN with hlarge | hbal
    · exact (hz.2 hlarge).elim
    · exact hbal
  let wB : ↥B → ℕ × ℕ := fun z => Classical.choose (hBbal z)
  have hwB : ∀ z : ↥B,
      (wB z).1 ≤ N ^ 4 ∧ (wB z).2 ≤ N ^ 3 ∧
      z.1 = (wB z).1 * (wB z).2 := by
    intro z
    exact Classical.choose_spec (hBbal z)
  let encB : ↥B → Fin (N ^ 4 + 1) × Fin (N ^ 3 + 1) := fun z =>
    (⟨(wB z).1, by have := (hwB z).1; omega⟩,
      ⟨(wB z).2, by have := (hwB z).2.1; omega⟩)
  have hBmem : ∀ z : ↥B, z.1 ∈ S := by
    intro z
    exact (Finset.mem_filter.mp z.property).1
  have hBrecon : ∀ z : ↥B,
      ((encB z).1 : ℕ) * ((encB z).2 : ℕ) = z.1 := by
    intro z
    exact (hwB z).2.2.symm
  have hB := factorEncoding_card_le
    (X := Fin (N ^ 4 + 1)) (Y := Fin (N ^ 3 + 1))
    S hcompat (fun z : ↥B => z.1) Subtype.val_injective hBmem
    encB (fun z => z.1) (fun z => z.1) hBrecon
  have hB' : (B.card : ℝ) ≤
      (N ^ 4 + 1 : ℕ) +
        (N ^ 3 + 1 : ℕ) * Real.sqrt (N ^ 4 + 1 : ℕ) := by
    simpa using hB
  have hpartR : (S.card : ℝ) = L.card + B.card := by
    exact_mod_cast hpart.symm
  linarith

/-- Specialization at the exact sixth-power cutoff. -/
theorem selfCompatible_card_le_sixthPower
    {N : ℕ} (hN : 1 < N) (S : Finset ℕ)
    (hS : S ⊆ Finset.Icc 1 (N ^ 6))
    (hcompat : CrossCompatible S S) :
    (S.card : ℝ) ≤
      (Nat.primeCounting (N ^ 6) : ℝ) +
        (N ^ 2 + 1 : ℕ) * Real.sqrt (Nat.primeCounting (N ^ 6)) +
      ((N ^ 4 + 1 : ℕ) +
        (N ^ 3 + 1 : ℕ) * Real.sqrt (N ^ 4 + 1 : ℕ)) :=
  selfCompatible_card_le_of_le_sixthPower hN le_rfl S hS hcompat

end Erdos796
