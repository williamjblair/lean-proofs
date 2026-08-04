import Research.FiniteVanDerWaerden
import Research.EdgeCodeFinset

namespace Erdos123

noncomputable section

/-- The complete-residue edge code contains arithmetic progressions of every
prescribed finite length.  The progression occurs among actual evaluations,
not merely among their residues. -/
theorem edgeCodeEval_arbitrarily_long_progressions {a b c : ℕ}
    (ha : 1 < a) (hb : 1 < b) (hc : 1 < c) (hacLt : a < c)
    (hab : Nat.Coprime a b) (hac : Nat.Coprime a c) (hbc : Nat.Coprime b c)
    (L : ℕ) (hL : 1 < L) :
    ∃ n B d : ℕ, 0 < d ∧
      ∃ words : Fin L → (Fin n → Fin c),
        ∀ r : Fin L,
          edgeCodeEval a b c n (words r) = B + (r : ℕ) * d := by
  let A := edgeDigitMass a b c
  rcases finite_van_der_waerden (A + 1) L hL with ⟨N, hN, hvdw⟩
  rcases pow_unbounded_of_one_lt N hc with ⟨n, hnStrict⟩
  have hn : N ≤ c ^ n := hnStrict.le
  let Q := c ^ n
  have hQ : 0 < Q := by
    dsimp [Q]
    positivity
  let residueMap : (Fin n → Fin c) → Fin Q := fun w =>
    ⟨edgeCodeEval a b c n w % Q, Nat.mod_lt _ hQ⟩
  have hresInj : Function.Injective residueMap := by
    intro u v huv
    apply edgeCodeEval_mod_injective hc hac.symm hbc.symm
    exact congrArg Fin.val huv
  have hcard : Fintype.card (Fin n → Fin c) = Fintype.card (Fin Q) := by
    simp [Q]
  have hresBij : Function.Bijective residueMap :=
    (Fintype.bijective_iff_injective_and_card residueMap).2 ⟨hresInj, hcard⟩
  let wordFor : Fin Q → (Fin n → Fin c) := fun r => Classical.choose (hresBij.2 r)
  have hwordFor (r : Fin Q) : residueMap (wordFor r) = r := by
    exact Classical.choose_spec (hresBij.2 r)
  have hcarry (r : Fin Q) :
      edgeCodeEval a b c n (wordFor r) / Q ≤ A := by
    apply Nat.div_le_of_le_mul
    have hbound := edgeCodeEval_le_mass_mul_pow (a := a) (b := b) (c := c)
      hacLt (wordFor r)
    simpa [A, Q, Nat.mul_comm] using hbound
  let color : ℕ → Fin (A + 1) := fun x =>
    ⟨edgeCodeEval a b c n (wordFor ⟨x % Q, Nat.mod_lt _ hQ⟩) / Q,
      by have := hcarry ⟨x % Q, Nat.mod_lt _ hQ⟩; omega⟩
  rcases hvdw color with ⟨b0, d, hd, hlast, hmono⟩
  have hquery (r : Fin L) : b0 + (r : ℕ) * d < Q := by
    have hrle : (r : ℕ) ≤ L - 1 := by omega
    have hle : b0 + (r : ℕ) * d ≤ b0 + (L - 1) * d :=
      Nat.add_le_add_left (Nat.mul_le_mul_right d hrle) b0
    exact hle.trans_lt (hlast.trans_le hn)
  let words : Fin L → (Fin n → Fin c) := fun r =>
    wordFor ⟨b0 + (r : ℕ) * d, hquery r⟩
  let zero : Fin L := ⟨0, by omega⟩
  have hcarryEq (r : Fin L) :
      edgeCodeEval a b c n (words r) / Q =
        edgeCodeEval a b c n (words zero) / Q := by
    have hcEq : color (b0 + (r : ℕ) * d) = color b0 := hmono r
    have hbQ : b0 < Q := by
      have hz := hquery zero
      simpa [zero] using hz
    simpa [color, words, zero, Nat.mod_eq_of_lt (hquery r),
      Nat.mod_eq_of_lt hbQ] using congrArg Fin.val hcEq
  have hresidue (r : Fin L) :
      edgeCodeEval a b c n (words r) % Q = b0 + (r : ℕ) * d := by
    have hw := congrArg Fin.val (hwordFor ⟨b0 + (r : ℕ) * d, hquery r⟩)
    exact hw
  let B := edgeCodeEval a b c n (words zero)
  refine ⟨n, B, d, hd, words, ?_⟩
  intro r
  have hdecomp := Nat.mod_add_div (edgeCodeEval a b c n (words r)) Q
  have hdecomp0 := Nat.mod_add_div (edgeCodeEval a b c n (words zero)) Q
  rw [hresidue r, hcarryEq r] at hdecomp
  have hzero : (zero : ℕ) = 0 := rfl
  rw [hresidue zero, hzero, Nat.zero_mul, Nat.add_zero] at hdecomp0
  dsimp [B]
  omega

/-- The arithmetic progressions above are realized by genuine primitive
subsets of one common homogeneous level. -/
theorem primitive_homogeneous_arbitrarily_long_progressions {a b c : ℕ}
    (ha : 1 < a) (hb : 1 < b) (hc : 1 < c) (hacLt : a < c)
    (hab : Nat.Coprime a b) (hac : Nat.Coprime a c) (hbc : Nat.Coprime b c)
    (L : ℕ) (hL : 1 < L) :
    ∃ n B d : ℕ, 0 < d ∧
      ∃ sets : Fin L → Finset ℕ,
        (∀ r x, x ∈ sets r → x ∈ Smooth3 a b c) ∧
        (∀ r, IsPrimitive (sets r)) ∧
        (∀ r : Fin L, (sets r).sum id = B + (r : ℕ) * d) := by
  rcases edgeCodeEval_arbitrarily_long_progressions ha hb hc hacLt hab hac hbc L hL with
    ⟨n, B, d, hd, words, hwords⟩
  let sets : Fin L → Finset ℕ := fun r => edgeCodeFinset a b c n (words r)
  refine ⟨n, B, d, hd, sets, ?_, ?_, ?_⟩
  · intro r x hx
    exact edgeCodeFinset_subset_smooth3 (words r) x hx
  · intro r
    exact edgeCodeFinset_isPrimitive ha hb hc hab hac hbc (words r)
  · intro r
    rw [show sets r = edgeCodeFinset a b c n (words r) by rfl,
      edgeCodeFinset_sum ha hb hc hab hac hbc (words r), hwords r]

end

end Erdos123
