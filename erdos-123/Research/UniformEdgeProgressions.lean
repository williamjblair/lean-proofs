import Research.EdgeCodeProgressions

namespace Erdos123

noncomputable section

/-- For a fixed requested length, the progression step can be chosen from one
fixed finite range at every sufficiently deep edge-code level. -/
theorem edgeCodeEval_uniform_bounded_step_progressions {a b c : ℕ}
    (ha : 1 < a) (hb : 1 < b) (hc : 1 < c) (hacLt : a < c)
    (hab : Nat.Coprime a b) (hac : Nat.Coprime a c) (hbc : Nat.Coprime b c)
    (L : ℕ) (hL : 1 < L) :
    ∃ N : ℕ, 0 < N ∧ ∀ n : ℕ, N ≤ c ^ n →
      ∃ B d : ℕ, 0 < d ∧ d < N ∧
        ∃ words : Fin L → (Fin n → Fin c),
          ∀ r : Fin L,
            edgeCodeEval a b c n (words r) = B + (r : ℕ) * d := by
  let A := edgeDigitMass a b c
  rcases finite_van_der_waerden (A + 1) L hL with ⟨N, hN, hvdw⟩
  refine ⟨N, hN, ?_⟩
  intro n hn
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
  have hdN : d < N := by
    have hLd : d ≤ (L - 1) * d := by
      have : 1 ≤ L - 1 := by omega
      nlinarith
    omega
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
  refine ⟨B, d, hd, hdN, words, ?_⟩
  intro r
  have hdecomp := Nat.mod_add_div (edgeCodeEval a b c n (words r)) Q
  have hdecomp0 := Nat.mod_add_div (edgeCodeEval a b c n (words zero)) Q
  rw [hresidue r, hcarryEq r] at hdecomp
  have hzero : (zero : ℕ) = 0 := rfl
  rw [hresidue zero, hzero, Nat.zero_mul, Nat.add_zero] at hdecomp0
  dsimp [B]
  omega

/-- Uniform bounded-step progressions transferred to actual primitive smooth
finsets. -/
theorem primitive_uniform_bounded_step_progressions {a b c : ℕ}
    (ha : 1 < a) (hb : 1 < b) (hc : 1 < c) (hacLt : a < c)
    (hab : Nat.Coprime a b) (hac : Nat.Coprime a c) (hbc : Nat.Coprime b c)
    (L : ℕ) (hL : 1 < L) :
    ∃ N : ℕ, 0 < N ∧ ∀ n : ℕ, N ≤ c ^ n →
      ∃ B d : ℕ, 0 < d ∧ d < N ∧
        ∃ sets : Fin L → Finset ℕ,
          (∀ r x, x ∈ sets r → x ∈ Smooth3 a b c) ∧
          (∀ r, IsPrimitive (sets r)) ∧
          (∀ r : Fin L, (sets r).sum id = B + (r : ℕ) * d) := by
  rcases edgeCodeEval_uniform_bounded_step_progressions
      ha hb hc hacLt hab hac hbc L hL with ⟨N, hN, hdeep⟩
  refine ⟨N, hN, ?_⟩
  intro n hn
  rcases hdeep n hn with ⟨B, d, hd, hdN, words, hwords⟩
  let sets : Fin L → Finset ℕ := fun r => edgeCodeFinset a b c n (words r)
  refine ⟨B, d, hd, hdN, sets, ?_, ?_, ?_⟩
  · intro r x hx
    exact edgeCodeFinset_subset_smooth3 (words r) x hx
  · intro r
    exact edgeCodeFinset_isPrimitive ha hb hc hab hac hbc (words r)
  · intro r
    rw [show sets r = edgeCodeFinset a b c n (words r) by rfl,
      edgeCodeFinset_sum ha hb hc hab hac hbc (words r), hwords r]

/-- For each fixed length, one positive numerical step recurs at infinitely
many (indeed, arbitrarily deep) homogeneous code levels. -/
theorem edgeCode_fixed_step_recurs_infinitely_often {a b c : ℕ}
    (ha : 1 < a) (hb : 1 < b) (hc : 1 < c) (hacLt : a < c)
    (hab : Nat.Coprime a b) (hac : Nat.Coprime a c) (hbc : Nat.Coprime b c)
    (L : ℕ) (hL : 1 < L) :
    ∃ n₀ d : ℕ, 0 < d ∧
      Set.Infinite {k : ℕ | ∃ B : ℕ,
        ∃ words : Fin L → (Fin (n₀ + k) → Fin c),
          ∀ r : Fin L,
            edgeCodeEval a b c (n₀ + k) (words r) = B + (r : ℕ) * d} := by
  rcases edgeCodeEval_uniform_bounded_step_progressions
      ha hb hc hacLt hab hac hbc L hL with ⟨N, hN, hdeep⟩
  rcases pow_unbounded_of_one_lt N hc with ⟨n₀, hn₀Strict⟩
  have hn₀ : N ≤ c ^ n₀ := hn₀Strict.le
  let Good : ℕ → Fin N → Prop := fun k q =>
    0 < (q : ℕ) ∧ ∃ B : ℕ,
      ∃ words : Fin L → (Fin (n₀ + k) → Fin c),
        ∀ r : Fin L,
          edgeCodeEval a b c (n₀ + k) (words r) =
            B + (r : ℕ) * (q : ℕ)
  have hex (k : ℕ) : ∃ q : Fin N, Good k q := by
    have hpow : N ≤ c ^ (n₀ + k) := by
      apply hn₀.trans
      exact Nat.pow_le_pow_right (by omega) (Nat.le_add_right n₀ k)
    rcases hdeep (n₀ + k) hpow with ⟨B, d, hd, hdN, words, hwords⟩
    exact ⟨⟨d, hdN⟩, hd, B, words, hwords⟩
  let step : ℕ → Fin N := fun k => Classical.choose (hex k)
  have hstep (k : ℕ) : Good k (step k) := Classical.choose_spec (hex k)
  obtain ⟨q, hq⟩ := Finite.exists_infinite_fiber step
  have hqSet : Set.Infinite (step ⁻¹' ({q} : Set (Fin N))) :=
    Set.infinite_coe_iff.mp hq
  have hfiberSub : step ⁻¹' ({q} : Set (Fin N)) ⊆ {k | Good k q} := by
    intro k hk
    have heq : step k = q := hk
    simpa [heq] using hstep k
  have hgoodInf : Set.Infinite {k | Good k q} := hqSet.mono hfiberSub
  have hnonempty : (step ⁻¹' ({q} : Set (Fin N))).Nonempty := hqSet.nonempty
  rcases hnonempty with ⟨k, hk⟩
  have hkq : step k = q := hk
  have hqd : 0 < (q : ℕ) := by
    rw [← hkq]
    exact (hstep k).1
  refine ⟨n₀, q, hqd, ?_⟩
  simpa [Good, hqd] using hgoodInf

end

end Erdos123
