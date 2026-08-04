import Research.HomogeneousLevel
import Research.Definitions

namespace Erdos123

set_option maxHeartbeats 1000000

private theorem exists_eventual_pow_period (x d : ℕ) (hd : 0 < d) :
    ∃ P T : ℕ, 0 < T ∧ ∀ k : ℕ,
      x ^ (P + k + T) ≡ x ^ (P + k) [MOD d] := by
  let f : Fin (d + 1) → Fin d := fun i => ⟨x ^ (i : ℕ) % d, Nat.mod_lt _ hd⟩
  obtain ⟨u, v, huv, heq⟩ := Fintype.exists_ne_map_eq_of_card_lt f (by simp)
  wlog huvlt : (u : ℕ) < (v : ℕ) generalizing u v
  · have hvult : (v : ℕ) < (u : ℕ) := by
      exact lt_of_le_of_ne (Nat.le_of_not_gt huvlt) (by
        intro h
        apply huv
        exact Fin.ext h.symm)
    exact this v u huv.symm heq.symm hvult
  let P := (u : ℕ)
  let T := (v : ℕ) - (u : ℕ)
  have hT : 0 < T := by dsimp [T]; omega
  refine ⟨P, T, hT, ?_⟩
  intro k
  have hbase : x ^ (u : ℕ) ≡ x ^ (v : ℕ) [MOD d] := by
    exact congrArg Fin.val heq
  have hmul := hbase.mul_right (x ^ k)
  have hv : (v : ℕ) = P + T := by dsimp [P, T]; omega
  simpa [P, hv, pow_add, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hmul.symm

private theorem pow_period_multiple {x d P T : ℕ} (hT : 0 < T)
    (h : ∀ k : ℕ, x ^ (P + k + T) ≡ x ^ (P + k) [MOD d])
    (m k : ℕ) : x ^ (P + k + m * T) ≡ x ^ (P + k) [MOD d] := by
  induction m with
  | zero => simpa using (Nat.ModEq.refl (n := d) (x ^ (P + k)))
  | succ m ih =>
      have hstep := h (k + m * T)
      have hstep' : x ^ (P + k + (m + 1) * T) ≡
          x ^ (P + k + m * T) [MOD d] := by
        simpa [Nat.succ_mul, add_assoc] using hstep
      exact hstep'.trans ih

private theorem pow_period_shift {x d P T P' : ℕ} (hPP : P ≤ P') (hT : 0 < T)
    (h : ∀ k : ℕ, x ^ (P + k + T) ≡ x ^ (P + k) [MOD d])
    (m k : ℕ) : x ^ (P' + k + m * T) ≡ x ^ (P' + k) [MOD d] := by
  have hs := pow_period_multiple hT h m (P' - P + k)
  have hcancel : P + (P' - P + k) = P' + k := by omega
  simpa [hcancel] using hs

/-- Three arbitrary bases have a common positive eventual exponent period
modulo every positive modulus. No coprimality with the modulus is needed. -/
theorem exists_common_pow_period (a b c d : ℕ) (hd : 0 < d) :
    ∃ P T : ℕ, 0 < P ∧ 0 < T ∧
      (∀ k, a ^ (P + k + T) ≡ a ^ (P + k) [MOD d]) ∧
      (∀ k, b ^ (P + k + T) ≡ b ^ (P + k) [MOD d]) ∧
      (∀ k, c ^ (P + k + T) ≡ c ^ (P + k) [MOD d]) := by
  obtain ⟨Pa, Ta, hTa, ha⟩ := exists_eventual_pow_period a d hd
  obtain ⟨Pb, Tb, hTb, hb⟩ := exists_eventual_pow_period b d hd
  obtain ⟨Pc, Tc, hTc, hc⟩ := exists_eventual_pow_period c d hd
  let P := Pa + Pb + Pc + 1
  let T := Ta * Tb * Tc
  have hP : 0 < P := by dsimp [P]; omega
  have hT : 0 < T := by dsimp [T]; positivity
  refine ⟨P, T, hP, hT, ?_, ?_, ?_⟩
  · intro k
    have h := pow_period_shift (P' := P) (by dsimp [P]; omega) hTa ha (Tb * Tc) k
    simpa [T, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using h
  · intro k
    have h := pow_period_shift (P' := P) (by dsimp [P]; omega) hTb hb (Ta * Tc) k
    simpa [T, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using h
  · intro k
    have h := pow_period_shift (P' := P) (by dsimp [P]; omega) hTc hc (Ta * Tb) k
    simpa [T, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using h


private theorem periodic_face_term_modEq {x y d P T D t : ℕ}
    (hT : 0 < T)
    (hx : ∀ k, x ^ (P + k + T) ≡ x ^ (P + k) [MOD d])
    (hy : ∀ k, y ^ (P + k + T) ≡ y ^ (P + k) [MOD d])
    (ht : t < D) :
    x ^ (P + D * T + t * T) * y ^ (P + D * T - t * T) ≡
      (x * y) ^ (P + D * T) [MOD d] := by
  have hxHigh := pow_period_multiple hT hx (D + t) 0
  have hxMid := pow_period_multiple hT hx D 0
  have hyLow := pow_period_multiple hT hy (D - t) 0
  have hyMid := pow_period_multiple hT hy D 0
  have hlow : P + D * T - t * T = P + (D - t) * T := by
    have htle : t ≤ D := Nat.le_of_lt ht
    rw [Nat.add_sub_assoc (Nat.mul_le_mul_right T htle),
      Nat.mul_sub_right_distrib]
  have hxEq : x ^ (P + D * T + t * T) ≡ x ^ (P + D * T) [MOD d] := by
    have he : P + (D + t) * T = P + D * T + t * T := by ring
    simpa [he] using hxHigh.trans hxMid.symm
  have hyEq : y ^ (P + D * T - t * T) ≡ y ^ (P + D * T) [MOD d] := by
    rw [hlow]
    exact hyLow.trans hyMid.symm
  simpa [mul_pow] using hxEq.mul hyEq

/-- The three opposite-face monomials `(bc)^K,(ac)^K,(ab)^K` have an
explicit integer Bezout combination equal to one. -/
theorem face_products_int_bezout {a b c K : ℕ}
    (hab : Nat.Coprime a b) (hac : Nat.Coprime a c) (hbc : Nat.Coprime b c) :
    ∃ u v w : ℤ,
      u * ((b * c : ℕ) ^ K : ℤ) + v * ((a * c : ℕ) ^ K : ℤ) +
        w * ((a * b : ℕ) ^ K : ℤ) = 1 := by
  have hbaPow : Nat.Coprime (b ^ K) (a ^ K) := hab.symm.pow K K
  have hc_ab : Nat.Coprime c (a * b) := hac.symm.mul_right hbc.symm
  have hcPow : Nat.Coprime (c ^ K) ((a * b) ^ K) := hc_ab.pow K K
  let u0 : ℤ := (b ^ K).gcdA (a ^ K)
  let v0 : ℤ := (b ^ K).gcdB (a ^ K)
  let x0 : ℤ := (c ^ K).gcdA ((a * b) ^ K)
  let w0 : ℤ := (c ^ K).gcdB ((a * b) ^ K)
  have huv : (b ^ K : ℤ) * u0 + (a ^ K : ℤ) * v0 = 1 := by
    have h := Nat.gcd_eq_gcd_ab (b ^ K) (a ^ K)
    rw [hbaPow] at h
    simpa [u0, v0] using h.symm
  have hxw : (c ^ K : ℤ) * x0 + ((a * b) ^ K : ℤ) * w0 = 1 := by
    have h := Nat.gcd_eq_gcd_ab (c ^ K) ((a * b) ^ K)
    rw [hcPow] at h
    simpa [x0, w0] using h.symm
  refine ⟨x0 * u0, x0 * v0, w0, ?_⟩
  push_cast
  rw [mul_pow, mul_pow, mul_pow]
  calc
    x0 * u0 * (b ^ K * c ^ K) + x0 * v0 * (a ^ K * c ^ K) +
        w0 * (a ^ K * b ^ K) =
      x0 * c ^ K * (b ^ K * u0 + a ^ K * v0) +
        (a * b) ^ K * w0 := by ring
    _ = x0 * c ^ K + (a * b) ^ K * w0 := by rw [huv]; ring
    _ = 1 := by linarith [hxw]

/-- An integer Bezout combination gives bounded nonnegative coefficients
realizing every residue modulo a positive modulus. -/
theorem bounded_residue_combo_of_int_bezout {g₁ g₂ g₃ d : ℕ} (hd : 0 < d)
    {u v w : ℤ}
    (hbez : u * (g₁ : ℤ) + v * (g₂ : ℤ) + w * (g₃ : ℤ) = 1)
    (r : ℕ) :
    ∃ i j k : ℕ, i < d ∧ j < d ∧ k < d ∧
      i * g₁ + j * g₂ + k * g₃ ≡ r [MOD d] := by
  letI : NeZero d := ⟨by omega⟩
  let R : ZMod d := r
  let I : ZMod d := R * u
  let J : ZMod d := R * v
  let K : ZMod d := R * w
  refine ⟨I.val, J.val, K.val, ZMod.val_lt I, ZMod.val_lt J, ZMod.val_lt K, ?_⟩
  rw [← ZMod.natCast_eq_natCast_iff]
  push_cast
  rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
  change I * g₁ + J * g₂ + K * g₃ = R
  dsimp [I, J, K, R]
  push_cast at ⊢
  have hbezZ : (u : ZMod d) * g₁ + (v : ZMod d) * g₂ +
      (w : ZMod d) * g₃ = 1 := by
    have hz := congrArg (Int.castRingHom (ZMod d)) hbez
    simpa using hz
  calc
    (r : ZMod d) * u * g₁ + (r : ZMod d) * v * g₂ +
        (r : ZMod d) * w * g₃ =
      (r : ZMod d) * (u * g₁ + v * g₂ + w * g₃) := by ring
    _ = r := by rw [hbezZ]; simp


/-- Every modulus has a complete residue system of subset sums cut from one
homogeneous exponent level. The representatives are primitive automatically. -/
theorem homogeneous_complete_residues {a b c d : ℕ}
    (ha : 1 < a) (hb : 1 < b) (hc : 1 < c)
    (hab : Nat.Coprime a b) (hac : Nat.Coprime a c) (hbc : Nat.Coprime b c)
    (hd : 0 < d) :
    ∃ D : ℕ, ∀ r : ℕ, ∃ s : Finset ℕ,
      (∀ z ∈ s, z ∈ Smooth3 a b c) ∧
      (∀ z ∈ s, ∃ i j k : ℕ, i + j + k = D ∧ z = eval3 a b c i j k) ∧
      IsPrimitive s ∧ s.sum id ≡ r [MOD d] := by
  obtain ⟨P, T, hP, hT, hpa, hpb, hpc⟩ := exists_common_pow_period a b c d hd
  let K := P + d * T
  obtain ⟨u, v, w, hbez⟩ := face_products_int_bezout (K := K) hab hac hbc
  refine ⟨2 * K, ?_⟩
  intro r
  obtain ⟨ni, nj, nk, hni, hnj, hnk, hcombo⟩ :=
    bounded_residue_combo_of_int_bezout hd hbez r
  let I := Fin ni ⊕ (Fin nj ⊕ Fin nk)
  let expo : I → ℕ × ℕ × ℕ := fun z => match z with
    | Sum.inl t => (0, K + (t : ℕ) * T, K - (t : ℕ) * T)
    | Sum.inr (Sum.inl t) => (K + (t : ℕ) * T, 0, K - (t : ℕ) * T)
    | Sum.inr (Sum.inr t) => (K + (t : ℕ) * T, K - (t : ℕ) * T, 0)
  let term : I → ℕ := fun z =>
    eval3 a b c (expo z).1 (expo z).2.1 (expo z).2.2
  let tagBase : I → ℕ := fun z => match z with
    | Sum.inl _ => (b * c) ^ K
    | Sum.inr (Sum.inl _) => (a * c) ^ K
    | Sum.inr (Sum.inr _) => (a * b) ^ K
  have hindex_lt : ∀ z : I, match z with
      | Sum.inl t => (t : ℕ) < d
      | Sum.inr (Sum.inl t) => (t : ℕ) < d
      | Sum.inr (Sum.inr t) => (t : ℕ) < d := by
    intro z
    cases z with
    | inl t => exact t.isLt.trans hni
    | inr z =>
      cases z with
      | inl t => exact t.isLt.trans hnj
      | inr t => exact t.isLt.trans hnk
  have hminus_pos (t : ℕ) (ht : t < d) : 0 < K - t * T := by
    apply Nat.sub_pos_of_lt
    have hmul : t * T < d * T := Nat.mul_lt_mul_of_pos_right ht hT
    dsimp [K]
    omega
  have hexpo_degree (z : I) : (expo z).1 + (expo z).2.1 + (expo z).2.2 = 2 * K := by
    have hz := hindex_lt z
    cases z with
    | inl t =>
      simp only [expo]
      have hle : (t : ℕ) * T ≤ K := by
        have hm := Nat.mul_le_mul_right T (Nat.le_of_lt hz)
        dsimp [K]
        omega
      omega
    | inr z =>
      cases z with
      | inl t =>
        simp only [expo]
        have hle : (t : ℕ) * T ≤ K := by
          have hm := Nat.mul_le_mul_right T (Nat.le_of_lt hz)
          dsimp [K]
          omega
        omega
      | inr t =>
        simp only [expo]
        have hle : (t : ℕ) * T ≤ K := by
          have hm := Nat.mul_le_mul_right T (Nat.le_of_lt hz)
          dsimp [K]
          omega
        omega
  have heval_inj : Function.Injective (fun p : ℕ × ℕ × ℕ =>
      eval3 a b c p.1 p.2.1 p.2.2) := by
    intro p q hpq
    change eval3 a b c p.1 p.2.1 p.2.2 =
      eval3 a b c q.1 q.2.1 q.2.2 at hpq
    have hpqD : eval3 a b c p.1 p.2.1 p.2.2 ∣
        eval3 a b c q.1 q.2.1 q.2.2 := by rw [hpq]
    have hqpD : eval3 a b c q.1 q.2.1 q.2.2 ∣
        eval3 a b c p.1 p.2.1 p.2.2 := by rw [hpq]
    have hle := (eval3_dvd_iff ha hb hc hab hac hbc).mp hpqD
    have hge := (eval3_dvd_iff ha hb hc hab hac hbc).mp hqpD
    apply Prod.ext
    · omega
    · apply Prod.ext <;> omega
  have hexpo_inj : Function.Injective expo := by
    intro z z' hzz'
    have hz := hindex_lt z
    have hz' := hindex_lt z'
    cases z with
    | inl t =>
      cases z' with
      | inl t' =>
        simp only [expo, Prod.mk.injEq] at hzz'
        have hm : (t : ℕ) * T = (t' : ℕ) * T := by omega
        have htt : t = t' := Fin.ext (Nat.eq_of_mul_eq_mul_right hT hm)
        exact congrArg (fun q : Fin ni => (Sum.inl q : I)) htt
      | inr z' =>
        cases z' with
        | inl t' =>
          exfalso
          simp only [expo, Prod.mk.injEq] at hzz'
          have hp := hminus_pos (t' : ℕ) hz'
          omega
        | inr t' =>
          exfalso
          simp only [expo, Prod.mk.injEq] at hzz'
          have hp := hminus_pos (t' : ℕ) hz'
          omega
    | inr z =>
      cases z with
      | inl t =>
        cases z' with
        | inl t' =>
          exfalso
          simp only [expo, Prod.mk.injEq] at hzz'
          have hp := hminus_pos (t : ℕ) hz
          omega
        | inr z' =>
          cases z' with
          | inl t' =>
            simp only [expo, Prod.mk.injEq] at hzz'
            have hm : (t : ℕ) * T = (t' : ℕ) * T := by omega
            have htt : t = t' := Fin.ext (Nat.eq_of_mul_eq_mul_right hT hm)
            exact congrArg (fun q : Fin nj => (Sum.inr (Sum.inl q) : I)) htt
          | inr t' =>
            exfalso
            simp only [expo, Prod.mk.injEq] at hzz'
            have hp := hminus_pos (t' : ℕ) hz'
            omega
      | inr t =>
        cases z' with
        | inl t' =>
          exfalso
          simp only [expo, Prod.mk.injEq] at hzz'
          have hp := hminus_pos (t : ℕ) hz
          omega
        | inr z' =>
          cases z' with
          | inl t' =>
            exfalso
            simp only [expo, Prod.mk.injEq] at hzz'
            have hp := hminus_pos (t : ℕ) hz
            omega
          | inr t' =>
            simp only [expo, Prod.mk.injEq] at hzz'
            have hm : (t : ℕ) * T = (t' : ℕ) * T := by omega
            have htt : t = t' := Fin.ext (Nat.eq_of_mul_eq_mul_right hT hm)
            exact congrArg (fun q : Fin nk => (Sum.inr (Sum.inr q) : I)) htt
  have hterm_inj : Function.Injective term := fun _ _ h =>
    hexpo_inj (heval_inj h)
  let s : Finset ℕ := Finset.univ.image term
  refine ⟨s, ?_, ?_, ?_, ?_⟩
  · intro z hz
    rcases Finset.mem_image.mp hz with ⟨idx, _hidx, rfl⟩
    exact ⟨(expo idx).1, (expo idx).2.1, (expo idx).2.2, rfl⟩
  · intro z hz
    rcases Finset.mem_image.mp hz with ⟨idx, _hidx, rfl⟩
    exact ⟨(expo idx).1, (expo idx).2.1, (expo idx).2.2,
      hexpo_degree idx, rfl⟩
  · intro x hx y hy hxy hdvd
    rcases Finset.mem_image.mp hx with ⟨ix, _hix, rfl⟩
    rcases Finset.mem_image.mp hy with ⟨iy, _hiy, rfl⟩
    apply hxy
    have he := exponents_eq_of_eval3_dvd_of_degree_eq ha hb hc hab hac hbc hdvd
      ((hexpo_degree ix).trans (hexpo_degree iy).symm)
    unfold term
    rw [he.1, he.2.1, he.2.2]
  · have htermMod : ∀ idx : I, term idx ≡ tagBase idx [MOD d] := by
      intro idx
      have hi := hindex_lt idx
      cases idx with
      | inl t =>
        dsimp [term, expo, tagBase, eval3, K]
        simp only [pow_zero, one_mul]
        exact periodic_face_term_modEq hT hpb hpc hi
      | inr idx =>
        cases idx with
        | inl t =>
          dsimp [term, expo, tagBase, eval3, K]
          simp only [pow_zero, mul_one]
          exact periodic_face_term_modEq hT hpa hpc hi
        | inr t =>
          dsimp [term, expo, tagBase, eval3, K]
          simp only [pow_zero, mul_one]
          exact periodic_face_term_modEq hT hpa hpb hi
    have hsumImage : s.sum id = ∑ idx : I, term idx := by
      change (Finset.univ.image term).sum id = ∑ idx : I, term idx
      rw [Finset.sum_image]
      · rfl
      · intro x _hx y _hy hxy
        exact hterm_inj hxy
    rw [hsumImage]
    have hsum : (∑ idx : I, term idx) ≡ (∑ idx : I, tagBase idx) [MOD d] :=
      Nat.ModEq.sum (s := Finset.univ) (fun idx _hidx => htermMod idx)
    have htag : (∑ idx : I, tagBase idx) =
        ni * (b * c) ^ K + nj * (a * c) ^ K + nk * (a * b) ^ K := by
      change (∑ idx : Fin ni ⊕ (Fin nj ⊕ Fin nk),
        match idx with
        | Sum.inl _ => (b * c) ^ K
        | Sum.inr (Sum.inl _) => (a * c) ^ K
        | Sum.inr (Sum.inr _) => (a * b) ^ K) = _
      rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
      simp only [Fin.sum_const, nsmul_eq_mul]
      ac_rfl
    rw [htag] at hsum
    exact hsum.trans hcombo

end Erdos123
