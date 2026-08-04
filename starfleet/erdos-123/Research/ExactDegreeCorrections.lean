import Research.HomogeneousResidueSystem

namespace Erdos123

set_option maxHeartbeats 1000000

private theorem period_multiple_from {x d P T : ℕ}
    (h : ∀ k, x ^ (P + k + T) ≡ x ^ (P + k) [MOD d])
    (m k : ℕ) : x ^ (P + k + m * T) ≡ x ^ (P + k) [MOD d] := by
  induction m with
  | zero => simpa using (Nat.ModEq.refl (n := d) (x ^ (P + k)))
  | succ m ih =>
      have hs := h (k + m * T)
      have hs' : x ^ (P + k + (m + 1) * T) ≡
          x ^ (P + k + m * T) [MOD d] := by
        simpa [Nat.succ_mul, add_assoc] using hs
      exact hs'.trans ih

private theorem periodic_split_modEq {x y d P T R D t count : ℕ}
    (hT : 0 < T) (hPR : P ≤ R)
    (hmargin : P + count * T ≤ D - R)
    (hx : ∀ k, x ^ (P + k + T) ≡ x ^ (P + k) [MOD d])
    (hy : ∀ k, y ^ (P + k + T) ≡ y ^ (P + k) [MOD d])
    (ht : t < count) :
    x ^ (R + t * T) * y ^ (D - R - t * T) ≡
      x ^ R * y ^ (D - R) [MOD d] := by
  have hx0 := period_multiple_from hx t (R - P)
  have hRP : P + (R - P) = R := by omega
  have hxEq : x ^ (R + t * T) ≡ x ^ R [MOD d] := by
    simpa [hRP] using hx0
  have htT : t * T ≤ D - R - P := by
    have hm : count * T ≤ D - R - P := by omega
    exact (Nat.mul_le_mul_right T (Nat.le_of_lt ht)).trans hm
  have hlowP : P ≤ D - R - t * T := by omega
  have hyLow := period_multiple_from hy t (D - R - t * T - P)
  have hstart : P + (D - R - t * T - P) = D - R - t * T := by omega
  have hend : D - R - t * T + t * T = D - R := by omega
  have hyEq : y ^ (D - R - t * T) ≡ y ^ (D - R) [MOD d] := by
    simpa [hstart, hend] using hyLow.symm
  exact hxEq.mul hyEq

/-- Asymmetric opposite-face products still have gcd one, with an explicit
integer Bezout identity. -/
theorem asymmetric_face_products_int_bezout {a b c R S : ℕ}
    (hab : Nat.Coprime a b) (hac : Nat.Coprime a c) (hbc : Nat.Coprime b c) :
    ∃ u v w : ℤ,
      u * ((b ^ R * c ^ S : ℕ) : ℤ) +
        v * ((a ^ R * c ^ S : ℕ) : ℤ) +
        w * ((a ^ S * b ^ R : ℕ) : ℤ) = 1 := by
  have hbaPow : Nat.Coprime (b ^ R) (a ^ R) := hab.symm.pow R R
  have hc_ab : Nat.Coprime c (a * b) := hac.symm.mul_right hbc.symm
  have hcPow : Nat.Coprime (c ^ S) (a ^ S * b ^ R) :=
    (hac.symm.pow S S).mul_right (hbc.symm.pow S R)
  let u0 : ℤ := (b ^ R).gcdA (a ^ R)
  let v0 : ℤ := (b ^ R).gcdB (a ^ R)
  let x0 : ℤ := (c ^ S).gcdA (a ^ S * b ^ R)
  let w0 : ℤ := (c ^ S).gcdB (a ^ S * b ^ R)
  have huv : (b ^ R : ℤ) * u0 + (a ^ R : ℤ) * v0 = 1 := by
    have h := Nat.gcd_eq_gcd_ab (b ^ R) (a ^ R)
    rw [hbaPow] at h
    simpa [u0, v0] using h.symm
  have hxw : (c ^ S : ℤ) * x0 + ((a ^ S * b ^ R : ℕ) : ℤ) * w0 = 1 := by
    have h := Nat.gcd_eq_gcd_ab (c ^ S) (a ^ S * b ^ R)
    rw [hcPow] at h
    simpa [x0, w0] using h.symm
  refine ⟨x0 * u0, x0 * v0, w0, ?_⟩
  push_cast
  calc
    x0 * u0 * (b ^ R * c ^ S) + x0 * v0 * (a ^ R * c ^ S) +
        w0 * (a ^ S * b ^ R) =
      x0 * c ^ S * (b ^ R * u0 + a ^ R * v0) +
        (a ^ S * b ^ R) * w0 := by ring
    _ = x0 * c ^ S + (a ^ S * b ^ R) * w0 := by rw [huv]; ring
    _ = (c ^ S : ℤ) * x0 + (a ^ S * b ^ R) * w0 := by ring
    _ = 1 := hxw

/-- On every sufficiently high exact homogeneous degree, every residue has a
primitive face-supported correction. For ordered bases `a≤c<b`, all correction
sums are bounded by one constant times `c^D`. -/
theorem exact_degree_bounded_face_corrections {a b c d : ℕ}
    (ha : 1 < a) (hb : 1 < b) (hc : 1 < c)
    (hacOrder : a ≤ c)
    (hab : Nat.Coprime a b) (hac : Nat.Coprime a c) (hbc : Nat.Coprime b c)
    (hd : 0 < d) :
    ∃ C D₀ : ℕ, 0 < C ∧ ∀ D : ℕ, D₀ ≤ D → ∀ r : ℕ,
      ∃ s : Finset ℕ,
        (∀ z ∈ s, z ∈ Smooth3 a b c) ∧
        (∀ z ∈ s, ∃ i j k : ℕ,
          i + j + k = D ∧ z = eval3 a b c i j k ∧
          (i = 0 ∨ j = 0 ∨ k = 0)) ∧
        IsPrimitive s ∧ s.sum id ≡ r [MOD d] ∧ s.sum id ≤ C * c ^ D := by
  obtain ⟨P, T, hP, hT, hpa, hpb, hpc⟩ := exists_common_pow_period a b c d hd
  let R := P + d * T
  let E := R + d * T
  let C := 3 * d * b ^ E
  let D₀ := R + (P + d * T)
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, D₀, hC, ?_⟩
  intro D hD r
  have hmargin : P + d * T ≤ D - R := by
    dsimp [D₀] at hD
    omega
  let S := D - R
  obtain ⟨u, v, w, hbez⟩ := asymmetric_face_products_int_bezout
    (R := R) (S := S) hab hac hbc
  obtain ⟨ni, nj, nk, hni, hnj, hnk, hcombo⟩ :=
    bounded_residue_combo_of_int_bezout hd hbez r
  let I := Fin ni ⊕ (Fin nj ⊕ Fin nk)
  let expo : I → ℕ × ℕ × ℕ := fun z => match z with
    | Sum.inl t => (0, R + (t : ℕ) * T, D - R - (t : ℕ) * T)
    | Sum.inr (Sum.inl t) => (R + (t : ℕ) * T, 0, D - R - (t : ℕ) * T)
    | Sum.inr (Sum.inr t) => (D - R - (t : ℕ) * T, R + (t : ℕ) * T, 0)
  let term : I → ℕ := fun z =>
    eval3 a b c (expo z).1 (expo z).2.1 (expo z).2.2
  let tagBase : I → ℕ := fun z => match z with
    | Sum.inl _ => b ^ R * c ^ S
    | Sum.inr (Sum.inl _) => a ^ R * c ^ S
    | Sum.inr (Sum.inr _) => a ^ S * b ^ R
  have hindex_lt : ∀ z : I, match z with
      | Sum.inl t => (t : ℕ) < d
      | Sum.inr (Sum.inl t) => (t : ℕ) < d
      | Sum.inr (Sum.inr t) => (t : ℕ) < d := by
    intro z
    cases z with
    | inl t => exact t.isLt.trans hni
    | inr z => cases z with
      | inl t => exact t.isLt.trans hnj
      | inr t => exact t.isLt.trans hnk
  have hlow_pos (t : ℕ) (ht : t < d) : 0 < D - R - t * T := by
    have hm : P + d * T ≤ D - R := hmargin
    have htT := Nat.mul_le_mul_right T (Nat.le_of_lt ht)
    omega
  have hexpo_degree (z : I) :
      (expo z).1 + (expo z).2.1 + (expo z).2.2 = D := by
    have hz := hindex_lt z
    cases z with
    | inl t =>
      simp only [expo]
      have ht := Nat.mul_le_mul_right T (Nat.le_of_lt hz)
      omega
    | inr z => cases z with
      | inl t =>
        simp only [expo]
        have ht := Nat.mul_le_mul_right T (Nat.le_of_lt hz)
        omega
      | inr t =>
        simp only [expo]
        have ht := Nat.mul_le_mul_right T (Nat.le_of_lt hz)
        omega
  have heval_inj : Function.Injective (fun p : ℕ × ℕ × ℕ =>
      eval3 a b c p.1 p.2.1 p.2.2) := by
    intro p q hpq
    change eval3 a b c p.1 p.2.1 p.2.2 =
      eval3 a b c q.1 q.2.1 q.2.2 at hpq
    have h1 : eval3 a b c p.1 p.2.1 p.2.2 ∣
        eval3 a b c q.1 q.2.1 q.2.2 := by rw [hpq]
    have h2 : eval3 a b c q.1 q.2.1 q.2.2 ∣
        eval3 a b c p.1 p.2.1 p.2.2 := by rw [hpq]
    have hle := (eval3_dvd_iff ha hb hc hab hac hbc).mp h1
    have hge := (eval3_dvd_iff ha hb hc hab hac hbc).mp h2
    apply Prod.ext
    · omega
    · apply Prod.ext <;> omega
  have hexpo_inj : Function.Injective expo := by
    intro z z' hzz'
    have hz := hindex_lt z
    have hz' := hindex_lt z'
    cases z with
    | inl t => cases z' with
      | inl t' =>
        simp only [expo, Prod.mk.injEq] at hzz'
        have hm : (t : ℕ) * T = (t' : ℕ) * T := by omega
        have htt : t = t' := Fin.ext (Nat.eq_of_mul_eq_mul_right hT hm)
        exact congrArg (fun q : Fin ni => (Sum.inl q : I)) htt
      | inr z' => cases z' with
        | inl t' =>
          exfalso
          simp only [expo, Prod.mk.injEq] at hzz'
          have hp := hlow_pos (t' : ℕ) hz'
          omega
        | inr t' =>
          exfalso
          simp only [expo, Prod.mk.injEq] at hzz'
          have hp := hlow_pos (t' : ℕ) hz'
          omega
    | inr z => cases z with
      | inl t => cases z' with
        | inl t' =>
          exfalso
          simp only [expo, Prod.mk.injEq] at hzz'
          have hp := hlow_pos (t : ℕ) hz
          omega
        | inr z' => cases z' with
          | inl t' =>
            simp only [expo, Prod.mk.injEq] at hzz'
            have hm : (t : ℕ) * T = (t' : ℕ) * T := by omega
            have htt : t = t' := Fin.ext (Nat.eq_of_mul_eq_mul_right hT hm)
            exact congrArg (fun q : Fin nj => (Sum.inr (Sum.inl q) : I)) htt
          | inr t' =>
            exfalso
            simp only [expo, Prod.mk.injEq] at hzz'
            have hp := hlow_pos (t' : ℕ) hz'
            omega
      | inr t => cases z' with
        | inl t' =>
          exfalso
          simp only [expo, Prod.mk.injEq] at hzz'
          have hp := hlow_pos (t : ℕ) hz
          omega
        | inr z' => cases z' with
          | inl t' =>
            exfalso
            simp only [expo, Prod.mk.injEq] at hzz'
            have hp := hlow_pos (t : ℕ) hz
            omega
          | inr t' =>
            simp only [expo, Prod.mk.injEq] at hzz'
            have hm : (t : ℕ) * T = (t' : ℕ) * T := by omega
            have htt : t = t' := Fin.ext (Nat.eq_of_mul_eq_mul_right hT hm)
            exact congrArg (fun q : Fin nk => (Sum.inr (Sum.inr q) : I)) htt
  have hterm_inj : Function.Injective term := fun _ _ h => hexpo_inj (heval_inj h)
  let s : Finset ℕ := Finset.univ.image term
  refine ⟨s, ?_, ?_, ?_, ?_, ?_⟩
  · intro z hz
    rcases Finset.mem_image.mp hz with ⟨idx, _hidx, rfl⟩
    exact ⟨(expo idx).1, (expo idx).2.1, (expo idx).2.2, rfl⟩
  · intro z hz
    rcases Finset.mem_image.mp hz with ⟨idx, _hidx, rfl⟩
    refine ⟨(expo idx).1, (expo idx).2.1, (expo idx).2.2,
      hexpo_degree idx, rfl, ?_⟩
    cases idx with
    | inl t => exact Or.inl rfl
    | inr idx => cases idx with
      | inl t => exact Or.inr (Or.inl rfl)
      | inr t => exact Or.inr (Or.inr rfl)
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
        dsimp [term, expo, tagBase, S, eval3]
        simp only [pow_zero, one_mul]
        exact periodic_split_modEq hT (by dsimp [R]; omega) hmargin hpb hpc hi
      | inr idx => cases idx with
        | inl t =>
          dsimp [term, expo, tagBase, S, eval3]
          simp only [pow_zero, mul_one]
          exact periodic_split_modEq hT (by dsimp [R]; omega) hmargin hpa hpc hi
        | inr t =>
          dsimp [term, expo, tagBase, S, eval3]
          simp only [pow_zero, mul_one]
          simpa [Nat.mul_comm] using
            (periodic_split_modEq hT (by dsimp [R]; omega) hmargin hpb hpa hi)
    have hsumImage : s.sum id = ∑ idx : I, term idx := by
      change (Finset.univ.image term).sum id = ∑ idx : I, term idx
      rw [Finset.sum_image]
      · rfl
      · intro x _hx y _hy hxy
        exact hterm_inj hxy
    rw [hsumImage]
    have hsum : (∑ idx : I, term idx) ≡ (∑ idx : I, tagBase idx) [MOD d] :=
      Nat.ModEq.sum (s := Finset.univ) (fun idx _ => htermMod idx)
    have htag : (∑ idx : I, tagBase idx) =
        ni * (b ^ R * c ^ S) + nj * (a ^ R * c ^ S) +
          nk * (a ^ S * b ^ R) := by
      change (∑ idx : Fin ni ⊕ (Fin nj ⊕ Fin nk),
        match idx with
        | Sum.inl _ => b ^ R * c ^ S
        | Sum.inr (Sum.inl _) => a ^ R * c ^ S
        | Sum.inr (Sum.inr _) => a ^ S * b ^ R) = _
      rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
      simp only [Fin.sum_const, nsmul_eq_mul]
      ac_rfl
    rw [htag] at hsum
    exact hsum.trans hcombo
  · have hcard : s.card ≤ 3 * d := by
      calc
        s.card ≤ Fintype.card I := by
          dsimp [s]
          exact (Finset.card_image_le.trans_eq (Finset.card_univ))
        _ = ni + nj + nk := by simp [I, Nat.add_assoc]
        _ ≤ 3 * d := by omega
    have htermBound : ∀ z ∈ s, z ≤ b ^ E * c ^ D := by
      intro z hz
      rcases Finset.mem_image.mp hz with ⟨idx, _hidx, rfl⟩
      have hi := hindex_lt idx
      cases idx with
      | inl t =>
        have hhigh : R + (t : ℕ) * T ≤ E := by
          dsimp [E]
          have hm := Nat.mul_le_mul_right T (Nat.le_of_lt hi)
          omega
        dsimp [term, expo, eval3]
        simp only [pow_zero, one_mul]
        have hbpow := Nat.pow_le_pow_right (by omega : 0 < b) hhigh
        have hcpow : c ^ (D - R - (t : ℕ) * T) ≤ c ^ D :=
          Nat.pow_le_pow_right (by omega) (by omega)
        exact Nat.mul_le_mul hbpow hcpow
      | inr idx => cases idx with
        | inl t =>
          have hhigh : R + (t : ℕ) * T ≤ E := by
            dsimp [E]
            have hm := Nat.mul_le_mul_right T (Nat.le_of_lt hi)
            omega
          dsimp [term, expo, eval3]
          simp only [pow_zero, mul_one]
          have hapow : a ^ (R + (t : ℕ) * T) ≤ c ^ (R + (t : ℕ) * T) :=
            Nat.pow_le_pow_left hacOrder _
          have hprod : a ^ (R + (t : ℕ) * T) *
              c ^ (D - R - (t : ℕ) * T) ≤ c ^ D := by
            calc
              _ ≤ c ^ (R + (t : ℕ) * T) *
                  c ^ (D - R - (t : ℕ) * T) :=
                Nat.mul_le_mul_right _ hapow
              _ = c ^ D := by rw [← pow_add]; congr 1; omega
          exact hprod.trans (Nat.le_mul_of_pos_left _ (pow_pos (by omega) E))
        | inr t =>
          have hhigh : R + (t : ℕ) * T ≤ E := by
            dsimp [E]
            have hm := Nat.mul_le_mul_right T (Nat.le_of_lt hi)
            omega
          dsimp [term, expo, eval3]
          simp only [pow_zero, mul_one]
          have hapow : a ^ (D - R - (t : ℕ) * T) ≤
              c ^ (D - R - (t : ℕ) * T) := Nat.pow_le_pow_left hacOrder _
          have hbpow := Nat.pow_le_pow_right (by omega : 0 < b) hhigh
          calc
            a ^ (D - R - (t : ℕ) * T) * b ^ (R + (t : ℕ) * T) ≤
                c ^ D * b ^ E := Nat.mul_le_mul
                  (hapow.trans (Nat.pow_le_pow_right (by omega) (by omega))) hbpow
            _ = b ^ E * c ^ D := by ac_rfl
    have hsumBound := Finset.sum_le_card_nsmul s id (b ^ E * c ^ D)
      (by simpa only [id_eq] using htermBound)
    calc
      s.sum id ≤ s.card * (b ^ E * c ^ D) := by simpa using hsumBound
      _ ≤ (3 * d) * (b ^ E * c ^ D) :=
        Nat.mul_le_mul_right _ hcard
      _ = C * c ^ D := by dsimp [C]; ring

end Erdos123
