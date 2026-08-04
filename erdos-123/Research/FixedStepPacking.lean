import Research.UniformEdgeProgressions
import Research.InductionStep

namespace Erdos123

noncomputable section

/-- Exponent information for every actual term selected by an edge-code word. -/
theorem edgeCodeFinset_exponent_region {a b c n : ℕ}
    (word : Fin n → Fin c) {x : ℕ} (hx : x ∈ edgeCodeFinset a b c n word) :
    ∃ i j k : ℕ, x = eval3 a b c i j k ∧
      i + j + k = edgeDigitDepth c + n - 1 ∧ j ≤ edgeDigitDepth c := by
  rcases Finset.mem_image.mp hx with ⟨p, hp, rfl⟩
  have hpRange : p.2 < c - 1 := by
    exact Finset.mem_range.mp
      ((Finset.mem_product.mp (Finset.mem_filter.mp hp).1).2)
  refine ⟨edgeCodeDegree c n p.1 - edgeDigitDepth c + c.totient * p.2,
    c.totient * (c - 1 - 1 - p.2), (p.1 : ℕ), rfl,
    edgeCodeTerm_total_degree p.1 hpRange, ?_⟩
  simp only [edgeDigitDepth]
  have hsub : c - 1 - 1 - p.2 ≤ c - 2 := by omega
  exact Nat.mul_le_mul_left c.totient hsub

/-- Multiplication by a positive scalar preserves a primitive finset. -/
theorem scaleFinset_isPrimitive {q : ℕ} (hq : 0 < q) {s : Finset ℕ}
    (hs : IsPrimitive s) : IsPrimitive (scaleFinset q s) := by
  intro x hx y hy hxy hdvd
  rcases Finset.mem_image.mp hx with ⟨u, hu, rfl⟩
  rcases Finset.mem_image.mp hy with ⟨v, hv, rfl⟩
  apply hs hu hv
  · intro huv
    subst v
    exact hxy rfl
  · exact (Nat.mul_dvd_mul_iff_left hq).mp hdvd

/-- Exact sum after scaling a finite set by a positive scalar. -/
theorem scaleFinset_sum {q : ℕ} (hq : 0 < q) (s : Finset ℕ) :
    (scaleFinset q s).sum id = q * s.sum id := by
  unfold scaleFinset
  rw [Finset.sum_image]
  · simpa only [id_eq] using (Finset.mul_sum s id q).symm
  · intro x _hx y _hy hxy
    exact Nat.eq_of_mul_eq_mul_left hq hxy

/-- Primitive finsets remain primitive after union when divisibility is
excluded in both cross directions. -/
theorem isPrimitive_union_of_cross {s t : Finset ℕ}
    (hs : IsPrimitive s) (ht : IsPrimitive t)
    (hst : ∀ x ∈ s, ∀ y ∈ t, ¬x ∣ y)
    (hts : ∀ y ∈ t, ∀ x ∈ s, ¬y ∣ x) : IsPrimitive (s ∪ t) := by
  intro x hx y hy hxy hdvd
  rcases Finset.mem_union.mp hx with hxs | hxt
  · rcases Finset.mem_union.mp hy with hys | hyt
    · exact hs hxs hys hxy hdvd
    · exact hst x hxs y hyt hdvd
  · rcases Finset.mem_union.mp hy with hys | hyt
    · exact hts x hxt y hys hdvd
    · exact ht hxt hyt hxy hdvd

/-- A coarse exponent region used by the recursive block packing. -/
def InExponentRegion (a b c bLo acHi : ℕ) (s : Finset ℕ) : Prop :=
  ∀ x ∈ s, ∃ i j k : ℕ,
    x = eval3 a b c i j k ∧ bLo ≤ j ∧ i + k ≤ acHi

/-- Scaling in the `b` direction raises the lower `b`-exponent bound and does
not change the `a+c` bound. -/
theorem scaleFinset_region {a b c q acHi : ℕ} {s : Finset ℕ}
    (hs : InExponentRegion a b c 0 acHi s) :
    InExponentRegion a b c q acHi (scaleFinset (b ^ q) s) := by
  intro x hx
  rcases Finset.mem_image.mp hx with ⟨y, hy, rfl⟩
  rcases hs y hy with ⟨i, j, k, rfl, _hj, hik⟩
  refine ⟨i, j + q, k, ?_, by omega, hik⟩
  simp only [scaleFinset, eval3]
  rw [pow_add]
  ac_rfl

/-- An edge-code finset lies below the expected `a+c` ceiling. -/
theorem edgeCodeFinset_region {a b c n : ℕ} (word : Fin n → Fin c) :
    InExponentRegion a b c 0 (edgeDigitDepth c + n - 1)
      (edgeCodeFinset a b c n word) := by
  intro x hx
  rcases edgeCodeFinset_exponent_region word hx with ⟨i, j, k, hval, hdeg, _hj⟩
  exact ⟨i, j, k, hval, Nat.zero_le _, by omega⟩

/-- A deep unshifted edge block and a shallower packed family shifted far in
its `b` exponent are cross-incomparable. -/
theorem edgeBlock_cross_scaled_region {a b c n nOld G : ℕ}
    (ha : 1 < a) (hb : 1 < b) (hc : 1 < c)
    (hab : Nat.Coprime a b) (hac : Nat.Coprime a c) (hbc : Nat.Coprime b c)
    (hG : edgeDigitDepth c < G)
    (hOld : 0 < nOld)
    (hn : edgeDigitDepth c + nOld < n)
    {word : Fin n → Fin c} {s : Finset ℕ}
    (hsreg : InExponentRegion a b c 0 (edgeDigitDepth c + nOld - 1) s) :
    (∀ x ∈ edgeCodeFinset a b c n word,
      ∀ y ∈ scaleFinset (b ^ G) s, ¬x ∣ y) ∧
    (∀ y ∈ scaleFinset (b ^ G) s,
      ∀ x ∈ edgeCodeFinset a b c n word, ¬y ∣ x) := by
  have hscaled := scaleFinset_region (q := G) hsreg
  constructor
  · intro x hx y hy hdvd
    rcases edgeCodeFinset_exponent_region word hx with
      ⟨ix, jx, kx, hxv, hxdeg, hjx⟩
    rcases hscaled y hy with ⟨iy, jy, ky, hyv, hjy, hiy⟩
    have hcoord := (eval3_dvd_iff ha hb hc hab hac hbc).mp (by
      simpa [hxv, hyv] using hdvd)
    have hxac : n - 1 ≤ ix + kx := by omega
    have hyac : iy + ky ≤ edgeDigitDepth c + nOld - 1 := hiy
    have hsub : edgeDigitDepth c + nOld - 1 < n - 1 := by
      apply Nat.sub_lt_sub_right (by omega : 1 ≤ edgeDigitDepth c + nOld)
      exact hn
    have haclt : iy + ky < ix + kx := hyac.trans_lt (hsub.trans_le hxac)
    exact (Nat.not_lt_of_ge (Nat.add_le_add hcoord.1 hcoord.2.2)) haclt
  · intro y hy x hx hdvd
    rcases edgeCodeFinset_exponent_region word hx with
      ⟨ix, jx, kx, hxv, _hxdeg, hjx⟩
    rcases hscaled y hy with ⟨iy, jy, ky, hyv, hjy, _hiy⟩
    have hcoord := (eval3_dvd_iff ha hb hc hab hac hbc).mp (by
      simpa [hyv, hxv] using hdvd)
    have : jy ≤ jx := hcoord.2.1
    omega

/-- Scaling a smooth finset in the `b` direction preserves smoothness. -/
theorem scaleFinset_subset_smooth3_b {a b c q : ℕ} {s : Finset ℕ}
    (hs : ∀ x ∈ s, x ∈ Smooth3 a b c) :
    ∀ x ∈ scaleFinset (b ^ q) s, x ∈ Smooth3 a b c := by
  intro x hx
  rcases Finset.mem_image.mp hx with ⟨y, hy, rfl⟩
  rcases hs y hy with ⟨i, j, k, rfl⟩
  refine ⟨i, j + q, k, ?_⟩
  rw [pow_add]
  ac_rfl

/-- The recurrent fixed-step blocks from F-027 can be packed recursively in
separated `b`-exponent bands. Consequently one numerical step supports
arbitrarily long primitive progressions. -/
theorem primitive_fixed_step_power_length_progressions {a b c : ℕ}
    (ha : 1 < a) (hb : 1 < b) (hc : 1 < c) (hacLt : a < c)
    (hab : Nat.Coprime a b) (hac : Nat.Coprime a c) (hbc : Nat.Coprime b c) :
    let G := edgeDigitDepth c + 1
    let Q := b ^ G
    ∃ d : ℕ, 0 < d ∧ ∀ M : ℕ,
      ∃ B : ℕ, ∃ sets : Fin (Q ^ M) → Finset ℕ,
        (∀ r x, x ∈ sets r → x ∈ Smooth3 a b c) ∧
        (∀ r, IsPrimitive (sets r)) ∧
        (∀ r : Fin (Q ^ M), (sets r).sum id = B + (r : ℕ) * d) := by
  dsimp only
  let G := edgeDigitDepth c + 1
  let Q := b ^ G
  have hG : edgeDigitDepth c < G := by dsimp [G]; omega
  have hGpos : G ≠ 0 := by dsimp [G]; omega
  have hQ : 1 < Q := by
    dsimp [Q]
    exact one_lt_pow₀ hb hGpos
  rcases edgeCode_fixed_step_recurs_infinitely_often
      ha hb hc hacLt hab hac hbc Q hQ with ⟨n₀, d, hd, hInf⟩
  refine ⟨d, hd, ?_⟩
  let Pack : ℕ → Prop := fun M =>
    ∃ nMax B : ℕ, 0 < nMax ∧
      ∃ sets : Fin (Q ^ M) → Finset ℕ,
        (∀ r x, x ∈ sets r → x ∈ Smooth3 a b c) ∧
        (∀ r, IsPrimitive (sets r)) ∧
        (∀ r : Fin (Q ^ M), (sets r).sum id = B + (r : ℕ) * d) ∧
        (∀ r, InExponentRegion a b c 0
          (edgeDigitDepth c + nMax - 1) (sets r))
  have hpack : ∀ M : ℕ, Pack M := by
    intro M
    induction M with
    | zero =>
        let sets : Fin (Q ^ 0) → Finset ℕ := fun _ => ∅
        refine ⟨1, 0, by omega, sets, ?_, ?_, ?_, ?_⟩
        · intro r x hx
          simp [sets] at hx
        · intro r
          intro x hx
          simp [sets] at hx
        · intro r
          change 0 = 0 + (r : ℕ) * d
          have hrlt : (r : ℕ) < 1 := by
            simpa only [pow_zero] using r.isLt
          have hr : (r : ℕ) = 0 := by omega
          simp [hr]
        · intro r x hx
          simp [sets] at hx
    | succ M ih =>
        rcases ih with ⟨nOld, BOld, hnOld, oldSets,
          hOldSmooth, hOldPrim, hOldSum, hOldRegion⟩
        rcases hInf.exists_gt (edgeDigitDepth c + nOld) with ⟨k, hk, hkgt⟩
        rcases hk with ⟨BNew, words, hwords⟩
        let n := n₀ + k
        have hnDeep : edgeDigitDepth c + nOld < n := by
          dsimp [n]
          omega
        let digitOf : Fin (Q ^ (M + 1)) → Fin Q := fun r =>
          ⟨(r : ℕ) % Q, Nat.mod_lt _ (by omega : 0 < Q)⟩
        let tailOf : Fin (Q ^ (M + 1)) → Fin (Q ^ M) := fun r =>
          ⟨(r : ℕ) / Q, by
            apply (Nat.div_lt_iff_lt_mul (by omega : 0 < Q)).2
            simpa [pow_succ] using r.isLt⟩
        let digitSets : Fin Q → Finset ℕ := fun r =>
          edgeCodeFinset a b c n (words r)
        let sets : Fin (Q ^ (M + 1)) → Finset ℕ := fun r =>
          digitSets (digitOf r) ∪ scaleFinset Q (oldSets (tailOf r))
        refine ⟨n, BNew + Q * BOld, by dsimp [n]; omega, sets, ?_, ?_, ?_, ?_⟩
        · intro r x hx
          rcases Finset.mem_union.mp hx with hxd | hxo
          · exact edgeCodeFinset_subset_smooth3 (words (digitOf r)) x hxd
          · exact scaleFinset_subset_smooth3_b (q := G)
              (hOldSmooth (tailOf r)) x (by simpa [Q] using hxo)
        · intro r
          have hcross := edgeBlock_cross_scaled_region ha hb hc hab hac hbc
            hG hnOld hnDeep (word := words (digitOf r))
            (s := oldSets (tailOf r)) (hOldRegion (tailOf r))
          apply isPrimitive_union_of_cross
          · exact edgeCodeFinset_isPrimitive ha hb hc hab hac hbc _
          · simpa [Q] using scaleFinset_isPrimitive (pow_pos (by omega) G)
              (hOldPrim (tailOf r))
          · intro x hx y hy
            exact hcross.1 x hx y (by simpa [Q] using hy)
          · intro y hy x hx
            exact hcross.2 y (by simpa [Q] using hy) x hx
        · intro r
          have hcross := edgeBlock_cross_scaled_region ha hb hc hab hac hbc
            hG hnOld hnDeep (word := words (digitOf r))
            (s := oldSets (tailOf r)) (hOldRegion (tailOf r))
          have hdis : Disjoint (digitSets (digitOf r))
              (scaleFinset Q (oldSets (tailOf r))) := by
            rw [Finset.disjoint_left]
            intro x hxd hxo
            exact hcross.1 x hxd x (by simpa [Q] using hxo) (dvd_refl x)
          change (digitSets (digitOf r) ∪
            scaleFinset Q (oldSets (tailOf r))).sum id = _
          rw [Finset.sum_union hdis]
          rw [show (digitSets (digitOf r)).sum id =
              BNew + ((digitOf r : Fin Q) : ℕ) * d by
            exact (edgeCodeFinset_sum ha hb hc hab hac hbc _).trans
              (hwords (digitOf r))]
          rw [scaleFinset_sum (by dsimp [Q]; positivity), hOldSum (tailOf r)]
          have hrdecomp : (r : ℕ) % Q + Q * ((r : ℕ) / Q) = (r : ℕ) :=
            Nat.mod_add_div _ _
          change (BNew + ((r : ℕ) % Q) * d) +
              Q * (BOld + ((r : ℕ) / Q) * d) =
            BNew + Q * BOld + (r : ℕ) * d
          calc
            (BNew + ((r : ℕ) % Q) * d) +
                Q * (BOld + ((r : ℕ) / Q) * d) =
              BNew + Q * BOld +
                ((r : ℕ) % Q + Q * ((r : ℕ) / Q)) * d := by ring
            _ = BNew + Q * BOld + (r : ℕ) * d := by rw [hrdecomp]
        · intro r x hx
          rcases Finset.mem_union.mp hx with hxd | hxo
          · exact edgeCodeFinset_region (words (digitOf r)) x hxd
          · have hs := scaleFinset_region (q := G) (hOldRegion (tailOf r))
            rcases hs x (by simpa [Q] using hxo) with ⟨i, j, kx, hv, hj, hik⟩
            exact ⟨i, j, kx, hv, by omega, hik.trans (by
              dsimp [n]
              omega)⟩
  intro M
  rcases hpack M with ⟨nMax, B, hnMax, sets, hsmooth, hprim, hsum, _hregion⟩
  exact ⟨B, sets, hsmooth, hprim, hsum⟩

end

end Erdos123
