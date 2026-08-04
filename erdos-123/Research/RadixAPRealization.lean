import Research.FixedStepPacking
import Research.HomogeneousRadixInterval
import Research.ExactDegreeCorrections

namespace Erdos123

set_option maxHeartbeats 3000000

/-- All members of a finset are strict-interior monomials on one exact level,
with a common upper bound on their `b` exponent. -/
def IsInteriorLevelBand (a b c D J : ℕ) (s : Finset ℕ) : Prop :=
  ∀ x ∈ s, ∃ i j k : ℕ,
    0 < i ∧ 0 < j ∧ 0 < k ∧ i + j + k = D ∧ j ≤ J ∧
      x = eval3 a b c i j k

/-- Exact-level exponent witnesses imply smoothness. -/
theorem interiorLevelBand_subset_smooth3 {a b c D J : ℕ} {s : Finset ℕ}
    (hs : IsInteriorLevelBand a b c D J s) :
    ∀ x ∈ s, x ∈ Smooth3 a b c := by
  intro x hx
  rcases hs x hx with ⟨i, j, k, _hi, _hj, _hk, _hdeg, _hband, rfl⟩
  exact ⟨i, j, k, rfl⟩

/-- Any finite set whose members have one exact exponent degree is primitive. -/
theorem isPrimitive_of_exact_level {a b c D : ℕ} {s : Finset ℕ}
    (ha : 1 < a) (hb : 1 < b) (hc : 1 < c)
    (hab : Nat.Coprime a b) (hac : Nat.Coprime a c) (hbc : Nat.Coprime b c)
    (hs : ∀ x ∈ s, ∃ i j k : ℕ,
      i + j + k = D ∧ x = eval3 a b c i j k) : IsPrimitive s := by
  intro x hx y hy hxy hdvd
  rcases hs x hx with ⟨ix, jx, kx, hxdeg, rfl⟩
  rcases hs y hy with ⟨iy, jy, ky, hydeg, rfl⟩
  apply not_eval3_dvd_of_same_degree ha hb hc hab hac hbc
    (hxdeg.trans hydeg.symm) _ hdvd
  intro he
  apply hxy
  rcases he with ⟨rfl, rfl, rfl⟩
  rfl

/-- In particular an interior level band is primitive. -/
theorem IsInteriorLevelBand.isPrimitive {a b c D J : ℕ} {s : Finset ℕ}
    (ha : 1 < a) (hb : 1 < b) (hc : 1 < c)
    (hab : Nat.Coprime a b) (hac : Nat.Coprime a c) (hbc : Nat.Coprime b c)
    (hs : IsInteriorLevelBand a b c D J s) : IsPrimitive s := by
  apply isPrimitive_of_exact_level ha hb hc hab hac hbc
  intro x hx
  rcases hs x hx with ⟨i, j, k, _hi, _hj, _hk, hdeg, _hband, hval⟩
  exact ⟨i, j, k, hdeg, hval⟩

/-- The sum of the homogeneous weights through stage `M`. -/
def homogeneousWeightMass (A B : ℕ) : ℕ → ℕ
  | 0 => 1
  | M + 1 => A * homogeneousWeightMass A B M + B ^ (M + 1)

/-- The homogeneous weight mass is bounded by one further power of the larger
base. -/
theorem homogeneousWeightMass_le_pow {A B M : ℕ}
    (hA : 0 < A) (hAB : A < B) :
    homogeneousWeightMass A B M ≤ B ^ (M + 1) := by
  induction M with
  | zero =>
      simp [homogeneousWeightMass]
      omega
  | succ M ih =>
      rw [homogeneousWeightMass]
      have hmul := Nat.mul_le_mul_left A ih
      have hApow : A * B ^ (M + 1) ≤ (B - 1) * B ^ (M + 1) :=
        Nat.mul_le_mul_right _ (by omega)
      calc
        A * homogeneousWeightMass A B M + B ^ (M + 1) ≤
            A * B ^ (M + 1) + B ^ (M + 1) := Nat.add_le_add_right hmul _
        _ ≤ (B - 1) * B ^ (M + 1) + B ^ (M + 1) :=
          Nat.add_le_add_right hApow _
        _ = B ^ (M + 2) := by
          have hB : 0 < B := hA.trans hAB
          have hB1 : 1 ≤ B := by omega
          calc
            (B - 1) * B ^ (M + 1) + B ^ (M + 1) =
                ((B - 1) + 1) * B ^ (M + 1) := by ring
            _ = B * B ^ (M + 1) := by rw [Nat.sub_add_cancel hB1]
            _ = B ^ (M + 2) := by
              rw [show M + 2 = (M + 1) + 1 by omega, pow_succ]
              ring

/-- Every bounded homogeneous-radix value is at most `L` times the homogeneous
weight mass. -/
theorem HomogeneousRadixRep.le_mass {A B L M n : ℕ}
    (hrep : HomogeneousRadixRep A B L M n) :
    n ≤ L * homogeneousWeightMass A B M := by
  induction M generalizing n with
  | zero =>
      simp only [HomogeneousRadixRep] at hrep
      simp [homogeneousWeightMass]
      omega
  | succ M ih =>
      rcases hrep with ⟨x, s, hx, hs, rfl⟩
      have hxle := ih hx
      rw [homogeneousWeightMass]
      calc
        A * x + B ^ (M + 1) * s ≤
            A * (L * homogeneousWeightMass A B M) + B ^ (M + 1) * L :=
          Nat.add_le_add (Nat.mul_le_mul_left A hxle)
            (Nat.mul_le_mul_left _ hs.le)
        _ = L * (A * homogeneousWeightMass A B M + B ^ (M + 1)) := by ring

/-- Scaling an interior band in the `a` direction preserves its interior
geometry and raises its exact degree. -/
theorem scaleInteriorBandA {a b c D J G : ℕ} {s : Finset ℕ}
    (ha : 0 < a) (hs : IsInteriorLevelBand a b c D J s) :
    IsInteriorLevelBand a b c (D + G) J (scaleFinset (a ^ G) s) := by
  intro x hx
  rcases Finset.mem_image.mp hx with ⟨y, hy, rfl⟩
  rcases hs y hy with ⟨i, j, k, hi, hj, hk, hdeg, hjJ, rfl⟩
  refine ⟨i + G, j, k, by omega, hj, hk, by omega, hjJ, ?_⟩
  dsimp [eval3]
  rw [pow_add]
  ring

/-- A raw edge block translated by `abc*(b^u c^v)^e` is a strict-interior
exact-level block in the corresponding `b`-exponent band. -/
theorem translatedEdgeCode_interiorBand {a b c n u v e : ℕ}
    (word : Fin n → Fin c) :
    let H := edgeDigitDepth c
    let δ := H + n - 1
    let q := a * b * c * (b ^ u * c ^ v) ^ e
    IsInteriorLevelBand a b c (δ + (u + v) * e + 3)
      (u * e + H + 1) (scaleFinset q (edgeCodeFinset a b c n word)) := by
  dsimp only
  let H := edgeDigitDepth c
  let δ := H + n - 1
  let q := a * b * c * (b ^ u * c ^ v) ^ e
  intro x hx
  rcases Finset.mem_image.mp hx with ⟨y, hy, rfl⟩
  rcases edgeCodeFinset_exponent_region word hy with
    ⟨i, j, k, rfl, hdegree, hjH⟩
  refine ⟨i + 1, j + u * e + 1, k + v * e + 1,
    by omega, by omega, by omega, ?_, by omega, ?_⟩
  · rw [Nat.add_mul]
    omega
  · dsimp [q, eval3]
    simp only [mul_pow, pow_mul]
    rw [pow_add, pow_add, pow_add]
    ring

/-- A bounded homogeneous-radix coefficient word can be realized by a union
of translated copies of one primitive AP digit family.  All actual terms are
strict-interior monomials on one exact degree, and the digit copies occupy
separated `b`-exponent bands. -/
theorem homogeneousRadixRep_realized_by_edge_AP
    {a b c n L B₀ d u v M value : ℕ}
    (ha : 1 < a) (hb : 1 < b) (hc : 1 < c) (hacLt : a < c)
    (hab : Nat.Coprime a b) (hac : Nat.Coprime a c) (hbc : Nat.Coprime b c)
    (huBand : edgeDigitDepth c + 1 < u)
    (words : Fin L → (Fin n → Fin c))
    (hwords : ∀ r : Fin L,
      edgeCodeEval a b c n (words r) = B₀ + (r : ℕ) * d)
    (hrep : HomogeneousRadixRep (a ^ (u + v)) (b ^ u * c ^ v) L M value) :
    let H := edgeDigitDepth c
    let δ := H + n - 1
    let A := a ^ (u + v)
    let B := b ^ u * c ^ v
    let q := a * b * c
    ∃ s : Finset ℕ,
      IsInteriorLevelBand a b c (δ + (u + v) * M + 3)
        (u * M + H + 1) s ∧
      s.sum id = q * (B₀ * homogeneousWeightMass A B M + d * value) := by
  dsimp only
  let H := edgeDigitDepth c
  let δ := H + n - 1
  let A := a ^ (u + v)
  let B := b ^ u * c ^ v
  let q := a * b * c
  induction M generalizing value with
  | zero =>
      simp only [HomogeneousRadixRep] at hrep
      let r : Fin L := ⟨value, hrep⟩
      let s := scaleFinset q (edgeCodeFinset a b c n (words r))
      refine ⟨s, ?_, ?_⟩
      · have hbnd := translatedEdgeCode_interiorBand (a := a) (b := b) (c := c)
          (u := u) (v := v) (e := 0) (words r)
        simpa [s, H, δ, q] using hbnd
      · dsimp [s]
        rw [scaleFinset_sum (by dsimp [q]; positivity)]
        rw [edgeCodeFinset_sum ha hb hc hab hac hbc, hwords r]
        simp [homogeneousWeightMass, r]
        ring
  | succ M ih =>
      rcases hrep with ⟨oldValue, digit, hold, hdigit, rfl⟩
      rcases ih hold with ⟨oldSet, holdBand, holdSum⟩
      let r : Fin L := ⟨digit, hdigit⟩
      let oldScaled := scaleFinset A oldSet
      let newSet := scaleFinset (q * B ^ (M + 1))
        (edgeCodeFinset a b c n (words r))
      let s := oldScaled ∪ newSet
      have holdScaled : IsInteriorLevelBand a b c
          (δ + (u + v) * M + 3 + (u + v))
          (u * M + H + 1) oldScaled := by
        exact scaleInteriorBandA (by omega : 0 < a) holdBand
      have hnewBand : IsInteriorLevelBand a b c
          (δ + (u + v) * (M + 1) + 3)
          (u * (M + 1) + H + 1) newSet := by
        have hbnd := translatedEdgeCode_interiorBand (a := a) (b := b) (c := c)
          (u := u) (v := v) (e := M + 1) (words r)
        simpa [newSet, q, B, H, δ, mul_assoc] using hbnd
      have hdegreeEq : δ + (u + v) * M + 3 + (u + v) =
          δ + (u + v) * (M + 1) + 3 := by ring
      have hdis : Disjoint oldScaled newSet := by
        rw [Finset.disjoint_left]
        intro x hxold hxnew
        rcases holdScaled x hxold with
          ⟨io, jo, ko, _hio, _hjo, _hko, _hdo, hjoBand, hxo⟩
        rcases hnewBand x hxnew with
          ⟨inw, jnw, knw, _hinw, _hjnw, _hknw, _hdn, _hjnwBand, hxn⟩
        have heq : eval3 a b c io jo ko = eval3 a b c inw jnw knw := by
          rw [← hxo, ← hxn]
        have hdvd : eval3 a b c io jo ko ∣ eval3 a b c inw jnw knw := by rw [heq]
        have hcoord := (eval3_dvd_iff ha hb hc hab hac hbc).mp hdvd
        have hdvdRev : eval3 a b c inw jnw knw ∣ eval3 a b c io jo ko := by
          rw [heq]
        have hcoordRev := (eval3_dvd_iff ha hb hc hab hac hbc).mp hdvdRev
        have hjnewLo : u * (M + 1) + 1 ≤ jnw := by
          rcases Finset.mem_image.mp hxnew with ⟨y, hy, hyv⟩
          rcases edgeCodeFinset_exponent_region (words r) hy with
            ⟨ii, jj, kk, hyval, _hdeg, _hjj⟩
          have hscaledVal : q * B ^ (M + 1) * y =
              eval3 a b c (ii + 1) (jj + u * (M + 1) + 1)
                (kk + v * (M + 1) + 1) := by
            rw [hyval]
            dsimp [q, B, eval3]
            simp only [mul_pow, pow_mul]
            rw [pow_add, pow_add, pow_add]
            ring
          have heqNew : eval3 a b c inw jnw knw =
              eval3 a b c (ii + 1) (jj + u * (M + 1) + 1)
                (kk + v * (M + 1) + 1) := by
            rw [← hxn, ← hyv, hscaledVal]
          have hd1 : eval3 a b c inw jnw knw ∣
              eval3 a b c (ii + 1) (jj + u * (M + 1) + 1)
                (kk + v * (M + 1) + 1) := by rw [heqNew]
          have hd2 : eval3 a b c (ii + 1) (jj + u * (M + 1) + 1)
                (kk + v * (M + 1) + 1) ∣ eval3 a b c inw jnw knw := by
            rw [heqNew]
          have _hc1 := (eval3_dvd_iff ha hb hc hab hac hbc).mp hd1
          have hc2 := (eval3_dvd_iff ha hb hc hab hac hbc).mp hd2
          exact (by
            calc
              u * (M + 1) + 1 ≤ jj + u * (M + 1) + 1 := by omega
              _ ≤ jnw := hc2.2.1)
        have : jo < jnw := by
          calc
            jo ≤ u * M + H + 1 := hjoBand
            _ < u * M + u + 1 := by omega
            _ = u * (M + 1) + 1 := by rw [Nat.mul_succ]
            _ ≤ jnw := hjnewLo
        exact (Nat.not_le_of_gt this) hcoordRev.2.1
      refine ⟨s, ?_, ?_⟩
      · intro x hx
        rcases Finset.mem_union.mp hx with hxold | hxnew
        · rcases holdScaled x hxold with
            ⟨i, j, k, hi, hj, hk, hdeg, hjBand, hval⟩
          have hjBound : j ≤ u * (M + 1) + H + 1 := by
            calc
              j ≤ u * M + H + 1 := hjBand
              _ ≤ u * (M + 1) + H + 1 := by
                exact Nat.add_le_add_right
                  (Nat.mul_le_mul_left u (by omega : M ≤ M + 1)) (H + 1)
          exact ⟨i, j, k, hi, hj, hk, hdeg.trans hdegreeEq, hjBound, hval⟩
        · exact hnewBand x hxnew
      · dsimp [s]
        rw [Finset.sum_union hdis]
        change oldScaled.sum id + newSet.sum id = _
        dsimp [oldScaled, newSet]
        rw [scaleFinset_sum (pow_pos (by omega) _), holdSum]
        rw [scaleFinset_sum (by dsimp [q, B]; positivity)]
        rw [edgeCodeFinset_sum ha hb hc hab hac hbc, hwords r]
        dsimp [A, B, q]
        rw [homogeneousWeightMass]
        ring

end Erdos123
