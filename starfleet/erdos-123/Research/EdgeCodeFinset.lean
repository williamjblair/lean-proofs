import Research.EdgeCodeBound

namespace Erdos123

/-- Available reserved positions: a c-layer and one of the `c-1` Euler-spaced
terms on its `a,b` edge. -/
abbrev EdgeCodeIndex (_c n : ℕ) := Fin n × ℕ

/-- Exponent evaluation attached to one reserved code position. -/
def edgeCodeValue (a b c n : ℕ) (p : EdgeCodeIndex c n) : ℕ :=
  eval3 a b c
    (edgeCodeDegree c n p.1 - edgeDigitDepth c + c.totient * p.2)
    (c.totient * (c - 1 - 1 - p.2)) (p.1 : ℕ)

/-- Positions selected by a nested-digit word. -/
def edgeCodeIndexSet {c n : ℕ} (word : Fin n → Fin c) :
    Finset (EdgeCodeIndex c n) :=
  ((Finset.univ : Finset (Fin n)).product (Finset.range (c - 1))).filter
    (fun p => p.2 < (word p.1 : ℕ))

/-- The actual finite set of smooth integer terms selected by a code word. -/
def edgeCodeFinset (a b c n : ℕ) (word : Fin n → Fin c) : Finset ℕ :=
  (edgeCodeIndexSet word).image (edgeCodeValue a b c n)

private theorem edgeCodeValue_eq {a b c n : ℕ} (p : EdgeCodeIndex c n) :
    edgeCodeValue a b c n p =
      c ^ (p.1 : ℕ) * edgeDigitTerm a b c (edgeCodeDegree c n p.1) p.2 := by
  unfold edgeCodeValue eval3 edgeDigitTerm correctionTerm
  rw [pow_add]
  have hcsub : c - 1 - 1 - p.2 = c - 2 - p.2 := by omega
  rw [hcsub]
  ac_rfl

private theorem edgeCodeValue_degree {c n : ℕ} (p : EdgeCodeIndex c n)
    (hp : p.2 < c - 1) :
    (edgeCodeDegree c n p.1 - edgeDigitDepth c + c.totient * p.2) +
      c.totient * (c - 1 - 1 - p.2) + (p.1 : ℕ) =
        edgeDigitDepth c + n - 1 := by
  exact edgeCodeTerm_total_degree p.1 hp

private theorem edgeCodeValue_injective {a b c n : ℕ}
    (ha : 1 < a) (hb : 1 < b) (hc : 1 < c)
    (hab : Nat.Coprime a b) (hac : Nat.Coprime a c) (hbc : Nat.Coprime b c)
    {p q : EdgeCodeIndex c n} (hp : p.2 < c - 1) (hq : q.2 < c - 1)
    (hpq : edgeCodeValue a b c n p = edgeCodeValue a b c n q) : p = q := by
  have hdiv : edgeCodeValue a b c n p ∣ edgeCodeValue a b c n q := by
    rw [hpq]
  have hexp := exponents_eq_of_eval3_dvd_of_degree_eq ha hb hc hab hac hbc hdiv
    (edgeCodeValue_degree p hp |>.trans (edgeCodeValue_degree q hq).symm)
  have hp1 : p.1 = q.1 := Fin.ext hexp.2.2
  have hmul : c.totient * p.2 = c.totient * q.2 := by
    have hdegree : edgeCodeDegree c n p.1 = edgeCodeDegree c n q.1 := by
      rw [hp1]
    omega
  have htot : 0 < c.totient := Nat.totient_pos.mpr (by omega)
  have hp2 : p.2 = q.2 := Nat.eq_of_mul_eq_mul_left htot hmul
  exact Prod.ext hp1 hp2

private theorem sum_range_if_lt {C r : ℕ} (hr : r ≤ C) (f : ℕ → ℕ) :
    (∑ t ∈ Finset.range C, if t < r then f t else 0) =
      ∑ t ∈ Finset.range r, f t := by
  calc
    (∑ t ∈ Finset.range C, if t < r then f t else 0) =
      ∑ t ∈ Finset.range r, if t < r then f t else 0 := by
        symm
        apply Finset.sum_subset
        · intro t ht
          simp only [Finset.mem_range] at ht ⊢
          omega
        · intro t htC htr
          simp only [Finset.mem_range] at htC htr
          simp [show ¬t < r by omega]
    _ = ∑ t ∈ Finset.range r, f t := by
      apply Finset.sum_congr rfl
      intro t ht
      simp only [Finset.mem_range] at ht
      simp [ht]

/-- Summing the actual finite set gives exactly the arithmetic radix evaluation
used in F-019. -/
theorem edgeCodeFinset_sum {a b c n : ℕ}
    (ha : 1 < a) (hb : 1 < b) (hc : 1 < c)
    (hab : Nat.Coprime a b) (hac : Nat.Coprime a c) (hbc : Nat.Coprime b c)
    (word : Fin n → Fin c) :
    (edgeCodeFinset a b c n word).sum id = edgeCodeEval a b c n word := by
  rw [edgeCodeFinset, Finset.sum_image]
  · rw [edgeCodeIndexSet, Finset.sum_filter]
    change (∑ p ∈ (Finset.univ : Finset (Fin n)).product (Finset.range (c - 1)),
      if p.2 < (word p.1 : ℕ) then edgeCodeValue a b c n p else 0) = _
    rw [show
      (∑ p ∈ (Finset.univ : Finset (Fin n)).product (Finset.range (c - 1)),
        if p.2 < (word p.1 : ℕ) then edgeCodeValue a b c n p else 0) =
      ∑ i : Fin n, ∑ t ∈ Finset.range (c - 1),
        if t < (word i : ℕ) then edgeCodeValue a b c n (i, t) else 0 by
          simpa using Finset.sum_product (Finset.univ : Finset (Fin n))
            (Finset.range (c - 1))
            (fun p => if p.2 < (word p.1 : ℕ) then
              edgeCodeValue a b c n p else 0)]
    rw [edgeCodeEval, radixEval]
    apply Finset.sum_congr rfl
    intro i _hi
    have hr : (word i : ℕ) ≤ c - 1 := by omega
    rw [sum_range_if_lt hr (fun t => edgeCodeValue a b c n (i, t))]
    rw [edgeDigit]
    calc
      (∑ t ∈ Finset.range (word i : ℕ), edgeCodeValue a b c n (i, t)) =
          ∑ t ∈ Finset.range (word i : ℕ),
            c ^ (i : ℕ) * edgeDigitTerm a b c (edgeCodeDegree c n i) t := by
              apply Finset.sum_congr rfl
              intro t _ht
              rw [edgeCodeValue_eq (p := (i, t))]
      _ = c ^ (i : ℕ) * (Finset.range (word i : ℕ)).sum
          (edgeDigitTerm a b c (edgeCodeDegree c n i)) := by
            rw [Finset.mul_sum]
  · intro p hp q hq hpq
    have hp' : p.2 < c - 1 := by
      exact Finset.mem_range.mp
        ((Finset.mem_product.mp (Finset.mem_filter.mp hp).1).2)
    have hq' : q.2 < c - 1 := by
      exact Finset.mem_range.mp
        ((Finset.mem_product.mp (Finset.mem_filter.mp hq).1).2)
    exact edgeCodeValue_injective ha hb hc hab hac hbc hp' hq' hpq

/-- Every selected value is an `a,b,c`-smooth monomial. -/
theorem edgeCodeFinset_subset_smooth3 {a b c n : ℕ} (word : Fin n → Fin c) :
    ∀ x ∈ edgeCodeFinset a b c n word, x ∈ Smooth3 a b c := by
  intro x hx
  rcases Finset.mem_image.mp hx with ⟨p, _hp, rfl⟩
  exact ⟨_, _, _, rfl⟩

/-- The selected code set is primitive because all its exponent triples have
one common total degree. -/
theorem edgeCodeFinset_isPrimitive {a b c n : ℕ}
    (ha : 1 < a) (hb : 1 < b) (hc : 1 < c)
    (hab : Nat.Coprime a b) (hac : Nat.Coprime a c) (hbc : Nat.Coprime b c)
    (word : Fin n → Fin c) : IsPrimitive (edgeCodeFinset a b c n word) := by
  intro x hx y hy hxy hdvd
  rcases Finset.mem_image.mp hx with ⟨p, hp, rfl⟩
  rcases Finset.mem_image.mp hy with ⟨q, hq, rfl⟩
  have hp' : p.2 < c - 1 := by
    exact Finset.mem_range.mp
      ((Finset.mem_product.mp (Finset.mem_filter.mp hp).1).2)
  have hq' : q.2 < c - 1 := by
    exact Finset.mem_range.mp
      ((Finset.mem_product.mp (Finset.mem_filter.mp hq).1).2)
  apply hxy
  have hexp := exponents_eq_of_eval3_dvd_of_degree_eq ha hb hc hab hac hbc hdvd
    (edgeCodeValue_degree p hp' |>.trans (edgeCodeValue_degree q hq').symm)
  unfold edgeCodeValue eval3
  rw [hexp.1, hexp.2.1, hexp.2.2]

/-- For every sufficiently deep code there are two genuine primitive smooth
subsets on the same homogeneous level whose sums differ by a nonzero amount
bounded independently of the depth. -/
theorem primitive_homogeneous_bounded_difference {a b c n : ℕ}
    (ha : 1 < a) (hb : 1 < b) (hc : 1 < c) (hacLt : a < c)
    (hab : Nat.Coprime a b) (hac : Nat.Coprime a c) (hbc : Nat.Coprime b c)
    (hn : edgeDigitMass a b c + 2 ≤ c ^ n) :
    ∃ s t : Finset ℕ,
      (∀ x ∈ s, x ∈ Smooth3 a b c) ∧
      (∀ x ∈ t, x ∈ Smooth3 a b c) ∧
      IsPrimitive s ∧ IsPrimitive t ∧
      0 < Nat.dist (s.sum id) (t.sum id) ∧
      Nat.dist (s.sum id) (t.sum id) ≤ edgeDigitMass a b c + 1 := by
  rcases edgeCode_bounded_difference hc hacLt hac.symm hbc.symm hn with
    ⟨u, v, _huv, hpos, hle⟩
  refine ⟨edgeCodeFinset a b c n u, edgeCodeFinset a b c n v,
    edgeCodeFinset_subset_smooth3 u, edgeCodeFinset_subset_smooth3 v,
    edgeCodeFinset_isPrimitive ha hb hc hab hac hbc u,
    edgeCodeFinset_isPrimitive ha hb hc hab hac hbc v, ?_, ?_⟩
  · rw [edgeCodeFinset_sum ha hb hc hab hac hbc u,
      edgeCodeFinset_sum ha hb hc hab hac hbc v]
    exact hpos
  · rw [edgeCodeFinset_sum ha hb hc hab hac hbc u,
      edgeCodeFinset_sum ha hb hc hab hac hbc v]
    exact hle

end Erdos123
