import Research.HomogeneousLevel

namespace Erdos123

/-- The `t`-th term in a residue correction gadget of length `r`. -/
def correctionTerm (a b c r t : ℕ) : ℕ :=
  b ^ (a.totient * t) * c ^ (a.totient * (r - 1 - t))

/-- The correction gadget as a genuine set of distinct integer summands. -/
def correctionSet (a b c r : ℕ) : Finset ℕ :=
  (Finset.range r).image (correctionTerm a b c r)

/-- Every correction term is congruent to one modulo `a`. -/
theorem correctionTerm_modEq_one {a b c r t : ℕ}
    (hab : Nat.Coprime a b) (hac : Nat.Coprime a c) :
    correctionTerm a b c r t ≡ 1 [MOD a] := by
  have hb : b ^ a.totient ≡ 1 [MOD a] := Nat.ModEq.pow_totient hab.symm
  have hc : c ^ a.totient ≡ 1 [MOD a] := Nat.ModEq.pow_totient hac.symm
  have hbt := hb.pow t
  have hct := hc.pow (r - 1 - t)
  simpa [correctionTerm, pow_mul] using hbt.mul hct

/-- Different indices in a gadget give monomials which do not divide one
another. -/
theorem correctionTerm_not_dvd {a b c r t u : ℕ}
    (ha : 1 < a) (hb : 1 < b) (hc : 1 < c)
    (hab : Nat.Coprime a b) (hac : Nat.Coprime a c) (hbc : Nat.Coprime b c)
    (ht : t < r) (hu : u < r) (htu : t ≠ u) :
    ¬correctionTerm a b c r t ∣ correctionTerm a b c r u := by
  have htot : 0 < a.totient := Nat.totient_pos.mpr (by omega)
  have ht' : t ≤ r - 1 := by omega
  have hu' : u ≤ r - 1 := by omega
  have htSum : t + (r - 1 - t) = r - 1 := by omega
  have huSum : u + (r - 1 - u) = r - 1 := by omega
  have hdegree :
      a.totient * t + a.totient * (r - 1 - t) + 0 =
      a.totient * u + a.totient * (r - 1 - u) + 0 := by
    simp only [add_zero, ← Nat.mul_add, htSum, huSum]
  have hne : ¬(a.totient * t = a.totient * u ∧
      a.totient * (r - 1 - t) = a.totient * (r - 1 - u) ∧ (0 : ℕ) = 0) := by
    intro h
    exact htu (Nat.eq_of_mul_eq_mul_left htot h.1)
  have h := not_eval3_dvd_of_same_degree hb hc ha hbc hab.symm hac.symm hdegree hne
  simpa [eval3, correctionTerm, mul_assoc] using h

/-- The index-to-value map is injective on the gadget range. -/
theorem correctionTerm_injOn {a b c r : ℕ}
    (ha : 1 < a) (hb : 1 < b) (hc : 1 < c)
    (hab : Nat.Coprime a b) (hac : Nat.Coprime a c) (hbc : Nat.Coprime b c) :
    Set.InjOn (correctionTerm a b c r) (Finset.range r : Set ℕ) := by
  intro t ht u hu heq
  by_contra htu
  have hnot := correctionTerm_not_dvd ha hb hc hab hac hbc
    (Finset.mem_range.mp ht) (Finset.mem_range.mp hu) htu
  apply hnot
  rw [heq]

/-- The correction set is a divisibility antichain. -/
theorem correctionSet_isPrimitive {a b c r : ℕ}
    (ha : 1 < a) (hb : 1 < b) (hc : 1 < c)
    (hab : Nat.Coprime a b) (hac : Nat.Coprime a c) (hbc : Nat.Coprime b c) :
    IsPrimitive (correctionSet a b c r) := by
  intro x hx y hy hxy
  rcases Finset.mem_image.mp hx with ⟨t, ht, rfl⟩
  rcases Finset.mem_image.mp hy with ⟨u, hu, rfl⟩
  apply correctionTerm_not_dvd ha hb hc hab hac hbc
    (Finset.mem_range.mp ht) (Finset.mem_range.mp hu)
  intro htu
  subst u
  exact hxy rfl

/-- A length-`r` correction gadget has sum congruent to `r` modulo `a`. -/
theorem correctionSet_sum_modEq {a b c r : ℕ}
    (ha : 1 < a) (hb : 1 < b) (hc : 1 < c)
    (hab : Nat.Coprime a b) (hac : Nat.Coprime a c) (hbc : Nat.Coprime b c) :
    (correctionSet a b c r).sum id ≡ r [MOD a] := by
  have hinj := correctionTerm_injOn (r := r) ha hb hc hab hac hbc
  rw [correctionSet, Finset.sum_image hinj]
  have hsum :
      (Finset.range r).sum (correctionTerm a b c r) ≡
      (Finset.range r).sum (fun _t => 1) [MOD a] :=
    Nat.ModEq.sum (fun t ht => correctionTerm_modEq_one hab hac)
  have hones : (Finset.range r).sum (fun _t => (1 : ℕ)) = r := by simp
  rw [hones] at hsum
  simpa only [id_eq] using hsum

end Erdos123
