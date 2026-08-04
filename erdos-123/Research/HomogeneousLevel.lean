import Research.Definitions

namespace Erdos123

/-- Evaluation of a three-dimensional exponent vector. -/
def eval3 (a b c i j k : ℕ) : ℕ := a ^ i * b ^ j * c ^ k

/-- For pairwise-coprime bases greater than one, divisibility of monomials is
exactly coordinatewise comparison of their exponent vectors. -/
theorem eval3_dvd_iff {a b c i j k i' j' k' : ℕ}
    (ha : 1 < a) (hb : 1 < b) (hc : 1 < c)
    (hab : Nat.Coprime a b) (hac : Nat.Coprime a c) (hbc : Nat.Coprime b c) :
    eval3 a b c i j k ∣ eval3 a b c i' j' k' ↔
      i ≤ i' ∧ j ≤ j' ∧ k ≤ k' := by
  constructor
  · intro hdiv
    have haiDivLhs : a ^ i ∣ eval3 a b c i j k := by
      exact ⟨b ^ j * c ^ k, by simp [eval3, mul_assoc]⟩
    have haiDivRhs : a ^ i ∣ eval3 a b c i' j' k' := haiDivLhs.trans hdiv
    have haiCoprime : Nat.Coprime (a ^ i) (b ^ j' * c ^ k') :=
      ((hab.pow_left i).pow_right j').mul_right ((hac.pow_left i).pow_right k')
    have haiDiv : a ^ i ∣ a ^ i' := by
      apply haiCoprime.dvd_of_dvd_mul_right
      simpa only [eval3, mul_assoc] using haiDivRhs

    have hbjDivLhs : b ^ j ∣ eval3 a b c i j k := by
      exact ⟨a ^ i * c ^ k, by simp [eval3, mul_assoc, mul_comm, mul_left_comm]⟩
    have hbjDivRhs : b ^ j ∣ eval3 a b c i' j' k' := hbjDivLhs.trans hdiv
    have hbjCoprime : Nat.Coprime (b ^ j) (a ^ i' * c ^ k') :=
      ((hab.symm.pow_left j).pow_right i').mul_right ((hbc.pow_left j).pow_right k')
    have hbjDiv : b ^ j ∣ b ^ j' := by
      apply hbjCoprime.dvd_of_dvd_mul_right
      simpa only [eval3, mul_assoc, mul_comm, mul_left_comm] using hbjDivRhs

    have hckDivLhs : c ^ k ∣ eval3 a b c i j k := by
      exact ⟨a ^ i * b ^ j, by simp [eval3, mul_assoc, mul_comm, mul_left_comm]⟩
    have hckDivRhs : c ^ k ∣ eval3 a b c i' j' k' := hckDivLhs.trans hdiv
    have hckCoprime : Nat.Coprime (c ^ k) (a ^ i' * b ^ j') :=
      ((hac.symm.pow_left k).pow_right i').mul_right ((hbc.symm.pow_left k).pow_right j')
    have hckDiv : c ^ k ∣ c ^ k' := by
      apply hckCoprime.dvd_of_dvd_mul_right
      simpa only [eval3, mul_assoc, mul_comm, mul_left_comm] using hckDivRhs

    exact ⟨(Nat.pow_dvd_pow_iff_le_right ha).mp haiDiv,
      (Nat.pow_dvd_pow_iff_le_right hb).mp hbjDiv,
      (Nat.pow_dvd_pow_iff_le_right hc).mp hckDiv⟩
  · rintro ⟨hi, hj, hk⟩
    exact Nat.mul_dvd_mul
      (Nat.mul_dvd_mul (pow_dvd_pow a hi) (pow_dvd_pow b hj))
      (pow_dvd_pow c hk)

/-- Divisibility between two monomials of the same total exponent degree forces
the exponent triples to be identical. -/
theorem exponents_eq_of_eval3_dvd_of_degree_eq
    {a b c i j k i' j' k' : ℕ}
    (ha : 1 < a) (hb : 1 < b) (hc : 1 < c)
    (hab : Nat.Coprime a b) (hac : Nat.Coprime a c) (hbc : Nat.Coprime b c)
    (hdiv : eval3 a b c i j k ∣ eval3 a b c i' j' k')
    (hdegree : i + j + k = i' + j' + k') :
    i = i' ∧ j = j' ∧ k = k' := by
  have hcoord := (eval3_dvd_iff ha hb hc hab hac hbc).mp hdiv
  omega

/-- Distinct exponent triples on one homogeneous level evaluate to a
pairwise-nondividing family, hence every subset of a level is a valid primitive
family of summands. -/
theorem not_eval3_dvd_of_same_degree
    {a b c i j k i' j' k' : ℕ}
    (ha : 1 < a) (hb : 1 < b) (hc : 1 < c)
    (hab : Nat.Coprime a b) (hac : Nat.Coprime a c) (hbc : Nat.Coprime b c)
    (hdegree : i + j + k = i' + j' + k')
    (hne : ¬(i = i' ∧ j = j' ∧ k = k')) :
    ¬eval3 a b c i j k ∣ eval3 a b c i' j' k' := by
  intro hdiv
  exact hne (exponents_eq_of_eval3_dvd_of_degree_eq
    ha hb hc hab hac hbc hdiv hdegree)

end Erdos123
