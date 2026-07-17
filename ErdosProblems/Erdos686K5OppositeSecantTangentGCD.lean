/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import ErdosProblems.Erdos686K5OppositeSecantCofactor
import ErdosProblems.Erdos686TangentDefectCRT

/-!
# Erdős 686, k=5: opposite-secant/tangent gcd elimination

The opposite-secant quotient identity gives a second linear equation in the
coprime row and column cofactors.  Combining it with the banked bipartite
tangent congruence forces the common part of the crossing modulus and the
secant-quotient product to divide the determinant of those two equations.

A separate local lemma retains the individual tangent congruences.  It shows
that the common part of one crossing owner and the two secant quotients divides
the corresponding fixed tangent coefficient.  No quotient is inverted, so a
zero coefficient remains an explicit branch.
-/

namespace Erdos686
namespace Erdos686Variant

/-- Determinant divisor for two linear equations in coprime natural
cofactors.  The second equation is an equality; the first is only required
modulo `X`. -/
theorem coprime_cofactor_determinant_gcd_dvd
    {X a b : ℕ} {U V c e S : ℤ}
    (hcop : Nat.Coprime a b)
    (hfirst : (X : ℤ) ∣ U * (a : ℤ) + V * (b : ℤ))
    (hsecond : S = c * (b : ℤ) - e * (a : ℤ)) :
    Nat.gcd X S.natAbs ∣ (c * U + e * V).natAbs := by
  let g := Nat.gcd X S.natAbs
  let K : ℤ := c * U + e * V
  have hgX : g ∣ X := Nat.gcd_dvd_left X S.natAbs
  have hgSabs : g ∣ S.natAbs := Nat.gcd_dvd_right X S.natAbs
  have hgFirstZ : (g : ℤ) ∣ U * (a : ℤ) + V * (b : ℤ) := by
    have hgXZ : (g : ℤ) ∣ (X : ℤ) := by exact_mod_cast hgX
    exact hgXZ.trans hfirst
  have hgSZ : (g : ℤ) ∣ S := by
    exact Int.natAbs_dvd_natAbs.mp (by simpa using hgSabs)
  have hgKaZ : (g : ℤ) ∣ K * (a : ℤ) := by
    have hcomb := dvd_sub (dvd_mul_of_dvd_right hgFirstZ c)
      (dvd_mul_of_dvd_right hgSZ V)
    convert hcomb using 1
    dsimp [K]
    rw [hsecond]
    ring
  have hgKbZ : (g : ℤ) ∣ K * (b : ℤ) := by
    have hcomb := dvd_add (dvd_mul_of_dvd_right hgFirstZ e)
      (dvd_mul_of_dvd_right hgSZ U)
    convert hcomb using 1
    dsimp [K]
    rw [hsecond]
    ring
  have hgKa : g ∣ K.natAbs * a := by
    have h := Int.natAbs_dvd_natAbs.mpr hgKaZ
    simpa [Int.natAbs_mul] using h
  have hgKb : g ∣ K.natAbs * b := by
    have h := Int.natAbs_dvd_natAbs.mpr hgKbZ
    simpa [Int.natAbs_mul] using h
  have hgGcd : g ∣ Nat.gcd (K.natAbs * a) (K.natAbs * b) :=
    Nat.dvd_gcd hgKa hgKb
  simpa [Nat.gcd_mul_left, hcop.gcd_eq_one, K] using hgGcd

/-- One cancelled tangent congruence and the opposite secant congruence bound
the common divisor of the crossing owner and the product of the two secant
quotients.  If `kappa = 0`, the conclusion deliberately remains divisibility
by zero. -/
theorem local_tangent_opposite_secant_gcd_dvd_coefficient
    {P xrest : ℕ} {C M N U V kappa epsilon : ℤ}
    (hP : P ≠ 0)
    (hcop : Nat.Coprime P xrest)
    (hsquare :
      ((P : ℤ) ^ 2) ∣
        C * (((P : ℤ) * M) * U) -
          kappa * ((P : ℤ) * (xrest : ℤ)))
    (hopposite : (P : ℤ) ∣ N * V - epsilon) :
    Nat.gcd P (U * V).natAbs ∣ (kappa * epsilon).natAbs := by
  let g := Nat.gcd P (U * V).natAbs
  have hcancel : (P : ℤ) ∣ C * M * U - kappa * (xrest : ℤ) := by
    exact owner_dvd_resultantQuotient_tangent_defect
      (by exact_mod_cast hP) hsquare
  have hcombined : (P : ℤ) ∣
      C * M * N * (U * V) - kappa * (xrest : ℤ) * epsilon := by
    have h₁ := dvd_mul_of_dvd_right hcancel (N * V)
    have h₂ := dvd_mul_of_dvd_right hopposite (kappa * (xrest : ℤ))
    have hsum := dvd_add h₁ h₂
    convert hsum using 1
    all_goals ring
  have hgP : g ∣ P := Nat.gcd_dvd_left P (U * V).natAbs
  have hgSabs : g ∣ (U * V).natAbs :=
    Nat.gcd_dvd_right P (U * V).natAbs
  have hgPZ : (g : ℤ) ∣ (P : ℤ) := by exact_mod_cast hgP
  have hgCombinedZ : (g : ℤ) ∣
      C * M * N * (U * V) - kappa * (xrest : ℤ) * epsilon :=
    hgPZ.trans hcombined
  have hgSZ : (g : ℤ) ∣ U * V := by
    exact Int.natAbs_dvd_natAbs.mp (by simpa using hgSabs)
  have hgFirstZ : (g : ℤ) ∣ C * M * N * (U * V) :=
    dvd_mul_of_dvd_right hgSZ (C * M * N)
  have hgCoeffXrestZ : (g : ℤ) ∣
      kappa * epsilon * (xrest : ℤ) := by
    have hsub := dvd_sub hgFirstZ hgCombinedZ
    convert hsub using 1
    all_goals ring
  have hgCoeffXrest : g ∣ (kappa * epsilon).natAbs * xrest := by
    have h := Int.natAbs_dvd_natAbs.mpr hgCoeffXrestZ
    simpa [Int.natAbs_mul, mul_assoc, mul_left_comm, mul_comm] using h
  have hcopg : Nat.Coprime g xrest := hcop.of_dvd_left hgP
  exact hcopg.dvd_of_dvd_mul_right hgCoeffXrest

/-- Explicit zero-coefficient dichotomy for the local fixed divisor. -/
theorem local_tangent_opposite_secant_gcd_zero_or_le_coefficient
    {P xrest : ℕ} {C M N U V kappa epsilon : ℤ}
    (hP : P ≠ 0)
    (hcop : Nat.Coprime P xrest)
    (hsquare :
      ((P : ℤ) ^ 2) ∣
        C * (((P : ℤ) * M) * U) -
          kappa * ((P : ℤ) * (xrest : ℤ)))
    (hopposite : (P : ℤ) ∣ N * V - epsilon) :
    kappa * epsilon = 0 ∨
      Nat.gcd P (U * V).natAbs ≤ (kappa * epsilon).natAbs := by
  by_cases hz : kappa * epsilon = 0
  · exact Or.inl hz
  · right
    exact Nat.le_of_dvd (Int.natAbs_pos.mpr hz)
      (local_tangent_opposite_secant_gcd_dvd_coefficient
        hP hcop hsquare hopposite)

/-- Proper-global specialization of the determinant divisor.  The secant
quotients are never divided out.  The final disjunction records the zero
determinant branch exactly; otherwise it gives the corresponding explicit
height bound for the common gcd. -/
theorem k5_proper_global_opposite_secant_tangent_determinant_gcd
    {n d t j₁ j₂ i₁ i₂ : ℕ}
    (data : CanonicalOwnerData 5 n d t)
    (hj₁ : j₁ ∈ Finset.Icc 1 5) (hj₂ : j₂ ∈ Finset.Icc 1 5)
    (hi₁ : i₁ ∈ Finset.Icc 1 5) (hi₂ : i₂ ∈ Finset.Icc 1 5)
    (hjneq : j₁ ≠ j₂) (hineq : i₁ ≠ i₂)
    (hfour : 4 ∣ n + d + t)
    (hj₁one : canonicalLowerResidual data j₁ = 1)
    (hj₂one : canonicalLowerResidual data j₂ = 1)
    (hi₁one : canonicalUpperResidual data i₁ = 1)
    (hi₂one : canonicalUpperResidual data i₂ = 1)
    (heq : blockProduct 5 (n + d) = 4 * blockProduct 5 n) :
    let A := (n + j₁) * (n + j₂)
    let B := upperTermAfterFour n d t i₁ * upperTermAfterFour n d t i₂
    let X := canonicalOwnerCell data j₁ i₁ *
      canonicalOwnerCell data j₁ i₂ *
      canonicalOwnerCell data j₂ i₁ *
      canonicalOwnerCell data j₂ i₂
    let Mplus := canonicalOwnerCell data j₁ i₁ *
      canonicalOwnerCell data j₂ i₂
    let Mminus := canonicalOwnerCell data j₁ i₂ *
      canonicalOwnerCell data j₂ i₁
    let c : ℤ := (((j₂ : ℤ) - j₁) ^ 2) *
      (k5UpperFourMultiplier t i₁ : ℤ) *
      (k5UpperFourMultiplier t i₂ : ℤ)
    let e : ℤ := ((i₂ : ℤ) - i₁) ^ 2
    let K : ℤ :=
      c * k5ProperTangentRowQuotient n d t j₁ j₂ i₁ i₂ +
        e * k5ProperTangentColumnQuotient n d t j₁ j₂ i₁ i₂
    ∃ Uplus Uminus : ℤ,
      k5OppositeSecantPlus n d j₁ j₂ i₁ i₂ =
          (Mplus : ℤ) * Uplus ∧
        k5OppositeSecantMinus n d j₁ j₂ i₁ i₂ =
          (Mminus : ℤ) * Uminus ∧
        Uplus * Uminus = c * (B / X : ℕ) - e * (A / X : ℕ) ∧
        Nat.gcd X (Uplus * Uminus).natAbs ∣ K.natAbs ∧
        (K = 0 ∨ Nat.gcd X (Uplus * Uminus).natAbs ≤ K.natAbs) := by
  dsimp only
  let A : ℕ := (n + j₁) * (n + j₂)
  let B : ℕ := upperTermAfterFour n d t i₁ *
    upperTermAfterFour n d t i₂
  let X : ℕ := canonicalOwnerCell data j₁ i₁ *
    canonicalOwnerCell data j₁ i₂ *
    canonicalOwnerCell data j₂ i₁ *
    canonicalOwnerCell data j₂ i₂
  let Mplus : ℕ := canonicalOwnerCell data j₁ i₁ *
    canonicalOwnerCell data j₂ i₂
  let Mminus : ℕ := canonicalOwnerCell data j₁ i₂ *
    canonicalOwnerCell data j₂ i₁
  let c : ℤ := (((j₂ : ℤ) - j₁) ^ 2) *
    (k5UpperFourMultiplier t i₁ : ℤ) *
    (k5UpperFourMultiplier t i₂ : ℤ)
  let e : ℤ := ((i₂ : ℤ) - i₁) ^ 2
  let UT : ℤ := k5ProperTangentRowQuotient n d t j₁ j₂ i₁ i₂
  let VT : ℤ := k5ProperTangentColumnQuotient n d t j₁ j₂ i₁ i₂
  let K : ℤ := c * UT + e * VT
  obtain ⟨a, b, hcop, hA, hB, Uplus, Uminus, hplus, hminus, hS⟩ :=
    k5_fullyOwned_opposite_secant_cofactor_identity data
      hj₁ hj₂ hi₁ hi₂ hjneq hineq hfour
      hj₁one hj₂one hi₁one hi₂one
  have hXpos : 0 < X := by
    dsimp [X]
    have h₁₁ := canonicalOwnerCell_pos data (j := j₁) (i := i₁)
    have h₁₂ := canonicalOwnerCell_pos data (j := j₁) (i := i₂)
    have h₂₁ := canonicalOwnerCell_pos data (j := j₂) (i := i₁)
    have h₂₂ := canonicalOwnerCell_pos data (j := j₂) (i := i₂)
    positivity
  have hA' : A = X * a := by simpa [A, X] using hA
  have hB' : B = X * b := by simpa [B, X] using hB
  have ha : A / X = a := by
    rw [hA', Nat.mul_div_cancel_left a hXpos]
  have hb : B / X = b := by
    rw [hB', Nat.mul_div_cancel_left b hXpos]
  have htangent :=
    k5_proper_global_crossing_dvd_coprime_cofactor_tangent_combination
      data hj₁ hj₂ hi₁ hi₂ hjneq hineq hfour
      hj₁one hj₂one hi₁one hi₂one heq
  have htangent' : Nat.Coprime (A / X) (B / X) ∧
      (X : ℤ) ∣ UT * (A / X : ℕ) + VT * (B / X : ℕ) := by
    simpa [A, B, X, UT, VT] using htangent
  have hS' : Uplus * Uminus = c * (B / X : ℕ) - e * (A / X : ℕ) := by
    simpa [c, e, ha, hb] using hS
  have hdet : Nat.gcd X (Uplus * Uminus).natAbs ∣ K.natAbs := by
    apply coprime_cofactor_determinant_gcd_dvd htangent'.1 htangent'.2 hS'
  have hzeroOrBound :
      K = 0 ∨ Nat.gcd X (Uplus * Uminus).natAbs ≤ K.natAbs := by
    by_cases hK : K = 0
    · exact Or.inl hK
    · right
      exact Nat.le_of_dvd (Int.natAbs_pos.mpr hK) hdet
  exact ⟨Uplus, Uminus,
    by simpa [Mplus] using hplus,
    by simpa [Mminus] using hminus,
    hS', by simpa [K, UT, VT, c, e] using hdet,
    by simpa [K, UT, VT, c, e] using hzeroOrBound⟩

#print axioms coprime_cofactor_determinant_gcd_dvd
#print axioms local_tangent_opposite_secant_gcd_dvd_coefficient
#print axioms local_tangent_opposite_secant_gcd_zero_or_le_coefficient
#print axioms k5_proper_global_opposite_secant_tangent_determinant_gcd

end Erdos686Variant
end Erdos686
