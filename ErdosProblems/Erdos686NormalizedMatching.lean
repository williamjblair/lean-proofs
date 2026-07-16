/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import ErdosProblems.Erdos686ReflectedAlignmentSquareLift

/-!
# Erdős 686: normalized matching arithmetic

This module banks the cancellation step needed to pass from a factorial
owner-square congruence to its reduced normalized form.  The cancellation is
made explicit: the owner modulus must have only prime support above the block
length, while the removed prefactor divides `(k-1)!`.
-/

namespace Erdos686
namespace Erdos686Variant

/-- Factorial-free normalized linear form at an owner cell. -/
def normalizedMatchingForm
    (a b sign delta x : ℤ) : ℤ :=
  b * delta - (4 * sign * a - b) * x

/-- The corresponding factorial-weighted form after writing the two local
coefficients as `q*b` and `q*a`. -/
def factorialMatchingForm
    (q a b sign delta x : ℤ) : ℤ :=
  (q * b) * delta - (4 * sign * (q * a) - q * b) * x

/-- Exact algebraic normalization identity. -/
theorem factorialMatchingForm_eq_prefactor_mul_normalized
    (q a b sign delta x : ℤ) :
    factorialMatchingForm q a b sign delta x =
      q * normalizedMatchingForm a b sign delta x := by
  simp only [factorialMatchingForm, normalizedMatchingForm]
  ring

/-- Equivalent upper-term presentation of the normalized form. -/
theorem normalizedMatchingForm_eq_upper_form
    (a b sign delta x : ℤ) :
    normalizedMatchingForm a b sign delta x =
      b * (x + delta) - 4 * sign * a * x := by
  simp only [normalizedMatchingForm]
  ring

/-- A natural number supported only on primes above `k` is coprime to
`(k-1)!`. -/
theorem largePrimeSupport_coprime_factorial
    {P k : ℕ}
    (hsupport : ∀ p, p.Prime → p ∣ P → k < p) :
    P.Coprime (k - 1).factorial := by
  by_contra hnot
  obtain ⟨p, hp, hpP, hpFact⟩ :=
    Nat.Prime.not_coprime_iff_dvd.mp hnot
  have hple : p ≤ k - 1 := hp.dvd_factorial.mp hpFact
  have hklt := hsupport p hp hpP
  omega

/-- Consequently the composite owner square is coprime, over the integers,
to every prefactor dividing `(k-1)!`. -/
theorem largePrimeSupport_square_isCoprime_of_dvd_factorial
    {P q k : ℕ}
    (hsupport : ∀ p, p.Prime → p ∣ P → k < p)
    (hq : q ∣ (k - 1).factorial) :
    IsCoprime ((P : ℤ) ^ 2) (q : ℤ) := by
  have hPq : P.Coprime q :=
    (largePrimeSupport_coprime_factorial hsupport).coprime_dvd_right hq
  exact (hPq.pow_left 2).isCoprime

/-- Cancellation modulo a possibly composite square, with the unit
hypothesis stated explicitly. -/
theorem owner_square_normalized_iff_of_isCoprime
    {P q a b sign delta x : ℤ}
    (hcop : IsCoprime (P ^ 2) q) :
    P ^ 2 ∣ factorialMatchingForm q a b sign delta x ↔
      P ^ 2 ∣ normalizedMatchingForm a b sign delta x := by
  rw [factorialMatchingForm_eq_prefactor_mul_normalized]
  constructor
  · exact hcop.dvd_of_dvd_mul_left
  · exact fun h => dvd_mul_of_dvd_right h q

/-- High-prime owner specialization of the normalized square equivalence.
This is the precise composite-modulus repair required by the imported
normalized-matching argument. -/
theorem owner_square_normalized_iff_of_largePrimeSupport
    {P q k : ℕ} {a b sign delta x : ℤ}
    (hsupport : ∀ p, p.Prime → p ∣ P → k < p)
    (hq : q ∣ (k - 1).factorial) :
    ((P : ℤ) ^ 2 ∣
        factorialMatchingForm (q : ℤ) a b sign delta x) ↔
      ((P : ℤ) ^ 2 ∣ normalizedMatchingForm a b sign delta x) := by
  exact owner_square_normalized_iff_of_isCoprime
    (largePrimeSupport_square_isCoprime_of_dvd_factorial hsupport hq)

#print axioms factorialMatchingForm_eq_prefactor_mul_normalized
#print axioms normalizedMatchingForm_eq_upper_form
#print axioms largePrimeSupport_coprime_factorial
#print axioms largePrimeSupport_square_isCoprime_of_dvd_factorial
#print axioms owner_square_normalized_iff_of_isCoprime
#print axioms owner_square_normalized_iff_of_largePrimeSupport

end Erdos686Variant
end Erdos686
