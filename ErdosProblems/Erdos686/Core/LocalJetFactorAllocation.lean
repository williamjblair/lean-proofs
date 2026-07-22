/- leanprover/lean4:v4.29.1 mathlib v4.29.1 -/
import ErdosProblems.Erdos686.Core.OsculationDichotomy
import Mathlib.Algebra.MvPolynomial.PDeriv

/-!
# Erdős 686: exact local allocation of a product jet

This module corrects the tempting but false assertion that a factor of an
osculating polynomial automatically inherits every support jet.  For the
support functional

`delta = b * partial_X + A * partial_Y`,

the Leibniz rule leaves three genuinely different possibilities.  They are
recorded below over the actual ring of integral bivariate polynomials and at
an actual integral specialization.
-/

namespace Erdos686
namespace Erdos686Variant

/-- The polynomial-valued support differential
`b * partial_X + A * partial_Y`. -/
noncomputable def supportDifferential (b A : ℤ)
    (F : BivariateIntPolynomial) : BivariateIntPolynomial :=
  MvPolynomial.C b * MvPolynomial.pderiv (0 : Fin 2) F +
    MvPolynomial.C A * MvPolynomial.pderiv (1 : Fin 2) F

/-- Evaluation of the support differential at an integral point. -/
noncomputable def supportDifferentialAt
    (p : Fin 2 → ℤ) (b A : ℤ)
    (F : BivariateIntPolynomial) : ℤ :=
  evalIntAt p (supportDifferential b A F)

/-- Exact polynomial product rule for the support differential. -/
theorem supportDifferential_mul (b A : ℤ)
    (H P : BivariateIntPolynomial) :
    supportDifferential b A (H * P) =
      supportDifferential b A H * P +
        H * supportDifferential b A P := by
  simp only [supportDifferential, MvPolynomial.pderiv_mul]
  ring

/-- Exact evaluated product rule

`delta(H P)(p) = delta H(p) P(p) + H(p) delta P(p)`.
-/
theorem supportDifferentialAt_mul
    (p : Fin 2 → ℤ) (b A : ℤ)
    (H P : BivariateIntPolynomial) :
    supportDifferentialAt p b A (H * P) =
      supportDifferentialAt p b A H * evalIntAt p P +
        evalIntAt p H * supportDifferentialAt p b A P := by
  rw [supportDifferentialAt, supportDifferential_mul]
  simp only [map_add, map_mul]
  rfl

/-- A factorization `F = H * P` gives the exact value and derivative
identities at a full support jet of `F`. -/
theorem local_jet_product_identities
    (p : Fin 2 → ℤ) (b A : ℤ)
    (F H P : BivariateIntPolynomial)
    (hfactor : F = H * P)
    (hvalue : evalIntAt p F = 0)
    (hdelta : supportDifferentialAt p b A F = 0) :
    evalIntAt p H * evalIntAt p P = 0 ∧
      supportDifferentialAt p b A H * evalIntAt p P +
          evalIntAt p H * supportDifferentialAt p b A P = 0 := by
  constructor
  · rw [hfactor, map_mul] at hvalue
    exact hvalue
  · rw [hfactor, supportDifferentialAt_mul] at hdelta
    exact hdelta

/-- Allocation case 1: when `H(p)` is nonzero, the quotient `P` inherits
both the value condition and the directional-derivative condition. -/
theorem local_jet_allocates_to_right_of_left_value_ne_zero
    (p : Fin 2 → ℤ) (b A : ℤ)
    (F H P : BivariateIntPolynomial)
    (hfactor : F = H * P)
    (hvalue : evalIntAt p F = 0)
    (hdelta : supportDifferentialAt p b A F = 0)
    (hH : evalIntAt p H ≠ 0) :
    evalIntAt p P = 0 ∧ supportDifferentialAt p b A P = 0 := by
  obtain ⟨hprod, hleibniz⟩ :=
    local_jet_product_identities p b A F H P hfactor hvalue hdelta
  have hP : evalIntAt p P = 0 :=
    (mul_eq_zero.mp hprod).resolve_left hH
  refine ⟨hP, ?_⟩
  rw [hP, mul_zero, zero_add] at hleibniz
  exact (mul_eq_zero.mp hleibniz).resolve_left hH

/-- Allocation case 2: if `H` has a simple zero in the support direction,
then the full product jet forces only the value `P(p)=0`; no derivative of
`P` is used. -/
theorem local_jet_simple_left_factor_forces_right_value
    (p : Fin 2 → ℤ) (b A : ℤ)
    (F H P : BivariateIntPolynomial)
    (hfactor : F = H * P)
    (hvalue : evalIntAt p F = 0)
    (hdelta : supportDifferentialAt p b A F = 0)
    (hH : evalIntAt p H = 0)
    (hdeltaH : supportDifferentialAt p b A H ≠ 0) :
    evalIntAt p P = 0 := by
  obtain ⟨_, hleibniz⟩ :=
    local_jet_product_identities p b A F H P hfactor hvalue hdelta
  rw [hH, zero_mul, add_zero] at hleibniz
  exact (mul_eq_zero.mp hleibniz).resolve_left hdeltaH

/-- Converse form of allocation case 2.  Once `H(p)=0` and `P(p)=0`, the
product has the full support jet without any hypothesis on `delta P(p)`.
This makes the word "only" in the classification literal. -/
theorem product_has_full_jet_of_left_and_right_values_zero
    (p : Fin 2 → ℤ) (b A : ℤ)
    (H P : BivariateIntPolynomial)
    (hH : evalIntAt p H = 0)
    (hP : evalIntAt p P = 0) :
    evalIntAt p (H * P) = 0 ∧
      supportDifferentialAt p b A (H * P) = 0 := by
  constructor
  · simp [hH, hP]
  · rw [supportDifferentialAt_mul, hH, hP]
    ring

/-- Allocation case 3: if `H` itself carries the full jet, then `H * P`
carries it for every quotient `P`.  Thus the quotient is locally
unrestricted by these two product-jet equations. -/
theorem product_has_full_jet_of_left_full_jet
    (p : Fin 2 → ℤ) (b A : ℤ)
    (H P : BivariateIntPolynomial)
    (hH : evalIntAt p H = 0)
    (hdeltaH : supportDifferentialAt p b A H = 0) :
    evalIntAt p (H * P) = 0 ∧
      supportDifferentialAt p b A (H * P) = 0 := by
  constructor
  · simp [hH]
  · rw [supportDifferentialAt_mul, hH, hdeltaH]
    ring

#print axioms supportDifferential_mul
#print axioms supportDifferentialAt_mul
#print axioms local_jet_product_identities
#print axioms local_jet_allocates_to_right_of_left_value_ne_zero
#print axioms local_jet_simple_left_factor_forces_right_value
#print axioms product_has_full_jet_of_left_and_right_values_zero
#print axioms product_has_full_jet_of_left_full_jet

end Erdos686Variant
end Erdos686
