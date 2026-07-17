/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import Mathlib

/-!
# Erdős 686: exact local factor allocation for first-order jets

The earlier common-component wording is not used here.  At a support point,
`delta = b * d/dX + A * d/dY` is represented by a value homomorphism together
with two derivations.  The product rule determines exactly which factor carries
which part of the jet.
-/

namespace Erdos686
namespace Erdos686Variant

/-- Algebraic data for evaluation at a point and the two formal partial
 derivatives there.  The displayed coefficients define
 `delta = b * dX + A * dY`. -/
structure BivariateSupportFunctional
    (R P : Type*) [CommRing R] [CommRing P] where
  eval : P →+* R
  dX : P →+ R
  dY : P →+ R
  dX_mul : ∀ F G, dX (F * G) = dX F * eval G + eval F * dX G
  dY_mul : ∀ F G, dY (F * G) = dY F * eval G + eval F * dY G
  b : R
  A : R

variable {R P : Type*} [CommRing R] [CommRing P]

/-- The support directional functional `b*d/dX + A*d/dY`. -/
def BivariateSupportFunctional.delta
    (J : BivariateSupportFunctional R P) (F : P) : R :=
  J.b * J.dX F + J.A * J.dY F

/-- Exact Leibniz rule for the support directional functional. -/
theorem BivariateSupportFunctional.delta_mul
    (J : BivariateSupportFunctional R P) (H Q : P) :
    J.delta (H * Q) =
      J.delta H * J.eval Q + J.eval H * J.delta Q := by
  rw [BivariateSupportFunctional.delta, J.dX_mul, J.dY_mul]
  simp only [map_mul, BivariateSupportFunctional.delta]
  ring

/-- Exact value and directional product rules at a support point. -/
theorem local_support_product_rule
    (J : BivariateSupportFunctional R P) (H Q : P) :
    J.eval (H * Q) = J.eval H * J.eval Q ∧
      J.delta (H * Q) =
        J.delta H * J.eval Q + J.eval H * J.delta Q := by
  exact ⟨map_mul J.eval H Q, J.delta_mul H Q⟩

section Domain

variable [IsDomain R]

/-- Case 1.  If the left factor does not vanish, the right factor carries the
 full value-and-direction jet. -/
theorem local_factor_allocation_of_left_value_ne_zero
    (J : BivariateSupportFunctional R P) (H Q : P)
    (hH : J.eval H ≠ 0)
    (hvalue : J.eval (H * Q) = 0)
    (hdirection : J.delta (H * Q) = 0) :
    J.eval Q = 0 ∧ J.delta Q = 0 := by
  have hQ : J.eval Q = 0 := by
    exact (mul_eq_zero.mp (by simpa using hvalue)).resolve_left hH
  constructor
  · exact hQ
  · have hprod : J.eval H * J.delta Q = 0 := by
      rw [J.delta_mul, hQ, mul_zero, add_zero] at hdirection
      exact hdirection
    exact (mul_eq_zero.mp hprod).resolve_left hH

/-- Case 2.  If the left factor vanishes but its directional derivative does
 not, the product jet forces only the value of the right factor to vanish. -/
theorem local_factor_allocation_of_left_simple_zero
    (J : BivariateSupportFunctional R P) (H Q : P)
    (hH : J.eval H = 0)
    (hdeltaH : J.delta H ≠ 0)
    (hdirection : J.delta (H * Q) = 0) :
    J.eval Q = 0 := by
  have hprod : J.delta H * J.eval Q = 0 := by
    rw [J.delta_mul, hH, zero_mul, add_zero] at hdirection
    exact hdirection
  exact (mul_eq_zero.mp hprod).resolve_left hdeltaH

/-- Case 3.  If the left factor carries the full jet, the right factor is
 locally unrestricted: every right factor gives a product with zero value and
 zero directional derivative. -/
theorem local_factor_allocation_of_left_full_jet
    (J : BivariateSupportFunctional R P) (H : P)
    (hH : J.eval H = 0) (hdeltaH : J.delta H = 0) :
    ∀ Q : P, J.eval (H * Q) = 0 ∧ J.delta (H * Q) = 0 := by
  intro Q
  constructor
  · simp [map_mul, hH]
  · rw [J.delta_mul, hH, hdeltaH]
    ring

/-- Exhaustive three-way allocation.  This is the replacement for the false
 statement that a common factor automatically inherits every support jet. -/
theorem local_factor_allocation_trichotomy
    (J : BivariateSupportFunctional R P) (H Q : P)
    (hvalue : J.eval (H * Q) = 0)
    (hdirection : J.delta (H * Q) = 0) :
    (J.eval H ≠ 0 ∧ J.eval Q = 0 ∧ J.delta Q = 0) ∨
      (J.eval H = 0 ∧ J.delta H ≠ 0 ∧ J.eval Q = 0) ∨
      (J.eval H = 0 ∧ J.delta H = 0) := by
  by_cases hH : J.eval H = 0
  · by_cases hdeltaH : J.delta H = 0
    · exact Or.inr (Or.inr ⟨hH, hdeltaH⟩)
    · exact Or.inr (Or.inl
        ⟨hH, hdeltaH,
          local_factor_allocation_of_left_simple_zero
            J H Q hH hdeltaH hdirection⟩)
  · exact Or.inl
      ⟨hH, local_factor_allocation_of_left_value_ne_zero
        J H Q hH hvalue hdirection⟩

end Domain

#print axioms BivariateSupportFunctional.delta_mul
#print axioms local_support_product_rule
#print axioms local_factor_allocation_of_left_value_ne_zero
#print axioms local_factor_allocation_of_left_simple_zero
#print axioms local_factor_allocation_of_left_full_jet
#print axioms local_factor_allocation_trichotomy

end Erdos686Variant
end Erdos686
