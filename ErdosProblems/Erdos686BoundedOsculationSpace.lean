/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import ErdosProblems.Erdos686OsculationKernel
import ErdosProblems.Erdos686OsculationTaylor
import Mathlib.LinearAlgebra.Dimension.Finite

/-!
# Erdős 686: canonical bounded osculation space

This module separates three objects which must not be conflated:

* the integral osculation lattice `Lambda_r(S)`;
* the rational span of its coefficient-bounded points `V_B(S)`;
* the full rational jet kernel `K_r(S)`.

No equality between `V_B(S)` and `K_r(S)` is asserted without a separate
spanning theorem.
-/

namespace Erdos686
namespace Erdos686Variant

open scoped BigOperators

/-- Support data for one value condition and one directional condition at each
of `m` cells. -/
structure OsculationSupportData (m : ℕ) where
  j : Fin m → ℤ
  rho : Fin m → ℤ
  b : Fin m → ℤ
  A : Fin m → ℤ

/-- The exact row count of the arithmetic osculation matrix. -/
theorem osculation_constraint_row_count (m : ℕ) :
    Fintype.card (Fin (2 * m)) = 2 * m := by
  simp

@[simp]
theorem osculationEvaluate_zero {r : ℕ} (x y : ℤ) :
    osculationEvaluate (0 : OsculationMonomial r → ℤ) x y = 0 := by
  simp [osculationEvaluate]

@[simp]
theorem osculationEvaluate_add {r : ℕ}
    (c d : OsculationMonomial r → ℤ) (x y : ℤ) :
    osculationEvaluate (c + d) x y =
      osculationEvaluate c x y + osculationEvaluate d x y := by
  simp [osculationEvaluate, add_mul, Finset.sum_add_distrib]

@[simp]
theorem osculationEvaluate_neg {r : ℕ}
    (c : OsculationMonomial r → ℤ) (x y : ℤ) :
    osculationEvaluate (-c) x y = -osculationEvaluate c x y := by
  simp [osculationEvaluate, Finset.sum_neg_distrib]

@[simp]
theorem osculationEvaluateDX_zero {r : ℕ} (x y : ℤ) :
    osculationEvaluateDX (0 : OsculationMonomial r → ℤ) x y = 0 := by
  simp [osculationEvaluateDX]

@[simp]
theorem osculationEvaluateDX_add {r : ℕ}
    (c d : OsculationMonomial r → ℤ) (x y : ℤ) :
    osculationEvaluateDX (c + d) x y =
      osculationEvaluateDX c x y + osculationEvaluateDX d x y := by
  simp [osculationEvaluateDX, add_mul, Finset.sum_add_distrib]

@[simp]
theorem osculationEvaluateDX_neg {r : ℕ}
    (c : OsculationMonomial r → ℤ) (x y : ℤ) :
    osculationEvaluateDX (-c) x y = -osculationEvaluateDX c x y := by
  simp [osculationEvaluateDX, Finset.sum_neg_distrib]

@[simp]
theorem osculationEvaluateDY_zero {r : ℕ} (x y : ℤ) :
    osculationEvaluateDY (0 : OsculationMonomial r → ℤ) x y = 0 := by
  simp [osculationEvaluateDY]

@[simp]
theorem osculationEvaluateDY_add {r : ℕ}
    (c d : OsculationMonomial r → ℤ) (x y : ℤ) :
    osculationEvaluateDY (c + d) x y =
      osculationEvaluateDY c x y + osculationEvaluateDY d x y := by
  simp [osculationEvaluateDY, add_mul, Finset.sum_add_distrib]

@[simp]
theorem osculationEvaluateDY_neg {r : ℕ}
    (c : OsculationMonomial r → ℤ) (x y : ℤ) :
    osculationEvaluateDY (-c) x y = -osculationEvaluateDY c x y := by
  simp [osculationEvaluateDY, Finset.sum_neg_distrib]

/-- The directional value `b_e*dF/dX + A_e*dF/dY` at a support cell. -/
def osculationDirectionalValue {r m : ℕ}
    (S : OsculationSupportData m) (e : Fin m)
    (c : OsculationMonomial r → ℤ) : ℤ :=
  S.b e * osculationEvaluateDX c (S.j e) (S.rho e) +
    S.A e * osculationEvaluateDY c (S.j e) (S.rho e)

@[simp]
theorem osculationDirectionalValue_zero {r m : ℕ}
    (S : OsculationSupportData m) (e : Fin m) :
    osculationDirectionalValue S e (0 : OsculationMonomial r → ℤ) = 0 := by
  simp [osculationDirectionalValue]

@[simp]
theorem osculationDirectionalValue_add {r m : ℕ}
    (S : OsculationSupportData m) (e : Fin m)
    (c d : OsculationMonomial r → ℤ) :
    osculationDirectionalValue S e (c + d) =
      osculationDirectionalValue S e c +
        osculationDirectionalValue S e d := by
  simp [osculationDirectionalValue]
  ring

@[simp]
theorem osculationDirectionalValue_neg {r m : ℕ}
    (S : OsculationSupportData m) (e : Fin m)
    (c : OsculationMonomial r → ℤ) :
    osculationDirectionalValue S e (-c) =
      -osculationDirectionalValue S e c := by
  simp [osculationDirectionalValue]
  ring

/-- The integral osculation lattice `Lambda_r(S)`.  Membership is exactly one
value equation and one directional equation at every support cell. -/
def integralOsculationLattice {r m : ℕ}
    (S : OsculationSupportData m) :
    AddSubgroup (OsculationMonomial r → ℤ) where
  carrier := {c | ∀ e,
    osculationEvaluate c (S.j e) (S.rho e) = 0 ∧
      osculationDirectionalValue S e c = 0}
  zero_mem' := by
    intro e
    simp
  add_mem' := by
    intro c d hc hd e
    rcases hc e with ⟨hcv, hcd⟩
    rcases hd e with ⟨hdv, hdd⟩
    constructor
    · simp [hcv, hdv]
    · simp [hcd, hdd]
  neg_mem' := by
    intro c hc e
    rcases hc e with ⟨hcv, hcd⟩
    constructor
    · simp [hcv]
    · simp [hcd]

/-- Coefficient sup norm on the finite total-degree basis. -/
def coefficientSupNorm {r : ℕ}
    (c : OsculationMonomial r → ℤ) : ℕ :=
  Finset.univ.sup fun u => (c u).natAbs

theorem coefficientSupNorm_le_iff {r B : ℕ}
    (c : OsculationMonomial r → ℤ) :
    coefficientSupNorm c ≤ B ↔ ∀ u, (c u).natAbs ≤ B := by
  simp [coefficientSupNorm]

/-- Coefficientwise extension from integers to rationals. -/
def rationalizeOsculationCoefficients {r : ℕ}
    (c : OsculationMonomial r → ℤ) : OsculationMonomial r → ℚ :=
  fun u => (c u : ℚ)

/-- The canonical bounded integral generating set. -/
def boundedIntegralOsculationGenerators {r m : ℕ}
    (S : OsculationSupportData m) (B : ℕ) :
    Set (OsculationMonomial r → ℚ) :=
  {v | ∃ c : OsculationMonomial r → ℤ,
    c ∈ integralOsculationLattice S ∧
      coefficientSupNorm c ≤ B ∧
      v = rationalizeOsculationCoefficients c}

/-- The canonical rational bounded space
`V_B(S) = span_Q {F in Lambda_r(S) : ||F||_infinity <= B}`. -/
noncomputable def boundedOsculationSpace {r m : ℕ}
    (S : OsculationSupportData m) (B : ℕ) :
    Submodule ℚ (OsculationMonomial r → ℚ) :=
  Submodule.span ℚ (boundedIntegralOsculationGenerators S B)

/-- Rational evaluation of a coefficient vector. -/
noncomputable def osculationEvaluateQ {r : ℕ}
    (c : OsculationMonomial r → ℚ) (x y : ℤ) : ℚ :=
  ∑ u, c u * (osculationMonomialValue u x y : ℚ)

@[simp]
theorem osculationEvaluateQ_zero {r : ℕ} (x y : ℤ) :
    osculationEvaluateQ (0 : OsculationMonomial r → ℚ) x y = 0 := by
  simp [osculationEvaluateQ]

@[simp]
theorem osculationEvaluateQ_add {r : ℕ}
    (c d : OsculationMonomial r → ℚ) (x y : ℤ) :
    osculationEvaluateQ (c + d) x y =
      osculationEvaluateQ c x y + osculationEvaluateQ d x y := by
  simp [osculationEvaluateQ, add_mul, Finset.sum_add_distrib]

@[simp]
theorem osculationEvaluateQ_smul {r : ℕ}
    (a : ℚ) (c : OsculationMonomial r → ℚ) (x y : ℤ) :
    osculationEvaluateQ (a • c) x y =
      a * osculationEvaluateQ c x y := by
  simp [osculationEvaluateQ, Finset.mul_sum, mul_assoc]

/-- The rational evaluation kernel at one integral point. -/
noncomputable def osculationEvaluationKernelQ {r : ℕ} (x y : ℤ) :
    Submodule ℚ (OsculationMonomial r → ℚ) where
  carrier := {c | osculationEvaluateQ c x y = 0}
  zero_mem' := by simp
  add_mem' := by
    intro c d hc hd
    simp [hc, hd]
  smul_mem' := by
    intro a c hc
    simp [hc]

@[simp]
theorem osculationEvaluateQ_rationalize {r : ℕ}
    (c : OsculationMonomial r → ℤ) (x y : ℤ) :
    osculationEvaluateQ (rationalizeOsculationCoefficients c) x y =
      (osculationEvaluate c x y : ℚ) := by
  simp [osculationEvaluateQ, rationalizeOsculationCoefficients,
    osculationEvaluate]

/-- The cancellation theorem extends from every bounded integral lattice point
to the whole canonical rational bounded space. -/
theorem boundedOsculationSpace_le_evaluationKernel
    {r m B : ℕ} (S : OsculationSupportData m) (n d : ℤ)
    (hcancel : ∀ c : OsculationMonomial r → ℤ,
      c ∈ integralOsculationLattice S →
      coefficientSupNorm c ≤ B →
      osculationEvaluate c (-n) (-d) = 0) :
    boundedOsculationSpace S B ≤
      osculationEvaluationKernelQ (-n) (-d) := by
  apply Submodule.span_le.mpr
  rintro v ⟨c, hc, hB, rfl⟩
  change osculationEvaluateQ
    (rationalizeOsculationCoefficients c) (-n) (-d) = 0
  rw [osculationEvaluateQ_rationalize]
  exact_mod_cast hcancel c hc hB

/-- Every element of `V_B(S)` vanishes at the target once cancellation is
proved on the bounded integral generators. -/
theorem boundedOsculationSpace_evaluate_eq_zero
    {r m B : ℕ} (S : OsculationSupportData m) (n d : ℤ)
    (hcancel : ∀ c : OsculationMonomial r → ℤ,
      c ∈ integralOsculationLattice S →
      coefficientSupNorm c ≤ B →
      osculationEvaluate c (-n) (-d) = 0)
    (F : OsculationMonomial r → ℚ)
    (hF : F ∈ boundedOsculationSpace S B) :
    osculationEvaluateQ F (-n) (-d) = 0 := by
  exact boundedOsculationSpace_le_evaluationKernel S n d hcancel hF

/-- A uniform square-divisibility and strict-height certificate supplies the
bounded-generator cancellation hypothesis. -/
theorem boundedOsculationSpace_evaluate_eq_zero_of_square_bound
    {r m B M : ℕ} (S : OsculationSupportData m) (n d : ℤ)
    (hdvd : ∀ c : OsculationMonomial r → ℤ,
      c ∈ integralOsculationLattice S →
      coefficientSupNorm c ≤ B →
      ((M ^ 2 : ℕ) : ℤ) ∣ osculationEvaluate c (-n) (-d))
    (hsmall : ∀ c : OsculationMonomial r → ℤ,
      c ∈ integralOsculationLattice S →
      coefficientSupNorm c ≤ B →
      (osculationEvaluate c (-n) (-d)).natAbs < M ^ 2)
    (F : OsculationMonomial r → ℚ)
    (hF : F ∈ boundedOsculationSpace S B) :
    osculationEvaluateQ F (-n) (-d) = 0 := by
  apply boundedOsculationSpace_evaluate_eq_zero S n d _ F hF
  intro c hc hB
  exact osculation_evaluate_eq_zero_of_product_square_bound
    c M n d (hdvd c hc hB) (hsmall c hc hB)

/-- The audited exact cancellation threshold.  Its optimality is supplied by
the checked integer certificate, not by this definitional equality. -/
def osculationCancellationThreshold : ℕ := 44

theorem osculationCancellationThreshold_eq :
    osculationCancellationThreshold = 44 := rfl

/-- Rationalized `2m`-row constraint map. -/
noncomputable def rationalOsculationConstraintMap {r m : ℕ}
    (S : OsculationSupportData m) :
    (OsculationMonomial r → ℚ) →ₗ[ℚ] (Fin (2 * m) → ℚ) where
  toFun c row :=
    ∑ u, (osculationConstraintMatrix r m S.j S.rho S.b S.A row u : ℚ) * c u
  map_add' := by
    intro c d
    funext row
    simp [mul_add, Finset.sum_add_distrib]
  map_smul' := by
    intro a c
    funext row
    simp [Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]

/-- The full rational jet space `K_r(S)`. -/
noncomputable def fullRationalJetSpace {r m : ℕ}
    (S : OsculationSupportData m) :
    Submodule ℚ (OsculationMonomial r → ℚ) :=
  (rationalOsculationConstraintMap S).ker

/-- Rank-nullity with exactly `2m` target coordinates gives
`dim K_r(S) >= N_r - 2m`. -/
theorem fullRationalJetSpace_finrank_lower {r m : ℕ}
    (S : OsculationSupportData m) :
    osculationMonomialCount r - 2 * m ≤
      Module.finrank ℚ (fullRationalJetSpace S) := by
  let L := rationalOsculationConstraintMap S
  have hrange : Module.finrank ℚ (LinearMap.range L) ≤ 2 * m := by
    calc
      Module.finrank ℚ (LinearMap.range L) ≤
          Module.finrank ℚ (Fin (2 * m) → ℚ) :=
        Submodule.finrank_le (LinearMap.range L)
      _ = 2 * m := by simp [Module.finrank_fin_fun]
  have hnull := LinearMap.finrank_ker_add_finrank_range L
  have hdomain :
      Module.finrank ℚ (OsculationMonomial r → ℚ) =
        osculationMonomialCount r := by
    simp [Module.finrank_fin_fun, osculationMonomialBasis_card]
  change osculationMonomialCount r - 2 * m ≤
    Module.finrank ℚ (LinearMap.ker L)
  rw [← hdomain]
  omega

/-- The extra hypothesis required before any full-space fixed-divisor theorem
may be transferred to the bounded space. -/
def BoundedSpaceSpansFullJet {r m : ℕ}
    (S : OsculationSupportData m) (B : ℕ) : Prop :=
  boundedOsculationSpace S B = fullRationalJetSpace S

#print axioms osculation_constraint_row_count
#print axioms coefficientSupNorm_le_iff
#print axioms boundedOsculationSpace_le_evaluationKernel
#print axioms boundedOsculationSpace_evaluate_eq_zero
#print axioms boundedOsculationSpace_evaluate_eq_zero_of_square_bound
#print axioms osculationCancellationThreshold_eq
#print axioms fullRationalJetSpace_finrank_lower

end Erdos686Variant
end Erdos686
