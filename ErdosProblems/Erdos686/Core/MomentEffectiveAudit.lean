/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import ErdosProblems.Erdos686.Core.BarycentricMomentLadder
import ErdosProblems.Erdos686.Core.EffectiveIntersectionInterface
import Mathlib.Analysis.Polynomial.CauchyBound

/-!
# Erdős 686: exact moment and effective-intersection audit bridges

This module records two interfaces requested by the corrected osculation
audit without changing the frozen source modules.  First, it packages the
finite generating identity at the first surviving moment and rewrites the
canonical-square quotient degree in the audited normal form
`m*(k-2)-q*k`.  Second, it gives the support-dependent resultant an explicit
coefficient-derived Cauchy root bound and proves that the existing finite
candidate rectangle contains every common integral zero.
-/

namespace Erdos686
namespace Erdos686Variant

open Polynomial

variable {R : Type*} [CommRing R]
variable {α : Type*} [DecidableEq α]

/-- Exact finite generating identity at the first candidate moment.  This is
the denominator-cleared generating-series statement: all lower moments give
the factor `X^q`, and the remaining numerator starts with `mu_q`. -/
theorem momentNumerator_first_block_generating_identity
    (S : Finset α) (j w : α → R) (q : ℕ)
    (hzero : ∀ p < q, mu S j w p = 0) :
    momentNumerator S j w 0 =
      X ^ q * (C (mu S j w q) * reverseW S j +
        X * momentNumerator S j w (q + 1)) := by
  rw [momentNumerator_eq_X_pow_of_lower_moments S j w q hzero,
    momentNumerator_recurrence]

omit [DecidableEq α] in
/-- The rational `Delta_q` criterion with the moments substituted directly.
It is an exact iff, not merely a nonvanishing implication. -/
theorem rational_moment_block_zero_iff
    (S : Finset α) (j rho w : α → ℚ) {q k : ℕ} (hk : 3 ≤ k) :
    momentDelta k (mu S j w q) (nu S j rho w (q - 1)) = 0 ↔
      mu S j w q = 0 ∧ nu S j rho w (q - 1) = 0 := by
  exact rational_momentDelta_eq_zero_iff hk

/-- The exact quotient degree in the normal form from the audited report:
`m*(k-2)-q*k`.  The source theorem states the definitionally equivalent
form `k*(m-q)-2*m`; this bridge performs only natural-number arithmetic. -/
theorem matchingPhi_quotient_natDegree_eq_m_mul_k_sub_two_sub_q_mul_k
    {S : Finset α} {j rho w : α → ℤ}
    (hS : S.Nonempty) {q k : ℕ}
    (hq : 1 ≤ q) (hqcard : q ≤ S.card)
    (hmu : ∀ p < q, mu S j w p = 0)
    (hnu : ∀ p < q - 1, nu S j rho w p = 0)
    (hdelta : momentDelta k (mu S j w q) (nu S j rho w (q - 1)) ≠ 0)
    (Q : Polynomial ℤ)
    (hfactor : matchingPhi k (U S j rho w 0) (V S j w) = (W S j) ^ 2 * Q) :
    Q.natDegree = S.card * (k - 2) - q * k := by
  rw [matchingPhi_quotient_natDegree_eq_first_nonzero_moment_block
    hS hq hqcard hmu hnu hdelta Q hfactor]
  simp only [Nat.mul_sub_left_distrib]
  rw [Nat.mul_comm k S.card, Nat.mul_comm k q, Nat.mul_comm 2 S.card]
  rw [Nat.sub_sub, Nat.sub_sub, Nat.add_comm]

/-- A canonical, coefficient-dependent natural bound for the integral roots
of an integer polynomial: the ceiling of the Cauchy bound after embedding in
`Q[T]`. -/
noncomputable def integerCauchyRootBound (p : Polynomial ℤ) : ℕ :=
  ⌈Polynomial.cauchyBound (p.map (algebraMap ℤ ℚ))⌉₊

/-- Every integral root of a nonzero integer polynomial lies strictly below
the explicit coefficient-derived Cauchy bound. -/
theorem integer_root_natAbs_lt_cauchyRootBound
    {p : Polynomial ℤ} (hp : p ≠ 0) {t : ℤ} (ht : p.eval t = 0) :
    t.natAbs < integerCauchyRootBound p := by
  have hpQ : p.map (algebraMap ℤ ℚ) ≠ 0 :=
    (Polynomial.map_ne_zero_iff
      (Int.cast_injective : Function.Injective (algebraMap ℤ ℚ))).mpr hp
  have htQ : (p.map (algebraMap ℤ ℚ)).IsRoot (t : ℚ) := by
    rw [Polynomial.IsRoot.def, Polynomial.eval_intCast_map]
    simpa only [map_zero] using congrArg (algebraMap ℤ ℚ) ht
  have hnorm := htQ.norm_lt_cauchyBound hpQ
  rw [integerCauchyRootBound, Nat.lt_ceil]
  have habs : (t.natAbs : NNReal) = ‖(t : ℚ)‖₊ := by
    calc
      (t.natAbs : NNReal) = ‖t‖₊ := NNReal.natCast_natAbs t
      _ = ‖(t : ℚ)‖₊ := NNReal.eq (Int.norm_cast_rat t).symm
  rwa [habs]

/-- The finite candidate rectangle exported by an effective certificate
contains the sheared coordinates of every common integral zero. -/
theorem EffectiveIntersectionCertificate.common_zero_mem_candidatePairs
    {P Q : BivariateIntPolynomial}
    {originalCurve : (Fin 2 → ℤ) → Prop}
    (C : EffectiveIntersectionCertificate P Q originalCurve)
    (p : Fin 2 → ℤ)
    (hP : evalIntAt p P = 0)
    (hQ : evalIntAt p Q = 0) :
    (p 0 + C.lambda * p 1, p 1) ∈ C.candidatePairs := by
  obtain ⟨ht, hy, hbound, hcurve⟩ := C.common_zero_enumerated p hP hQ
  simp only [EffectiveIntersectionCertificate.candidatePairs,
    Finset.mem_biUnion, Finset.mem_image]
  exact ⟨p 0 + C.lambda * p 1, ht, p 1, hy, rfl⟩

/-- Full effective-interface audit package.  A common integral zero gives a
root of the supplied nonzero resultant, satisfies its canonical Cauchy bound,
gives a root of the supplied fiber gcd, belongs to both exact root lists and
their finite candidate rectangle, and passes verification on the original
curve. -/
theorem EffectiveIntersectionCertificate.common_zero_effective_package
    {P Q : BivariateIntPolynomial}
    {originalCurve : (Fin 2 → ℤ) → Prop}
    (C : EffectiveIntersectionCertificate P Q originalCurve)
    (p : Fin 2 → ℤ)
    (hP : evalIntAt p P = 0)
    (hQ : evalIntAt p Q = 0) :
    let t := p 0 + C.lambda * p 1
    C.resultant.eval t = 0 ∧
      t.natAbs < integerCauchyRootBound C.resultant ∧
      t.natAbs ≤ C.rootBound ∧
      t ∈ C.integralTRoots ∧
      (C.fiberGCD t).eval (p 1) = 0 ∧
      p 1 ∈ C.integralYRoots t ∧
      (t, p 1) ∈ C.candidatePairs ∧
      originalCurve p := by
  let t := p 0 + C.lambda * p 1
  have hR : C.resultant.eval t = 0 :=
    C.resultant_of_common_zero p hP hQ
  have hcauchy : t.natAbs < integerCauchyRootBound C.resultant :=
    integer_root_natAbs_lt_cauchyRootBound C.resultant_ne_zero hR
  have henum := C.common_zero_enumerated p hP hQ
  have hG : (C.fiberGCD t).eval (p 1) = 0 :=
    C.fiberGCD_of_common_zero p hP hQ
  have hpair : (t, p 1) ∈ C.candidatePairs :=
    C.common_zero_mem_candidatePairs p hP hQ
  exact ⟨hR, hcauchy, henum.2.2.1, henum.1, hG, henum.2.1,
    hpair, henum.2.2.2⟩

#print axioms momentNumerator_first_block_generating_identity
#print axioms rational_moment_block_zero_iff
#print axioms matchingPhi_quotient_natDegree_eq_m_mul_k_sub_two_sub_q_mul_k
#print axioms integer_root_natAbs_lt_cauchyRootBound
#print axioms EffectiveIntersectionCertificate.common_zero_mem_candidatePairs
#print axioms EffectiveIntersectionCertificate.common_zero_effective_package

end Erdos686Variant
end Erdos686
