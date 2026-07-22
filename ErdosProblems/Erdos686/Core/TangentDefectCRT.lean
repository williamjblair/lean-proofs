/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import ErdosProblems.Erdos686.Core.MatchingResultant
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Nat.ChineseRemainder

/-!
# Erdős 686: tangent defect after matching interpolation

This file proves the exact square-level Taylor congruence needed after the
ordinary matching resultant has been divided by the product of its pairwise
coprime owner moduli.  All moduli are allowed to be composite.

The local normalized owner congruence is supplied as

`P^2 ∣ b*y - (signedFourA-b)*x`.

If `Phi(j)=L*i`, `x=n+j`, and `y=d+i-j`, the common matching resultant

`R=L*(n+d)+Phi(-n)`

satisfies

`P^2 ∣ b*R-(signedFourA*L-b*Phi'(j))*x`.
-/

namespace Erdos686
namespace Erdos686Variant

open Polynomial

/-- The exact first-order Taylor remainder of an integer polynomial is
divisible by the square of the displacement. -/
theorem sq_dvd_eval_sub_eval_sub_derivative
    (Phi : Polynomial ℤ) (x y : ℤ) :
    (x - y) ^ 2 ∣
      Phi.eval x - Phi.eval y - Phi.derivative.eval y * (x - y) := by
  let Q := Phi /ₘ (X - C y)
  have hdivision :
      (X - C y) * Q = Phi - C (Phi.eval y) := by
    calc
      (X - C y) * Q =
          Phi - Phi %ₘ (X - C y) := by
            simpa [Q] using
              X_sub_C_mul_divByMonic_eq_sub_modByMonic Phi y
      _ = Phi - C (Phi.eval y) := by
        rw [modByMonic_X_sub_C_eq_C_eval]
  have heval :
      (x - y) * Q.eval x = Phi.eval x - Phi.eval y := by
    have h := congrArg (fun P : Polynomial ℤ => P.eval x) hdivision
    simpa [eval_mul, eval_sub] using h
  have hderiv :
      Q.eval y = Phi.derivative.eval y := by
    have h := divByMonic_add_X_sub_C_mul_derivative_divByMonic_eq_derivative
      Phi y
    have h' := congrArg (fun P : Polynomial ℤ => P.eval y) h
    simpa [Q, eval_add, eval_mul, eval_sub] using h'
  have hlinear : x - y ∣ Q.eval x - Q.eval y :=
    Polynomial.sub_dvd_eval_sub x y Q
  obtain ⟨q, hq⟩ := hlinear
  refine ⟨q, ?_⟩
  calc
    Phi.eval x - Phi.eval y -
        Phi.derivative.eval y * (x - y) =
        (x - y) * (Q.eval x - Q.eval y) := by
          rw [← heval, ← hderiv]
          ring
    _ = (x - y) ^ 2 * q := by rw [hq]; ring

/-- Taylor expansion of the interpolation polynomial at one owner node,
reduced modulo the square of the (possibly composite) owner modulus. -/
theorem owner_sq_dvd_matchingResultant_taylor_remainder
    {P L n d j i : ℤ} {Phi : Polynomial ℤ}
    (hrow : P ∣ n + j)
    (hnode : Phi.eval j = L * i) :
    P ^ 2 ∣ matchingResultant L n d Phi -
      ((L - Phi.derivative.eval j) * (n + j) +
        L * (d + i - j)) := by
  have hsquare : P ^ 2 ∣ ((-n) - j) ^ 2 := by
    have hneg : P ∣ (-n) - j := by
      obtain ⟨q, hq⟩ := hrow
      refine ⟨-q, ?_⟩
      calc
        (-n) - j = -(n + j) := by ring
        _ = -(P * q) := by rw [hq]
        _ = P * (-q) := by ring
    exact pow_dvd_pow_of_dvd hneg 2
  have htaylor := sq_dvd_eval_sub_eval_sub_derivative Phi (-n) j
  have hrem : P ^ 2 ∣
      Phi.eval (-n) - Phi.eval j -
        Phi.derivative.eval j * ((-n) - j) :=
    dvd_trans hsquare htaylor
  convert hrem using 1
  rw [matchingResultant, hnode]
  ring

/-- The normalized owner-square congruence and the Taylor expansion combine
to give the exact tangent-defect square divisor. -/
theorem owner_sq_dvd_matchingResultant_tangent_defect
    {P b signedFourA L n d j i : ℤ} {Phi : Polynomial ℤ}
    (hrow : P ∣ n + j)
    (hnode : Phi.eval j = L * i)
    (hnormalized :
      P ^ 2 ∣
        b * (d + i - j) - (signedFourA - b) * (n + j)) :
    P ^ 2 ∣
      b * matchingResultant L n d Phi -
        (signedFourA * L - b * Phi.derivative.eval j) * (n + j) := by
  have htaylor :=
    owner_sq_dvd_matchingResultant_taylor_remainder
      (d := d) hrow hnode
  have hbTaylor := dvd_mul_of_dvd_right htaylor b
  have hLNorm := dvd_mul_of_dvd_right hnormalized L
  have hadd := dvd_add hbTaylor hLNorm
  convert hadd using 1
  ring

/-- Equation-facing specialization of the tangent-defect theorem to the
banked normalized binomial owner-square congruence. -/
theorem matched_owner_sq_dvd_matchingResultant_tangent_defect
    {k n d i j P : ℕ} {L : ℤ} {Phi : Polynomial ℤ}
    (hd : k ≤ d)
    (hi : i ∈ Finset.Icc 1 k)
    (hj : j ∈ Finset.Icc 1 k)
    (hsupport : ∀ p, p.Prime → p ∣ P → k < p)
    (hlower : P ∣ n + j)
    (hupper : P ∣ n + d + i)
    (heq : blockProduct k (n + d) = 4 * blockProduct k n)
    (hnode : Phi.eval (j : ℤ) = L * (i : ℤ)) :
    ((P : ℤ) ^ 2) ∣
      (reducedMatchingRight k i j : ℤ) *
          matchingResultant L (n : ℤ) (d : ℤ) Phi -
        (4 * ((-1 : ℤ) ^ (i + j)) *
              (reducedMatchingLeft k i j : ℤ) * L -
            (reducedMatchingRight k i j : ℤ) *
              Phi.derivative.eval (j : ℤ)) *
          ((n + j : ℕ) : ℤ) := by
  have hnormalized :=
    matched_owner_normalized_square_dvd
      hd hi hj hsupport hlower hupper heq
  have hjle : j ≤ d + i := by
    have hjk := (Finset.mem_Icc.mp hj).2
    have hi1 := (Finset.mem_Icc.mp hi).1
    omega
  have hdelta :
      (((d + i - j : ℕ) : ℤ)) =
        (d : ℤ) + (i : ℤ) - (j : ℤ) := by
    exact_mod_cast (Nat.sub_eq_iff_eq_add hjle).2 (by omega)
  have hnormalized' :
      ((P : ℤ) ^ 2) ∣
        (reducedMatchingRight k i j : ℤ) *
            ((d : ℤ) + (i : ℤ) - (j : ℤ)) -
          (4 * ((-1 : ℤ) ^ (i + j)) *
              (reducedMatchingLeft k i j : ℤ) -
            (reducedMatchingRight k i j : ℤ)) *
              ((n + j : ℕ) : ℤ) := by
    simpa [normalizedMatchingForm, hdelta] using hnormalized
  have hrowZ :
      (P : ℤ) ∣ (n : ℤ) + (j : ℤ) := by
    exact_mod_cast hlower
  have htangent :=
    owner_sq_dvd_matchingResultant_tangent_defect
      (P := (P : ℤ))
      (b := (reducedMatchingRight k i j : ℤ))
      (signedFourA :=
        4 * ((-1 : ℤ) ^ (i + j)) *
          (reducedMatchingLeft k i j : ℤ))
      (L := L) (n := (n : ℤ)) (d := (d : ℤ))
      (j := (j : ℤ)) (i := (i : ℤ))
      hrowZ hnode hnormalized'
  simpa only [Nat.cast_add] using htangent

/-- After writing `R=M*U`, `M=P*Mrest`, and `x=P*xrest`, the square tangent
defect cancels one exact factor `P` and gives a congruence for `U` modulo
the composite owner `P`.  No modular inverse is used or hidden. -/
theorem owner_dvd_resultantQuotient_tangent_defect
    {P Mrest U xrest b kappa : ℤ}
    (hP : P ≠ 0)
    (hsquare :
      P ^ 2 ∣ b * ((P * Mrest) * U) - kappa * (P * xrest)) :
    P ∣ b * Mrest * U - kappa * xrest := by
  obtain ⟨q, hq⟩ := hsquare
  refine ⟨q, ?_⟩
  apply mul_left_cancel₀ hP
  calc
    P * (b * Mrest * U - kappa * xrest) =
        b * ((P * Mrest) * U) - kappa * (P * xrest) := by ring
    _ = P ^ 2 * q := hq
    _ = P * (P * q) := by ring

/-- Congruence form of the exactly cancelled quotient defect. -/
theorem resultantQuotient_tangent_modEq
    {P Mrest U xrest b kappa : ℤ}
    (hP : P ≠ 0)
    (hsquare :
      P ^ 2 ∣ b * ((P * Mrest) * U) - kappa * (P * xrest)) :
    b * Mrest * U ≡ kappa * xrest [ZMOD P] := by
  apply Int.modEq_iff_dvd.mpr
  have h := owner_dvd_resultantQuotient_tangent_defect hP hsquare
  simpa [Int.dvd_neg] using dvd_neg.mpr h

/-- Exact inversion of the local quotient congruence modulo a composite
owner.  The Bézout identity exposes, rather than assumes silently, the
invertibility of `b*Mrest`. -/
theorem resultantQuotient_tangent_modEq_explicit_inverse
    {P Mrest U xrest b kappa inverse bezoutCoeff : ℤ}
    (hP : P ≠ 0)
    (hsquare :
      P ^ 2 ∣ b * ((P * Mrest) * U) - kappa * (P * xrest))
    (hbezout :
      (b * Mrest) * inverse + P * bezoutCoeff = 1) :
    U ≡ inverse * (kappa * xrest) [ZMOD P] := by
  have hlocal :=
    owner_dvd_resultantQuotient_tangent_defect hP hsquare
  obtain ⟨q, hq⟩ := hlocal
  apply Int.modEq_iff_dvd.mpr
  refine ⟨-(bezoutCoeff * U + inverse * q), ?_⟩
  calc
    inverse * (kappa * xrest) - U =
        inverse * ((b * Mrest) * U - P * q) - U := by
          rw [← hq]
          ring
    _ = P * (-(bezoutCoeff * U + inverse * q)) := by
          linear_combination U * hbezout

/-- Canonical exact CRT representative for a finite family of pairwise
coprime positive composite owner moduli. -/
noncomputable def tangentCRTRepresentative
    {α : Type*} [DecidableEq α]
    (S : Finset α) (residue modulus : α → ℕ)
    (hmod : ∀ e ∈ S, modulus e ≠ 0)
    (hpair : Set.Pairwise (↑S : Set α)
      (Function.onFun Nat.Coprime modulus)) : ℕ :=
  Nat.chineseRemainderOfFinset residue modulus S hmod hpair

/-- Every requested local congruence is satisfied by the canonical exact CRT
representative. -/
theorem tangentCRTRepresentative_modEq
    {α : Type*} [DecidableEq α]
    (S : Finset α) (residue modulus : α → ℕ)
    (hmod : ∀ e ∈ S, modulus e ≠ 0)
    (hpair : Set.Pairwise (↑S : Set α)
      (Function.onFun Nat.Coprime modulus))
    (e : α) (he : e ∈ S) :
    tangentCRTRepresentative S residue modulus hmod hpair ≡ residue e
      [MOD modulus e] := by
  exact (Nat.chineseRemainderOfFinset residue modulus S hmod hpair).prop e he

/-- The canonical CRT representative lies in the exact product interval. -/
theorem tangentCRTRepresentative_lt_product
    {α : Type*} [DecidableEq α]
    (S : Finset α) (residue modulus : α → ℕ)
    (hmod : ∀ e ∈ S, modulus e ≠ 0)
    (hpair : Set.Pairwise (↑S : Set α)
      (Function.onFun Nat.Coprime modulus)) :
    tangentCRTRepresentative S residue modulus hmod hpair <
      ∏ e ∈ S, modulus e := by
  exact Nat.chineseRemainderOfFinset_lt_prod residue modulus hmod hpair

#print axioms sq_dvd_eval_sub_eval_sub_derivative
#print axioms owner_sq_dvd_matchingResultant_taylor_remainder
#print axioms owner_sq_dvd_matchingResultant_tangent_defect
#print axioms matched_owner_sq_dvd_matchingResultant_tangent_defect
#print axioms owner_dvd_resultantQuotient_tangent_defect
#print axioms resultantQuotient_tangent_modEq
#print axioms resultantQuotient_tangent_modEq_explicit_inverse
#print axioms tangentCRTRepresentative_modEq
#print axioms tangentCRTRepresentative_lt_product

end Erdos686Variant
end Erdos686
