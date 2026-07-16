/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import ErdosProblems.Erdos686ControlledPairing
import Mathlib.Algebra.Polynomial.Div
import Mathlib.RingTheory.Coprime.Lemmas

/-!
# Erdős 686: matching interpolation resultant

This module isolates the exact arithmetic after an integer interpolation
polynomial has been constructed.  Each owner modulus divides one common
resultant, and pairwise coprimality combines the local divisibilities without
assuming that the moduli are prime.
-/

namespace Erdos686
namespace Erdos686Variant

open scoped BigOperators

/-- Common integer matching resultant
`R = L*(n+d) + Phi(-n)`. -/
def matchingResultant
    (L n d : ℤ) (Phi : Polynomial ℤ) : ℤ :=
  L * (n + d) + Phi.eval (-n)

/-- One owner modulus divides the common matching resultant whenever `Phi`
interpolates `L*i` at its row node. -/
theorem owner_dvd_matchingResultant
    {P L n d j i rho : ℤ} {Phi : Polynomial ℤ}
    (hrow : P ∣ n + j)
    (hdiag : P ∣ d + rho)
    (hrho : rho = i - j)
    (hnode : Phi.eval j = L * i) :
    P ∣ matchingResultant L n d Phi := by
  have hpoint : P ∣ n + d + i := by
    have hsum := dvd_add hrow hdiag
    convert hsum using 1
    rw [hrho]
    ring
  have hneg : P ∣ (-n) - j := by
    have := dvd_neg.mpr hrow
    convert this using 1 <;> ring
  have hevalDiff : P ∣ Phi.eval (-n) - Phi.eval j := by
    exact dvd_trans hneg (Polynomial.sub_dvd_eval_sub (-n) j Phi)
  have hmain : P ∣ L * (n + d + i) :=
    dvd_mul_of_dvd_right hpoint L
  have hadd := dvd_add hmain hevalDiff
  rw [matchingResultant]
  convert hadd using 1
  rw [hnode]
  ring

/-- Pairwise-coprime owner moduli all divide the same matching resultant, so
their product divides it. -/
theorem matching_support_product_dvd_resultant
    {α : Type*} {S : Finset α}
    (P : α → ℤ) (row column offset : α → ℤ)
    (L n d : ℤ) (Phi : Polynomial ℤ)
    (hpair : (S : Set α).Pairwise (Function.onFun IsCoprime P))
    (hrow : ∀ e ∈ S, P e ∣ n + row e)
    (hdiag : ∀ e ∈ S, P e ∣ d + offset e)
    (hoffset : ∀ e ∈ S, offset e = column e - row e)
    (hnode : ∀ e ∈ S, Phi.eval (row e) = L * column e) :
    (∏ e ∈ S, P e) ∣ matchingResultant L n d Phi := by
  classical
  apply Finset.prod_dvd_of_coprime hpair
  intro e he
  exact owner_dvd_matchingResultant
    (hrow e he) (hdiag e he) (hoffset e he) (hnode e he)

/-- Owner-cell specialization of the common resultant divisor. -/
theorem owner_cell_support_product_dvd_resultant
    {S : Finset (ℕ × ℕ)}
    (P : (ℕ × ℕ) → ℤ)
    (L n d : ℤ) (Phi : Polynomial ℤ)
    (hpair : (S : Set (ℕ × ℕ)).Pairwise
      (Function.onFun IsCoprime P))
    (hrow : ∀ e ∈ S, P e ∣ n + (ownerCellRow e : ℤ))
    (hdiag : ∀ e ∈ S, P e ∣ d + ownerCellOffset e)
    (hnode : ∀ e ∈ S,
      Phi.eval (ownerCellRow e : ℤ) =
        L * (ownerCellColumn e : ℤ)) :
    (∏ e ∈ S, P e) ∣ matchingResultant L n d Phi := by
  apply matching_support_product_dvd_resultant P
    (fun e => (ownerCellRow e : ℤ))
    (fun e => (ownerCellColumn e : ℤ))
    ownerCellOffset L n d Phi hpair hrow hdiag
  · intro e he
    simp [ownerCellOffset, ownerDiagonalOffset, ownerCellColumn, ownerCellRow]
  · exact hnode

#print axioms owner_dvd_matchingResultant
#print axioms matching_support_product_dvd_resultant
#print axioms owner_cell_support_product_dvd_resultant

end Erdos686Variant
end Erdos686
