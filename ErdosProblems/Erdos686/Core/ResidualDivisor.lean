/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import ErdosProblems.Erdos686.Core.MatchingResultant

/-!
# Erdős 686: the nonzero-branch residual divisor

This file isolates the division-free arithmetic behind the barycentric
nonzero branch.  In particular, the statement that a row cofactor is
`k`-smooth is kept behind an explicit full-large-part hypothesis; it is not
inferred merely from the divisibility of the row by its selected owner.
-/

namespace Erdos686
namespace Erdos686Variant

open scoped BigOperators

/-- The value of `U(-n) + d V(-n)` in the division-free barycentric basis.
Here `j` is the row node, `rho` the diagonal offset, `w` the barycentric
weight, and `c` the coefficient of the node polynomial. -/
def barycentricResidualValue
    {α : Type*} [DecidableEq α] (S : Finset α) (j rho w : α → ℤ)
    (c n d : ℤ) : ℤ :=
  c * ∏ e ∈ S, (-n - j e) +
    ∑ e ∈ S,
      w e * (d + rho e) * ∏ f ∈ S.erase e, (-n - j f)

/-- The denominator-cleared barycentric value.  This is the primary interface
when the original barycentric coordinates are rational: `gamma` and `omega`
are the integral cleared coordinates, so this definition itself contains no
division. -/
def scaledBarycentricResidualValue
    {α : Type*} [DecidableEq α] (S : Finset α) (j rho omega : α → ℤ)
    (gamma n d : ℤ) : ℤ :=
  gamma * ∏ e ∈ S, (-n - j e) +
    ∑ e ∈ S,
      omega e * (d + rho e) * ∏ f ∈ S.erase e, (-n - j f)

/-- Clearing the integral coordinates term by term gives the scaled value. -/
theorem Lambda_mul_barycentricResidualValue_eq_scaled
    {α : Type*} [DecidableEq α]
    (S : Finset α) (j rho w omega : α → ℤ)
    (c gamma Lambda n d : ℤ)
    (hgamma : Lambda * c = gamma)
    (homega : ∀ e ∈ S, Lambda * w e = omega e) :
    Lambda * barycentricResidualValue S j rho w c n d =
      scaledBarycentricResidualValue S j rho omega gamma n d := by
  rw [barycentricResidualValue, scaledBarycentricResidualValue,
    mul_add, Finset.mul_sum]
  rw [show Lambda * (c * ∏ e ∈ S, (-n - j e)) =
      gamma * ∏ e ∈ S, (-n - j e) by rw [← hgamma]; ring]
  apply congrArg (gamma * ∏ e ∈ S, (-n - j e) + ·)
  apply Finset.sum_congr rfl
  intro e he
  rw [← homega e he]
  ring

/-- The integral residual left after extracting the complete owner product
from the scaled barycentric value. -/
def barycentricResidualCofactor
    {α : Type*} [DecidableEq α] (S : Finset α) (R H omega : α → ℤ)
    (gamma : ℤ) : ℤ :=
  gamma * ∏ e ∈ S, R e -
    ∑ e ∈ S, omega e * H e * ∏ f ∈ S.erase e, R f

private theorem prod_neg_factorization
    {α : Type*} [DecidableEq α] (S : Finset α)
    (P R : α → ℤ) :
    (∏ e ∈ S, (-(P e * R e))) =
      (-1 : ℤ) ^ S.card * (∏ e ∈ S, P e) * (∏ e ∈ S, R e) := by
  rw [Finset.prod_neg]
  rw [Finset.prod_mul_distrib]
  ring

private theorem one_term_neg_factorization
    {α : Type*} [DecidableEq α] {S : Finset α} {e : α}
    (he : e ∈ S) (P R H : α → ℤ) :
    P e * H e * (∏ f ∈ S.erase e, (-(P f * R f))) =
      -((-1 : ℤ) ^ S.card) * (∏ f ∈ S, P f) *
        (H e * ∏ f ∈ S.erase e, R f) := by
  have hcard : (S.erase e).card + 1 = S.card := by
    exact Finset.card_erase_add_one he
  have hprodP : P e * ∏ f ∈ S.erase e, P f = ∏ f ∈ S, P f := by
    simpa [mul_comm] using (Finset.mul_prod_erase S P he)
  rw [prod_neg_factorization]
  rw [← hprodP]
  have hsign : (-1 : ℤ) ^ (S.erase e).card = -((-1 : ℤ) ^ S.card) := by
    rw [← hcard, pow_succ]
    ring
  rw [hsign]
  ring

/-- Exact factorization from the imported pass:
`Lambda * (U(-n)+dV(-n)) = (-1)^m M S_S`.

The hypotheses `hrow`, `hdiag`, `hgamma`, and `homega` are all equalities,
so no divisibility cancellation or choice of quotients is hidden here. -/
theorem barycentric_residual_exact_factorization
    {α : Type*} [DecidableEq α]
    (S : Finset α) (j rho P R H w omega : α → ℤ)
    (c gamma Lambda n d : ℤ)
    (hrow : ∀ e ∈ S, n + j e = P e * R e)
    (hdiag : ∀ e ∈ S, d + rho e = P e * H e)
    (hgamma : Lambda * c = gamma)
    (homega : ∀ e ∈ S, Lambda * w e = omega e) :
    Lambda * barycentricResidualValue S j rho w c n d =
      (-1 : ℤ) ^ S.card * (∏ e ∈ S, P e) *
        barycentricResidualCofactor S R H omega gamma := by
  classical
  have hrowNeg : ∀ e ∈ S, -n - j e = -(P e * R e) := by
    intro e he
    rw [← hrow e he]
    ring
  rw [barycentricResidualValue, barycentricResidualCofactor]
  rw [mul_add, Finset.mul_sum]
  rw [show Lambda * (c * ∏ e ∈ S, (-n - j e)) =
      gamma * ((-1 : ℤ) ^ S.card * (∏ e ∈ S, P e) *
        (∏ e ∈ S, R e)) by
    rw [← hgamma]
    have hprod : (∏ e ∈ S, (-n - j e)) =
        ∏ e ∈ S, (-(P e * R e)) := by
      apply Finset.prod_congr rfl
      intro e he
      exact hrowNeg e he
    rw [hprod, prod_neg_factorization]
    ring]
  have hterm : ∀ e ∈ S,
      Lambda * (w e * (d + rho e) *
        ∏ f ∈ S.erase e, (-n - j f)) =
      -((-1 : ℤ) ^ S.card) * (∏ f ∈ S, P f) *
        (omega e * H e * ∏ f ∈ S.erase e, R f) := by
    intro e he
    rw [hdiag e he]
    have herase : ∀ f ∈ S.erase e, -n - j f = -(P f * R f) := by
      intro f hf
      exact hrowNeg f (Finset.mem_of_mem_erase hf)
    calc
      Lambda * (w e * (P e * H e) *
          ∏ f ∈ S.erase e, (-n - j f)) =
          omega e * (P e * H e) *
            ∏ f ∈ S.erase e, (-(P f * R f)) := by
              have hprod : (∏ f ∈ S.erase e, (-n - j f)) =
                  ∏ f ∈ S.erase e, (-(P f * R f)) := by
                apply Finset.prod_congr rfl
                intro f hf
                exact herase f hf
              rw [hprod, ← homega e he]
              ring
      _ = -((-1 : ℤ) ^ S.card) * (∏ f ∈ S, P f) *
          (omega e * H e * ∏ f ∈ S.erase e, R f) := by
            rw [show omega e * (P e * H e) =
              omega e * (P e * H e) by rfl]
            have hfac := one_term_neg_factorization he P R H
            calc
              omega e * (P e * H e) *
                  ∏ f ∈ S.erase e, (-(P f * R f)) =
                  omega e *
                    (P e * H e * ∏ f ∈ S.erase e, (-(P f * R f))) := by ring
              _ = omega e *
                  (-((-1 : ℤ) ^ S.card) * (∏ f ∈ S, P f) *
                    (H e * ∏ f ∈ S.erase e, R f)) := by rw [hfac]
              _ = _ := by ring
  rw [Finset.sum_congr rfl hterm]
  rw [← Finset.mul_sum]
  ring

/-- Denominator-cleared form of the exact factorization.  Unlike the
`Lambda` wrapper, this theorem only mentions integral cleared coordinates. -/
theorem scaled_barycentric_residual_exact_factorization
    {α : Type*} [DecidableEq α]
    (S : Finset α) (j rho P R H omega : α → ℤ)
    (gamma n d : ℤ)
    (hrow : ∀ e ∈ S, n + j e = P e * R e)
    (hdiag : ∀ e ∈ S, d + rho e = P e * H e) :
    scaledBarycentricResidualValue S j rho omega gamma n d =
      (-1 : ℤ) ^ S.card * (∏ e ∈ S, P e) *
        barycentricResidualCofactor S R H omega gamma := by
  simpa [scaledBarycentricResidualValue, barycentricResidualValue] using
    (barycentric_residual_exact_factorization S j rho P R H omega omega
      gamma gamma 1 n d hrow hdiag (by simp) (by simp))

/-- Cancellation of one complete owner product.  This is the exact logical
input needed for `M ∣ S_S`: the square of the product must already divide the
scaled barycentric value, and the product must be nonzero. -/
theorem barycentric_residual_cofactor_dvd
    {α : Type*} [DecidableEq α]
    (S : Finset α) (j rho P R H w omega : α → ℤ)
    (c gamma Lambda n d : ℤ)
    (hrow : ∀ e ∈ S, n + j e = P e * R e)
    (hdiag : ∀ e ∈ S, d + rho e = P e * H e)
    (hgamma : Lambda * c = gamma)
    (homega : ∀ e ∈ S, Lambda * w e = omega e)
    (hM : (∏ e ∈ S, P e) ≠ 0)
    (hsquare : (∏ e ∈ S, P e) ^ 2 ∣
      Lambda * barycentricResidualValue S j rho w c n d) :
    (∏ e ∈ S, P e) ∣
      barycentricResidualCofactor S R H omega gamma := by
  let M : ℤ := ∏ e ∈ S, P e
  let q : ℤ := (-1 : ℤ) ^ S.card
  let T : ℤ := barycentricResidualValue S j rho w c n d
  let C : ℤ := barycentricResidualCofactor S R H omega gamma
  have hfactor : Lambda * T = q * M * C := by
    exact barycentric_residual_exact_factorization S j rho P R H w omega
      c gamma Lambda n d hrow hdiag hgamma homega
  obtain ⟨z, hz⟩ := hsquare
  have heq : q * M * C = M ^ 2 * z := by
    rw [← hfactor]
    exact hz
  have hqq : q * q = 1 := by
    dsimp [q]
    rw [← pow_add]
    simp
  have hmul : M * C = M * (M * (q * z)) := by
    calc
      M * C = (q * q) * (M * C) := by rw [hqq]; ring
      _ = q * (q * M * C) := by ring
      _ = q * (M ^ 2 * z) := by rw [heq]
      _ = M * (M * (q * z)) := by ring
  have hC : C = M * (q * z) := mul_left_cancel₀ hM hmul
  exact ⟨q * z, hC⟩

/-- Convenient unscaled interface: the global owner-square theorem normally
supplies `M^2 ∣ U(-n)+dV(-n)` itself.  Multiplying by `Lambda` then feeds the
exact cancellation theorem above; no coprimality between `Lambda` and `M` is
needed. -/
theorem barycentric_residual_cofactor_dvd_of_unscaled_square
    {α : Type*} [DecidableEq α]
    (S : Finset α) (j rho P R H w omega : α → ℤ)
    (c gamma Lambda n d : ℤ)
    (hrow : ∀ e ∈ S, n + j e = P e * R e)
    (hdiag : ∀ e ∈ S, d + rho e = P e * H e)
    (hgamma : Lambda * c = gamma)
    (homega : ∀ e ∈ S, Lambda * w e = omega e)
    (hM : (∏ e ∈ S, P e) ≠ 0)
    (hsquare : (∏ e ∈ S, P e) ^ 2 ∣
      barycentricResidualValue S j rho w c n d) :
    (∏ e ∈ S, P e) ∣
      barycentricResidualCofactor S R H omega gamma := by
  apply barycentric_residual_cofactor_dvd S j rho P R H w omega
    c gamma Lambda n d hrow hdiag hgamma homega hM
  exact dvd_mul_of_dvd_right hsquare Lambda

/-- Every prime divisor of a `k`-smooth integer is at most `k`. -/
def IsKSmoothInt (k : ℕ) (R : ℤ) : Prop :=
  ∀ p : ℕ, p.Prime → (p : ℤ) ∣ R → p ≤ k

/-- Exact meaning of the selected owner containing the complete `> k` part
of a row: every complementary factor in an exact owner factorization is
`k`-smooth.  This deliberately records multiplicities through the quantified
factorization, rather than merely requiring that the owner contain each
large prime once. -/
def ContainsFullLargePrimePart (k : ℕ) (P x : ℤ) : Prop :=
  ∀ R : ℤ, x = P * R → IsKSmoothInt k R

/-- The row cofactor is `k`-smooth only under the explicit full-large-part
hypothesis. -/
theorem row_cofactor_kSmooth_of_containsFullLargePrimePart
    {k : ℕ} {P x R : ℤ}
    (hfull : ContainsFullLargePrimePart k P x)
    (hfactor : x = P * R) :
    IsKSmoothInt k R :=
  hfull R hfactor

/-- The exact coefficient mass `C_S = |gamma| + sum |omega_j|`. -/
def residualCoefficientMass
    {α : Type*} (S : Finset α) (omega : α → ℤ) (gamma : ℤ) : ℕ :=
  gamma.natAbs + ∑ e ∈ S, (omega e).natAbs

private theorem natAbs_prod_le_pow
    {α : Type*} [DecidableEq α] (S : Finset α) (R : α → ℤ) (B : ℕ)
    (hR : ∀ e ∈ S, (R e).natAbs ≤ B) :
    (∏ e ∈ S, R e).natAbs ≤ B ^ S.card := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert e S he ih =>
      rw [Finset.prod_insert he, Int.natAbs_mul,
        Finset.card_insert_of_notMem he, pow_succ']
      exact Nat.mul_le_mul (hR e (Finset.mem_insert_self e S))
        (ih fun f hf ↦ hR f (Finset.mem_insert_of_mem hf))

/-- If all row and diagonal cofactors have absolute value at most `B`, then
the residual has the sharp division-free coefficient estimate
`|S_S| <= C_S B^m`. -/
theorem barycentric_residual_cofactor_natAbs_le
    {α : Type*} [DecidableEq α]
    (S : Finset α) (R H omega : α → ℤ) (gamma : ℤ) (B : ℕ)
    (hR : ∀ e ∈ S, (R e).natAbs ≤ B)
    (hH : ∀ e ∈ S, (H e).natAbs ≤ B) :
    (barycentricResidualCofactor S R H omega gamma).natAbs ≤
      residualCoefficientMass S omega gamma * B ^ S.card := by
  have hprodR : (∏ e ∈ S, R e).natAbs ≤ B ^ S.card :=
    natAbs_prod_le_pow S R B hR
  have hterm : ∀ e ∈ S,
      (omega e * H e * ∏ f ∈ S.erase e, R f).natAbs ≤
        (omega e).natAbs * B ^ S.card := by
    intro e he
    have hprodErase : (∏ f ∈ S.erase e, R f).natAbs ≤
        B ^ (S.erase e).card := by
      apply natAbs_prod_le_pow
      intro f hf
      exact hR f (Finset.mem_of_mem_erase hf)
    have hcard : (S.erase e).card + 1 = S.card :=
      Finset.card_erase_add_one he
    rw [Int.natAbs_mul, Int.natAbs_mul]
    calc
      (omega e).natAbs * (H e).natAbs *
          (∏ f ∈ S.erase e, R f).natAbs ≤
          (omega e).natAbs * B * B ^ (S.erase e).card := by
            gcongr
            exact hH e he
      _ = (omega e).natAbs * B ^ S.card := by
            rw [← hcard, pow_succ']
            ring
  have hsum :
      (∑ e ∈ S, omega e * H e * ∏ f ∈ S.erase e, R f).natAbs ≤
        (∑ e ∈ S, (omega e).natAbs) * B ^ S.card := by
    calc
      (∑ e ∈ S, omega e * H e * ∏ f ∈ S.erase e, R f).natAbs ≤
          ∑ e ∈ S,
            (omega e * H e * ∏ f ∈ S.erase e, R f).natAbs :=
        Int.natAbs_sum_le S _
      _ ≤ ∑ e ∈ S, (omega e).natAbs * B ^ S.card := by
        exact Finset.sum_le_sum fun e he ↦ hterm e he
      _ = (∑ e ∈ S, (omega e).natAbs) * B ^ S.card := by
        rw [Finset.sum_mul]
  rw [barycentricResidualCofactor]
  calc
    (gamma * ∏ e ∈ S, R e -
        ∑ e ∈ S, omega e * H e * ∏ f ∈ S.erase e, R f).natAbs ≤
        (gamma * ∏ e ∈ S, R e).natAbs +
          (∑ e ∈ S, omega e * H e * ∏ f ∈ S.erase e, R f).natAbs :=
      Int.natAbs_sub_le _ _
    _ ≤ gamma.natAbs * B ^ S.card +
        (∑ e ∈ S, (omega e).natAbs) * B ^ S.card := by
      rw [Int.natAbs_mul]
      exact Nat.add_le_add (Nat.mul_le_mul_left _ hprodR) hsum
    _ = residualCoefficientMass S omega gamma * B ^ S.card := by
      simp [residualCoefficientMass, add_mul]

#print axioms barycentric_residual_exact_factorization
#print axioms scaled_barycentric_residual_exact_factorization
#print axioms barycentric_residual_cofactor_dvd
#print axioms barycentric_residual_cofactor_dvd_of_unscaled_square
#print axioms row_cofactor_kSmooth_of_containsFullLargePrimePart
#print axioms barycentric_residual_cofactor_natAbs_le

end Erdos686Variant
end Erdos686
