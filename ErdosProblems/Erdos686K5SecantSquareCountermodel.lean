import ErdosProblems.Erdos686K5OppositeSecantCofactor

/-!
# Erdős 686, k=5: a local square-secant countermodel

This exact witness satisfies the four crossing-owner square congruences,
pairwise coprimality of the four nontrivial crossing owners, exact fully owned
row and column factorizations with coprime complements, and both opposite
secant factorizations.  It even lies in the repaired rational cone
`d < n`, `40*d < 13*n`.  Nevertheless the product of the two remaining
secant quotients is coprime to the complete crossing product.

This is a local algebra countermodel, not a solution of the five-factor block
equation.  It shows precisely that square owner defects plus secant
factorization alone cannot supply the missing gcd lower bound; a global
solution equation or a zero local tangent coefficient is essential.
-/

namespace Erdos686
namespace Erdos686Variant

/-- An exact local countermodel to any universal claim that a nontrivial
crossing owner must remain in the product of the two opposite-secant
quotients after the four owner-square congruences are imposed. -/
theorem k5_local_square_secant_no_forced_crossing_factor_witness :
    let n : ℕ := 25091779
    let d : ℕ := 7035040
    let P₁₁ : ℕ := 5
    let P₁₂ : ℕ := 7
    let P₂₁ : ℕ := 11
    let P₂₂ : ℕ := 13
    let Uplus : ℤ := -277796
    let Uminus : ℤ := 1068966
    d < n ∧ 40 * d < 13 * n ∧
      Nat.Coprime (P₁₁ * P₂₂) (P₁₂ * P₂₁) ∧
      Nat.Coprime (P₁₁ * P₁₂ * P₂₁ * P₂₂)
        (716908 * 175467 * 584124 * 353042) ∧
      n + 1 = P₁₁ * P₁₂ * 716908 ∧
      n + 2 = P₂₁ * P₂₂ * 175467 ∧
      n + d + 1 = P₁₁ * P₂₁ * 584124 ∧
      n + d + 3 = P₁₂ * P₂₂ * 353042 ∧
      k5OwnerSquareDefect n d 1 1 = (P₁₁ : ℤ) ^ 2 * (-65510688) ∧
      k5OwnerSquareDefect n d 1 3 = (P₁₂ : ℤ) ^ 2 * (-46536808) ∧
      k5OwnerSquareDefect n d 2 1 = (P₂₁ : ℤ) ^ 2 * 11349144 ∧
      k5OwnerSquareDefect n d 2 3 = (P₂₂ : ℤ) ^ 2 * 4323728 ∧
      k5OppositeSecantPlus n d 1 2 1 3 =
        ((P₁₁ * P₂₂ : ℕ) : ℤ) * Uplus ∧
      k5OppositeSecantMinus n d 1 2 1 3 =
        ((P₁₂ * P₂₁ : ℕ) : ℤ) * Uminus ∧
      Nat.gcd (P₁₁ * P₂₂ * (P₁₂ * P₂₁))
        (Uplus * Uminus).natAbs = 1 := by
  have hc₁ : localBlockCoefficient 5 1 = 24 := by
    rw [localBlockCoefficient_eq_sign_mul_nat (by norm_num)]
    norm_num [localBlockCoefficientNat]
  have hc₂ : localBlockCoefficient 5 2 = -6 := by
    rw [localBlockCoefficient_eq_sign_mul_nat (by norm_num)]
    norm_num [localBlockCoefficientNat]
  have hc₃ : localBlockCoefficient 5 3 = 4 := by
    rw [localBlockCoefficient_eq_sign_mul_nat (by norm_num)]
    norm_num [localBlockCoefficientNat]
  norm_num [k5OwnerSquareDefect, k5OppositeSecantPlus,
    k5OppositeSecantMinus, hc₁, hc₂, hc₃, Nat.Coprime]

end Erdos686Variant
end Erdos686
