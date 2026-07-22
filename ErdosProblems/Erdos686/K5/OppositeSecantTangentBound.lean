import ErdosProblems.Erdos686.K5.OppositeSecantTangentRatio

/-!
# Erdős 686, k=5: nonzero secant-tangent gcd bound

The exact ratio certificate eliminates the zero-coefficient branch from the
proper-global opposite-secant determinant theorem.  The resulting interface
retains the two integral secant quotients and their exact product identity,
while returning both divisibility by and an explicit upper bound through the
nonzero tangent coefficient.

There is deliberately no claimed lower bound for the displayed gcd.  The
fully owned factorizations remove the four crossing owners exactly when
forming `Uplus` and `Uminus`; nontriviality of those owners therefore gives a
lower bound for `X`, but not for `gcd X |Uplus*Uminus|`.
-/

namespace Erdos686
namespace Erdos686Variant

open scoped BigOperators

theorem k5_proper_global_opposite_secant_tangent_gcd_bound
    {n d t j₁ j₂ i₁ i₂ : ℕ}
    (data : CanonicalOwnerData 5 n d t)
    (hn : 2811 ≤ n) (hd : 5 ≤ d)
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
    ∃ Uplus Uminus : ℤ,
      k5OppositeSecantPlus n d j₁ j₂ i₁ i₂ =
          (Mplus : ℤ) * Uplus ∧
        k5OppositeSecantMinus n d j₁ j₂ i₁ i₂ =
          (Mminus : ℤ) * Uminus ∧
        Uplus * Uminus =
          ((((j₂ : ℤ) - j₁) ^ 2) *
              (k5UpperFourMultiplier t i₁ : ℤ) *
              (k5UpperFourMultiplier t i₂ : ℤ)) * (B / X : ℕ) -
            (((i₂ : ℤ) - i₁) ^ 2) * (A / X : ℕ) ∧
        Nat.gcd X (Uplus * Uminus).natAbs ∣
          (k5ProperTangentCombination n d t j₁ j₂ i₁ i₂).natAbs ∧
        Nat.gcd X (Uplus * Uminus).natAbs ≤
          (k5ProperTangentCombination n d t j₁ j₂ i₁ i₂).natAbs := by
  dsimp only
  obtain ⟨Uplus, Uminus, hplus, hminus, hprod, hdiv, hzeroOr⟩ :=
    k5_proper_global_opposite_secant_tangent_determinant_gcd
      data hj₁ hj₂ hi₁ hi₂ hjneq hineq hfour
      hj₁one hj₂one hi₁one hi₂one heq
  have hK : k5ProperTangentCombination n d t j₁ j₂ i₁ i₂ ≠ 0 :=
    k5ProperTangentCombination_ne_zero_of_solution hn hd heq hfour
      hj₁ hj₂ hi₁ hi₂ hjneq hineq
  refine ⟨Uplus, Uminus, hplus, hminus, hprod, ?_, ?_⟩
  · simpa [k5ProperTangentCombination] using hdiv
  · have hbound := hzeroOr.resolve_left ?_
    · simpa [k5ProperTangentCombination] using hbound
    · simpa [k5ProperTangentCombination] using hK

end Erdos686Variant
end Erdos686
