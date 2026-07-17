import ErdosProblems.Erdos686K5OppositeSecantTangentBound
import ErdosProblems.Erdos686K5ZeroSecantGCDLower

/-!
# Erdős 686, k=5: equation-facing residual-profile dispatch

The global residual is enumerated through the eight positive divisors of
`4!`.  Each lower and modified-upper residual vector is then classified for
selection purposes: it has two unit positions, except for the exact
one-unit multiset `{1,2,2,2,3}` at global residual `24`.

Whenever both sides have two units, this module selects the resulting `2 x
2` grid and attaches the kernel-checked nonzero tangent gcd bound.  It also
separates the already formalized `G=12` zero-local-coefficient profile.  The
remaining third branch is stated explicitly rather than silently discarded:
one of the `G=24` residual vectors may still have the exceptional one-unit
multiset.
-/

namespace Erdos686
namespace Erdos686Variant

/-- The exact finite list of positive divisors of `4!`. -/
def K5AllowedGlobalResidual (G : ℕ) : Prop :=
  G = 1 ∨ G = 2 ∨ G = 3 ∨ G = 4 ∨
    G = 6 ∨ G = 8 ∨ G = 12 ∨ G = 24

/-- A residual vector has two distinct unit positions. -/
def K5TwoUnitResidualProfile (f : ℕ → ℕ) : Prop :=
  ∃ a, a ∈ Finset.Icc 1 5 ∧
    ∃ b, b ∈ Finset.Icc 1 5 ∧ b ≠ a ∧ f a = 1 ∧ f b = 1

/-- The exact selectable-profile alternative supplied by `G ∣ 24`: either
two distinct units, or the unique one-unit multiset at `G=24`. -/
def K5ResidualSelectionProfile (f : ℕ → ℕ) : Prop :=
  K5TwoUnitResidualProfile f ∨ K5ExceptionalResidualProfile f

/-- A fully owned `2 x 2` grid together with the exact nonzero tangent gcd
divisor and bound furnished by the solution-facing theorem. -/
def K5ProperNonzeroTangentGrid
    {n d t : ℕ} (data : CanonicalOwnerData 5 n d t) : Prop :=
  ∃ j₁, j₁ ∈ Finset.Icc 1 5 ∧
    ∃ j₂, j₂ ∈ Finset.Icc 1 5 ∧ j₂ ≠ j₁ ∧
    ∃ i₁, i₁ ∈ Finset.Icc 1 5 ∧
    ∃ i₂, i₂ ∈ Finset.Icc 1 5 ∧ i₂ ≠ i₁ ∧
      canonicalLowerResidual data j₁ = 1 ∧
      canonicalLowerResidual data j₂ = 1 ∧
      canonicalUpperResidual data i₁ = 1 ∧
      canonicalUpperResidual data i₂ = 1 ∧
      k5ProperTangentCombination n d t j₁ j₂ i₁ i₂ ≠ 0 ∧
      ∃ Uplus Uminus : ℤ,
        k5OppositeSecantPlus n d j₁ j₂ i₁ i₂ =
            ((canonicalOwnerCell data j₁ i₁ *
              canonicalOwnerCell data j₂ i₂ : ℕ) : ℤ) * Uplus ∧
        k5OppositeSecantMinus n d j₁ j₂ i₁ i₂ =
            ((canonicalOwnerCell data j₁ i₂ *
              canonicalOwnerCell data j₂ i₁ : ℕ) : ℤ) * Uminus ∧
        Nat.gcd
            (canonicalOwnerCell data j₁ i₁ *
              canonicalOwnerCell data j₁ i₂ *
              canonicalOwnerCell data j₂ i₁ *
              canonicalOwnerCell data j₂ i₂)
            (Uplus * Uminus).natAbs ∣
          (k5ProperTangentCombination n d t j₁ j₂ i₁ i₂).natAbs ∧
        Nat.gcd
            (canonicalOwnerCell data j₁ i₁ *
              canonicalOwnerCell data j₁ i₂ *
              canonicalOwnerCell data j₂ i₁ *
              canonicalOwnerCell data j₂ i₂)
            (Uplus * Uminus).natAbs ≤
          (k5ProperTangentCombination n d t j₁ j₂ i₁ i₂).natAbs

private theorem k5_allowed_global_residual
    {n d t : ℕ} (data : CanonicalOwnerData 5 n d t) :
    K5AllowedGlobalResidual (canonicalOwnerResidual data) := by
  have hpos : 0 < canonicalOwnerResidual data := by
    classical
    unfold canonicalOwnerResidual
    apply Finset.prod_pos
    intro p hp
    exact pow_pos (Nat.prime_of_mem_primeFactors hp).pos _
  have hdvd := canonicalOwnerResidual_dvd_factorial data
  have hle : canonicalOwnerResidual data ≤ 24 := by
    have := Nat.le_of_dvd (by norm_num : 0 < (4 : ℕ).factorial) hdvd
    norm_num at this ⊢
    exact this
  unfold K5AllowedGlobalResidual
  interval_cases hG : canonicalOwnerResidual data <;>
    norm_num at hdvd <;> omega

private theorem k5_proper_nonzero_tangent_grid_of_units
    {n d t j₁ j₂ i₁ i₂ : ℕ}
    (data : CanonicalOwnerData 5 n d t)
    (hn : 2811 ≤ n) (hd : 5 ≤ d)
    (hj₁ : j₁ ∈ Finset.Icc 1 5) (hj₂ : j₂ ∈ Finset.Icc 1 5)
    (hi₁ : i₁ ∈ Finset.Icc 1 5) (hi₂ : i₂ ∈ Finset.Icc 1 5)
    (hjneq : j₂ ≠ j₁) (hineq : i₂ ≠ i₁)
    (hfour : 4 ∣ n + d + t)
    (hj₁one : canonicalLowerResidual data j₁ = 1)
    (hj₂one : canonicalLowerResidual data j₂ = 1)
    (hi₁one : canonicalUpperResidual data i₁ = 1)
    (hi₂one : canonicalUpperResidual data i₂ = 1)
    (heq : blockProduct 5 (n + d) = 4 * blockProduct 5 n) :
    K5ProperNonzeroTangentGrid data := by
  have hK := k5ProperTangentCombination_ne_zero_of_solution
    hn hd heq hfour hj₁ hj₂ hi₁ hi₂ hjneq.symm hineq.symm
  obtain ⟨Uplus, Uminus, hplus, hminus, -, hdiv, hbound⟩ :=
    k5_proper_global_opposite_secant_tangent_gcd_bound
      data hn hd hj₁ hj₂ hi₁ hi₂ hjneq.symm hineq.symm hfour
      hj₁one hj₂one hi₁one hi₂one heq
  exact ⟨j₁, hj₁, j₂, hj₂, hjneq, i₁, hi₁, i₂, hi₂, hineq,
    hj₁one, hj₂one, hi₁one, hi₂one, hK,
    Uplus, Uminus, hplus, hminus, hdiv, hbound⟩

/-- Exhaustive equation-facing residual dispatch.  The third branch is the
precise still-live obstruction to the desired binary dispatch: at `G=24`,
one side may have the one-unit multiset `{1,2,2,2,3}`, so a `2 x 2` unit grid
cannot be selected. -/
theorem k5_equation_residual_profile_dispatch
    {n d t : ℕ} (data : CanonicalOwnerData 5 n d t)
    (hn : 2811 ≤ n) (hd : 5 ≤ d)
    (ht : t ∈ Finset.Icc 1 5)
    (hfour : 4 ∣ n + d + t)
    (hblocks : upperBlockAfterFour 5 n d t = blockProduct 5 n)
    (heq : blockProduct 5 (n + d) = 4 * blockProduct 5 n) :
    K5AllowedGlobalResidual (canonicalOwnerResidual data) ∧
      K5ResidualSelectionProfile (canonicalLowerResidual data) ∧
      K5ResidualSelectionProfile (canonicalUpperResidual data) ∧
      ((K5ProperNonzeroTangentGrid data ∧
          ¬ K5G12ZeroResidualProfile data) ∨
        K5G12ZeroResidualProfile data ∨
        (canonicalOwnerResidual data = 24 ∧
          (K5ExceptionalResidualProfile (canonicalLowerResidual data) ∨
            K5ExceptionalResidualProfile
              (canonicalUpperResidual data)))) := by
  have hallowed := k5_allowed_global_residual data
  by_cases hG : canonicalOwnerResidual data = 24
  · have hl := k5_lower_residual_profile_of_global_eq_twenty_four data hG
    have hu := k5_upper_residual_profile_of_global_eq_twenty_four
      data ht hfour hblocks hG
    refine ⟨hallowed, hl, hu, ?_⟩
    rcases hl with hl | hl
    · rcases hu with hu | hu
      · obtain ⟨j₁, hj₁, j₂, hj₂, hjneq, hj₁one, hj₂one⟩ := hl
        obtain ⟨i₁, hi₁, i₂, hi₂, hineq, hi₁one, hi₂one⟩ := hu
        have hgrid := k5_proper_nonzero_tangent_grid_of_units
          data hn hd hj₁ hj₂ hi₁ hi₂ hjneq hineq hfour
          hj₁one hj₂one hi₁one hi₂one heq
        by_cases hz : K5G12ZeroResidualProfile data
        · exact Or.inr (Or.inl hz)
        · exact Or.inl ⟨hgrid, hz⟩
      · exact Or.inr (Or.inr ⟨hG, Or.inr hu⟩)
    · exact Or.inr (Or.inr ⟨hG, Or.inl hl⟩)
  · have hl := exists_two_k5_unit_lower_residuals_of_global_ne_twenty_four
      data hG
    have hu := exists_two_k5_unit_upper_residuals_of_global_ne_twenty_four
      data ht hfour hblocks hG
    refine ⟨hallowed, Or.inl hl, Or.inl hu, ?_⟩
    obtain ⟨j₁, hj₁, j₂, hj₂, hjneq, hj₁one, hj₂one⟩ := hl
    obtain ⟨i₁, hi₁, i₂, hi₂, hineq, hi₁one, hi₂one⟩ := hu
    have hgrid := k5_proper_nonzero_tangent_grid_of_units
      data hn hd hj₁ hj₂ hi₁ hi₂ hjneq hineq hfour
      hj₁one hj₂one hi₁one hi₂one heq
    by_cases hz : K5G12ZeroResidualProfile data
    · exact Or.inr (Or.inl hz)
    · exact Or.inl ⟨hgrid, hz⟩

/-- The requested binary dispatch follows exactly once the still-live
one-unit `G=24` profile is excluded on both sides. -/
theorem k5_equation_residual_profile_binary_dispatch_of_no_G24_exceptional
    {n d t : ℕ} (data : CanonicalOwnerData 5 n d t)
    (hn : 2811 ≤ n) (hd : 5 ≤ d)
    (ht : t ∈ Finset.Icc 1 5)
    (hfour : 4 ∣ n + d + t)
    (hblocks : upperBlockAfterFour 5 n d t = blockProduct 5 n)
    (heq : blockProduct 5 (n + d) = 4 * blockProduct 5 n)
    (hno24 : canonicalOwnerResidual data = 24 →
      ¬ K5ExceptionalResidualProfile (canonicalLowerResidual data) ∧
      ¬ K5ExceptionalResidualProfile (canonicalUpperResidual data)) :
    (K5ProperNonzeroTangentGrid data ∧
        ¬ K5G12ZeroResidualProfile data) ∨
      K5G12ZeroResidualProfile data := by
  obtain ⟨-, -, -, hdispatch⟩ := k5_equation_residual_profile_dispatch
    data hn hd ht hfour hblocks heq
  rcases hdispatch with hgrid | hG12 | h24
  · exact Or.inl hgrid
  · exact Or.inr hG12
  · obtain ⟨hG, hl | hu⟩ := h24
    · exact (hno24 hG).1 hl |>.elim
    · exact (hno24 hG).2 hu |>.elim

end Erdos686Variant
end Erdos686
