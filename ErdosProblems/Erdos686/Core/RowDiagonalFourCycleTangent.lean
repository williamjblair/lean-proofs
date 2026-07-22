/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import ErdosProblems.Erdos686.Core.RowDiagonalFourCycle
import ErdosProblems.Erdos686.Core.LargeOwnerTwoRegularArithmetic

/-!
# Erdős 686: four-cycle additive tangent product

The secant cycle uses lower-row and signed-diagonal factorizations.  This
module adds the independent upper-column equations.  At each corner the
exact identity `upper = lower + diagonal` cancels the common owner and writes
the upper quotient as a sum of the row and diagonal quotients.

Applying the first normalized tangent congruence at all four corners gives a
cycle-level dichotomy.  If their product is nonzero, the complete four-owner
mass is bounded by that tangent product.  If one tangent vanishes, the row
partner at that corner divides the corresponding diagonal cofactor.  The
latter is a genuine extra-owner crowding statement, not a row/diagonal
capacity inequality.  No claim is made here that either branch already
excludes every canonical four-cycle.
-/

namespace Erdos686
namespace Erdos686Variant

/-- First-tangent defect after the common owner has been removed from the
upper and lower terms.  In the normalized matching specialization `b` is the
reduced right binomial coefficient and `c = 4*sign*a`. -/
def fourCycleTangentDefect (b c z rowOwner rowCofactor : ℤ) : ℤ :=
  b * z - c * rowOwner * rowCofactor

/-- One upper-column equation cancels its nonzero common owner exactly. -/
theorem fourCycle_upper_quotient_eq_row_add_diagonal
    {P R D r q z x y u : ℤ}
    (hP : P ≠ 0)
    (hx : x = P * R * r)
    (hy : y = P * D * q)
    (hu : u = P * z)
    (hadd : u = x + y) :
    z = R * r + D * q := by
  apply mul_left_cancel₀ hP
  calc
    P * z = u := hu.symm
    _ = x + y := hadd
    _ = P * R * r + P * D * q := by rw [hx, hy]
    _ = P * (R * r + D * q) := by ring

/-- The four upper-column equations on a row/diagonal four-cycle give the
complete additive quotient system. -/
theorem fourCycle_upper_quotient_additive_system
    {A B C D r₁ r₂ q₁ q₂
      z₁₁ z₁₂ z₂₁ z₂₂ x₁ x₂ y₁ y₂
      u₁₁ u₁₂ u₂₁ u₂₂ : ℤ}
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0) (hD : D ≠ 0)
    (hx₁ : x₁ = A * B * r₁)
    (hx₂ : x₂ = C * D * r₂)
    (hy₁ : y₁ = A * C * q₁)
    (hy₂ : y₂ = B * D * q₂)
    (hu₁₁ : u₁₁ = A * z₁₁)
    (hu₁₂ : u₁₂ = B * z₁₂)
    (hu₂₁ : u₂₁ = C * z₂₁)
    (hu₂₂ : u₂₂ = D * z₂₂)
    (hadd₁₁ : u₁₁ = x₁ + y₁)
    (hadd₁₂ : u₁₂ = x₁ + y₂)
    (hadd₂₁ : u₂₁ = x₂ + y₁)
    (hadd₂₂ : u₂₂ = x₂ + y₂) :
    z₁₁ = B * r₁ + C * q₁ ∧
      z₁₂ = A * r₁ + D * q₂ ∧
      z₂₁ = D * r₂ + A * q₁ ∧
      z₂₂ = C * r₂ + B * q₂ := by
  exact ⟨
    fourCycle_upper_quotient_eq_row_add_diagonal
      hA hx₁ hy₁ hu₁₁ hadd₁₁,
    fourCycle_upper_quotient_eq_row_add_diagonal
      hB (by simpa [mul_assoc, mul_comm, mul_left_comm] using hx₁)
        (by simpa [mul_assoc, mul_comm, mul_left_comm] using hy₂)
        hu₁₂ hadd₁₂,
    fourCycle_upper_quotient_eq_row_add_diagonal
      hC hx₂ (by simpa [mul_assoc, mul_comm, mul_left_comm] using hy₁)
        hu₂₁ hadd₂₁,
    fourCycle_upper_quotient_eq_row_add_diagonal
      hD (by simpa [mul_assoc, mul_comm, mul_left_comm] using hx₂)
        (by simpa [mul_assoc, mul_comm, mul_left_comm] using hy₂)
        hu₂₂ hadd₂₂⟩

/-- If one tangent defect vanishes, exact upper additivity turns it into an
extra-owner divisor of the diagonal cofactor.  Only coprimality with the
coefficient-weighted diagonal owner is used. -/
theorem fourCycle_zero_tangent_forces_rowOwner_dvd_diagonalCofactor
    {R D r q z b c : ℤ}
    (hadd : z = R * r + D * q)
    (hcop : IsCoprime R (b * D))
    (hzero : fourCycleTangentDefect b c z R r = 0) :
    R ∣ q := by
  have hdvd : R ∣ (b * D) * q := by
    refine ⟨(c - b) * r, ?_⟩
    unfold fourCycleTangentDefect at hzero
    rw [hadd] at hzero
    calc
      (b * D) * q = b * (R * r + D * q) - b * R * r := by ring
      _ = c * R * r - b * R * r := by
        rw [sub_eq_zero.mp hzero]
      _ = R * ((c - b) * r) := by ring
  exact hcop.dvd_of_dvd_mul_left hdvd

/-- Direct bridge from one normalized owner-square congruence to the tangent
defect used by the four-cycle product.  The upper quotient is kept whole, so
no hypothesis about the number of owners in its column is required. -/
theorem normalized_square_implies_owner_dvd_fourCycleTangentDefect
    {P R r z x delta u a b sign : ℤ}
    (hP : P ≠ 0)
    (hx : x = P * R * r)
    (hu : u = P * z)
    (hupper : u = x + delta)
    (hsquare : P ^ 2 ∣ normalizedMatchingForm a b sign delta x) :
    P ∣ fourCycleTangentDefect b (4 * sign * a) z R r := by
  have hform : normalizedMatchingForm a b sign delta x =
      P * fourCycleTangentDefect b (4 * sign * a) z R r := by
    rw [normalizedMatchingForm_eq_upper_form, ← hupper, hx, hu]
    unfold fourCycleTangentDefect
    ring
  rw [hform] at hsquare
  exact (square_dvd_owner_mul_iff_owner_dvd_int hP).mp hsquare

/-- Abstract cycle-level additive/tangent dichotomy.  The four local tangent
divisibilities multiply without any complementary-product lift.  Thus the
nonzero branch sees the complete owner mass.  In the zero branch, upper
additivity forces one of the four row partners into the adjacent diagonal
cofactor. -/
theorem fourCycle_tangentProduct_or_extraOwner_crowding
    {A B C D r₁ r₂ q₁ q₂
      z₁₁ z₁₂ z₂₁ z₂₂
      b₁₁ b₁₂ b₂₁ b₂₂ c₁₁ c₁₂ c₂₁ c₂₂ : ℤ}
    (hadd₁₁ : z₁₁ = B * r₁ + C * q₁)
    (hadd₁₂ : z₁₂ = A * r₁ + D * q₂)
    (hadd₂₁ : z₂₁ = D * r₂ + A * q₁)
    (hadd₂₂ : z₂₂ = C * r₂ + B * q₂)
    (hcop₁₁ : IsCoprime B (b₁₁ * C))
    (hcop₁₂ : IsCoprime A (b₁₂ * D))
    (hcop₂₁ : IsCoprime D (b₂₁ * A))
    (hcop₂₂ : IsCoprime C (b₂₂ * B))
    (hdiv₁₁ : A ∣ fourCycleTangentDefect b₁₁ c₁₁ z₁₁ B r₁)
    (hdiv₁₂ : B ∣ fourCycleTangentDefect b₁₂ c₁₂ z₁₂ A r₁)
    (hdiv₂₁ : C ∣ fourCycleTangentDefect b₂₁ c₂₁ z₂₁ D r₂)
    (hdiv₂₂ : D ∣ fourCycleTangentDefect b₂₂ c₂₂ z₂₂ C r₂) :
    (A * B * C * D).natAbs ≤
        (fourCycleTangentDefect b₁₁ c₁₁ z₁₁ B r₁ *
          fourCycleTangentDefect b₁₂ c₁₂ z₁₂ A r₁ *
          fourCycleTangentDefect b₂₁ c₂₁ z₂₁ D r₂ *
          fourCycleTangentDefect b₂₂ c₂₂ z₂₂ C r₂).natAbs ∨
      B ∣ q₁ ∨ A ∣ q₂ ∨ D ∣ q₁ ∨ C ∣ q₂ := by
  let T₁₁ := fourCycleTangentDefect b₁₁ c₁₁ z₁₁ B r₁
  let T₁₂ := fourCycleTangentDefect b₁₂ c₁₂ z₁₂ A r₁
  let T₂₁ := fourCycleTangentDefect b₂₁ c₂₁ z₂₁ D r₂
  let T₂₂ := fourCycleTangentDefect b₂₂ c₂₂ z₂₂ C r₂
  by_cases hprod : T₁₁ * T₁₂ * T₂₁ * T₂₂ = 0
  · right
    rcases mul_eq_zero.mp hprod with hleft | hT₂₂
    · rcases mul_eq_zero.mp hleft with hleft | hT₂₁
      · rcases mul_eq_zero.mp hleft with hT₁₁ | hT₁₂
        · exact Or.inl
            (fourCycle_zero_tangent_forces_rowOwner_dvd_diagonalCofactor
              hadd₁₁ hcop₁₁ hT₁₁)
        · exact Or.inr (Or.inl
            (fourCycle_zero_tangent_forces_rowOwner_dvd_diagonalCofactor
              hadd₁₂ hcop₁₂ hT₁₂))
      · exact Or.inr (Or.inr (Or.inl
          (fourCycle_zero_tangent_forces_rowOwner_dvd_diagonalCofactor
            hadd₂₁ hcop₂₁ hT₂₁)))
    · exact Or.inr (Or.inr (Or.inr
        (fourCycle_zero_tangent_forces_rowOwner_dvd_diagonalCofactor
          hadd₂₂ hcop₂₂ hT₂₂)))
  · left
    apply Nat.le_of_dvd (Int.natAbs_pos.mpr hprod)
    apply Int.natAbs_dvd_natAbs.mpr
    obtain ⟨w₁₁, hw₁₁⟩ := hdiv₁₁
    obtain ⟨w₁₂, hw₁₂⟩ := hdiv₁₂
    obtain ⟨w₂₁, hw₂₁⟩ := hdiv₂₁
    obtain ⟨w₂₂, hw₂₂⟩ := hdiv₂₂
    change T₁₁ = A * w₁₁ at hw₁₁
    change T₁₂ = B * w₁₂ at hw₁₂
    change T₂₁ = C * w₂₁ at hw₂₁
    change T₂₂ = D * w₂₂ at hw₂₂
    refine ⟨w₁₁ * w₁₂ * w₂₁ * w₂₂, ?_⟩
    rw [hw₁₁, hw₁₂, hw₂₁, hw₂₂]
    ring

/-- Re-express the zero branch as literal repeated-owner crowding in the
product of the two signed-diagonal terms.  For example, `B ∣ q₁` means that
the ordinary four-owner mass occurs in `y₁*y₂` together with a second copy
of `B`. -/
theorem fourCycle_tangentProduct_or_diagonalProduct_ownerCrowding
    {A B C D r₁ r₂ q₁ q₂ y₁ y₂
      z₁₁ z₁₂ z₂₁ z₂₂
      b₁₁ b₁₂ b₂₁ b₂₂ c₁₁ c₁₂ c₂₁ c₂₂ : ℤ}
    (hy₁ : y₁ = A * C * q₁)
    (hy₂ : y₂ = B * D * q₂)
    (hadd₁₁ : z₁₁ = B * r₁ + C * q₁)
    (hadd₁₂ : z₁₂ = A * r₁ + D * q₂)
    (hadd₂₁ : z₂₁ = D * r₂ + A * q₁)
    (hadd₂₂ : z₂₂ = C * r₂ + B * q₂)
    (hcop₁₁ : IsCoprime B (b₁₁ * C))
    (hcop₁₂ : IsCoprime A (b₁₂ * D))
    (hcop₂₁ : IsCoprime D (b₂₁ * A))
    (hcop₂₂ : IsCoprime C (b₂₂ * B))
    (hdiv₁₁ : A ∣ fourCycleTangentDefect b₁₁ c₁₁ z₁₁ B r₁)
    (hdiv₁₂ : B ∣ fourCycleTangentDefect b₁₂ c₁₂ z₁₂ A r₁)
    (hdiv₂₁ : C ∣ fourCycleTangentDefect b₂₁ c₂₁ z₂₁ D r₂)
    (hdiv₂₂ : D ∣ fourCycleTangentDefect b₂₂ c₂₂ z₂₂ C r₂) :
    (A * B * C * D).natAbs ≤
        (fourCycleTangentDefect b₁₁ c₁₁ z₁₁ B r₁ *
          fourCycleTangentDefect b₁₂ c₁₂ z₁₂ A r₁ *
          fourCycleTangentDefect b₂₁ c₂₁ z₂₁ D r₂ *
          fourCycleTangentDefect b₂₂ c₂₂ z₂₂ C r₂).natAbs ∨
      (A * B * C * D) * B ∣ y₁ * y₂ ∨
      (A * B * C * D) * A ∣ y₁ * y₂ ∨
      (A * B * C * D) * D ∣ y₁ * y₂ ∨
      (A * B * C * D) * C ∣ y₁ * y₂ := by
  rcases fourCycle_tangentProduct_or_extraOwner_crowding
      hadd₁₁ hadd₁₂ hadd₂₁ hadd₂₂ hcop₁₁ hcop₁₂ hcop₂₁ hcop₂₂
      hdiv₁₁ hdiv₁₂ hdiv₂₁ hdiv₂₂ with hnonzero | hzero
  · exact Or.inl hnonzero
  · right
    rcases hzero with hB | hA | hD | hC
    · left
      obtain ⟨w, hw⟩ := hB
      refine ⟨w * q₂, ?_⟩
      rw [hy₁, hy₂, hw]
      ring
    · right; left
      obtain ⟨w, hw⟩ := hA
      refine ⟨q₁ * w, ?_⟩
      rw [hy₁, hy₂, hw]
      ring
    · right; right; left
      obtain ⟨w, hw⟩ := hD
      refine ⟨w * q₂, ?_⟩
      rw [hy₁, hy₂, hw]
      ring
    · right; right; right
      obtain ⟨w, hw⟩ := hC
      refine ⟨q₁ * w, ?_⟩
      rw [hy₁, hy₂, hw]
      ring

/-- Equation-facing wrapper: derive the four additive upper quotients from
the shared row, diagonal, and upper-column equations, then apply the tangent
product dichotomy. -/
theorem fourCycle_equations_tangentProduct_or_extraOwner_crowding
    {A B C D r₁ r₂ q₁ q₂
      z₁₁ z₁₂ z₂₁ z₂₂ x₁ x₂ y₁ y₂
      u₁₁ u₁₂ u₂₁ u₂₂
      b₁₁ b₁₂ b₂₁ b₂₂ c₁₁ c₁₂ c₂₁ c₂₂ : ℤ}
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0) (hD : D ≠ 0)
    (hx₁ : x₁ = A * B * r₁)
    (hx₂ : x₂ = C * D * r₂)
    (hy₁ : y₁ = A * C * q₁)
    (hy₂ : y₂ = B * D * q₂)
    (hu₁₁ : u₁₁ = A * z₁₁)
    (hu₁₂ : u₁₂ = B * z₁₂)
    (hu₂₁ : u₂₁ = C * z₂₁)
    (hu₂₂ : u₂₂ = D * z₂₂)
    (hadd₁₁ : u₁₁ = x₁ + y₁)
    (hadd₁₂ : u₁₂ = x₁ + y₂)
    (hadd₂₁ : u₂₁ = x₂ + y₁)
    (hadd₂₂ : u₂₂ = x₂ + y₂)
    (hcop₁₁ : IsCoprime B (b₁₁ * C))
    (hcop₁₂ : IsCoprime A (b₁₂ * D))
    (hcop₂₁ : IsCoprime D (b₂₁ * A))
    (hcop₂₂ : IsCoprime C (b₂₂ * B))
    (hdiv₁₁ : A ∣ fourCycleTangentDefect b₁₁ c₁₁ z₁₁ B r₁)
    (hdiv₁₂ : B ∣ fourCycleTangentDefect b₁₂ c₁₂ z₁₂ A r₁)
    (hdiv₂₁ : C ∣ fourCycleTangentDefect b₂₁ c₂₁ z₂₁ D r₂)
    (hdiv₂₂ : D ∣ fourCycleTangentDefect b₂₂ c₂₂ z₂₂ C r₂) :
    (A * B * C * D).natAbs ≤
        (fourCycleTangentDefect b₁₁ c₁₁ z₁₁ B r₁ *
          fourCycleTangentDefect b₁₂ c₁₂ z₁₂ A r₁ *
          fourCycleTangentDefect b₂₁ c₂₁ z₂₁ D r₂ *
          fourCycleTangentDefect b₂₂ c₂₂ z₂₂ C r₂).natAbs ∨
      B ∣ q₁ ∨ A ∣ q₂ ∨ D ∣ q₁ ∨ C ∣ q₂ := by
  obtain ⟨hz₁₁, hz₁₂, hz₂₁, hz₂₂⟩ :=
    fourCycle_upper_quotient_additive_system hA hB hC hD
      hx₁ hx₂ hy₁ hy₂ hu₁₁ hu₁₂ hu₂₁ hu₂₂
      hadd₁₁ hadd₁₂ hadd₂₁ hadd₂₂
  exact fourCycle_tangentProduct_or_extraOwner_crowding
    hz₁₁ hz₁₂ hz₂₁ hz₂₂ hcop₁₁ hcop₁₂ hcop₂₁ hcop₂₂
    hdiv₁₁ hdiv₁₂ hdiv₂₁ hdiv₂₂

/-- Strong equation-facing form with the zero branch stated as an additional
copy of one cycle owner in the two-diagonal product. -/
theorem fourCycle_equations_tangentProduct_or_diagonalProduct_ownerCrowding
    {A B C D r₁ r₂ q₁ q₂
      z₁₁ z₁₂ z₂₁ z₂₂ x₁ x₂ y₁ y₂
      u₁₁ u₁₂ u₂₁ u₂₂
      b₁₁ b₁₂ b₂₁ b₂₂ c₁₁ c₁₂ c₂₁ c₂₂ : ℤ}
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0) (hD : D ≠ 0)
    (hx₁ : x₁ = A * B * r₁)
    (hx₂ : x₂ = C * D * r₂)
    (hy₁ : y₁ = A * C * q₁)
    (hy₂ : y₂ = B * D * q₂)
    (hu₁₁ : u₁₁ = A * z₁₁)
    (hu₁₂ : u₁₂ = B * z₁₂)
    (hu₂₁ : u₂₁ = C * z₂₁)
    (hu₂₂ : u₂₂ = D * z₂₂)
    (hadd₁₁ : u₁₁ = x₁ + y₁)
    (hadd₁₂ : u₁₂ = x₁ + y₂)
    (hadd₂₁ : u₂₁ = x₂ + y₁)
    (hadd₂₂ : u₂₂ = x₂ + y₂)
    (hcop₁₁ : IsCoprime B (b₁₁ * C))
    (hcop₁₂ : IsCoprime A (b₁₂ * D))
    (hcop₂₁ : IsCoprime D (b₂₁ * A))
    (hcop₂₂ : IsCoprime C (b₂₂ * B))
    (hdiv₁₁ : A ∣ fourCycleTangentDefect b₁₁ c₁₁ z₁₁ B r₁)
    (hdiv₁₂ : B ∣ fourCycleTangentDefect b₁₂ c₁₂ z₁₂ A r₁)
    (hdiv₂₁ : C ∣ fourCycleTangentDefect b₂₁ c₂₁ z₂₁ D r₂)
    (hdiv₂₂ : D ∣ fourCycleTangentDefect b₂₂ c₂₂ z₂₂ C r₂) :
    (A * B * C * D).natAbs ≤
        (fourCycleTangentDefect b₁₁ c₁₁ z₁₁ B r₁ *
          fourCycleTangentDefect b₁₂ c₁₂ z₁₂ A r₁ *
          fourCycleTangentDefect b₂₁ c₂₁ z₂₁ D r₂ *
          fourCycleTangentDefect b₂₂ c₂₂ z₂₂ C r₂).natAbs ∨
      (A * B * C * D) * B ∣ y₁ * y₂ ∨
      (A * B * C * D) * A ∣ y₁ * y₂ ∨
      (A * B * C * D) * D ∣ y₁ * y₂ ∨
      (A * B * C * D) * C ∣ y₁ * y₂ := by
  obtain ⟨hz₁₁, hz₁₂, hz₂₁, hz₂₂⟩ :=
    fourCycle_upper_quotient_additive_system hA hB hC hD
      hx₁ hx₂ hy₁ hy₂ hu₁₁ hu₁₂ hu₂₁ hu₂₂
      hadd₁₁ hadd₁₂ hadd₂₁ hadd₂₂
  exact fourCycle_tangentProduct_or_diagonalProduct_ownerCrowding
    hy₁ hy₂ hz₁₁ hz₁₂ hz₂₁ hz₂₂ hcop₁₁ hcop₁₂ hcop₂₁ hcop₂₂
    hdiv₁₁ hdiv₁₂ hdiv₂₁ hdiv₂₂

/-- Fully normalized-square-facing version.  This theorem starts from the
four owner-square congruences themselves, derives their first tangent
defects using the exact upper-column equations, and returns the cycle owner
mass bound or literal repeated-owner crowding in the diagonal product. -/
theorem fourCycle_normalizedSquares_tangentProduct_or_diagonalProduct_ownerCrowding
    {A B C D r₁ r₂ q₁ q₂
      z₁₁ z₁₂ z₂₁ z₂₂ x₁ x₂ y₁ y₂
      u₁₁ u₁₂ u₂₁ u₂₂
      a₁₁ a₁₂ a₂₁ a₂₂ b₁₁ b₁₂ b₂₁ b₂₂
      sign₁₁ sign₁₂ sign₂₁ sign₂₂ : ℤ}
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0) (hD : D ≠ 0)
    (hx₁ : x₁ = A * B * r₁)
    (hx₂ : x₂ = C * D * r₂)
    (hy₁ : y₁ = A * C * q₁)
    (hy₂ : y₂ = B * D * q₂)
    (hu₁₁ : u₁₁ = A * z₁₁)
    (hu₁₂ : u₁₂ = B * z₁₂)
    (hu₂₁ : u₂₁ = C * z₂₁)
    (hu₂₂ : u₂₂ = D * z₂₂)
    (hadd₁₁ : u₁₁ = x₁ + y₁)
    (hadd₁₂ : u₁₂ = x₁ + y₂)
    (hadd₂₁ : u₂₁ = x₂ + y₁)
    (hadd₂₂ : u₂₂ = x₂ + y₂)
    (hcop₁₁ : IsCoprime B (b₁₁ * C))
    (hcop₁₂ : IsCoprime A (b₁₂ * D))
    (hcop₂₁ : IsCoprime D (b₂₁ * A))
    (hcop₂₂ : IsCoprime C (b₂₂ * B))
    (hsquare₁₁ : A ^ 2 ∣ normalizedMatchingForm a₁₁ b₁₁ sign₁₁ y₁ x₁)
    (hsquare₁₂ : B ^ 2 ∣ normalizedMatchingForm a₁₂ b₁₂ sign₁₂ y₂ x₁)
    (hsquare₂₁ : C ^ 2 ∣ normalizedMatchingForm a₂₁ b₂₁ sign₂₁ y₁ x₂)
    (hsquare₂₂ : D ^ 2 ∣ normalizedMatchingForm a₂₂ b₂₂ sign₂₂ y₂ x₂) :
    (A * B * C * D).natAbs ≤
        (fourCycleTangentDefect b₁₁ (4 * sign₁₁ * a₁₁) z₁₁ B r₁ *
          fourCycleTangentDefect b₁₂ (4 * sign₁₂ * a₁₂) z₁₂ A r₁ *
          fourCycleTangentDefect b₂₁ (4 * sign₂₁ * a₂₁) z₂₁ D r₂ *
          fourCycleTangentDefect b₂₂ (4 * sign₂₂ * a₂₂) z₂₂ C r₂).natAbs ∨
      (A * B * C * D) * B ∣ y₁ * y₂ ∨
      (A * B * C * D) * A ∣ y₁ * y₂ ∨
      (A * B * C * D) * D ∣ y₁ * y₂ ∨
      (A * B * C * D) * C ∣ y₁ * y₂ := by
  have hdiv₁₁ := normalized_square_implies_owner_dvd_fourCycleTangentDefect
    (P := A) (R := B) (r := r₁) (z := z₁₁)
      hA hx₁ hu₁₁ hadd₁₁ hsquare₁₁
  have hdiv₁₂ := normalized_square_implies_owner_dvd_fourCycleTangentDefect
    (P := B) (R := A) (r := r₁) (z := z₁₂)
      hB (by simpa [mul_assoc, mul_comm, mul_left_comm] using hx₁)
      hu₁₂ hadd₁₂ hsquare₁₂
  have hdiv₂₁ := normalized_square_implies_owner_dvd_fourCycleTangentDefect
    (P := C) (R := D) (r := r₂) (z := z₂₁)
      hC hx₂ hu₂₁ hadd₂₁ hsquare₂₁
  have hdiv₂₂ := normalized_square_implies_owner_dvd_fourCycleTangentDefect
    (P := D) (R := C) (r := r₂) (z := z₂₂)
      hD (by simpa [mul_assoc, mul_comm, mul_left_comm] using hx₂)
      hu₂₂ hadd₂₂ hsquare₂₂
  exact fourCycle_equations_tangentProduct_or_diagonalProduct_ownerCrowding
    hA hB hC hD hx₁ hx₂ hy₁ hy₂ hu₁₁ hu₁₂ hu₂₁ hu₂₂
    hadd₁₁ hadd₁₂ hadd₂₁ hadd₂₂ hcop₁₁ hcop₁₂ hcop₂₁ hcop₂₂
    hdiv₁₁ hdiv₁₂ hdiv₂₁ hdiv₂₂

#print axioms fourCycle_upper_quotient_eq_row_add_diagonal
#print axioms fourCycle_upper_quotient_additive_system
#print axioms fourCycle_zero_tangent_forces_rowOwner_dvd_diagonalCofactor
#print axioms normalized_square_implies_owner_dvd_fourCycleTangentDefect
#print axioms fourCycle_tangentProduct_or_extraOwner_crowding
#print axioms fourCycle_tangentProduct_or_diagonalProduct_ownerCrowding
#print axioms fourCycle_equations_tangentProduct_or_extraOwner_crowding
#print axioms fourCycle_equations_tangentProduct_or_diagonalProduct_ownerCrowding
#print axioms fourCycle_normalizedSquares_tangentProduct_or_diagonalProduct_ownerCrowding

end Erdos686Variant
end Erdos686
