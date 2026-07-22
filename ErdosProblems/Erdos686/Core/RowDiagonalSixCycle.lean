/- leanprover/lean4:v4.29.1 mathlib v4.29.1 -/
import ErdosProblems.Erdos686.Core.RowDiagonalFourCycleObstruction

/-!
# Erdős 686: a non-tautological six-cycle secant invariant

Write the three row terms of an alternating six-cycle as

`x₁=a₁b₁r₁`, `x₂=a₂b₂r₂`, `x₃=a₃b₃r₃`

and its three signed-diagonal terms as

`y₁=b₁a₂q₁`, `y₂=b₂a₃q₂`, `y₃=b₃a₁q₃`.

The product of the three cyclic secants is exactly `(b₁b₂b₃)^2`
times a product of three square-weighted cofactor defects.  This gives a
genuine nonzero size branch without inserting missing owners by hand.  In
the zero branch, one defect vanishes and forces a squared middle owner and
its two neighbouring owners into two diagonal cofactors.
-/

namespace Erdos686
namespace Erdos686Variant

/-- One five-owner quotient exposed by adjacent row/diagonal secants in a
six-cycle. -/
def sixCycleLocalQuotient
    (aLeft aMid aRight rLeft rMid qLeft qRight : ℤ) : ℤ :=
  aLeft * aRight * rLeft * qRight - aMid ^ 2 * rMid * qLeft

/-- Product of the three cyclic row/diagonal secants. -/
def sixCycleSecantProduct
    (x₁ x₂ x₃ y₁ y₂ y₃ : ℤ) : ℤ :=
  (x₁ * y₂ - x₂ * y₁) *
    (x₂ * y₃ - x₃ * y₂) *
      (x₃ * y₁ - x₁ * y₃)

/-- Exact five-owner factorization of one adjacent cyclic secant. -/
theorem sixCycle_adjacent_secant_factorization
    {aLeft aMid aRight bLeft bRight rLeft rMid qLeft qRight
      xLeft xMid yLeft yRight : ℤ}
    (hxLeft : xLeft = aLeft * bLeft * rLeft)
    (hxMid : xMid = aMid * bRight * rMid)
    (hyLeft : yLeft = bLeft * aMid * qLeft)
    (hyRight : yRight = bRight * aRight * qRight) :
    xLeft * yRight - xMid * yLeft =
      bLeft * bRight *
        sixCycleLocalQuotient
          aLeft aMid aRight rLeft rMid qLeft qRight := by
  rw [hxLeft, hxMid, hyLeft, hyRight]
  unfold sixCycleLocalQuotient
  ring

/-- Exact factorization of the complete cyclic secant product. -/
theorem sixCycle_secantProduct_factorization
    {a₁ a₂ a₃ b₁ b₂ b₃ r₁ r₂ r₃ q₁ q₂ q₃
      x₁ x₂ x₃ y₁ y₂ y₃ : ℤ}
    (hx₁ : x₁ = a₁ * b₁ * r₁)
    (hx₂ : x₂ = a₂ * b₂ * r₂)
    (hx₃ : x₃ = a₃ * b₃ * r₃)
    (hy₁ : y₁ = b₁ * a₂ * q₁)
    (hy₂ : y₂ = b₂ * a₃ * q₂)
    (hy₃ : y₃ = b₃ * a₁ * q₃) :
    sixCycleSecantProduct x₁ x₂ x₃ y₁ y₂ y₃ =
      (b₁ * b₂ * b₃) ^ 2 *
        sixCycleLocalQuotient a₁ a₂ a₃ r₁ r₂ q₁ q₂ *
        sixCycleLocalQuotient a₂ a₃ a₁ r₂ r₃ q₂ q₃ *
        sixCycleLocalQuotient a₃ a₁ a₂ r₃ r₁ q₃ q₁ := by
  unfold sixCycleSecantProduct
  rw [sixCycle_adjacent_secant_factorization hx₁ hx₂ hy₁ hy₂,
    sixCycle_adjacent_secant_factorization hx₂ hx₃ hy₂ hy₃,
    sixCycle_adjacent_secant_factorization hx₃ hx₁ hy₃ hy₁]
  ring

/-- Nonzero branch: one alternating half of the complete cycle owner mass,
squared, is bounded by the unweighted cyclic secant product. -/
theorem sixCycle_alternatingMass_sq_le_secantProduct_natAbs
    {a₁ a₂ a₃ b₁ b₂ b₃ r₁ r₂ r₃ q₁ q₂ q₃ : ℕ}
    {x₁ x₂ x₃ y₁ y₂ y₃ : ℤ}
    (hx₁ : x₁ = (a₁ : ℤ) * b₁ * r₁)
    (hx₂ : x₂ = (a₂ : ℤ) * b₂ * r₂)
    (hx₃ : x₃ = (a₃ : ℤ) * b₃ * r₃)
    (hy₁ : y₁ = (b₁ : ℤ) * a₂ * q₁)
    (hy₂ : y₂ = (b₂ : ℤ) * a₃ * q₂)
    (hy₃ : y₃ = (b₃ : ℤ) * a₁ * q₃)
    (hnonzero : sixCycleSecantProduct x₁ x₂ x₃ y₁ y₂ y₃ ≠ 0) :
    (b₁ * b₂ * b₃) ^ 2 ≤
      (sixCycleSecantProduct x₁ x₂ x₃ y₁ y₂ y₃).natAbs := by
  apply Nat.le_of_dvd (Int.natAbs_pos.mpr hnonzero)
  have hdvdZ : (((b₁ * b₂ * b₃) ^ 2 : ℕ) : ℤ) ∣
      sixCycleSecantProduct x₁ x₂ x₃ y₁ y₂ y₃ := by
    rw [sixCycle_secantProduct_factorization
      hx₁ hx₂ hx₃ hy₁ hy₂ hy₃]
    refine ⟨sixCycleLocalQuotient (a₁ : ℤ) a₂ a₃ r₁ r₂ q₁ q₂ *
        sixCycleLocalQuotient a₂ a₃ a₁ r₂ r₃ q₂ q₃ *
        sixCycleLocalQuotient a₃ a₁ a₂ r₃ r₁ q₃ q₁, ?_⟩
    push_cast
    ring
  simpa using Int.natAbs_dvd_natAbs.mpr hdvdZ

/-- Arithmetic zero-quotient kernel.  A vanished five-owner quotient forces
the middle owner square and the product of its two neighbours into the two
opposite diagonal cofactors. -/
theorem sixCycle_zero_localQuotient_forces_crowding
    {aLeft aMid aRight rLeft rMid qLeft qRight : ℕ}
    (hmid : (aMid ^ 2).Coprime (aLeft * aRight * rLeft))
    (hneighbours : (aLeft * aRight).Coprime (aMid ^ 2 * rMid))
    (hzero : aLeft * aRight * rLeft * qRight =
      aMid ^ 2 * rMid * qLeft) :
    (aLeft * aRight) * aMid ^ 2 ∣ qLeft * qRight := by
  have hmidDvd : aMid ^ 2 ∣
      (aLeft * aRight * rLeft) * qRight := by
    rw [hzero]
    exact ⟨rMid * qLeft, by ring⟩
  have hmidQ : aMid ^ 2 ∣ qRight :=
    hmid.dvd_of_dvd_mul_left hmidDvd
  have hneighbourDvd : aLeft * aRight ∣
      (aMid ^ 2 * rMid) * qLeft := by
    rw [← hzero]
    exact ⟨rLeft * qRight, by ring⟩
  have hneighbourQ : aLeft * aRight ∣ qLeft :=
    hneighbours.dvd_of_dvd_mul_left hneighbourDvd
  exact Nat.mul_dvd_mul hneighbourQ hmidQ

/-- Complete six-cycle dichotomy.  Either the cyclic secant product is
nonzero and bounds the square of the alternating `b`-owner mass, or one of
the three cyclic local quotients vanishes and forces an extra owner square
into the corresponding pair of diagonal cofactors. -/
theorem sixCycle_secant_or_ownerSquare_crowding
    {a₁ a₂ a₃ b₁ b₂ b₃ r₁ r₂ r₃ q₁ q₂ q₃ : ℕ}
    {x₁ x₂ x₃ y₁ y₂ y₃ : ℤ}
    (hb₁ : 0 < b₁) (hb₂ : 0 < b₂) (hb₃ : 0 < b₃)
    (hmid₁₂₃ : (a₂ ^ 2).Coprime (a₁ * a₃ * r₁))
    (hneighbour₁₂₃ : (a₁ * a₃).Coprime (a₂ ^ 2 * r₂))
    (hmid₂₃₁ : (a₃ ^ 2).Coprime (a₂ * a₁ * r₂))
    (hneighbour₂₃₁ : (a₂ * a₁).Coprime (a₃ ^ 2 * r₃))
    (hmid₃₁₂ : (a₁ ^ 2).Coprime (a₃ * a₂ * r₃))
    (hneighbour₃₁₂ : (a₃ * a₂).Coprime (a₁ ^ 2 * r₁))
    (hx₁ : x₁ = (a₁ : ℤ) * b₁ * r₁)
    (hx₂ : x₂ = (a₂ : ℤ) * b₂ * r₂)
    (hx₃ : x₃ = (a₃ : ℤ) * b₃ * r₃)
    (hy₁ : y₁ = (b₁ : ℤ) * a₂ * q₁)
    (hy₂ : y₂ = (b₂ : ℤ) * a₃ * q₂)
    (hy₃ : y₃ = (b₃ : ℤ) * a₁ * q₃) :
    (b₁ * b₂ * b₃) ^ 2 ≤
        (sixCycleSecantProduct x₁ x₂ x₃ y₁ y₂ y₃).natAbs ∨
      ((a₁ * a₃) * a₂ ^ 2 ∣ q₁ * q₂) ∨
      ((a₂ * a₁) * a₃ ^ 2 ∣ q₂ * q₃) ∨
      ((a₃ * a₂) * a₁ ^ 2 ∣ q₃ * q₁) := by
  by_cases hsec : sixCycleSecantProduct x₁ x₂ x₃ y₁ y₂ y₃ = 0
  · right
    unfold sixCycleSecantProduct at hsec
    rcases mul_eq_zero.mp hsec with hfirst | h31
    · rcases mul_eq_zero.mp hfirst with h12 | h23
      · left
        have hfactor := sixCycle_adjacent_secant_factorization
          hx₁ hx₂ hy₁ hy₂
        rw [h12] at hfactor
        have hqz : sixCycleLocalQuotient
            (a₁ : ℤ) a₂ a₃ r₁ r₂ q₁ q₂ = 0 := by
          apply (mul_eq_zero.mp hfactor.symm).resolve_left
          exact mul_ne_zero (Int.ofNat_ne_zero.mpr (Nat.ne_of_gt hb₁))
            (Int.ofNat_ne_zero.mpr (Nat.ne_of_gt hb₂))
        unfold sixCycleLocalQuotient at hqz
        have hzero : a₁ * a₃ * r₁ * q₂ = a₂ ^ 2 * r₂ * q₁ := by
          exact_mod_cast sub_eq_zero.mp hqz
        exact sixCycle_zero_localQuotient_forces_crowding
          hmid₁₂₃ hneighbour₁₂₃ hzero
      · right; left
        have hfactor := sixCycle_adjacent_secant_factorization
          hx₂ hx₃ hy₂ hy₃
        rw [h23] at hfactor
        have hqz : sixCycleLocalQuotient
            (a₂ : ℤ) a₃ a₁ r₂ r₃ q₂ q₃ = 0 := by
          apply (mul_eq_zero.mp hfactor.symm).resolve_left
          exact mul_ne_zero (Int.ofNat_ne_zero.mpr (Nat.ne_of_gt hb₂))
            (Int.ofNat_ne_zero.mpr (Nat.ne_of_gt hb₃))
        unfold sixCycleLocalQuotient at hqz
        have hzero : a₂ * a₁ * r₂ * q₃ = a₃ ^ 2 * r₃ * q₂ := by
          exact_mod_cast sub_eq_zero.mp hqz
        exact sixCycle_zero_localQuotient_forces_crowding
          hmid₂₃₁ hneighbour₂₃₁ hzero
    · right; right
      have hfactor := sixCycle_adjacent_secant_factorization
        hx₃ hx₁ hy₃ hy₁
      rw [h31] at hfactor
      have hqz : sixCycleLocalQuotient
          (a₃ : ℤ) a₁ a₂ r₃ r₁ q₃ q₁ = 0 := by
        apply (mul_eq_zero.mp hfactor.symm).resolve_left
        exact mul_ne_zero (Int.ofNat_ne_zero.mpr (Nat.ne_of_gt hb₃))
          (Int.ofNat_ne_zero.mpr (Nat.ne_of_gt hb₁))
      unfold sixCycleLocalQuotient at hqz
      have hzero : a₃ * a₂ * r₃ * q₁ = a₁ ^ 2 * r₁ * q₃ := by
        exact_mod_cast sub_eq_zero.mp hqz
      exact sixCycle_zero_localQuotient_forces_crowding
        hmid₃₁₂ hneighbour₃₁₂ hzero
  · left
    exact sixCycle_alternatingMass_sq_le_secantProduct_natAbs
      hx₁ hx₂ hx₃ hy₁ hy₂ hy₃ hsec

#print axioms sixCycle_adjacent_secant_factorization
#print axioms sixCycle_secantProduct_factorization
#print axioms sixCycle_alternatingMass_sq_le_secantProduct_natAbs
#print axioms sixCycle_zero_localQuotient_forces_crowding
#print axioms sixCycle_secant_or_ownerSquare_crowding

end Erdos686Variant
end Erdos686
