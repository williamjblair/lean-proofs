/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import ErdosProblems.Erdos686.K5.ExceptionalDiagonalGCD
import ErdosProblems.Erdos686.K5.IntegralLift
import ErdosProblems.Erdos686.Core.NormalizedMatching

/-!
# Erdős 686, k=5: the exceptional crossing square defect

At each of the four possible exceptional crossings both relevant local
derivative coefficients are `-6`.  Cancelling this coefficient is legitimate
because the exceptional crossing owner is coprime to six.  The owner square
therefore divides the single signed linear defect

`d + i - j - 3 * (n + j)`.

Together with the centered window `d < n+3`, this gives a strict bound on the
crossing square.  This is genuinely stronger than the exact gcd-star residual,
which by itself contains no square condition from the block equation.
-/

namespace Erdos686
namespace Erdos686Variant

/-- At an even/even `k=5` owner cell, coprimality with six cancels the common
local derivative coefficient and leaves the normalized square defect. -/
theorem k5_even_crossing_owner_sq_dvd_linear_defect
    {n d i j P : ℕ}
    (hi : i = 2 ∨ i = 4)
    (hj : j = 2 ∨ j = 4)
    (hd : 5 ≤ d)
    (hcop : Nat.Coprime P 6)
    (hlower : P ∣ n + j)
    (hupper : P ∣ n + d + i)
    (heq : blockProduct 5 (n + d) = 4 * blockProduct 5 n) :
    ((P : ℤ) ^ 2) ∣
      ((d + i - j : ℕ) : ℤ) - 3 * ((n + j : ℕ) : ℤ) := by
  have hiIcc : i ∈ Finset.Icc 1 5 := by rcases hi with rfl | rfl <;> norm_num
  have hjIcc : j ∈ Finset.Icc 1 5 := by rcases hj with rfl | rfl <;> norm_num
  have hraw := matched_owner_local_coefficients_dvd_sq
    hjIcc hiIcc hlower hupper heq
  rw [localBlockCoefficient_eq_sign_mul_nat hiIcc,
    localBlockCoefficient_eq_sign_mul_nat hjIcc] at hraw
  have hji : j ≤ d + i := by
    rcases hi with rfl | rfl <;> rcases hj with rfl | rfl <;> omega
  have hcastD :
      ((d + i - j : ℕ) : ℤ) = (d : ℤ) + (i : ℤ) - (j : ℤ) := by
    rw [Nat.cast_sub hji]
    push_cast
    rfl
  have hdefect :
      (((-1 : ℤ) ^ (i - 1) * (localBlockCoefficientNat 5 i : ℤ)) *
          ((n + d + i : ℕ) : ℤ) -
        4 * ((-1 : ℤ) ^ (j - 1) * (localBlockCoefficientNat 5 j : ℤ)) *
          ((n + j : ℕ) : ℤ)) =
        -6 * (((d + i - j : ℕ) : ℤ) -
          3 * ((n + j : ℕ) : ℤ)) := by
    rw [hcastD]
    rcases hi with rfl | rfl <;> rcases hj with rfl | rfl <;>
      norm_num [localBlockCoefficientNat] <;> ring
  rw [hdefect] at hraw
  have hraw' :
      ((P : ℤ) ^ 2) ∣
        6 * (((d + i - j : ℕ) : ℤ) -
          3 * ((n + j : ℕ) : ℤ)) := by
    have := dvd_neg.mpr hraw
    convert this using 1 <;> ring
  have hcopSq : IsCoprime ((P : ℤ) ^ 2) (6 : ℤ) :=
    (hcop.pow_left 2).isCoprime
  exact hcopSq.dvd_of_dvd_mul_left hraw'

/-- Equation-facing specialization to an actual exceptional crossing owner. -/
theorem k5_exceptional_crossing_owner_sq_dvd_linear_defect
    {n d t i j : ℕ} (data : CanonicalOwnerData 5 n d t)
    (hi : i = 2 ∨ i = 4)
    (hj : j = 2 ∨ j = 4)
    (hfour : 4 ∣ n + d + t)
    (hd : 5 ≤ d)
    (hcop : Nat.Coprime (canonicalOwnerCell data j i) 6)
    (heq : blockProduct 5 (n + d) = 4 * blockProduct 5 n) :
    (((canonicalOwnerCell data j i : ℕ) : ℤ) ^ 2) ∣
      ((d + i - j : ℕ) : ℤ) - 3 * ((n + j : ℕ) : ℤ) := by
  apply k5_even_crossing_owner_sq_dvd_linear_defect hi hj hd hcop
  · exact canonicalOwnerCell_dvd_lower data
  · exact dvd_trans (canonicalOwnerCell_dvd_upper data)
      (upperTermAfterFour_dvd_original hfour)
  · exact heq

/-- The centered `k=5` window bounds the exceptional crossing square strictly
by three times its fully owned lower term. -/
theorem k5_exceptional_crossing_owner_sq_lt_three_lower
    {n d t i j : ℕ} (data : CanonicalOwnerData 5 n d t)
    (hi : i = 2 ∨ i = 4)
    (hj : j = 2 ∨ j = 4)
    (hfour : 4 ∣ n + d + t)
    (hd : 5 ≤ d)
    (hcop : Nat.Coprime (canonicalOwnerCell data j i) 6)
    (hpos : 0 < canonicalOwnerCell data j i)
    (heq : blockProduct 5 (n + d) = 4 * blockProduct 5 n) :
    (canonicalOwnerCell data j i) ^ 2 < 3 * (n + j) := by
  let u := n + 3
  let v := n + d + 3
  have hu : 3 ≤ u := by dsimp [u]; omega
  have hsol : K5CenteredEq v u := k5_centered_of_eq heq
  have hwindow := k5_integral_solution_window hu hsol
  have hdlt : d < n + 3 := by
    dsimp [u, v] at hwindow
    omega
  have hDlt : d + i - j < 3 * (n + j) := by
    rcases hi with rfl | rfl <;> rcases hj with rfl | rfl <;> omega
  have hsquare := k5_exceptional_crossing_owner_sq_dvd_linear_defect
    data hi hj hfour hd hcop heq
  have hji : j ≤ d + i := by
    rcases hi with rfl | rfl <;> rcases hj with rfl | rfl <;> omega
  have hcast :
      -(((d + i - j : ℕ) : ℤ) - 3 * ((n + j : ℕ) : ℤ)) =
        ((3 * (n + j) - (d + i - j) : ℕ) : ℤ) := by
    rw [Nat.cast_sub (Nat.le_of_lt hDlt), Nat.cast_sub hji]
    push_cast
    ring
  have hdivZ :
      ((canonicalOwnerCell data j i : ℤ) ^ 2) ∣
        ((3 * (n + j) - (d + i - j) : ℕ) : ℤ) := by
    rw [← hcast]
    exact dvd_neg.mpr hsquare
  have hdiv :
      (canonicalOwnerCell data j i) ^ 2 ∣
        3 * (n + j) - (d + i - j) := by
    exact_mod_cast hdivZ
  have hdiffPos : 0 < 3 * (n + j) - (d + i - j) := Nat.sub_pos_of_lt hDlt
  have hle := Nat.le_of_dvd hdiffPos hdiv
  omega

/-- Every exceptional residual placement inherits the strict square bound at
its nontrivial even/even crossing.  This packages the new equation-facing
information with the four exact placement cases. -/
theorem k5_exceptional_crossing_square_bound
    {n d t : ℕ} (data : CanonicalOwnerData 5 n d t)
    (ht : t ∈ Finset.Icc 1 5)
    (hfour : 4 ∣ n + d + t)
    (hblocks : upperBlockAfterFour 5 n d t = blockProduct 5 n)
    (htail : 10 ^ 1000 ≤ d)
    (heq : blockProduct 5 (n + d) = 4 * blockProduct 5 n)
    (hlower : K5ExceptionalResidualProfile (canonicalLowerResidual data))
    (hupper : K5ExceptionalResidualProfile (canonicalUpperResidual data)) :
    (d % 6 = 0 ∧
      (canonicalOwnerCell data 2 2) ^ 2 < 3 * (n + 2)) ∨
    (d % 6 = 2 ∧
      (canonicalOwnerCell data 2 4) ^ 2 < 3 * (n + 2)) ∨
    (d % 6 = 4 ∧
      (canonicalOwnerCell data 4 2) ^ 2 < 3 * (n + 4)) ∨
    (d % 6 = 0 ∧
      (canonicalOwnerCell data 4 4) ^ 2 < 3 * (n + 4)) := by
  have hd : 5 ≤ d := by
    have hbase : 5 ≤ 10 ^ 1000 := by
      rw [show 1000 = 999 + 1 by omega, pow_succ]
      have hp0 : 0 < (10 : ℕ) ^ 999 := pow_pos (by norm_num) _
      have hp : 1 ≤ (10 : ℕ) ^ 999 := hp0
      calc
        5 ≤ 1 * 10 := by norm_num
        _ ≤ 10 ^ 999 * 10 := Nat.mul_le_mul_right 10 hp
    exact le_trans hbase htail
  have hcases := k5_exceptional_exact_unit_crossing_constraints
    data ht hfour hblocks htail heq hlower hupper
  rcases hcases with hc | hc | hc | hc
  · left
    rcases hc with ⟨hmod, -, -, -, -, hcop, -⟩
    refine ⟨hmod, k5_exceptional_crossing_owner_sq_lt_three_lower
      data (by left; rfl) (by left; rfl) hfour hd hcop
      (canonicalOwnerCell_pos data) heq⟩
  · right; left
    rcases hc with ⟨hmod, -, -, -, -, hcop, -⟩
    refine ⟨hmod, k5_exceptional_crossing_owner_sq_lt_three_lower
      data (by right; rfl) (by left; rfl) hfour hd hcop
      (canonicalOwnerCell_pos data) heq⟩
  · right; right; left
    rcases hc with ⟨hmod, -, -, -, -, hcop, -⟩
    refine ⟨hmod, k5_exceptional_crossing_owner_sq_lt_three_lower
      data (by left; rfl) (by right; rfl) hfour hd hcop
      (canonicalOwnerCell_pos data) heq⟩
  · right; right; right
    rcases hc with ⟨hmod, -, -, -, -, hcop, -⟩
    refine ⟨hmod, k5_exceptional_crossing_owner_sq_lt_three_lower
      data (by right; rfl) (by right; rfl) hfour hd hcop
      (canonicalOwnerCell_pos data) heq⟩

#print axioms k5_even_crossing_owner_sq_dvd_linear_defect
#print axioms k5_exceptional_crossing_owner_sq_dvd_linear_defect
#print axioms k5_exceptional_crossing_owner_sq_lt_three_lower
#print axioms k5_exceptional_crossing_square_bound

end Erdos686Variant
end Erdos686
