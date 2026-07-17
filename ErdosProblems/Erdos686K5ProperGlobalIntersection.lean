/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import ErdosProblems.Erdos686K5ProperGlobalCRT
import ErdosProblems.Erdos686ReflectedAlignmentSquareLift

/-!
# Erdős 686, k=5: the exact four-crossing intersection bound

The two fully owned rows and columns in the proper-global branch do not give
four independent moduli: their only possible common prime-power mass lies in
the four crossing owner cells.  This module makes that loss exact enough for
the simultaneous diagonal-window estimate.  In particular the product of the
four consecutive-term moduli divides the degree-nine window times the four
crossing owners, and hence is at most a degree-thirteen polynomial in `d`.
-/

namespace Erdos686
namespace Erdos686Variant

open scoped BigOperators

/-- The uncancelled second-order defect at a `k=5` owner crossing.  Keeping
the signed local coefficients avoids any primality or coefficient-coprimality
hypothesis on the (possibly composite) canonical owner cell. -/
def k5OwnerSquareDefect (n d j i : ℕ) : ℤ :=
  localBlockCoefficient 5 i * ((n + d + i : ℕ) : ℤ) -
    4 * localBlockCoefficient 5 j * ((n + j : ℕ) : ℤ)

/-- Every canonical crossing owner satisfies its exact uncancelled tangent
congruence modulo the owner square. -/
theorem canonicalOwnerCell_sq_dvd_k5OwnerSquareDefect
    {n d t j i : ℕ} (data : CanonicalOwnerData 5 n d t)
    (hj : j ∈ Finset.Icc 1 5) (hi : i ∈ Finset.Icc 1 5)
    (hfour : 4 ∣ n + d + t)
    (heq : blockProduct 5 (n + d) = 4 * blockProduct 5 n) :
    ((canonicalOwnerCell data j i : ℕ) : ℤ) ^ 2 ∣
      k5OwnerSquareDefect n d j i := by
  unfold k5OwnerSquareDefect
  exact matched_owner_local_coefficients_dvd_sq hj hi
    (canonicalOwnerCell_dvd_lower data)
    (dvd_trans (canonicalOwnerCell_dvd_upper data)
      (upperTermAfterFour_dvd_original hfour)) heq

/-- None of the 25 fixed `k=5` tangent defects can vanish on an admissible
solution.  This discharges the zero branch before any absolute-value bound is
taken. -/
theorem k5OwnerSquareDefect_ne_zero_of_solution
    {n d j i : ℕ} (hd : 5 ≤ d)
    (hj : j ∈ Finset.Icc 1 5) (hi : i ∈ Finset.Icc 1 5)
    (heq : blockProduct 5 (n + d) = 4 * blockProduct 5 n) :
    k5OwnerSquareDefect n d j i ≠ 0 := by
  have hgap : 2 * d < n :=
    twice_gap_lt_n_of_four_solution (by norm_num) hd heq
  have hj1 := (Finset.mem_Icc.mp hj).1
  have hj5 := (Finset.mem_Icc.mp hj).2
  have hi1 := (Finset.mem_Icc.mp hi).1
  have hi5 := (Finset.mem_Icc.mp hi).2
  intro hzero
  unfold k5OwnerSquareDefect at hzero
  rw [localBlockCoefficient_eq_sign_mul_nat hi,
    localBlockCoefficient_eq_sign_mul_nat hj] at hzero
  interval_cases j <;> interval_cases i <;>
    norm_num [k5OwnerSquareDefect, localBlockCoefficientNat] at hzero <;> omega

private lemma k5_localBlockCoefficient_natAbs_le_twenty_four
    {i : ℕ} (hi : i ∈ Finset.Icc 1 5) :
    (localBlockCoefficient 5 i).natAbs ≤ 24 := by
  rw [localBlockCoefficient_eq_sign_mul_nat hi, Int.natAbs_mul]
  have hi1 := (Finset.mem_Icc.mp hi).1
  have hi5 := (Finset.mem_Icc.mp hi).2
  interval_cases i <;> norm_num [localBlockCoefficientNat]

/-- Uniform exact height bound for every nonzero `k=5` tangent defect. -/
theorem k5OwnerSquareDefect_natAbs_le
    {n d j i : ℕ} (hd : 5 ≤ d)
    (hj : j ∈ Finset.Icc 1 5) (hi : i ∈ Finset.Icc 1 5)
    (heq : blockProduct 5 (n + d) = 4 * blockProduct 5 n) :
    (k5OwnerSquareDefect n d j i).natAbs ≤ 240 * n := by
  have hgap : 2 * d < n :=
    twice_gap_lt_n_of_four_solution (by norm_num) hd heq
  have hj5 := (Finset.mem_Icc.mp hj).2
  have hi5 := (Finset.mem_Icc.mp hi).2
  have hnpos : 0 < n := by omega
  have hfirst :
      (localBlockCoefficient 5 i * ((n + d + i : ℕ) : ℤ)).natAbs ≤
        24 * (n + d + i) := by
    rw [Int.natAbs_mul]
    norm_num
    exact Nat.mul_le_mul_right _ (k5_localBlockCoefficient_natAbs_le_twenty_four hi)
  have hsecond :
      (4 * localBlockCoefficient 5 j * ((n + j : ℕ) : ℤ)).natAbs ≤
        96 * (n + j) := by
    rw [Int.natAbs_mul, Int.natAbs_mul]
    have hcoeff := k5_localBlockCoefficient_natAbs_le_twenty_four hj
    rw [Int.natAbs_natCast]
    norm_num
    calc
      4 * (localBlockCoefficient 5 j).natAbs * (n + j) ≤
          4 * (24 * (n + j)) :=
        by simpa only [mul_assoc] using
          Nat.mul_le_mul_left 4 (Nat.mul_le_mul_right (n + j) hcoeff)
      _ = 96 * (n + j) := by ring
  calc
    (k5OwnerSquareDefect n d j i).natAbs ≤
        (localBlockCoefficient 5 i * ((n + d + i : ℕ) : ℤ)).natAbs +
          (4 * localBlockCoefficient 5 j * ((n + j : ℕ) : ℤ)).natAbs := by
      exact Int.natAbs_sub_le _ _
    _ ≤ 24 * (n + d + i) + 96 * (n + j) := Nat.add_le_add hfirst hsecond
    _ ≤ 240 * n := by omega

private lemma gcd_mul_mul_dvd_four_gcds
    (a b c e : ℕ) :
    Nat.gcd (a * b) (c * e) ∣
      Nat.gcd a c * Nat.gcd a e * Nat.gcd b c * Nat.gcd b e := by
  have hab : Nat.gcd (a * b) (c * e) ∣
      Nat.gcd a (c * e) * Nat.gcd b (c * e) := by
    have h := gcd_mul_dvd_mul_gcd (c * e) a b
    change Nat.gcd (c * e) (a * b) ∣
      Nat.gcd (c * e) a * Nat.gcd (c * e) b at h
    rw [Nat.gcd_comm (c * e) (a * b), Nat.gcd_comm (c * e) a,
      Nat.gcd_comm (c * e) b] at h
    exact h
  have ha : Nat.gcd a (c * e) ∣ Nat.gcd a c * Nat.gcd a e :=
    gcd_mul_dvd_mul_gcd a c e
  have hb : Nat.gcd b (c * e) ∣ Nat.gcd b c * Nat.gcd b e :=
    gcd_mul_dvd_mul_gcd b c e
  have hprod := Nat.mul_dvd_mul ha hb
  have hprod' : Nat.gcd a (c * e) * Nat.gcd b (c * e) ∣
      Nat.gcd a c * Nat.gcd a e * Nat.gcd b c * Nat.gcd b e := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using hprod
  exact hab.trans hprod'

private lemma gcd_mul_mul_eq_four_gcds_of_coprime
    {a b c e : ℕ} (hab : Nat.Coprime a b) (hce : Nat.Coprime c e) :
    Nat.gcd (a * b) (c * e) =
      Nat.gcd a c * Nat.gcd a e * Nat.gcd b c * Nat.gcd b e := by
  calc
    Nat.gcd (a * b) (c * e) =
        Nat.gcd (a * b) c * Nat.gcd (a * b) e := hce.gcd_mul (a * b)
    _ = (Nat.gcd a c * Nat.gcd b c) *
        (Nat.gcd a e * Nat.gcd b e) := by
      rw [Nat.gcd_comm (a * b) c, hab.gcd_mul c,
        Nat.gcd_comm c a, Nat.gcd_comm c b,
        Nat.gcd_comm (a * b) e, hab.gcd_mul e,
        Nat.gcd_comm e a, Nat.gcd_comm e b]
    _ = Nat.gcd a c * Nat.gcd a e * Nat.gcd b c * Nat.gcd b e := by ring

/-- For two fully owned rows and two fully owned modified columns, every
common factor of the two row/column products is accounted for by the four
crossing owner cells. -/
theorem k5_proper_global_row_column_gcd_dvd_crossings
    {n d t j₁ j₂ i₁ i₂ : ℕ}
    (data : CanonicalOwnerData 5 n d t)
    (hj₁ : j₁ ∈ Finset.Icc 1 5) (hj₂ : j₂ ∈ Finset.Icc 1 5)
    (hi₁ : i₁ ∈ Finset.Icc 1 5) (hi₂ : i₂ ∈ Finset.Icc 1 5)
    (hj₁one : canonicalLowerResidual data j₁ = 1)
    (hj₂one : canonicalLowerResidual data j₂ = 1)
    (hi₁one : canonicalUpperResidual data i₁ = 1)
    (hi₂one : canonicalUpperResidual data i₂ = 1) :
    Nat.gcd ((n + j₁) * (n + j₂))
        (upperTermAfterFour n d t i₁ * upperTermAfterFour n d t i₂) ∣
      canonicalOwnerCell data j₁ i₁ *
        canonicalOwnerCell data j₁ i₂ *
        canonicalOwnerCell data j₂ i₁ *
        canonicalOwnerCell data j₂ i₂ := by
  have h := gcd_mul_mul_dvd_four_gcds
    (n + j₁) (n + j₂)
    (upperTermAfterFour n d t i₁) (upperTermAfterFour n d t i₂)
  rw [canonicalOwner_fullyOwned_gcd_modifiedUpper_eq_cell
      data hj₁ hi₁ hj₁one hi₁one,
    canonicalOwner_fullyOwned_gcd_modifiedUpper_eq_cell
      data hj₁ hi₂ hj₁one hi₂one,
    canonicalOwner_fullyOwned_gcd_modifiedUpper_eq_cell
      data hj₂ hi₁ hj₂one hi₁one,
    canonicalOwner_fullyOwned_gcd_modifiedUpper_eq_cell
      data hj₂ hi₂ hj₂one hi₂one] at h
  exact h

/-- Exact version of the four-crossing intersection theorem.  Distinct fully
owned rows are coprime, as are distinct fully owned modified columns, so no
proper divisor is lost in the preceding estimate. -/
theorem k5_proper_global_row_column_gcd_eq_crossings
    {n d t j₁ j₂ i₁ i₂ : ℕ}
    (data : CanonicalOwnerData 5 n d t)
    (hj₁ : j₁ ∈ Finset.Icc 1 5) (hj₂ : j₂ ∈ Finset.Icc 1 5)
    (hi₁ : i₁ ∈ Finset.Icc 1 5) (hi₂ : i₂ ∈ Finset.Icc 1 5)
    (hjneq : j₁ ≠ j₂) (hineq : i₁ ≠ i₂)
    (hj₁one : canonicalLowerResidual data j₁ = 1)
    (hj₂one : canonicalLowerResidual data j₂ = 1)
    (hi₁one : canonicalUpperResidual data i₁ = 1)
    (hi₂one : canonicalUpperResidual data i₂ = 1) :
    Nat.gcd ((n + j₁) * (n + j₂))
        (upperTermAfterFour n d t i₁ * upperTermAfterFour n d t i₂) =
      canonicalOwnerCell data j₁ i₁ *
        canonicalOwnerCell data j₁ i₂ *
        canonicalOwnerCell data j₂ i₁ *
        canonicalOwnerCell data j₂ i₂ := by
  have hjcop : Nat.Coprime (n + j₁) (n + j₂) := by
    rcases le_total j₁ j₂ with hle | hle
    · exact (canonicalOwner_two_fullyOwned_lower_rows_coprime_offset
        data hj₁ hj₂ hjneq hle hj₁one hj₂one).1
    · exact (canonicalOwner_two_fullyOwned_lower_rows_coprime_offset
        data hj₂ hj₁ hjneq.symm hle hj₂one hj₁one).1.symm
  have hicop : Nat.Coprime (upperTermAfterFour n d t i₁)
      (upperTermAfterFour n d t i₂) :=
    canonicalOwner_two_fullyOwned_modifiedUpper_columns_coprime
      data hi₁ hi₂ hineq hi₁one hi₂one
  rw [gcd_mul_mul_eq_four_gcds_of_coprime hjcop hicop,
    canonicalOwner_fullyOwned_gcd_modifiedUpper_eq_cell
      data hj₁ hi₁ hj₁one hi₁one,
    canonicalOwner_fullyOwned_gcd_modifiedUpper_eq_cell
      data hj₁ hi₂ hj₁one hi₂one,
    canonicalOwner_fullyOwned_gcd_modifiedUpper_eq_cell
      data hj₂ hi₁ hj₂one hi₁one,
    canonicalOwner_fullyOwned_gcd_modifiedUpper_eq_cell
      data hj₂ hi₂ hj₂one hi₂one]

/-- The square of the exact four-crossing intersection divides the product
of the four independent tangent defects.  This is the square-level gain that
is invisible in the degree-nine diagonal-window divisor alone. -/
theorem k5_crossing_product_sq_dvd_four_tangent_defects
    {n d t j₁ j₂ i₁ i₂ : ℕ}
    (data : CanonicalOwnerData 5 n d t)
    (hj₁ : j₁ ∈ Finset.Icc 1 5) (hj₂ : j₂ ∈ Finset.Icc 1 5)
    (hi₁ : i₁ ∈ Finset.Icc 1 5) (hi₂ : i₂ ∈ Finset.Icc 1 5)
    (hfour : 4 ∣ n + d + t)
    (heq : blockProduct 5 (n + d) = 4 * blockProduct 5 n) :
    ((canonicalOwnerCell data j₁ i₁ *
        canonicalOwnerCell data j₁ i₂ *
        canonicalOwnerCell data j₂ i₁ *
        canonicalOwnerCell data j₂ i₂ : ℕ) : ℤ) ^ 2 ∣
      k5OwnerSquareDefect n d j₁ i₁ *
        k5OwnerSquareDefect n d j₁ i₂ *
        k5OwnerSquareDefect n d j₂ i₁ *
        k5OwnerSquareDefect n d j₂ i₂ := by
  have h₁₁ := canonicalOwnerCell_sq_dvd_k5OwnerSquareDefect
    data hj₁ hi₁ hfour heq
  have h₁₂ := canonicalOwnerCell_sq_dvd_k5OwnerSquareDefect
    data hj₁ hi₂ hfour heq
  have h₂₁ := canonicalOwnerCell_sq_dvd_k5OwnerSquareDefect
    data hj₂ hi₁ hfour heq
  have h₂₂ := canonicalOwnerCell_sq_dvd_k5OwnerSquareDefect
    data hj₂ hi₂ hfour heq
  have hmul := Int.mul_dvd_mul (Int.mul_dvd_mul h₁₁ h₁₂)
    (Int.mul_dvd_mul h₂₁ h₂₂)
  convert hmul using 1 <;> push_cast <;> ring

/-- Quantitative square-level crossing bound.  The former diagonal estimate
paid four full factors of size `d`; tangent lifting replaces that by a square
bound of degree four in `n`, after ruling out all zero defects. -/
theorem k5_crossing_product_sq_le_tangent_height
    {n d t j₁ j₂ i₁ i₂ : ℕ}
    (data : CanonicalOwnerData 5 n d t) (hd : 5 ≤ d)
    (hj₁ : j₁ ∈ Finset.Icc 1 5) (hj₂ : j₂ ∈ Finset.Icc 1 5)
    (hi₁ : i₁ ∈ Finset.Icc 1 5) (hi₂ : i₂ ∈ Finset.Icc 1 5)
    (hfour : 4 ∣ n + d + t)
    (heq : blockProduct 5 (n + d) = 4 * blockProduct 5 n) :
    (canonicalOwnerCell data j₁ i₁ *
        canonicalOwnerCell data j₁ i₂ *
        canonicalOwnerCell data j₂ i₁ *
        canonicalOwnerCell data j₂ i₂) ^ 2 ≤ (240 * n) ^ 4 := by
  let X : ℕ := canonicalOwnerCell data j₁ i₁ *
    canonicalOwnerCell data j₁ i₂ *
    canonicalOwnerCell data j₂ i₁ *
    canonicalOwnerCell data j₂ i₂
  let F : ℤ := k5OwnerSquareDefect n d j₁ i₁ *
    k5OwnerSquareDefect n d j₁ i₂ *
    k5OwnerSquareDefect n d j₂ i₁ *
    k5OwnerSquareDefect n d j₂ i₂
  have hdivZ : (X : ℤ) ^ 2 ∣ F := by
    dsimp [X, F]
    exact k5_crossing_product_sq_dvd_four_tangent_defects
      data hj₁ hj₂ hi₁ hi₂ hfour heq
  have hdiv : X ^ 2 ∣ F.natAbs := by
    have h := Int.natAbs_dvd_natAbs.mpr hdivZ
    simpa [Int.natAbs_pow] using h
  have hFne : F ≠ 0 := by
    dsimp [F]
    exact mul_ne_zero
      (mul_ne_zero
        (mul_ne_zero
          (k5OwnerSquareDefect_ne_zero_of_solution hd hj₁ hi₁ heq)
          (k5OwnerSquareDefect_ne_zero_of_solution hd hj₁ hi₂ heq))
        (k5OwnerSquareDefect_ne_zero_of_solution hd hj₂ hi₁ heq))
      (k5OwnerSquareDefect_ne_zero_of_solution hd hj₂ hi₂ heq)
  have hpos : 0 < F.natAbs := Int.natAbs_pos.mpr hFne
  have hle : X ^ 2 ≤ F.natAbs := Nat.le_of_dvd hpos hdiv
  have hheight : F.natAbs ≤ (240 * n) ^ 4 := by
    dsimp [F]
    simp only [Int.natAbs_mul]
    calc
      (k5OwnerSquareDefect n d j₁ i₁).natAbs *
          (k5OwnerSquareDefect n d j₁ i₂).natAbs *
          (k5OwnerSquareDefect n d j₂ i₁).natAbs *
          (k5OwnerSquareDefect n d j₂ i₂).natAbs ≤
          (240 * n) * (240 * n) * (240 * n) * (240 * n) := by
        gcongr
        · exact k5OwnerSquareDefect_natAbs_le hd hj₁ hi₁ heq
        · exact k5OwnerSquareDefect_natAbs_le hd hj₁ hi₂ heq
        · exact k5OwnerSquareDefect_natAbs_le hd hj₂ hi₁ heq
        · exact k5OwnerSquareDefect_natAbs_le hd hj₂ hi₂ heq
      _ = (240 * n) ^ 4 := by ring
  exact hle.trans hheight

private lemma mul_mul_dvd_of_both_dvd_and_gcd_dvd
    {a b w x : ℕ} (ha : a ∣ w) (hb : b ∣ w)
    (hg : Nat.gcd a b ∣ x) :
    a * b ∣ w * x := by
  have hl : Nat.lcm a b ∣ w := Nat.lcm_dvd ha hb
  have hm := Nat.mul_dvd_mul hl hg
  rw [Nat.lcm_mul_gcd] at hm
  exact hm

/-- The exact intersection-corrected simultaneous divisor.  Compared with
using the two window divisibilities separately, only the four crossing
owners are paid for. -/
theorem k5_proper_global_four_terms_dvd_window_mul_crossings
    {n d t j₁ j₂ i₁ i₂ : ℕ}
    (data : CanonicalOwnerData 5 n d t) (hd : 5 ≤ d)
    (hj₁ : j₁ ∈ Finset.Icc 1 5) (hj₂ : j₂ ∈ Finset.Icc 1 5)
    (hi₁ : i₁ ∈ Finset.Icc 1 5) (hi₂ : i₂ ∈ Finset.Icc 1 5)
    (hjneq : j₁ ≠ j₂) (hineq : i₁ ≠ i₂)
    (hfour : 4 ∣ n + d + t)
    (hj₁one : canonicalLowerResidual data j₁ = 1)
    (hj₂one : canonicalLowerResidual data j₂ = 1)
    (hi₁one : canonicalUpperResidual data i₁ = 1)
    (hi₂one : canonicalUpperResidual data i₂ = 1) :
    ((n + j₁) * (n + j₂)) *
        (upperTermAfterFour n d t i₁ * upperTermAfterFour n d t i₂) ∣
      k5DiagonalWindow d *
        (canonicalOwnerCell data j₁ i₁ *
          canonicalOwnerCell data j₁ i₂ *
          canonicalOwnerCell data j₂ i₁ *
          canonicalOwnerCell data j₂ i₂) := by
  apply mul_mul_dvd_of_both_dvd_and_gcd_dvd
  · exact k5_two_fullyOwned_lower_rows_product_dvd_diagonalWindow
      data hd hj₁ hj₂ hjneq hfour hj₁one hj₂one
  · exact k5_two_fullyOwned_modifiedUpper_product_dvd_diagonalWindow
      data hd hi₁ hi₂ hineq hfour hi₁one hi₂one
  · exact k5_proper_global_row_column_gcd_dvd_crossings data
      hj₁ hj₂ hi₁ hi₂ hj₁one hj₂one hi₁one hi₂one

/-- Square-level elimination of the crossing loss.  Squaring the exact
intersection-corrected window divisor and then substituting the four tangent
congruences removes the owner cells altogether: the square of the four-term
modulus divides a completely explicit polynomial in `n,d` and the four fixed
row/column indices. -/
theorem k5_proper_global_four_terms_sq_dvd_window_sq_mul_tangent_defects
    {n d t j₁ j₂ i₁ i₂ : ℕ}
    (data : CanonicalOwnerData 5 n d t) (hd : 5 ≤ d)
    (hj₁ : j₁ ∈ Finset.Icc 1 5) (hj₂ : j₂ ∈ Finset.Icc 1 5)
    (hi₁ : i₁ ∈ Finset.Icc 1 5) (hi₂ : i₂ ∈ Finset.Icc 1 5)
    (hjneq : j₁ ≠ j₂) (hineq : i₁ ≠ i₂)
    (hfour : 4 ∣ n + d + t)
    (hj₁one : canonicalLowerResidual data j₁ = 1)
    (hj₂one : canonicalLowerResidual data j₂ = 1)
    (hi₁one : canonicalUpperResidual data i₁ = 1)
    (hi₂one : canonicalUpperResidual data i₂ = 1)
    (heq : blockProduct 5 (n + d) = 4 * blockProduct 5 n) :
    ((((n + j₁) * (n + j₂)) *
        (upperTermAfterFour n d t i₁ *
          upperTermAfterFour n d t i₂ : ℕ) : ℕ) : ℤ) ^ 2 ∣
      ((k5DiagonalWindow d : ℕ) : ℤ) ^ 2 *
        (k5OwnerSquareDefect n d j₁ i₁ *
          k5OwnerSquareDefect n d j₁ i₂ *
          k5OwnerSquareDefect n d j₂ i₁ *
          k5OwnerSquareDefect n d j₂ i₂) := by
  let T : ℕ := ((n + j₁) * (n + j₂)) *
    (upperTermAfterFour n d t i₁ * upperTermAfterFour n d t i₂)
  let W : ℕ := k5DiagonalWindow d
  let X : ℕ := canonicalOwnerCell data j₁ i₁ *
    canonicalOwnerCell data j₁ i₂ *
    canonicalOwnerCell data j₂ i₁ *
    canonicalOwnerCell data j₂ i₂
  let F : ℤ := k5OwnerSquareDefect n d j₁ i₁ *
    k5OwnerSquareDefect n d j₁ i₂ *
    k5OwnerSquareDefect n d j₂ i₁ *
    k5OwnerSquareDefect n d j₂ i₂
  have hnat : T ∣ W * X := by
    dsimp [T, W, X]
    exact k5_proper_global_four_terms_dvd_window_mul_crossings
      data hd hj₁ hj₂ hi₁ hi₂ hjneq hineq hfour
        hj₁one hj₂one hi₁one hi₂one
  have hint : (T : ℤ) ∣ ((W * X : ℕ) : ℤ) := by
    exact_mod_cast hnat
  have hsquare := pow_dvd_pow_of_dvd hint 2
  have hsquare' : (T : ℤ) ^ 2 ∣ (W : ℤ) ^ 2 * (X : ℤ) ^ 2 := by
    convert hsquare using 1 <;> push_cast <;> ring
  have hx : (X : ℤ) ^ 2 ∣ F := by
    dsimp [X, F]
    exact k5_crossing_product_sq_dvd_four_tangent_defects
      data hj₁ hj₂ hi₁ hi₂ hfour heq
  have hreplace : (W : ℤ) ^ 2 * (X : ℤ) ^ 2 ∣ (W : ℤ) ^ 2 * F :=
    mul_dvd_mul_left ((W : ℤ) ^ 2) hx
  dsimp [T, W, F] at *
  exact hsquare'.trans hreplace

/-- Strict quantitative improvement over the degree-thirteen crossing-loss
bound: the exact tangent square replaces four diagonal-size crossing factors
by only `(240*n)^2`. -/
theorem k5_proper_global_four_terms_le_window_mul_tangent_height
    {n d t j₁ j₂ i₁ i₂ : ℕ}
    (data : CanonicalOwnerData 5 n d t) (hd : 5 ≤ d)
    (hj₁ : j₁ ∈ Finset.Icc 1 5) (hj₂ : j₂ ∈ Finset.Icc 1 5)
    (hi₁ : i₁ ∈ Finset.Icc 1 5) (hi₂ : i₂ ∈ Finset.Icc 1 5)
    (hjneq : j₁ ≠ j₂) (hineq : i₁ ≠ i₂)
    (hfour : 4 ∣ n + d + t)
    (hj₁one : canonicalLowerResidual data j₁ = 1)
    (hj₂one : canonicalLowerResidual data j₂ = 1)
    (hi₁one : canonicalUpperResidual data i₁ = 1)
    (hi₂one : canonicalUpperResidual data i₂ = 1)
    (heq : blockProduct 5 (n + d) = 4 * blockProduct 5 n) :
    ((n + j₁) * (n + j₂)) *
        (upperTermAfterFour n d t i₁ * upperTermAfterFour n d t i₂) ≤
      k5DiagonalWindow d * (240 * n) ^ 2 := by
  let T : ℕ := ((n + j₁) * (n + j₂)) *
    (upperTermAfterFour n d t i₁ * upperTermAfterFour n d t i₂)
  let W : ℕ := k5DiagonalWindow d
  let X : ℕ := canonicalOwnerCell data j₁ i₁ *
    canonicalOwnerCell data j₁ i₂ *
    canonicalOwnerCell data j₂ i₁ *
    canonicalOwnerCell data j₂ i₂
  have hdvd : T ∣ W * X := by
    dsimp [T, W, X]
    exact k5_proper_global_four_terms_dvd_window_mul_crossings
      data hd hj₁ hj₂ hi₁ hi₂ hjneq hineq hfour
        hj₁one hj₂one hi₁one hi₂one
  have hWpos : 0 < W := by dsimp [W]; exact k5DiagonalWindow_pos hd
  have hXpos : 0 < X := by
    dsimp [X]
    have h₁₁ := canonicalOwnerCell_pos data (j := j₁) (i := i₁)
    have h₁₂ := canonicalOwnerCell_pos data (j := j₁) (i := i₂)
    have h₂₁ := canonicalOwnerCell_pos data (j := j₂) (i := i₁)
    have h₂₂ := canonicalOwnerCell_pos data (j := j₂) (i := i₂)
    positivity
  have hT : T ≤ W * X := Nat.le_of_dvd (Nat.mul_pos hWpos hXpos) hdvd
  have hXsq : X ^ 2 ≤ (240 * n) ^ 4 := by
    dsimp [X]
    exact k5_crossing_product_sq_le_tangent_height
      data hd hj₁ hj₂ hi₁ hi₂ hfour heq
  have hXsq' : X ^ 2 ≤ ((240 * n) ^ 2) ^ 2 := by
    calc
      X ^ 2 ≤ (240 * n) ^ 4 := hXsq
      _ = ((240 * n) ^ 2) ^ 2 := by ring
  have hX : X ≤ (240 * n) ^ 2 :=
    (Nat.pow_le_pow_iff_left (by norm_num : (2 : ℕ) ≠ 0)).mp hXsq'
  dsimp [T, W] at *
  exact hT.trans (Nat.mul_le_mul_left _ hX)

private lemma canonicalOwnerCell_le_d_add_four
    {n d t j i : ℕ} (data : CanonicalOwnerData 5 n d t)
    (hd : 5 ≤ d) (hj : j ∈ Finset.Icc 1 5) (hi : i ∈ Finset.Icc 1 5)
    (hfour : 4 ∣ n + d + t) :
    canonicalOwnerCell data j i ≤ d + 4 := by
  have hshiftpos : 0 < d + i - j := by
    have hi1 := (Finset.mem_Icc.mp hi).1
    have hj5 := (Finset.mem_Icc.mp hj).2
    omega
  have hle := Nat.le_of_dvd hshiftpos
    (canonicalOwnerCell_dvd_shiftedDifference data hd hj hi hfour)
  have hshiftle : d + i - j ≤ d + 4 := by
    have hi5 := (Finset.mem_Icc.mp hi).2
    have hj1 := (Finset.mem_Icc.mp hj).1
    omega
  exact hle.trans hshiftle

/-- Size form of the intersection-corrected divisor.  The four-term product
has degree four in the consecutive terms but is bounded by only thirteen
diagonal factors: nine from the common window and four from its exact
row-column intersection. -/
theorem k5_proper_global_four_terms_le_pow_thirteen
    {n d t j₁ j₂ i₁ i₂ : ℕ}
    (data : CanonicalOwnerData 5 n d t) (hd : 5 ≤ d)
    (hj₁ : j₁ ∈ Finset.Icc 1 5) (hj₂ : j₂ ∈ Finset.Icc 1 5)
    (hi₁ : i₁ ∈ Finset.Icc 1 5) (hi₂ : i₂ ∈ Finset.Icc 1 5)
    (hjneq : j₁ ≠ j₂) (hineq : i₁ ≠ i₂)
    (hfour : 4 ∣ n + d + t)
    (hj₁one : canonicalLowerResidual data j₁ = 1)
    (hj₂one : canonicalLowerResidual data j₂ = 1)
    (hi₁one : canonicalUpperResidual data i₁ = 1)
    (hi₂one : canonicalUpperResidual data i₂ = 1) :
    ((n + j₁) * (n + j₂)) *
        (upperTermAfterFour n d t i₁ * upperTermAfterFour n d t i₂) ≤
      (d + 4) ^ 13 := by
  have hdvd := k5_proper_global_four_terms_dvd_window_mul_crossings
    data hd hj₁ hj₂ hi₁ hi₂ hjneq hineq hfour
      hj₁one hj₂one hi₁one hi₂one
  have hwindowpos := k5DiagonalWindow_pos hd
  have hcellpos₁₁ := canonicalOwnerCell_pos data (j := j₁) (i := i₁)
  have hcellpos₁₂ := canonicalOwnerCell_pos data (j := j₁) (i := i₂)
  have hcellpos₂₁ := canonicalOwnerCell_pos data (j := j₂) (i := i₁)
  have hcellpos₂₂ := canonicalOwnerCell_pos data (j := j₂) (i := i₂)
  have hpos : 0 < k5DiagonalWindow d *
      (canonicalOwnerCell data j₁ i₁ *
        canonicalOwnerCell data j₁ i₂ *
        canonicalOwnerCell data j₂ i₁ *
        canonicalOwnerCell data j₂ i₂) := by positivity
  have hle := Nat.le_of_dvd hpos hdvd
  calc
    ((n + j₁) * (n + j₂)) *
        (upperTermAfterFour n d t i₁ * upperTermAfterFour n d t i₂)
        ≤ k5DiagonalWindow d *
          (canonicalOwnerCell data j₁ i₁ *
            canonicalOwnerCell data j₁ i₂ *
            canonicalOwnerCell data j₂ i₁ *
            canonicalOwnerCell data j₂ i₂) := hle
    _ ≤ (d + 4) ^ 9 *
          ((d + 4) * (d + 4) * (d + 4) * (d + 4)) := by
      gcongr
      · exact k5DiagonalWindow_le_pow
      · exact canonicalOwnerCell_le_d_add_four data hd hj₁ hi₁ hfour
      · exact canonicalOwnerCell_le_d_add_four data hd hj₁ hi₂ hfour
      · exact canonicalOwnerCell_le_d_add_four data hd hj₂ hi₁ hfour
      · exact canonicalOwnerCell_le_d_add_four data hd hj₂ hi₂ hfour
    _ = (d + 4) ^ 13 := by ring

/-- Equation-facing proper-global package.  A hypothetical `k=5` tail
solution supplies two rows and two columns for which the common part is
*exactly* the four nontrivial crossing owners; after correcting for precisely
that intersection, all four consecutive-term moduli divide one degree-nine
diagonal window. -/
theorem k5_tail_proper_global_intersection_corrected_window
    {n d t : ℕ} (data : CanonicalOwnerData 5 n d t)
    (ht : t ∈ Finset.Icc 1 5)
    (hfour : 4 ∣ n + d + t)
    (hblocks : upperBlockAfterFour 5 n d t = blockProduct 5 n)
    (htail : 10 ^ 1000 ≤ d)
    (heq : blockProduct 5 (n + d) = 4 * blockProduct 5 n)
    (hGne : canonicalOwnerResidual data ≠ 24) :
    ∃ j₁, j₁ ∈ Finset.Icc 1 5 ∧
      ∃ j₂, j₂ ∈ Finset.Icc 1 5 ∧ j₁ ≠ j₂ ∧
      ∃ i₁, i₁ ∈ Finset.Icc 1 5 ∧
      ∃ i₂, i₂ ∈ Finset.Icc 1 5 ∧ i₁ ≠ i₂ ∧
        canonicalLowerResidual data j₁ = 1 ∧
        canonicalLowerResidual data j₂ = 1 ∧
        canonicalUpperResidual data i₁ = 1 ∧
        canonicalUpperResidual data i₂ = 1 ∧
        1 < canonicalOwnerCell data j₁ i₁ ∧
        1 < canonicalOwnerCell data j₁ i₂ ∧
        1 < canonicalOwnerCell data j₂ i₁ ∧
        1 < canonicalOwnerCell data j₂ i₂ ∧
        Nat.gcd ((n + j₁) * (n + j₂))
            (upperTermAfterFour n d t i₁ * upperTermAfterFour n d t i₂) =
          canonicalOwnerCell data j₁ i₁ *
            canonicalOwnerCell data j₁ i₂ *
            canonicalOwnerCell data j₂ i₁ *
            canonicalOwnerCell data j₂ i₂ ∧
        ((n + j₁) * (n + j₂)) *
            (upperTermAfterFour n d t i₁ * upperTermAfterFour n d t i₂) ∣
          k5DiagonalWindow d *
            (canonicalOwnerCell data j₁ i₁ *
              canonicalOwnerCell data j₁ i₂ *
              canonicalOwnerCell data j₂ i₁ *
              canonicalOwnerCell data j₂ i₂) ∧
        ((n + j₁) * (n + j₂)) *
            (upperTermAfterFour n d t i₁ * upperTermAfterFour n d t i₂) ≤
          (d + 4) ^ 13 := by
  have hfive : 5 ≤ 10 ^ 1000 := by
    rw [show 1000 = 999 + 1 by omega, pow_succ]
    have hp : 0 < 10 ^ 999 := pow_pos (by norm_num) _
    calc
      5 ≤ 1 * 10 := by norm_num
      _ ≤ 10 ^ 999 * 10 := Nat.mul_le_mul_right 10 hp
  have hd : 5 ≤ d := hfive.trans htail
  obtain ⟨j₁, hj₁, j₂, hj₂, hjlt, hj₁one, hj₂one, -⟩ :=
    k5_proper_global_two_coprime_lower_adjacent_equations data hGne
  obtain ⟨i₁, hi₁, i₂, hi₂, hineq, hi₁one, hi₂one⟩ :=
    exists_two_k5_unit_upper_residuals_of_global_ne_twenty_four
      data ht hfour hblocks hGne
  have hcells := (k5_tail_complete_support_unit_cross
    data ht hfour hblocks htail heq).1
  have hgcd := k5_proper_global_row_column_gcd_eq_crossings data
    hj₁ hj₂ hi₁ hi₂ hjlt.ne hineq.symm
      hj₁one hj₂one hi₁one hi₂one
  have hdvd := k5_proper_global_four_terms_dvd_window_mul_crossings data hd
    hj₁ hj₂ hi₁ hi₂ hjlt.ne hineq.symm hfour
      hj₁one hj₂one hi₁one hi₂one
  have hle := k5_proper_global_four_terms_le_pow_thirteen data hd
    hj₁ hj₂ hi₁ hi₂ hjlt.ne hineq.symm hfour
      hj₁one hj₂one hi₁one hi₂one
  exact ⟨j₁, hj₁, j₂, hj₂, hjlt.ne, i₁, hi₁, i₂, hi₂, hineq.symm,
    hj₁one, hj₂one, hi₁one, hi₂one,
    hcells j₁ hj₁ i₁ hi₁, hcells j₁ hj₁ i₂ hi₂,
    hcells j₂ hj₂ i₁ hi₁, hcells j₂ hj₂ i₂ hi₂,
    hgcd, hdvd, hle⟩

#print axioms k5_proper_global_row_column_gcd_dvd_crossings
#print axioms k5_proper_global_row_column_gcd_eq_crossings
#print axioms canonicalOwnerCell_sq_dvd_k5OwnerSquareDefect
#print axioms k5OwnerSquareDefect_ne_zero_of_solution
#print axioms k5OwnerSquareDefect_natAbs_le
#print axioms k5_crossing_product_sq_dvd_four_tangent_defects
#print axioms k5_crossing_product_sq_le_tangent_height
#print axioms k5_proper_global_four_terms_dvd_window_mul_crossings
#print axioms k5_proper_global_four_terms_sq_dvd_window_sq_mul_tangent_defects
#print axioms k5_proper_global_four_terms_le_window_mul_tangent_height
#print axioms k5_proper_global_four_terms_le_pow_thirteen
#print axioms k5_tail_proper_global_intersection_corrected_window

end Erdos686Variant
end Erdos686
