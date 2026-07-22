/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import ErdosProblems.Erdos686.K5.GenusTwoReduction
import ErdosProblems.Erdos686.Core.CFTailBand
import ErdosProblems.Erdos686.Core.SmallCore

/-!
# Erdős 686, k=5: integral lift and the finite-height exclusion

For an integral centered solution `P₅(v)=4P₅(u)`, this module banks the
weighted-projective lift

`(A:B:C) = (v : 10v³-40u³-16v+64u : 2u)`

to the reduced genus-two curve.  It also proves the exact window
`u < v < 2u`, the cubic height bound, and a stronger version of the requested
finite exclusion: there is no admissible solution with `u < 10^1000`.
-/

namespace Erdos686
namespace Erdos686Variant

/-- The centered quintic over the integers. -/
def k5PolynomialZ (z : ℤ) : ℤ :=
  z ^ 5 - 5 * z ^ 3 + 4 * z

/-- The reduced genus-two sextic used by Magma. -/
def k5ReducedGenusTwoRhs (x : ℚ) : ℚ :=
  36 * x ^ 6 + 128 * x ^ 5 - 100 * x ^ 3 + 8 * x + 9

/-- Affine rational points on the reduced genus-two model. -/
def K5ReducedGenusTwoPoint (x z : ℚ) : Prop :=
  z ^ 2 = k5ReducedGenusTwoRhs x

/-- The integral weighted-projective `B` coordinate. -/
def k5IntegralLiftB (u v : ℤ) : ℤ :=
  10 * v ^ 3 - 40 * u ^ 3 - 16 * v + 64 * u

/-- The reduced affine `X` coordinate of the integral lift. -/
def k5IntegralLiftX (u v : ℕ) : ℚ :=
  (v : ℚ) / (2 * (u : ℚ))

/-- The reduced affine `Z` coordinate of the integral lift. -/
def k5IntegralLiftZ (u v : ℕ) : ℚ :=
  (k5IntegralLiftB (u : ℤ) (v : ℤ) : ℚ) / (2 * (u : ℚ)) ^ 3

lemma k5_centered_eq_iff_integer_polynomial {u v : ℕ} :
    K5CenteredEq v u ↔
      k5PolynomialZ (v : ℤ) = 4 * k5PolynomialZ (u : ℤ) := by
  unfold K5CenteredEq k5PolynomialZ
  constructor <;> intro h
  · have hz :
        (v : ℤ) ^ 5 + 4 * (v : ℤ) + 20 * (u : ℤ) ^ 3 =
          4 * (u : ℤ) ^ 5 + 16 * (u : ℤ) + 5 * (v : ℤ) ^ 3 := by
      exact_mod_cast h
    linarith
  · have hz :
        (v : ℤ) ^ 5 + 4 * (v : ℤ) + 20 * (u : ℤ) ^ 3 =
          4 * (u : ℤ) ^ 5 + 16 * (u : ℤ) + 5 * (v : ℤ) ^ 3 := by
      linarith
    exact_mod_cast hz

/-- Exact weighted-projective equation for the integral lift. -/
theorem k5_integral_lift_weighted_equation
    {u v : ℕ} (hsol : K5CenteredEq v u) :
    k5IntegralLiftB (u : ℤ) (v : ℤ) ^ 2 =
      36 * (v : ℤ) ^ 6 +
        128 * (v : ℤ) ^ 5 * (2 * (u : ℤ)) -
        100 * (v : ℤ) ^ 3 * (2 * (u : ℤ)) ^ 3 +
        8 * (v : ℤ) * (2 * (u : ℤ)) ^ 5 +
        9 * (2 * (u : ℤ)) ^ 6 := by
  have hpoly := k5_centered_eq_iff_integer_polynomial.mp hsol
  have hid :
      k5IntegralLiftB (u : ℤ) (v : ℤ) ^ 2 -
          (36 * (v : ℤ) ^ 6 +
            128 * (v : ℤ) ^ 5 * (2 * (u : ℤ)) -
            100 * (v : ℤ) ^ 3 * (2 * (u : ℤ)) ^ 3 +
            8 * (v : ℤ) * (2 * (u : ℤ)) ^ 5 +
            9 * (2 * (u : ℤ)) ^ 6) =
        -64 * (4 * (u : ℤ) - (v : ℤ)) *
          (k5PolynomialZ (v : ℤ) - 4 * k5PolynomialZ (u : ℤ)) := by
    simp only [k5IntegralLiftB, k5PolynomialZ]
    ring
  have hzero :
      k5PolynomialZ (v : ℤ) - 4 * k5PolynomialZ (u : ℤ) = 0 :=
    sub_eq_zero.mpr hpoly
  rw [hzero, mul_zero] at hid
  linarith

/-- The displayed affine coordinates are exactly `X=A/C` and `Z=B/C³`. -/
theorem k5_integral_lift_affine_coordinates (u v : ℕ) :
    k5IntegralLiftX u v = (v : ℚ) / (2 * (u : ℚ)) ∧
      k5IntegralLiftZ u v =
        (k5IntegralLiftB (u : ℤ) (v : ℤ) : ℚ) /
          (2 * (u : ℚ)) ^ 3 := by
  exact ⟨rfl, rfl⟩

/-- Every positive integral centered solution lies on the reduced genus-two
model under the weighted-projective lift. -/
theorem k5_integral_lift_to_reduced_genusTwo
    {u v : ℕ} (hu : 0 < u) (hsol : K5CenteredEq v u) :
    K5ReducedGenusTwoPoint (k5IntegralLiftX u v) (k5IntegralLiftZ u v) := by
  have hweighted := k5_integral_lift_weighted_equation hsol
  have huq : (u : ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt hu)
  unfold K5ReducedGenusTwoPoint k5IntegralLiftX k5IntegralLiftZ
    k5ReducedGenusTwoRhs
  rw [div_pow]
  have hweightedQ :
      (k5IntegralLiftB (u : ℤ) (v : ℤ) : ℚ) ^ 2 =
        36 * (v : ℚ) ^ 6 +
          128 * (v : ℚ) ^ 5 * (2 * (u : ℚ)) -
          100 * (v : ℚ) ^ 3 * (2 * (u : ℚ)) ^ 3 +
          8 * (v : ℚ) * (2 * (u : ℚ)) ^ 5 +
          9 * (2 * (u : ℚ)) ^ 6 := by
    exact_mod_cast hweighted
  field_simp [huq]
  ring_nf at hweightedQ ⊢
  exact hweightedQ

lemma k5PolynomialZ_succ_sub (z : ℤ) :
    k5PolynomialZ (z + 1) - k5PolynomialZ z =
      5 * z * (z - 1) * (z + 1) * (z + 2) := by
  simp only [k5PolynomialZ]
  ring

lemma k5PolynomialZ_nat_succ_lt {n : ℕ} (hn : 3 ≤ n) :
    k5PolynomialZ (n : ℤ) < k5PolynomialZ ((n + 1 : ℕ) : ℤ) := by
  have hnz : (3 : ℤ) ≤ (n : ℤ) := by exact_mod_cast hn
  have hdiff := k5PolynomialZ_succ_sub (n : ℤ)
  have hn0 : (0 : ℤ) < (n : ℤ) := by omega
  have hn1 : (0 : ℤ) < (n : ℤ) - 1 := by omega
  have hnp1 : (0 : ℤ) < (n : ℤ) + 1 := by omega
  have hnp2 : (0 : ℤ) < (n : ℤ) + 2 := by omega
  have hpos :
      0 < 5 * (n : ℤ) * ((n : ℤ) - 1) *
        ((n : ℤ) + 1) * ((n : ℤ) + 2) := by positivity
  rw [← sub_pos]
  push_cast
  rw [hdiff]
  exact hpos

/-- `P₅` is strictly increasing on natural inputs at least three. -/
theorem k5PolynomialZ_strictMono_from_three
    {u v : ℕ} (hu : 3 ≤ u) (hv : 3 ≤ v) (huv : u < v) :
    k5PolynomialZ (u : ℤ) < k5PolynomialZ (v : ℤ) := by
  let f : ℕ → ℤ := fun n => k5PolynomialZ ((n : ℤ) + 3)
  have hf : StrictMono f := strictMono_nat_of_lt_succ fun n => by
    dsimp [f]
    have hstep := k5PolynomialZ_nat_succ_lt (n := n + 3) (by omega)
    push_cast at hstep
    exact hstep
  have hsub : u - 3 < v - 3 := by omega
  have h := hf hsub
  dsimp [f] at h
  have huEq : ((u - 3 : ℕ) : ℤ) + 3 = (u : ℤ) := by
    exact_mod_cast Nat.sub_add_cancel hu
  have hvEq : ((v - 3 : ℕ) : ℤ) + 3 = (v : ℤ) := by
    exact_mod_cast Nat.sub_add_cancel hv
  rw [huEq, hvEq] at h
  exact h

lemma k5PolynomialZ_pos_from_three {u : ℕ} (hu : 3 ≤ u) :
    0 < k5PolynomialZ (u : ℤ) := by
  have huz : (3 : ℤ) ≤ (u : ℤ) := by exact_mod_cast hu
  have hid :
      k5PolynomialZ (u : ℤ) =
        (u : ℤ) * ((u : ℤ) - 1) * ((u : ℤ) + 1) *
          ((u : ℤ) - 2) * ((u : ℤ) + 2) := by
    simp only [k5PolynomialZ]
    ring
  rw [hid]
  have hu0 : (0 : ℤ) < (u : ℤ) := by omega
  have hu1 : (0 : ℤ) < (u : ℤ) - 1 := by omega
  have hu2 : (0 : ℤ) < (u : ℤ) - 2 := by omega
  have hup1 : (0 : ℤ) < (u : ℤ) + 1 := by omega
  have hup2 : (0 : ℤ) < (u : ℤ) + 2 := by omega
  positivity

/-- A positive centered solution has `u < v`. -/
theorem k5_integral_solution_lower_window
    {u v : ℕ} (hu : 3 ≤ u) (hsol : K5CenteredEq v u) :
    u < v := by
  have hpoly := k5_centered_eq_iff_integer_polynomial.mp hsol
  have hupos := k5PolynomialZ_pos_from_three hu
  have hvpos : 0 < k5PolynomialZ (v : ℤ) := by nlinarith
  have hv : 3 ≤ v := by
    by_contra h
    have : v ≤ 2 := by omega
    interval_cases v <;> norm_num [k5PolynomialZ] at hvpos
  by_contra hnot
  have hvu : v ≤ u := Nat.le_of_not_gt hnot
  rcases eq_or_lt_of_le hvu with rfl | hvu'
  · nlinarith
  · have hmono := k5PolynomialZ_strictMono_from_three hv hu hvu'
    nlinarith

/-- Exact value of `P₅(2u)-4P₅(u)`. -/
theorem k5PolynomialZ_two_mul_sub_four (u : ℕ) :
    k5PolynomialZ (2 * (u : ℤ)) - 4 * k5PolynomialZ (u : ℤ) =
      4 * (u : ℤ) * (7 * (u : ℤ) ^ 4 - 5 * (u : ℤ) ^ 2 - 2) := by
  simp only [k5PolynomialZ]
  ring

lemma k5PolynomialZ_two_mul_gt_four {u : ℕ} (hu : 3 ≤ u) :
    4 * k5PolynomialZ (u : ℤ) < k5PolynomialZ (2 * (u : ℤ)) := by
  have huz : (3 : ℤ) ≤ (u : ℤ) := by exact_mod_cast hu
  have hid := k5PolynomialZ_two_mul_sub_four u
  have hfactor :
      0 < 4 * (u : ℤ) *
        (7 * (u : ℤ) ^ 4 - 5 * (u : ℤ) ^ 2 - 2) := by
    have hsq : 1 < (u : ℤ) ^ 2 := by nlinarith
    have hfac :
        7 * (u : ℤ) ^ 4 - 5 * (u : ℤ) ^ 2 - 2 =
          ((u : ℤ) ^ 2 - 1) * (7 * (u : ℤ) ^ 2 + 2) := by ring
    rw [hfac]
    have hu0 : (0 : ℤ) < (u : ℤ) := by omega
    have hleft : (0 : ℤ) < (u : ℤ) ^ 2 - 1 := by omega
    have hright : (0 : ℤ) < 7 * (u : ℤ) ^ 2 + 2 := by nlinarith
    positivity
  linarith

/-- Every positive centered solution satisfies the exact coarse window
`u < v < 2u`. -/
theorem k5_integral_solution_window
    {u v : ℕ} (hu : 3 ≤ u) (hsol : K5CenteredEq v u) :
    u < v ∧ v < 2 * u := by
  have huv := k5_integral_solution_lower_window hu hsol
  refine ⟨huv, ?_⟩
  have hpoly := k5_centered_eq_iff_integer_polynomial.mp hsol
  have htwo := k5PolynomialZ_two_mul_gt_four hu
  by_contra hnot
  have hv : 2 * u ≤ v := Nat.le_of_not_gt hnot
  have hmono :
      k5PolynomialZ ((2 * u : ℕ) : ℤ) ≤ k5PolynomialZ (v : ℤ) := by
    rcases eq_or_lt_of_le hv with rfl | hv'
    · exact le_rfl
    · exact (k5PolynomialZ_strictMono_from_three (by omega) (by omega) hv').le
  push_cast at hmono
  nlinarith

/-- Exact cubic bound for the weighted-projective `B` coordinate. -/
theorem k5_integral_lift_B_abs_lt
    {u v : ℕ} (hu : 3 ≤ u) (hsol : K5CenteredEq v u) :
    |k5IntegralLiftB (u : ℤ) (v : ℤ)| < 46 * (u : ℤ) ^ 3 := by
  obtain ⟨huv, hv2u⟩ := k5_integral_solution_window hu hsol
  have huz : (3 : ℤ) ≤ (u : ℤ) := by exact_mod_cast hu
  have huvz : (u : ℤ) < (v : ℤ) := by exact_mod_cast huv
  have hv2uz : (v : ℤ) < 2 * (u : ℤ) := by exact_mod_cast hv2u
  have hv0 : (0 : ℤ) ≤ (v : ℤ) := Int.natCast_nonneg v
  have hvCube :
      (v : ℤ) ^ 3 < (2 * (u : ℤ)) ^ 3 :=
    pow_lt_pow_left₀ hv2uz hv0 (by norm_num)
  have huCube :
      (u : ℤ) ^ 3 < (v : ℤ) ^ 3 :=
    pow_lt_pow_left₀ huvz (by positivity) (by norm_num)
  have huCubic : 9 * (u : ℤ) ≤ (u : ℤ) ^ 3 := by
    nlinarith [sq_nonneg ((u : ℤ) - 3)]
  have hupper :
      k5IntegralLiftB (u : ℤ) (v : ℤ) < 46 * (u : ℤ) ^ 3 := by
    simp only [k5IntegralLiftB]
    nlinarith [sq_nonneg ((u : ℤ) - 3)]
  have hlower :
      -(46 * (u : ℤ) ^ 3) <
        k5IntegralLiftB (u : ℤ) (v : ℤ) := by
    simp only [k5IntegralLiftB]
    nlinarith
  exact (abs_lt).2 ⟨hlower, hupper⟩

/-- Cubed form of `H(P)<4u`; this avoids introducing real cube roots.
Primitive weighted-projective reduction can only decrease these coordinates. -/
theorem k5_integral_lift_height_cube_lt
    {u v : ℕ} (hu : 3 ≤ u) (hsol : K5CenteredEq v u) :
    max (v ^ 3)
      (max ((2 * u) ^ 3) (k5IntegralLiftB (u : ℤ) (v : ℤ)).natAbs) <
        (4 * u) ^ 3 := by
  obtain ⟨_, hv2u⟩ := k5_integral_solution_window hu hsol
  have hB := k5_integral_lift_B_abs_lt hu hsol
  have hBnat :
      (k5IntegralLiftB (u : ℤ) (v : ℤ)).natAbs < 46 * u ^ 3 := by
    have hz :
        ((k5IntegralLiftB (u : ℤ) (v : ℤ)).natAbs : ℤ) <
          (46 * u ^ 3 : ℕ) := by
      rw [Int.natCast_natAbs]
      exact hB
    exact_mod_cast hz
  have hv : v ^ 3 < (4 * u) ^ 3 := by
    exact Nat.pow_lt_pow_left (by omega) (by norm_num)
  have hC : (2 * u) ^ 3 < (4 * u) ^ 3 := by
    exact Nat.pow_lt_pow_left (by omega) (by norm_num)
  have h46 : 46 * u ^ 3 < (4 * u) ^ 3 := by
    have hu3 : 0 < u ^ 3 := pow_pos (by omega) 3
    nlinarith
  simp only [max_lt_iff]
  exact ⟨hv, hC, lt_trans hBnat h46⟩

private lemma blockProduct_five_centered_public (m : ℕ) :
    blockProduct 5 m + 5 * (m + 3) ^ 3 = (m + 3) ^ 5 + 4 * (m + 3) := by
  norm_num [blockProduct, Finset.prod_Icc_succ_top, Finset.Icc_self,
    Finset.prod_singleton]
  ring

/-- A centered integral solution is exactly the original five-factor block
equation after undoing the shift by three. -/
theorem k5_blockProduct_eq_of_centered
    {u v : ℕ} (hu : 3 ≤ u) (huv : u ≤ v) (hsol : K5CenteredEq v u) :
    blockProduct 5 (v - 3) = 4 * blockProduct 5 (u - 3) := by
  have hv : 3 ≤ v := by omega
  have huShift : u - 3 + 3 = u := Nat.sub_add_cancel hu
  have hvShift : v - 3 + 3 = v := Nat.sub_add_cancel hv
  have h1 := blockProduct_five_centered_public (v - 3)
  have h2 := blockProduct_five_centered_public (u - 3)
  rw [huShift] at h2
  rw [hvShift] at h1
  unfold K5CenteredEq at hsol
  linarith

/-- No admissible centered solution occurs below the already certified
`10^1000` Farey boundary. -/
theorem no_k5_admissible_centered_solution_below_e1000
    {u v : ℕ} (hu : 3 ≤ u) (hgap : 5 ≤ v - u)
    (huBound : u < 10 ^ 1000) :
    ¬ K5CenteredEq v u := by
  intro hsol
  obtain ⟨huv, hv2u⟩ := k5_integral_solution_window hu hsol
  let n := u - 3
  let d := v - u
  have hdu : d < u := by
    dsimp [d]
    omega
  have hkd : 5 ≤ d := by simpa [d] using hgap
  have heq0 := k5_blockProduct_eq_of_centered hu huv.le hsol
  have hnd : n + d = v - 3 := by
    dsimp [n, d]
    omega
  have hn : n = u - 3 := rfl
  have heq : blockProduct 5 (n + d) = 4 * blockProduct 5 n := by
    rw [hnd, hn]
    exact heq0
  rcases Nat.lt_or_ge d 221 with hdSmall | hdLarge
  · obtain ⟨hup, hlo⟩ := ratio_window_four_nat heq
    have hescape := row_full_escape_small_k_d_le_220
      (k := 5) (n := n) (d := d) (by norm_num) (by norm_num)
      hkd (by omega) hup hlo
    obtain ⟨j, hj, hnot⟩ := hescape
    exact hnot (individual_divisor_skeleton_four hkd hj heq)
  · exact no_gap_solution_four_five_below_e1000 hdLarge
      (lt_trans hdu huBound) heq

/-- Requested finite-height corollary. -/
theorem no_k5_admissible_centered_solution_u_le_5000
    {u v : ℕ} (hu : 3 ≤ u) (hgap : 5 ≤ v - u) (hu5000 : u ≤ 5000) :
    ¬ K5CenteredEq v u := by
  apply no_k5_admissible_centered_solution_below_e1000 hu hgap
  have hbound : (5000 : ℕ) < 10 ^ 4 := by norm_num
  have hp : (10 : ℕ) ^ 4 ≤ 10 ^ 1000 :=
    Nat.pow_le_pow_right (by norm_num) (by norm_num)
  exact lt_of_le_of_lt hu5000 (lt_of_lt_of_le hbound hp)

#print axioms k5_integral_lift_weighted_equation
#print axioms k5_integral_lift_to_reduced_genusTwo
#print axioms k5PolynomialZ_strictMono_from_three
#print axioms k5_integral_solution_window
#print axioms k5_integral_lift_B_abs_lt
#print axioms k5_integral_lift_height_cube_lt
#print axioms no_k5_admissible_centered_solution_below_e1000
#print axioms no_k5_admissible_centered_solution_u_le_5000

end Erdos686Variant
end Erdos686
