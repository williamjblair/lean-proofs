/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import ErdosProblems.Erdos686K5G12AntidiagonalUnitaryOverlap
import ErdosProblems.Erdos686K5IntegralLift

/-!
# Erdős 686, k=5: the nonlinear centered-sum resultant in the G=12 branch

For centered variables `u=n+3`, `v=n+d+3`, put `S=u+v`.  The exact
complement equation identifies `S-1` with `P^2 Q K`.  Reducing the centered
quintic equation modulo `S-1` gives the nonzero gap resultant

`5 (d-3)^2 (d-1) (d+1) (d+3)`.

In the `G=12` profile the four forced anti-diagonal owners occupy precisely
those four gap factors.  Cancelling them gives an exact divisibility for the
remaining complement quotient `J=K/(A*B)`.  This is a degree-five nonlinear
equation consequence, not the profile-free degree-nine window identity.
-/

namespace Erdos686
namespace Erdos686Variant

/-- The centered quintic difference after clearing the powers of two in
`v=(S+d)/2` and `u=(S-d)/2`. -/
def k5CenteredSumDifference (S d : ℤ) : ℤ :=
  (S + d) ^ 5 - 20 * (S + d) ^ 3 + 64 * (S + d) -
    4 * ((S - d) ^ 5 - 20 * (S - d) ^ 3 + 64 * (S - d))

/-- Quotient in the division of the cleared centered equation by `S-1`. -/
def k5CenteredSumCofactor (S d : ℤ) : ℤ :=
  -3 * S ^ 4 + (25 * d - 3) * S ^ 3 +
    (-30 * d ^ 2 + 25 * d + 57) * S ^ 2 +
    (50 * d ^ 3 - 30 * d ^ 2 - 275 * d + 57) * S -
    15 * d ^ 4 + 50 * d ^ 3 + 150 * d ^ 2 - 275 * d - 135

/-- Nonzero remainder at `S=1`. -/
def k5CenteredGapResultant (d : ℤ) : ℤ :=
  5 * (d - 3) ^ 2 * (d - 1) * (d + 1) * (d + 3)

/-- Exact polynomial division of the centered quintic difference by `S-1`. -/
theorem k5_centered_sum_polynomial_division (S d : ℤ) :
    k5CenteredSumDifference S d =
      (S - 1) * k5CenteredSumCofactor S d + k5CenteredGapResultant d := by
  unfold k5CenteredSumDifference k5CenteredSumCofactor k5CenteredGapResultant
  ring

/-- The five-block equation forces the centered sum modulus to divide the
degree-five gap resultant. -/
theorem k5_centered_sum_sub_one_dvd_gap_resultant
    {n d : ℕ} (hd : 5 ≤ d)
    (heq : blockProduct 5 (n + d) = 4 * blockProduct 5 n) :
    2 * n + d + 5 ∣
      5 * (d - 3) ^ 2 * (d - 1) * (d + 1) * (d + 3) := by
  let u : ℤ := n + 3
  let v : ℤ := n + d + 3
  let S : ℤ := 2 * n + d + 6
  let dz : ℤ := d
  have hcenter : K5CenteredEq (n + d + 3) (n + 3) := k5_centered_of_eq heq
  have hpoly := k5_centered_eq_iff_integer_polynomial.mp hcenter
  have hS : S = u + v := by
    dsimp [S, u, v]
    push_cast
    ring
  have hdifference : dz = v - u := by
    dsimp [dz, u, v]
    push_cast
    ring
  have hcleared : k5CenteredSumDifference S dz = 0 := by
    calc
      k5CenteredSumDifference S dz =
          32 * (k5PolynomialZ v - 4 * k5PolynomialZ u) := by
            rw [hS, hdifference]
            unfold k5CenteredSumDifference k5PolynomialZ
            ring
      _ = 0 := by
        have hv : v = ((n + d + 3 : ℕ) : ℤ) := by
          dsimp [v]
        have hu : u = ((n + 3 : ℕ) : ℤ) := by
          dsimp [u]
        rw [hv, hu, hpoly]
        ring
  have hdivision := k5_centered_sum_polynomial_division S dz
  rw [hcleared] at hdivision
  have hdivZ : S - 1 ∣ k5CenteredGapResultant dz := by
    refine ⟨-k5CenteredSumCofactor S dz, ?_⟩
    linarith
  have hleft : S - 1 = ((2 * n + d + 5 : ℕ) : ℤ) := by
    dsimp [S]
    push_cast
    ring
  have hright : k5CenteredGapResultant dz =
      ((5 * (d - 3) ^ 2 * (d - 1) * (d + 1) * (d + 3) : ℕ) : ℤ) := by
    dsimp [k5CenteredGapResultant, dz]
    rw [Nat.cast_sub (by omega : 3 ≤ d), Nat.cast_sub (by omega : 1 ≤ d)]
    push_cast
    ring
  rw [hleft, hright] at hdivZ
  exact_mod_cast hdivZ

/-- After the four forced anti-diagonal owners are cancelled, the remaining
complement quotient `J` divides the product of the four exact gap quotients.
This is the equation-facing nonlinear constraint absent from the aggregate
CRT model. -/
theorem k5_G12_remaining_complement_quotient_dvd_centered_resultant
    {n d t : ℕ}
    (data : CanonicalOwnerData 5 n d t)
    (hfour : 4 ∣ n + d + t)
    (hd : 5 ≤ d)
    (heq : blockProduct 5 (n + d) = 4 * blockProduct 5 n)
    (hprofile : K5G12ZeroResidualProfile data) :
    let P := canonicalOwnerCell data 4 1
    let Q := canonicalOwnerCell data 2 3
    let A := canonicalOwnerCell data 3 2
    let B := canonicalOwnerCell data 1 4
    let R := (n + 4) / P
    let C := (n + d + 1) / P
    let K := (R + C) / (P * Q)
    let J := K / (A * B)
    J ∣ 5 * ((d - 3) / P) ^ 2 * ((d - 1) / A) *
      ((d + 1) / Q) * ((d + 3) / B) := by
  dsimp only
  let P := canonicalOwnerCell data 4 1
  let Q := canonicalOwnerCell data 2 3
  let A := canonicalOwnerCell data 3 2
  let B := canonicalOwnerCell data 1 4
  let R := (n + 4) / P
  let C := (n + d + 1) / P
  let K := (R + C) / (P * Q)
  let J := K / (A * B)
  let p := (d - 3) / P
  let q := (d + 1) / Q
  let a := (d - 1) / A
  let b := (d + 3) / B
  have hforced := k5_G12_anti_diagonal_owner_product_dvd_complement_quotient
    data hfour heq hprofile
  have hABdvdK : A * B ∣ K := hforced.1
  have htarget : 2 * n + d + 5 = P ^ 2 * Q * K := by
    have ht := hforced.2.2
    change (n + 3) + (n + d + 2) = P ^ 2 * Q * K at ht
    omega
  have hKeq : K = A * B * J := by
    dsimp [J]
    exact (Nat.mul_div_cancel' hABdvdK).symm
  have hPd : P ∣ d - 3 := by
    dsimp [P]
    simpa using canonicalOwnerCell_dvd_shiftedDifference data hd
      (by norm_num) (by norm_num) hfour
  have hQd : Q ∣ d + 1 := by
    dsimp [Q]
    simpa using canonicalOwnerCell_dvd_shiftedDifference data hd
      (by norm_num) (by norm_num) hfour
  have hAd : A ∣ d - 1 := by
    dsimp [A]
    simpa using canonicalOwnerCell_dvd_shiftedDifference data hd
      (by norm_num) (by norm_num) hfour
  have hBd : B ∣ d + 3 := by
    dsimp [B]
    simpa using canonicalOwnerCell_dvd_shiftedDifference data hd
      (by norm_num) (by norm_num) hfour
  have hPfactor : d - 3 = P * p := by
    dsimp [p]
    exact (Nat.mul_div_cancel' hPd).symm
  have hQfactor : d + 1 = Q * q := by
    dsimp [q]
    exact (Nat.mul_div_cancel' hQd).symm
  have hAfactor : d - 1 = A * a := by
    dsimp [a]
    exact (Nat.mul_div_cancel' hAd).symm
  have hBfactor : d + 3 = B * b := by
    dsimp [b]
    exact (Nat.mul_div_cancel' hBd).symm
  have hresultant := k5_centered_sum_sub_one_dvd_gap_resultant hd heq
  have hNpos : 0 < P ^ 2 * Q * (A * B) := by
    exact Nat.mul_pos (Nat.mul_pos
      (Nat.pow_pos (canonicalOwnerCell_pos data))
      (canonicalOwnerCell_pos data))
      (Nat.mul_pos (canonicalOwnerCell_pos data) (canonicalOwnerCell_pos data))
  apply (Nat.mul_dvd_mul_iff_left hNpos).mp
  have hleft : (P ^ 2 * Q * (A * B)) * J = 2 * n + d + 5 := by
    rw [htarget, hKeq]
    ring
  have hright : (P ^ 2 * Q * (A * B)) *
      (5 * p ^ 2 * a * q * b) =
      5 * (d - 3) ^ 2 * (d - 1) * (d + 1) * (d + 3) := by
    rw [hPfactor, hQfactor, hAfactor, hBfactor]
    ring
  rw [hleft, hright]
  simpa [p, q, a, b] using hresultant

#print axioms k5_centered_sum_polynomial_division
#print axioms k5_centered_sum_sub_one_dvd_gap_resultant
#print axioms k5_G12_remaining_complement_quotient_dvd_centered_resultant

end Erdos686Variant
end Erdos686
