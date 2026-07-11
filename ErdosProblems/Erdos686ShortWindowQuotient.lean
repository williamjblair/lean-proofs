/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import ErdosProblems.Erdos686FourthLocalLift

/-!
# Erdős 686: third-quotient restrictions in the three-owner short window

Write the composed third obstruction at one cleaned owner as `T=P^2*z`.
The composed fourth lift first cancels to

`P | 3*b*c*z + J`.

Eliminating the cofactor product `t=abc` between this congruence and the
composed second obstruction gives a fixed-coefficient congruence

`P | 27*C^2*b*c*z + K*g^4`.

Consequently every common divisor of `P` and `z` divides `K*g^4`.  The
coefficient `K` depends only on the row coefficients and the two owner
offsets.  This module also records the exact three-row determinant identity
among the three third quotients and a generic archimedean quotient bound.

These are proper consequences of the fourth lift and short window.  They do
not close the three-owner branch.
-/

namespace Erdos686
namespace Erdos686Variant

/-- Fixed coefficient obtained after eliminating the cofactor product from
the fourth correction with the composed second obstruction. -/
def threeBucketReducedFourthCoefficient
    (C D E H deltaLeft deltaRight : ℤ) : ℤ :=
  108 * (deltaLeft * deltaRight) *
    (-108 * D ^ 3 * (deltaLeft * deltaRight) +
      C * D *
        (-108 * D * (deltaLeft + deltaRight) +
          324 * E * (deltaLeft * deltaRight)) +
      567 * C ^ 2 * H * (deltaLeft * deltaRight))

/-- Multiplier of the composed second obstruction in the exact reduction
identity. -/
def threeBucketReducedFourthMultiplier
    (C D E t g deltaLeft deltaRight : ℤ) : ℤ :=
  -9 * D *
      (3 * C * t + 36 * D * g ^ 2 * (deltaLeft * deltaRight)) +
    3 * C * g ^ 2 *
      (-108 * D * (deltaLeft + deltaRight) +
        324 * E * (deltaLeft * deltaRight))

/-- Exact polynomial identity behind the fixed-coefficient fourth reduction.
It is valid over signed integers and does not divide by `3`, `C`, or `g`. -/
theorem three_bucket_reduced_fourth_identity
    (C D E H t g deltaLeft deltaRight : ℤ) :
    9 * C ^ 2 *
        threeBucketFourthCorrection D E H t g deltaLeft deltaRight =
      threeBucketReducedFourthMultiplier C D E t g deltaLeft deltaRight *
          (3 * (C * t - 12 * D * g ^ 2 * deltaLeft * deltaRight)) +
        threeBucketReducedFourthCoefficient C D E H deltaLeft deltaRight *
          g ^ 4 := by
  simp [threeBucketFourthCorrection,
    threeBucketReducedFourthMultiplier,
    threeBucketReducedFourthCoefficient]
  ring

/-- Cancel `P^2` from a `P^3` divisibility without assuming primality. -/
theorem square_factor_cancel_from_cube_dvd
    {P W : ℤ} (hP : P ≠ 0) (hdiv : P ^ 3 ∣ P ^ 2 * W) :
    P ∣ W := by
  rcases hdiv with ⟨q, hq⟩
  refine ⟨q, ?_⟩
  apply mul_left_cancel₀ (pow_ne_zero 2 hP)
  calc
    P ^ 2 * W = P ^ 3 * q := hq
    _ = P ^ 2 * (P * q) := by ring

/-- If the third obstruction is `P^2*z`, the composed fourth obstruction is
equivalent to one ordinary `P`-divisibility involving `z`. -/
theorem three_bucket_fourth_to_third_quotient
    {P b c T J z : ℤ}
    (hP : P ≠ 0)
    (hT : T = P ^ 2 * z)
    (hfourth : P ^ 3 ∣ 3 * b * c * T + P ^ 2 * J) :
    P ∣ 3 * b * c * z + J := by
  have hraw : P ^ 3 ∣ P ^ 2 * (3 * b * c * z + J) := by
    convert hfourth using 1 <;> rw [hT] <;> ring
  exact square_factor_cancel_from_cube_dvd hP hraw

/-- Direct specialization to the banked three-bucket fourth obstruction. -/
theorem three_bucket_fourth_obstruction_to_quotient
    {P b c C D E H a g deltaLeft deltaRight gap z : ℤ}
    (hP : P ≠ 0)
    (hthird :
      threeBucketThirdObstruction C D E a b c g
          deltaLeft deltaRight gap = P ^ 2 * z)
    (hfourth : P ^ 3 ∣
      threeBucketFourthObstruction P b c C D E H a g
        deltaLeft deltaRight gap) :
    P ∣ 3 * b * c * z +
      threeBucketFourthCorrection D E H (a * b * c) g
        deltaLeft deltaRight := by
  apply three_bucket_fourth_to_third_quotient hP hthird
  simpa [threeBucketFourthObstruction] using hfourth

/-- Eliminate `t` from the quotient congruence using the composed second
obstruction.  The right-hand coefficient is independent of `t` and `d`. -/
theorem three_bucket_reduced_fourth_quotient_dvd
    {P C D E H t g b c z deltaLeft deltaRight : ℤ}
    (hsecond : P ∣
      3 * (C * t - 12 * D * g ^ 2 * deltaLeft * deltaRight))
    (hquotient : P ∣
      3 * b * c * z +
        threeBucketFourthCorrection D E H t g deltaLeft deltaRight) :
    P ∣
      27 * C ^ 2 * b * c * z +
        threeBucketReducedFourthCoefficient C D E H
          deltaLeft deltaRight * g ^ 4 := by
  have hq := dvd_mul_of_dvd_right hquotient (9 * C ^ 2)
  have hs := dvd_mul_of_dvd_right hsecond
    (threeBucketReducedFourthMultiplier C D E t g deltaLeft deltaRight)
  have hdiff := dvd_sub hq hs
  convert hdiff using 1 <;>
    simp [threeBucketFourthCorrection,
      threeBucketReducedFourthMultiplier,
      threeBucketReducedFourthCoefficient] <;> ring

/-- Direct fixed-coefficient consequence of the banked second and fourth
three-bucket obstructions once the third quotient is named. -/
theorem three_bucket_fourth_obstruction_reduced_dvd
    {P b c C D E H a g deltaLeft deltaRight gap z : ℤ}
    (hP : P ≠ 0)
    (hsecond : P ∣
      threeBucketSecondObstruction C D a b c g deltaLeft deltaRight)
    (hthird :
      threeBucketThirdObstruction C D E a b c g
          deltaLeft deltaRight gap = P ^ 2 * z)
    (hfourth : P ^ 3 ∣
      threeBucketFourthObstruction P b c C D E H a g
        deltaLeft deltaRight gap) :
    P ∣
      27 * C ^ 2 * b * c * z +
        threeBucketReducedFourthCoefficient C D E H
          deltaLeft deltaRight * g ^ 4 := by
  apply three_bucket_reduced_fourth_quotient_dvd (t := a * b * c)
  · convert hsecond using 1 <;>
      simp [threeBucketSecondObstruction] <;> ring
  · exact three_bucket_fourth_obstruction_to_quotient
      hP hthird hfourth

/-- The reduced fourth coefficient vanishes when both odd Taylor
coefficients vanish, as happens at the center of every odd target row. -/
theorem three_bucket_reduced_fourth_coefficient_eq_zero_of_odd_coefficients
    {C D E H deltaLeft deltaRight : ℤ}
    (hD : D = 0) (hH : H = 0) :
    threeBucketReducedFourthCoefficient C D E H
      deltaLeft deltaRight = 0 := by
  simp [threeBucketReducedFourthCoefficient, hD, hH]

/-- Every common divisor of the cleaned component and its third quotient is
absorbed by the fixed fourth coefficient and the fourth power of the loss. -/
theorem common_component_third_quotient_dvd_fixed
    {G P C D E H g b c z deltaLeft deltaRight : ℤ}
    (hGP : G ∣ P)
    (hGz : G ∣ z)
    (hreduced : P ∣
      27 * C ^ 2 * b * c * z +
        threeBucketReducedFourthCoefficient C D E H
          deltaLeft deltaRight * g ^ 4) :
    G ∣ threeBucketReducedFourthCoefficient C D E H
      deltaLeft deltaRight * g ^ 4 := by
  have hwhole := dvd_trans hGP hreduced
  have hzterm : G ∣ 27 * C ^ 2 * b * c * z :=
    dvd_mul_of_dvd_right hGz (27 * C ^ 2 * b * c)
  have hdiff := dvd_sub hwhole hzterm
  convert hdiff using 1 <;> ring

/-- A divisor common to one cleaned component and an opposite residual
cofactor divides the corresponding explicit owner offset.  No coprimality or
primality is used. -/
theorem common_component_opposite_cofactor_dvd_offset
    {G P Q a b delta : ℤ}
    (hGP : G ∣ P)
    (hGb : G ∣ b)
    (hresidual : a * P ^ 2 - b * Q ^ 2 = 3 * delta) :
    G ∣ 3 * delta := by
  have hPtwo : G ∣ P ^ 2 :=
    dvd_trans hGP (dvd_pow_self P (by norm_num))
  have hleft : G ∣ a * P ^ 2 := dvd_mul_of_dvd_right hPtwo a
  have hright : G ∣ b * Q ^ 2 := dvd_mul_of_dvd_left hGb (Q ^ 2)
  have hdiff := dvd_sub hleft hright
  rw [hresidual] at hdiff
  exact hdiff

/-- Cofactor of the first coordinate in the cross product of three affine
coefficient rows `(A_s,B_s)`. -/
def threeRowWeightOne (A₂ B₂ A₃ B₃ : ℤ) : ℤ := A₂ * B₃ - A₃ * B₂

def threeRowWeightTwo (A₁ B₁ A₃ B₃ : ℤ) : ℤ := A₃ * B₁ - A₁ * B₃

def threeRowWeightThree (A₁ B₁ A₂ B₂ : ℤ) : ℤ := A₁ * B₂ - A₂ * B₁

/-- Exact three-term lattice identity.  If three third obstructions are
affine in the common variables `t` and `u*d`, their cross-product combination
removes both, leaving only the fixed `u` correction. -/
theorem three_third_quotient_lattice_identity
    {P Q R zP zQ zR A₁ A₂ A₃ B₁ B₂ B₃ G₁ G₂ G₃ t u d : ℤ}
    (hP : P ^ 2 * zP = A₁ * t + B₁ * u * d + G₁ * u)
    (hQ : Q ^ 2 * zQ = A₂ * t + B₂ * u * d + G₂ * u)
    (hR : R ^ 2 * zR = A₃ * t + B₃ * u * d + G₃ * u) :
    threeRowWeightOne A₂ B₂ A₃ B₃ * (P ^ 2 * zP) +
        threeRowWeightTwo A₁ B₁ A₃ B₃ * (Q ^ 2 * zQ) +
        threeRowWeightThree A₁ B₁ A₂ B₂ * (R ^ 2 * zR) =
      u *
        (threeRowWeightOne A₂ B₂ A₃ B₃ * G₁ +
          threeRowWeightTwo A₁ B₁ A₃ B₃ * G₂ +
          threeRowWeightThree A₁ B₁ A₂ B₂ * G₃) := by
  rw [hP, hQ, hR]
  simp [threeRowWeightOne, threeRowWeightTwo, threeRowWeightThree]
  ring

/-- Pairwise packing plus one weighted square bound.  This is the generic
size estimate used when two third quotients vanish: the two corresponding
components divide one common `L*g^4`, while the lattice identity bounds the
square of the remaining component. -/
theorem two_zero_third_quotient_gap_square_bound
    {P Q R g d L Gamma W : ℕ}
    (hL : 0 < L) (hg : 0 < g)
    (hPQ : P.Coprime Q)
    (hd : d = g * P * Q * R)
    (hP : P ∣ L * g ^ 4)
    (hQ : Q ∣ L * g ^ 4)
    (hR : R ^ 2 * W ≤ Gamma * g ^ 2) :
    d ^ 2 * W ≤ L ^ 2 * Gamma * g ^ 12 := by
  have hPQdiv : P * Q ∣ L * g ^ 4 :=
    hPQ.mul_dvd_of_dvd_of_dvd hP hQ
  have hcommonPos : 0 < L * g ^ 4 := by positivity
  have hPQle : P * Q ≤ L * g ^ 4 := Nat.le_of_dvd hcommonPos hPQdiv
  have hPQsq : (P * Q) ^ 2 ≤ (L * g ^ 4) ^ 2 :=
    Nat.pow_le_pow_left hPQle 2
  calc
    d ^ 2 * W = (g ^ 2 * (P * Q) ^ 2) * (R ^ 2 * W) := by
      rw [hd]
      ring
    _ ≤ (g ^ 2 * (L * g ^ 4) ^ 2) * (Gamma * g ^ 2) :=
      Nat.mul_le_mul (Nat.mul_le_mul le_rfl hPQsq) hR
    _ = L ^ 2 * Gamma * g ^ 12 := by ring

/-- Numeric cutoff interface for the two-zero quotient packing bound. -/
theorem two_zero_third_quotient_gap_lt_cutoff
    {P Q R g d L Gamma W G cutoff : ℕ}
    (hL : 0 < L) (hg : 0 < g)
    (hPQ : P.Coprime Q)
    (hd : d = g * P * Q * R)
    (hP : P ∣ L * g ^ 4)
    (hQ : Q ∣ L * g ^ 4)
    (hR : R ^ 2 * W ≤ Gamma * g ^ 2)
    (hgmax : g ≤ G)
    (hcut : L ^ 2 * Gamma * G ^ 12 < W * cutoff ^ 2) :
    d < cutoff := by
  have hbase := two_zero_third_quotient_gap_square_bound
    hL hg hPQ hd hP hQ hR
  have hgpow : g ^ 12 ≤ G ^ 12 := Nat.pow_le_pow_left hgmax 12
  have hmajor : L ^ 2 * Gamma * g ^ 12 ≤
      L ^ 2 * Gamma * G ^ 12 :=
    Nat.mul_le_mul_left (L ^ 2 * Gamma) hgpow
  have hstrict : d ^ 2 * W < W * cutoff ^ 2 :=
    lt_of_le_of_lt (le_trans hbase hmajor) hcut
  by_contra hnot
  have hcutle : cutoff ≤ d := Nat.le_of_not_gt hnot
  have hpows : cutoff ^ 2 ≤ d ^ 2 := Nat.pow_le_pow_left hcutle 2
  have hmul : W * cutoff ^ 2 ≤ d ^ 2 * W := by
    simpa [mul_comm] using Nat.mul_le_mul_left W hpows
  omega

/-- Generic arithmetic behind the short-window third-quotient bound. -/
theorem third_quotient_bound_of_short_window
    {P a d z B g : ℕ}
    (hd : 0 < d)
    (ha : 0 < a)
    (hB : 0 < B)
    (hg : 0 < g)
    (hlower : 5 * d < a * P ^ 2)
    (hsize : P ^ 2 * z < B * g ^ 2 * d) :
    5 * z < B * g ^ 2 * a := by
  by_cases hz : z = 0
  · subst z
    simp [hB, hg, ha]
  have hzpos : 0 < z := Nat.pos_of_ne_zero hz
  have hlowMul : 5 * d * z < a * P ^ 2 * z :=
    Nat.mul_lt_mul_of_pos_right hlower hzpos
  have hsizeMul : a * (P ^ 2 * z) < a * (B * g ^ 2 * d) :=
    Nat.mul_lt_mul_of_pos_left hsize ha
  have hdcancel : d * (5 * z) < d * (B * g ^ 2 * a) := by
    calc
      d * (5 * z) = 5 * d * z := by ring
      _ < a * P ^ 2 * z := hlowMul
      _ = a * (P ^ 2 * z) := by ring
      _ < a * (B * g ^ 2 * d) := hsizeMul
      _ = d * (B * g ^ 2 * a) := by ring
  exact (Nat.mul_lt_mul_left hd).mp hdcancel

#print axioms three_bucket_reduced_fourth_identity
#print axioms square_factor_cancel_from_cube_dvd
#print axioms three_bucket_fourth_to_third_quotient
#print axioms three_bucket_fourth_obstruction_to_quotient
#print axioms three_bucket_reduced_fourth_quotient_dvd
#print axioms three_bucket_fourth_obstruction_reduced_dvd
#print axioms three_bucket_reduced_fourth_coefficient_eq_zero_of_odd_coefficients
#print axioms common_component_third_quotient_dvd_fixed
#print axioms common_component_opposite_cofactor_dvd_offset
#print axioms three_third_quotient_lattice_identity
#print axioms two_zero_third_quotient_gap_square_bound
#print axioms two_zero_third_quotient_gap_lt_cutoff
#print axioms third_quotient_bound_of_short_window

end Erdos686Variant
end Erdos686
