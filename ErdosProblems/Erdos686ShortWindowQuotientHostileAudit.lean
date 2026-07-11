/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import ErdosProblems.Erdos686ShortWindowQuotient

/-!
# Erdős 686 ShortWindowQuotient: independent hostile kernel audit

The frozen `Erdos686ShortWindowQuotientAudit.lean` is a producer-side
importer.  This distinctly named module independently reproves all thirteen
public producer theorems and checks the finite two-zero count arithmetic.
-/

namespace Erdos686
namespace Erdos686Variant
namespace ShortWindowQuotientHostileAudit

theorem hostile_reduced_fourth_identity
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

theorem hostile_square_factor_cancel
    {P W : ℤ} (hP : P ≠ 0) (hdiv : P ^ 3 ∣ P ^ 2 * W) :
    P ∣ W := by
  rcases hdiv with ⟨q, hq⟩
  refine ⟨q, ?_⟩
  apply mul_left_cancel₀ (pow_ne_zero 2 hP)
  calc
    P ^ 2 * W = P ^ 3 * q := hq
    _ = P ^ 2 * (P * q) := by ring

theorem hostile_fourth_to_third_quotient
    {P b c T J z : ℤ}
    (hP : P ≠ 0)
    (hT : T = P ^ 2 * z)
    (hfourth : P ^ 3 ∣ 3 * b * c * T + P ^ 2 * J) :
    P ∣ 3 * b * c * z + J := by
  have hraw : P ^ 3 ∣ P ^ 2 * (3 * b * c * z + J) := by
    convert hfourth using 1 <;> rw [hT] <;> ring
  exact hostile_square_factor_cancel hP hraw

theorem hostile_fourth_obstruction_to_quotient
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
  apply hostile_fourth_to_third_quotient hP hthird
  simpa [threeBucketFourthObstruction] using hfourth

theorem hostile_reduced_fourth_quotient_dvd
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

theorem hostile_fourth_obstruction_reduced_dvd
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
  apply hostile_reduced_fourth_quotient_dvd (t := a * b * c)
  · convert hsecond using 1 <;>
      simp [threeBucketSecondObstruction] <;> ring
  · exact hostile_fourth_obstruction_to_quotient hP hthird hfourth

theorem hostile_reduced_coefficient_center_zero
    {C D E H deltaLeft deltaRight : ℤ}
    (hD : D = 0) (hH : H = 0) :
    threeBucketReducedFourthCoefficient C D E H
      deltaLeft deltaRight = 0 := by
  simp [threeBucketReducedFourthCoefficient, hD, hH]

theorem hostile_common_component_quotient_dvd
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

theorem hostile_common_component_cofactor_dvd_offset
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

theorem hostile_three_quotient_lattice_identity
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

theorem hostile_two_zero_gap_square_bound
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

theorem hostile_two_zero_gap_lt_cutoff
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
  have hbase := hostile_two_zero_gap_square_bound hL hg hPQ hd hP hQ hR
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

theorem hostile_third_quotient_short_bound
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

theorem hostile_target_constant_checks :
    threeBucketReducedFourthCoefficient 24 50 35 10 (-1) (-2) =
        5656573440 ∧
      threeBucketReducedFourthCoefficient 4 0 (-5) 0 2 (-2) = 0 ∧
      18 + 75 + 196 + 405 + 726 + 1183 = 2603 ∧
      18 + 75 + 196 + 405 + 726 + 901 = 2321 ∧
      1183 - 901 = 282 := by
  norm_num [threeBucketReducedFourthCoefficient]

#print axioms hostile_reduced_fourth_identity
#print axioms hostile_square_factor_cancel
#print axioms hostile_fourth_to_third_quotient
#print axioms hostile_fourth_obstruction_to_quotient
#print axioms hostile_reduced_fourth_quotient_dvd
#print axioms hostile_fourth_obstruction_reduced_dvd
#print axioms hostile_reduced_coefficient_center_zero
#print axioms hostile_common_component_quotient_dvd
#print axioms hostile_common_component_cofactor_dvd_offset
#print axioms hostile_three_quotient_lattice_identity
#print axioms hostile_two_zero_gap_square_bound
#print axioms hostile_two_zero_gap_lt_cutoff
#print axioms hostile_third_quotient_short_bound
#print axioms hostile_target_constant_checks

end ShortWindowQuotientHostileAudit
end Erdos686Variant
end Erdos686

#print axioms Erdos686.Erdos686Variant.three_bucket_reduced_fourth_identity
#print axioms Erdos686.Erdos686Variant.square_factor_cancel_from_cube_dvd
#print axioms Erdos686.Erdos686Variant.three_bucket_fourth_to_third_quotient
#print axioms Erdos686.Erdos686Variant.three_bucket_fourth_obstruction_to_quotient
#print axioms Erdos686.Erdos686Variant.three_bucket_reduced_fourth_quotient_dvd
#print axioms Erdos686.Erdos686Variant.three_bucket_fourth_obstruction_reduced_dvd
#print axioms Erdos686.Erdos686Variant.three_bucket_reduced_fourth_coefficient_eq_zero_of_odd_coefficients
#print axioms Erdos686.Erdos686Variant.common_component_third_quotient_dvd_fixed
#print axioms Erdos686.Erdos686Variant.common_component_opposite_cofactor_dvd_offset
#print axioms Erdos686.Erdos686Variant.three_third_quotient_lattice_identity
#print axioms Erdos686.Erdos686Variant.two_zero_third_quotient_gap_square_bound
#print axioms Erdos686.Erdos686Variant.two_zero_third_quotient_gap_lt_cutoff
#print axioms Erdos686.Erdos686Variant.third_quotient_bound_of_short_window
