/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import ErdosProblems.Erdos686.Core.ExactRatioThirdSign
import ErdosProblems.Erdos686.Core.FifthLocalLift

/-!
# Erdős 686: the center/reflected three-bucket determinant

The only target-row owner views where the reduced fifth coefficient loses its
quadratic gap term have the owner at the center and the other two owners at a
reflected pair.  In that specialization the coefficient is not constant: it
is exactly linear in the gap.  Thus the fifth congruence does not become a
fixed-divisor contradiction.

There is, however, a useful relation between the *two endpoint* third
obstructions.  Write the center residual as `X`, put the endpoints at distance
`r`, and write their third obstructions as `T₋, T₊`.  Reflection gives

`(X-3r)T₊ - (X+3r)T₋
   = 54r (C t - 8D X g²r - 40E g²r²d)`.

The left side is divisible by `Q²R²`.  The exact ratio lower bound proves that
the parenthesized cubic cannot vanish in any of the 27 target reflected
positions.  A finite packing certificate then closes all reflected pairs in
rows 5, 7, and 9, and the three inner pairs in row 11.  The two outer row-11
pairs and every row-13/15 pair remain outside that historical `10^120`
cutoff.  At the upgraded `10^1000` odd-tail boundary, all 27 pairs close for
a supplied exact center/reflected three-bucket decomposition; the final
theorem derives every packing bound from the original block equation.
-/

namespace Erdos686
namespace Erdos686Variant

/-- Row-wise residual ceiling used in the existing local-lift bounds. -/
def targetReflectedResidualCeiling : ℕ → ℕ
  | 5 => 14
  | 7 => 17
  | 9 => 23
  | 11 => 26
  | 13 => 29
  | 15 => 35
  | _ => 0

/-- The center/reflected specialization of the reduced fifth coefficient is
linear in the gap.  In particular its constant and quadratic coefficients are
both zero. -/
theorem three_bucket_reduced_fifth_center_reflected
    (C E G gap r : ℤ) :
    threeBucketReducedFifthCoefficient C 0 E 0 G gap r (-r) =
      8748 * r ^ 4 * C * (255 * C * G + 180 * E ^ 2) * gap := by
  simp [threeBucketReducedFifthCoefficient]
  ring

/-- Endpoint third obstruction at the left member of a reflected pair. -/
def reflectedLeftThird
    (C D E t g r gap : ℤ) : ℤ :=
  -9 * C * t + 216 * D * g ^ 2 * r ^ 2 +
    360 * E * g ^ 2 * r ^ 2 * gap

/-- Endpoint third obstruction at the right member of a reflected pair. -/
def reflectedRightThird
    (C D E t g r gap : ℤ) : ℤ :=
  -9 * C * t - 216 * D * g ^ 2 * r ^ 2 +
    360 * E * g ^ 2 * r ^ 2 * gap

/-- Exact determinant of the two reflected endpoint third obstructions. -/
theorem reflected_third_determinant_identity
    (C D E t g r gap X : ℤ) :
    (X - 3 * r) * reflectedRightThird C D E t g r gap -
        (X + 3 * r) * reflectedLeftThird C D E t g r gap =
      54 * r *
        (C * t - 8 * D * X * g ^ 2 * r -
          40 * E * g ^ 2 * r ^ 2 * gap) := by
  simp [reflectedLeftThird, reflectedRightThird]
  ring

/-- The determinant carries both endpoint squares.  No coprimality is needed:
each residual supplies one square and the opposite third obstruction supplies
the other. -/
theorem reflected_third_determinant_dvd_endpoint_squares
    {C D E t g r gap X Q R b c : ℤ}
    (hleftResidual : X - 3 * r = b * Q ^ 2)
    (hrightResidual : X + 3 * r = c * R ^ 2)
    (hleftThird : Q ^ 2 ∣ reflectedLeftThird C D E t g r gap)
    (hrightThird : R ^ 2 ∣ reflectedRightThird C D E t g r gap) :
    Q ^ 2 * R ^ 2 ∣
      (X - 3 * r) * reflectedRightThird C D E t g r gap -
        (X + 3 * r) * reflectedLeftThird C D E t g r gap := by
  rcases hleftThird with ⟨u, hu⟩
  rcases hrightThird with ⟨v, hv⟩
  refine ⟨b * v - c * u, ?_⟩
  rw [hleftResidual, hrightResidual, hu, hv]
  ring

/-- The three residual squares and the cleaned gap decomposition give the
exact cubic identity used to rule out a zero determinant. -/
theorem reflected_three_bucket_product_identity
    {a b c P Q R g d r X : ℤ}
    (hcenter : X = a * P ^ 2)
    (hleft : X - 3 * r = b * Q ^ 2)
    (hright : X + 3 * r = c * R ^ 2)
    (hgap : d = g * P * Q * R) :
    (a * b * c) * d ^ 2 =
      g ^ 2 * X * (X ^ 2 - 9 * r ^ 2) := by
  have hpairs :
      (b * Q ^ 2) * (c * R ^ 2) =
        (X - 3 * r) * (X + 3 * r) := by
    rw [← hleft, ← hright]
  calc
    (a * b * c) * d ^ 2 =
        g ^ 2 * (a * P ^ 2) * ((b * Q ^ 2) * (c * R ^ 2)) := by
      rw [hgap]
      ring
    _ = g ^ 2 * X * ((X - 3 * r) * (X + 3 * r)) := by
      rw [← hcenter, hpairs]
    _ = g ^ 2 * X * (X ^ 2 - 9 * r ^ 2) := by ring

/-- If the determinant's inner factor vanished, the exact product identity
would force a specific cubic relation in `X/d`. -/
theorem reflected_inner_zero_forces_cubic_zero
    {C D E t g r d X : ℤ}
    (hg : g ≠ 0)
    (hproduct : t * d ^ 2 = g ^ 2 * X * (X ^ 2 - 9 * r ^ 2))
    (hzero : C * t - 8 * D * X * g ^ 2 * r -
        40 * E * g ^ 2 * r ^ 2 * d = 0) :
    C * X * (X ^ 2 - 9 * r ^ 2) - 8 * D * X * r * d ^ 2 -
        40 * E * r ^ 2 * d ^ 3 = 0 := by
  have hscaled : g ^ 2 *
      (C * X * (X ^ 2 - 9 * r ^ 2) - 8 * D * X * r * d ^ 2 -
        40 * E * r ^ 2 * d ^ 3) = 0 := by
    calc
      g ^ 2 *
          (C * X * (X ^ 2 - 9 * r ^ 2) - 8 * D * X * r * d ^ 2 -
            40 * E * r ^ 2 * d ^ 3) =
          C * (g ^ 2 * X * (X ^ 2 - 9 * r ^ 2)) -
            8 * D * X * g ^ 2 * r * d ^ 2 -
            40 * E * g ^ 2 * r ^ 2 * d ^ 3 := by ring
      _ = C * (t * d ^ 2) -
            8 * D * X * g ^ 2 * r * d ^ 2 -
            40 * E * g ^ 2 * r ^ 2 * d ^ 3 := by rw [hproduct]
      _ = d ^ 2 *
            (C * t - 8 * D * X * g ^ 2 * r -
              40 * E * g ^ 2 * r ^ 2 * d) := by ring
      _ = 0 := by rw [hzero]; ring
  exact (mul_eq_zero.mp hscaled).resolve_left (pow_ne_zero 2 hg)

/-- Exact natural-number domination lemma behind the finite ratio
certificate.  `R/H` is the strict lower bound for `X/d`; `U` is its upper
integer ceiling. -/
theorem reflected_cubic_abs_domination_nat
    {Cabs Dabs Eabs R H U r d X target : ℕ}
    (hC : 0 < Cabs) (hR : 0 < R) (hH : 0 < H)
    (hr : 0 < r) (hd : 0 < d) (hX : 0 < X)
    (hlower : R * d < H * X)
    (hupper : X < U * d)
    (hD : 8 * Dabs * r * H ^ 2 < Cabs * R ^ 2)
    (hE : 40 * Eabs * r ^ 2 * H ^ 3 <
      R * (Cabs * R ^ 2 - 8 * Dabs * r * H ^ 2))
    (hoffset : 9 * Cabs * r ^ 2 * U * H ^ 3 < target ^ 2 *
      (R * (Cabs * R ^ 2 - 8 * Dabs * r * H ^ 2) -
        40 * Eabs * r ^ 2 * H ^ 3))
    (htarget : target ≤ d) :
    9 * Cabs * r ^ 2 * X + 8 * Dabs * X * r * d ^ 2 +
        40 * Eabs * r ^ 2 * d ^ 3 < Cabs * X ^ 3 := by
  let beta := 8 * Dabs * r
  let epsilon := 40 * Eabs * r ^ 2
  let A := Cabs * R ^ 2 - beta * H ^ 2
  let N := R * A - epsilon * H ^ 3
  have hbeta : beta * H ^ 2 < Cabs * R ^ 2 := by
    simpa [beta, mul_assoc] using hD
  have hAeq : A + beta * H ^ 2 = Cabs * R ^ 2 := by
    dsimp [A]
    exact Nat.sub_add_cancel (Nat.le_of_lt hbeta)
  have hepsilon : epsilon * H ^ 3 < R * A := by
    simpa [epsilon, A] using hE
  have hNeq : N + epsilon * H ^ 3 = R * A := by
    dsimp [N]
    exact Nat.sub_add_cancel (Nat.le_of_lt hepsilon)
  have hApos : 0 < A := by
    by_contra hnot
    have hAzero : A = 0 := Nat.eq_zero_of_not_pos hnot
    rw [hAzero] at hepsilon
    simp at hepsilon
  have hNpos : 0 < N := by
    have : epsilon * H ^ 3 < R * A := hepsilon
    exact Nat.sub_pos_of_lt this
  have hsqRaw := Nat.pow_lt_pow_left hlower (by norm_num : 2 ≠ 0)
  have hsq : R ^ 2 * d ^ 2 < H ^ 2 * X ^ 2 := by
    simpa [mul_pow] using hsqRaw
  have hbase :
      A * d ^ 2 + beta * H ^ 2 * d ^ 2 < Cabs * H ^ 2 * X ^ 2 := by
    calc
      A * d ^ 2 + beta * H ^ 2 * d ^ 2 =
          (A + beta * H ^ 2) * d ^ 2 := by ring
      _ = Cabs * R ^ 2 * d ^ 2 := by rw [hAeq]
      _ = Cabs * (R ^ 2 * d ^ 2) := by ring
      _ < Cabs * (H ^ 2 * X ^ 2) :=
        Nat.mul_lt_mul_of_pos_left hsq hC
      _ = Cabs * H ^ 2 * X ^ 2 := by ring
  have hlowScaled : R * A * d ^ 3 < H * X * (A * d ^ 2) := by
    have hpos : 0 < A * d ^ 2 := Nat.mul_pos hApos (pow_pos hd _)
    have hmul := Nat.mul_lt_mul_of_pos_right hlower hpos
    convert hmul using 1 <;> ring
  have hbaseScaled :
      (A * d ^ 2 + beta * H ^ 2 * d ^ 2) * (H * X) <
        (Cabs * H ^ 2 * X ^ 2) * (H * X) :=
    Nat.mul_lt_mul_of_pos_right hbase (Nat.mul_pos hH hX)
  have hmain :
      R * A * d ^ 3 + beta * H ^ 3 * X * d ^ 2 <
        Cabs * H ^ 3 * X ^ 3 := by
    calc
      R * A * d ^ 3 + beta * H ^ 3 * X * d ^ 2 <
          H * X * (A * d ^ 2) + beta * H ^ 3 * X * d ^ 2 :=
        Nat.add_lt_add_right hlowScaled _
      _ = (A * d ^ 2 + beta * H ^ 2 * d ^ 2) * (H * X) := by ring
      _ < (Cabs * H ^ 2 * X ^ 2) * (H * X) := hbaseScaled
      _ = Cabs * H ^ 3 * X ^ 3 := by ring
  have hmargin :
      N * d ^ 3 + H ^ 3 * (beta * X * d ^ 2 + epsilon * d ^ 3) <
        H ^ 3 * (Cabs * X ^ 3) := by
    calc
      N * d ^ 3 + H ^ 3 * (beta * X * d ^ 2 + epsilon * d ^ 3) =
          R * A * d ^ 3 + beta * H ^ 3 * X * d ^ 2 := by
        rw [← hNeq]
        ring
      _ < Cabs * H ^ 3 * X ^ 3 := hmain
      _ = H ^ 3 * (Cabs * X ^ 3) := by ring
  let offset := 9 * Cabs * r ^ 2
  have hoffsetBase : offset * U * H ^ 3 < target ^ 2 * N := by
    simpa [offset, N, A] using hoffset
  have hoffsetX : H ^ 3 * (offset * X) < H ^ 3 * (offset * (U * d)) := by
    have hoffpos : 0 < offset := by
      dsimp [offset]
      positivity
    have hmul := Nat.mul_lt_mul_of_pos_left hupper hoffpos
    exact Nat.mul_lt_mul_of_pos_left hmul (pow_pos hH _)
  have htargetSq : target ^ 2 ≤ d ^ 2 := Nat.pow_le_pow_left htarget 2
  have hoffsetMargin : H ^ 3 * (offset * X) < N * d ^ 3 := by
    calc
      H ^ 3 * (offset * X) < H ^ 3 * (offset * (U * d)) := hoffsetX
      _ = (offset * U * H ^ 3) * d := by ring
      _ < (target ^ 2 * N) * d :=
        Nat.mul_lt_mul_of_pos_right hoffsetBase hd
      _ ≤ (d ^ 2 * N) * d :=
        Nat.mul_le_mul_right d (Nat.mul_le_mul_right N htargetSq)
      _ = N * d ^ 3 := by ring
  have hallScaled :
      H ^ 3 *
          (offset * X + beta * X * d ^ 2 + epsilon * d ^ 3) <
        H ^ 3 * (Cabs * X ^ 3) := by
    calc
      H ^ 3 *
          (offset * X + beta * X * d ^ 2 + epsilon * d ^ 3) =
          H ^ 3 * (offset * X) +
            H ^ 3 * (beta * X * d ^ 2 + epsilon * d ^ 3) := by ring
      _ < N * d ^ 3 +
          H ^ 3 * (beta * X * d ^ 2 + epsilon * d ^ 3) :=
        Nat.add_lt_add_right hoffsetMargin _
      _ < H ^ 3 * (Cabs * X ^ 3) := hmargin
  have hall := Nat.lt_of_mul_lt_mul_left hallScaled
  simpa [offset, beta, epsilon, mul_assoc, mul_left_comm, mul_comm] using hall

/-- Absolute-value domination rules out the cubic forced by a zero
determinant. -/
theorem reflected_cubic_ne_zero_of_abs_domination
    {C D E : ℤ} {r d X : ℕ}
    (hdom :
      9 * Int.natAbs C * r ^ 2 * X +
          8 * Int.natAbs D * X * r * d ^ 2 +
          40 * Int.natAbs E * r ^ 2 * d ^ 3 <
        Int.natAbs C * X ^ 3) :
    C * (X : ℤ) * ((X : ℤ) ^ 2 - 9 * (r : ℤ) ^ 2) -
        8 * D * (X : ℤ) * (r : ℤ) * (d : ℤ) ^ 2 -
        40 * E * (r : ℤ) ^ 2 * (d : ℤ) ^ 3 ≠ 0 := by
  intro hzero
  have heq :
      C * (X : ℤ) ^ 3 =
        9 * C * (r : ℤ) ^ 2 * (X : ℤ) +
          8 * D * (X : ℤ) * (r : ℤ) * (d : ℤ) ^ 2 +
          40 * E * (r : ℤ) ^ 2 * (d : ℤ) ^ 3 := by
    nlinarith
  have habsEq := congrArg Int.natAbs heq
  have htri₁ := Int.natAbs_add_le
    (9 * C * (r : ℤ) ^ 2 * (X : ℤ))
    (8 * D * (X : ℤ) * (r : ℤ) * (d : ℤ) ^ 2)
  have htri₂ := Int.natAbs_add_le
    (9 * C * (r : ℤ) ^ 2 * (X : ℤ) +
      8 * D * (X : ℤ) * (r : ℤ) * (d : ℤ) ^ 2)
    (40 * E * (r : ℤ) ^ 2 * (d : ℤ) ^ 3)
  have hrhs :
      Int.natAbs
          (9 * C * (r : ℤ) ^ 2 * (X : ℤ) +
            8 * D * (X : ℤ) * (r : ℤ) * (d : ℤ) ^ 2 +
            40 * E * (r : ℤ) ^ 2 * (d : ℤ) ^ 3) ≤
        9 * Int.natAbs C * r ^ 2 * X +
          8 * Int.natAbs D * X * r * d ^ 2 +
          40 * Int.natAbs E * r ^ 2 * d ^ 3 := by
    calc
      Int.natAbs
          (9 * C * (r : ℤ) ^ 2 * (X : ℤ) +
            8 * D * (X : ℤ) * (r : ℤ) * (d : ℤ) ^ 2 +
            40 * E * (r : ℤ) ^ 2 * (d : ℤ) ^ 3) ≤
          Int.natAbs
              (9 * C * (r : ℤ) ^ 2 * (X : ℤ) +
                8 * D * (X : ℤ) * (r : ℤ) * (d : ℤ) ^ 2) +
            Int.natAbs (40 * E * (r : ℤ) ^ 2 * (d : ℤ) ^ 3) := htri₂
      _ ≤ (Int.natAbs (9 * C * (r : ℤ) ^ 2 * (X : ℤ)) +
            Int.natAbs (8 * D * (X : ℤ) * (r : ℤ) * (d : ℤ) ^ 2)) +
          Int.natAbs (40 * E * (r : ℤ) ^ 2 * (d : ℤ) ^ 3) :=
        Nat.add_le_add_right htri₁ _
      _ = 9 * Int.natAbs C * r ^ 2 * X +
          8 * Int.natAbs D * X * r * d ^ 2 +
          40 * Int.natAbs E * r ^ 2 * d ^ 3 := by
        simp [Int.natAbs_mul, Int.natAbs_pow]
  have hleft : Int.natAbs (C * (X : ℤ) ^ 3) =
      Int.natAbs C * X ^ 3 := by
    simp [Int.natAbs_mul, Int.natAbs_pow]
  have hbad : Int.natAbs C * X ^ 3 < Int.natAbs C * X ^ 3 := by
    calc
      Int.natAbs C * X ^ 3 = Int.natAbs (C * (X : ℤ) ^ 3) := hleft.symm
      _ = Int.natAbs
          (9 * C * (r : ℤ) ^ 2 * (X : ℤ) +
            8 * D * (X : ℤ) * (r : ℤ) * (d : ℤ) ^ 2 +
            40 * E * (r : ℤ) ^ 2 * (d : ℤ) ^ 3) := habsEq
      _ ≤ 9 * Int.natAbs C * r ^ 2 * X +
          8 * Int.natAbs D * X * r * d ^ 2 +
          40 * Int.natAbs E * r ^ 2 * d ^ 3 := hrhs
      _ < Int.natAbs C * X ^ 3 := hdom
  exact (Nat.lt_irrefl _ hbad)

/-- Exact finite certificate for every one of the 27 center/reflected pairs.
The first two inequalities prove monotone cubic domination from the sharp
ratio lower bound; the last absorbs the finite `9r²X` term at target size. -/
theorem target_reflected_cubic_coefficient_certificate
    {k r : ℕ}
    (hk : k = 5 ∨ k = 7 ∨ k = 9 ∨ k = 11 ∨ k = 13 ∨ k = 15)
    (hr : 1 ≤ r ∧ r < (k + 1) / 2) :
    let i := (k + 1) / 2 - r
    let Cabs := Int.natAbs (localSecondConstant k i)
    let Dabs := Int.natAbs (localSecondLinear k i)
    let Eabs := Int.natAbs (localThirdQuadratic k i)
    let R := exactRatioResidualNumerator k
    let H := exactRatioResidualDenominator k
    let U := targetReflectedResidualCeiling k
    0 < Cabs ∧ 0 < R ∧ 0 < H ∧
      8 * Dabs * r * H ^ 2 < Cabs * R ^ 2 ∧
      40 * Eabs * r ^ 2 * H ^ 3 <
        R * (Cabs * R ^ 2 - 8 * Dabs * r * H ^ 2) ∧
      9 * Cabs * r ^ 2 * U * H ^ 3 < (10 ^ 120) ^ 2 *
        (R * (Cabs * R ^ 2 - 8 * Dabs * r * H ^ 2) -
          40 * Eabs * r ^ 2 * H ^ 3) := by
  have hi : (k + 1) / 2 - r ∈ Finset.Icc 1 k := by
    rw [Finset.mem_Icc]
    constructor <;> omega
  dsimp
  rw [localSecondConstant_eq_table hk hi,
    localSecondLinear_eq_table hk hi,
    localThirdQuadratic_eq_table hk hi]
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hr with ⟨hr1, hrlt⟩ <;>
    interval_cases r <;>
    norm_num [secondCoefficientTable, thirdCoefficientTable,
      exactRatioResidualNumerator, exactRatioResidualDenominator,
      exactRatioBracketNumerator, exactRatioBracketDenominator,
      targetReflectedResidualCeiling] at *

/-- In all 27 target reflected positions, the exact equation window rules out
the cubic relation forced by a zero endpoint determinant. -/
theorem target_reflected_cubic_ne_zero
    {k n d r : ℕ}
    (hk : k = 5 ∨ k = 7 ∨ k = 9 ∨ k = 11 ∨ k = 13 ∨ k = 15)
    (hr : 1 ≤ r ∧ r < (k + 1) / 2)
    (hd : 10 ^ 120 ≤ d)
    (heq : blockProduct k (n + d) = 4 * blockProduct k n)
    (hupper : localResidual n d ((k + 1) / 2) <
      targetReflectedResidualCeiling k * d) :
    let i := (k + 1) / 2 - r
    localSecondConstant k i *
          (localResidual n d ((k + 1) / 2) : ℤ) *
          ((localResidual n d ((k + 1) / 2) : ℤ) ^ 2 -
            9 * (r : ℤ) ^ 2) -
        8 * localSecondLinear k i *
          (localResidual n d ((k + 1) / 2) : ℤ) * (r : ℤ) * (d : ℤ) ^ 2 -
        40 * localThirdQuadratic k i * (r : ℤ) ^ 2 * (d : ℤ) ^ 3 ≠ 0 := by
  let center := (k + 1) / 2
  let i := center - r
  let X := localResidual n d center
  have hcenter : center ∈ Finset.Icc 1 k := by
    dsimp [center]
    rw [Finset.mem_Icc]
    constructor <;> omega
  have hratio := target_exactRatio_localResidual_lower hk hcenter hd heq
  have hcert := target_reflected_cubic_coefficient_certificate hk hr
  have hdpos : 0 < d := lt_of_lt_of_le (by norm_num) hd
  have hXpos : 0 < X := by
    have hRpos := hcert.2.1
    have hleftPos : 0 < exactRatioResidualNumerator k * d :=
      Nat.mul_pos hRpos hdpos
    have hrightPos : 0 < exactRatioResidualDenominator k * X :=
      lt_trans hleftPos (by simpa [X, center] using hratio)
    exact Nat.pos_of_mul_pos_left hrightPos
  have hdom := reflected_cubic_abs_domination_nat
    (Cabs := Int.natAbs (localSecondConstant k i))
    (Dabs := Int.natAbs (localSecondLinear k i))
    (Eabs := Int.natAbs (localThirdQuadratic k i))
    (R := exactRatioResidualNumerator k)
    (H := exactRatioResidualDenominator k)
    (U := targetReflectedResidualCeiling k)
    (r := r) (d := d) (X := X) (target := 10 ^ 120)
    hcert.1 hcert.2.1 hcert.2.2.1 hr.1 hdpos hXpos
    (by simpa [X, center] using hratio)
    (by simpa [X, center] using hupper)
    hcert.2.2.2.1 hcert.2.2.2.2.1 hcert.2.2.2.2.2 hd
  simpa [i, X, center] using
    (reflected_cubic_ne_zero_of_abs_domination
      (C := localSecondConstant k i)
      (D := localSecondLinear k i)
      (E := localThirdQuadratic k i) hdom)

/-- The actual parenthesized determinant factor is nonzero once the three
residual product identity is supplied. -/
theorem target_reflected_third_inner_ne_zero
    {k n d r t g : ℕ}
    (hk : k = 5 ∨ k = 7 ∨ k = 9 ∨ k = 11 ∨ k = 13 ∨ k = 15)
    (hr : 1 ≤ r ∧ r < (k + 1) / 2)
    (hd : 10 ^ 120 ≤ d)
    (hg : 0 < g)
    (heq : blockProduct k (n + d) = 4 * blockProduct k n)
    (hupper : localResidual n d ((k + 1) / 2) <
      targetReflectedResidualCeiling k * d)
    (hproduct : (t : ℤ) * (d : ℤ) ^ 2 =
      (g : ℤ) ^ 2 * (localResidual n d ((k + 1) / 2) : ℤ) *
        ((localResidual n d ((k + 1) / 2) : ℤ) ^ 2 - 9 * (r : ℤ) ^ 2)) :
    let i := (k + 1) / 2 - r
    localSecondConstant k i * (t : ℤ) -
        8 * localSecondLinear k i *
          (localResidual n d ((k + 1) / 2) : ℤ) * (g : ℤ) ^ 2 * (r : ℤ) -
        40 * localThirdQuadratic k i * (g : ℤ) ^ 2 *
          (r : ℤ) ^ 2 * (d : ℤ) ≠ 0 := by
  let i := (k + 1) / 2 - r
  let X := localResidual n d ((k + 1) / 2)
  dsimp
  intro hzero
  have hcubic := reflected_inner_zero_forces_cubic_zero
    (C := localSecondConstant k i)
    (D := localSecondLinear k i)
    (E := localThirdQuadratic k i)
    (t := (t : ℤ)) (g := (g : ℤ)) (r := (r : ℤ))
    (d := (d : ℤ)) (X := (X : ℤ))
    (by exact_mod_cast (Nat.ne_of_gt hg)) hproduct
    (by simpa [i, X] using hzero)
  exact (target_reflected_cubic_ne_zero hk hr hd heq hupper)
    (by simpa [i, X] using hcubic)

/-- Product identity plus the short residual ceiling bounds the cofactor
product by `g² U³ d`. -/
theorem reflected_cofactor_product_lt
    {t g X U d : ℕ}
    (hg : 0 < g) (hd : 0 < d)
    (hupper : X < U * d)
    (hproduct : t * d ^ 2 ≤ g ^ 2 * X ^ 3) :
    t < g ^ 2 * U ^ 3 * d := by
  have hcubeRaw := Nat.pow_lt_pow_left hupper (by norm_num : 3 ≠ 0)
  have hcube : X ^ 3 < U ^ 3 * d ^ 3 := by
    simpa [mul_pow] using hcubeRaw
  have hscaled : g ^ 2 * X ^ 3 < g ^ 2 * (U ^ 3 * d ^ 3) :=
    Nat.mul_lt_mul_of_pos_left hcube (pow_pos hg _)
  have htd : t * d ^ 2 < (g ^ 2 * U ^ 3 * d) * d ^ 2 := by
    calc
      t * d ^ 2 ≤ g ^ 2 * X ^ 3 := hproduct
      _ < g ^ 2 * (U ^ 3 * d ^ 3) := hscaled
      _ = (g ^ 2 * U ^ 3 * d) * d ^ 2 := by ring
  exact Nat.lt_of_mul_lt_mul_right htd

/-- Archimedean bound for the nonzero inner determinant factor. -/
theorem reflected_third_inner_abs_lt
    {C D E : ℤ} {t g X U r d : ℕ}
    (hC : 0 < Int.natAbs C)
    (hupper : X < U * d)
    (ht : t < g ^ 2 * U ^ 3 * d) :
    Int.natAbs
        (C * (t : ℤ) - 8 * D * (X : ℤ) * (g : ℤ) ^ 2 * (r : ℤ) -
          40 * E * (g : ℤ) ^ 2 * (r : ℤ) ^ 2 * (d : ℤ)) <
      (Int.natAbs C * U ^ 3 + 8 * Int.natAbs D * U * r +
        40 * Int.natAbs E * r ^ 2) * g ^ 2 * d := by
  have htri₁ := Int.natAbs_sub_le
    (C * (t : ℤ)) (8 * D * (X : ℤ) * (g : ℤ) ^ 2 * (r : ℤ))
  have htri₂ := Int.natAbs_sub_le
    (C * (t : ℤ) - 8 * D * (X : ℤ) * (g : ℤ) ^ 2 * (r : ℤ))
    (40 * E * (g : ℤ) ^ 2 * (r : ℤ) ^ 2 * (d : ℤ))
  have habs :
      Int.natAbs
          (C * (t : ℤ) - 8 * D * (X : ℤ) * (g : ℤ) ^ 2 * (r : ℤ) -
            40 * E * (g : ℤ) ^ 2 * (r : ℤ) ^ 2 * (d : ℤ)) ≤
        Int.natAbs C * t + 8 * Int.natAbs D * X * g ^ 2 * r +
          40 * Int.natAbs E * g ^ 2 * r ^ 2 * d := by
    calc
      Int.natAbs
          (C * (t : ℤ) - 8 * D * (X : ℤ) * (g : ℤ) ^ 2 * (r : ℤ) -
            40 * E * (g : ℤ) ^ 2 * (r : ℤ) ^ 2 * (d : ℤ)) ≤
          Int.natAbs
              (C * (t : ℤ) - 8 * D * (X : ℤ) * (g : ℤ) ^ 2 * (r : ℤ)) +
            Int.natAbs
              (40 * E * (g : ℤ) ^ 2 * (r : ℤ) ^ 2 * (d : ℤ)) := htri₂
      _ ≤ (Int.natAbs (C * (t : ℤ)) +
            Int.natAbs (8 * D * (X : ℤ) * (g : ℤ) ^ 2 * (r : ℤ))) +
          Int.natAbs (40 * E * (g : ℤ) ^ 2 * (r : ℤ) ^ 2 * (d : ℤ)) :=
        Nat.add_le_add_right htri₁ _
      _ = Int.natAbs C * t + 8 * Int.natAbs D * X * g ^ 2 * r +
          40 * Int.natAbs E * g ^ 2 * r ^ 2 * d := by
        simp [Int.natAbs_mul, Int.natAbs_pow]
  have hmain : Int.natAbs C * t <
      Int.natAbs C * (g ^ 2 * U ^ 3 * d) :=
    Nat.mul_lt_mul_of_pos_left ht hC
  have hlinear : 8 * Int.natAbs D * X * g ^ 2 * r ≤
      8 * Int.natAbs D * (U * d) * g ^ 2 * r := by
    have hraw := Nat.mul_le_mul_right (g ^ 2 * r)
      (Nat.mul_le_mul_left (8 * Int.natAbs D) (Nat.le_of_lt hupper))
    simpa only [mul_assoc] using hraw
  calc
    Int.natAbs
        (C * (t : ℤ) - 8 * D * (X : ℤ) * (g : ℤ) ^ 2 * (r : ℤ) -
          40 * E * (g : ℤ) ^ 2 * (r : ℤ) ^ 2 * (d : ℤ)) ≤
        Int.natAbs C * t + 8 * Int.natAbs D * X * g ^ 2 * r +
          40 * Int.natAbs E * g ^ 2 * r ^ 2 * d := habs
    _ < Int.natAbs C * (g ^ 2 * U ^ 3 * d) +
          8 * Int.natAbs D * (U * d) * g ^ 2 * r +
          40 * Int.natAbs E * g ^ 2 * r ^ 2 * d :=
      Nat.add_lt_add_of_lt_of_le
        (Nat.add_lt_add_of_lt_of_le hmain hlinear) (le_refl _)
    _ = (Int.natAbs C * U ^ 3 + 8 * Int.natAbs D * U * r +
          40 * Int.natAbs E * r ^ 2) * g ^ 2 * d := by ring

/-- Endpoint-square divisibility and a nonzero determinant turn any strict
absolute determinant bound into the corresponding endpoint product bound. -/
theorem reflected_endpoint_square_product_lt_of_determinant
    {Q R K g d : ℕ} {det : ℤ}
    (hdiv : (Q : ℤ) ^ 2 * (R : ℤ) ^ 2 ∣ det)
    (hne : det ≠ 0)
    (hsize : Int.natAbs det < K * g ^ 2 * d) :
    Q ^ 2 * R ^ 2 < K * g ^ 2 * d := by
  have hdivNat : Q ^ 2 * R ^ 2 ∣ Int.natAbs det := by
    have hraw := Int.natAbs_dvd_natAbs.mpr hdiv
    simpa [Int.natAbs_mul, Int.natAbs_pow] using hraw
  have habsPos : 0 < Int.natAbs det := Int.natAbs_pos.mpr hne
  exact lt_of_le_of_lt (Nat.le_of_dvd habsPos hdivNat) hsize

/-- Table-based upper bound for the absolute reflected determinant. -/
def targetReflectedDeterminantBound (k r : ℕ) : ℕ :=
  let i := (k + 1) / 2 - r
  let C := Int.natAbs (secondCoefficientTable k i).1
  let D := Int.natAbs (secondCoefficientTable k i).2
  let E := Int.natAbs (thirdCoefficientTable k i)
  let U := targetReflectedResidualCeiling k
  54 * r * (C * U ^ 3 + 8 * D * U * r + 40 * E * r ^ 2)

/-- Center cubic coefficient in the existing raw center lift. -/
def targetReflectedCenterCubeBound (k : ℕ) : ℕ :=
  (((k - 1) / 2).factorial) ^ 2 * targetReflectedResidualCeiling k

/-- Every target-row residual is positive and lies below the row ceiling at
the upgraded odd-tail scale. -/
theorem target_reflected_residual_window_tail1000
    {k n d i : ℕ}
    (hk : k = 5 ∨ k = 7 ∨ k = 9 ∨ k = 11 ∨ k = 13 ∨ k = 15)
    (hi : i ∈ Finset.Icc 1 k)
    (htail : 10 ^ 1000 ≤ d)
    (heq : blockProduct k (n + d) = 4 * blockProduct k n) :
    0 < localResidual n d i ∧
      localResidual n d i < targetReflectedResidualCeiling k * d := by
  have hkd : k ≤ d := by
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
      norm_num at htail ⊢ <;> omega
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl
  · simpa [targetReflectedResidualCeiling] using
      (localResidual_pos_lt_of_base_bound (by norm_num) hkd hi heq
        (row_base_upper_k5 (ratio_window_four_nat heq).2) (by norm_num))
  · simpa [targetReflectedResidualCeiling] using
      (localResidual_pos_lt_of_base_bound (by norm_num) hkd hi heq
        (row_base_upper_k7 (ratio_window_four_nat heq).2) (by norm_num))
  · simpa [targetReflectedResidualCeiling] using
      (localResidual_pos_lt_of_base_bound (by norm_num) hkd hi heq
        (row_base_upper_k9 (ratio_window_four_nat heq).2) (by norm_num))
  · simpa [targetReflectedResidualCeiling] using
      (localResidual_pos_lt_of_base_bound (by norm_num) hkd hi heq
        (row_base_upper_k11 (ratio_window_four_nat heq).2) (by norm_num))
  · simpa [targetReflectedResidualCeiling] using
      (localResidual_pos_lt_of_base_bound (by norm_num) hkd hi heq
        (row_base_upper_k13 (ratio_window_four_nat heq).2) (by norm_num))
  · simpa [targetReflectedResidualCeiling] using
      (localResidual_pos_lt_of_base_bound (by norm_num) hkd hi heq
        (row_base_upper_k15 (ratio_window_four_nat heq).2) (by norm_num))

/-- Reflection fixes the even Taylor coefficients and negates the odd linear
coefficient at every target center/reflected pair. -/
theorem target_reflected_coefficient_symmetry
    {k r : ℕ}
    (hk : k = 5 ∨ k = 7 ∨ k = 9 ∨ k = 11 ∨ k = 13 ∨ k = 15)
    (hr : 1 ≤ r ∧ r < (k + 1) / 2) :
    let left := (k + 1) / 2 - r
    let right := (k + 1) / 2 + r
    localSecondConstant k right = localSecondConstant k left ∧
      localSecondLinear k right = -localSecondLinear k left ∧
      localThirdQuadratic k right = localThirdQuadratic k left := by
  have hleft : (k + 1) / 2 - r ∈ Finset.Icc 1 k := by
    rw [Finset.mem_Icc]
    constructor <;> omega
  have hright : (k + 1) / 2 + r ∈ Finset.Icc 1 k := by
    rw [Finset.mem_Icc]
    constructor <;> omega
  dsimp
  rw [localSecondConstant_eq_table hk hright,
    localSecondConstant_eq_table hk hleft,
    localSecondLinear_eq_table hk hright,
    localSecondLinear_eq_table hk hleft,
    localThirdQuadratic_eq_table hk hright,
    localThirdQuadratic_eq_table hk hleft]
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hr with ⟨hr1, hrlt⟩ <;>
    interval_cases r <;>
    norm_num [secondCoefficientTable, thirdCoefficientTable] at *

/-- Normalize the table definition of the determinant constant to the local
coefficients at the left endpoint. -/
theorem target_reflected_determinant_bound_eq
    {k r : ℕ}
    (hk : k = 5 ∨ k = 7 ∨ k = 9 ∨ k = 11 ∨ k = 13 ∨ k = 15)
    (hr : 1 ≤ r ∧ r < (k + 1) / 2) :
    let left := (k + 1) / 2 - r
    targetReflectedDeterminantBound k r =
      54 * r *
        (Int.natAbs (localSecondConstant k left) *
            targetReflectedResidualCeiling k ^ 3 +
          8 * Int.natAbs (localSecondLinear k left) *
            targetReflectedResidualCeiling k * r +
          40 * Int.natAbs (localThirdQuadratic k left) * r ^ 2) := by
  have hleft : (k + 1) / 2 - r ∈ Finset.Icc 1 k := by
    rw [Finset.mem_Icc]
    constructor <;> omega
  dsimp [targetReflectedDeterminantBound]
  rw [localSecondConstant_eq_table hk hleft,
    localSecondLinear_eq_table hk hleft,
    localThirdQuadratic_eq_table hk hleft]

/-- Equation-facing center cubic bound for the supplied cleaned center
bucket. -/
theorem target_reflected_center_cube_bound_tail1000
    {k n d g P Q R : ℕ}
    (hk : k = 5 ∨ k = 7 ∨ k = 9 ∨ k = 11 ∨ k = 13 ∨ k = 15)
    (htail : 10 ^ 1000 ≤ d)
    (hgap : d = g * P * Q * R)
    (hcenterFactor : P ∣ n + (k + 1) / 2)
    (heq : blockProduct k (n + d) = 4 * blockProduct k n) :
    P ^ 3 < targetReflectedCenterCubeBound k * d := by
  have hkd : k ≤ d := by
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
      norm_num at htail ⊢ <;> omega
  have hPdvd : P ∣ d := by
    refine ⟨g * Q * R, ?_⟩
    rw [hgap]
    ring
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl
  · simpa [targetReflectedCenterCubeBound,
      targetReflectedResidualCeiling] using
      (center_raw_cube_lt_factorial_sq_mul
        (h := P) (r := 2) (C := 4) (A := 14)
        (by norm_num) hkd heq
        (row_base_upper_k5 (ratio_window_four_nat heq).2)
        (by norm_num) hPdvd hcenterFactor)
  · simpa [targetReflectedCenterCubeBound,
      targetReflectedResidualCeiling] using
      (center_raw_cube_lt_factorial_sq_mul
        (h := P) (r := 3) (C := 5) (A := 17)
        (by norm_num) hkd heq
        (row_base_upper_k7 (ratio_window_four_nat heq).2)
        (by norm_num) hPdvd hcenterFactor)
  · simpa [targetReflectedCenterCubeBound,
      targetReflectedResidualCeiling] using
      (center_raw_cube_lt_factorial_sq_mul
        (h := P) (r := 4) (C := 7) (A := 23)
        (by norm_num) hkd heq
        (row_base_upper_k9 (ratio_window_four_nat heq).2)
        (by norm_num) hPdvd hcenterFactor)
  · simpa [targetReflectedCenterCubeBound,
      targetReflectedResidualCeiling] using
      (center_raw_cube_lt_factorial_sq_mul
        (h := P) (r := 5) (C := 8) (A := 26)
        (by norm_num) hkd heq
        (row_base_upper_k11 (ratio_window_four_nat heq).2)
        (by norm_num) hPdvd hcenterFactor)
  · simpa [targetReflectedCenterCubeBound,
      targetReflectedResidualCeiling] using
      (center_raw_cube_lt_factorial_sq_mul
        (h := P) (r := 6) (C := 9) (A := 29)
        (by norm_num) hkd heq
        (row_base_upper_k13 (ratio_window_four_nat heq).2)
        (by norm_num) hPdvd hcenterFactor)
  · simpa [targetReflectedCenterCubeBound,
      targetReflectedResidualCeiling] using
      (center_raw_cube_lt_factorial_sq_mul
        (h := P) (r := 7) (C := 11) (A := 35)
        (by norm_num) hkd heq
        (row_base_upper_k15 (ratio_window_four_nat heq).2)
        (by norm_num) hPdvd hcenterFactor)

/-- Exactly the reflected positions closed by the determinant-plus-center
packing inequality at the `10^120` cutoff. -/
def targetReflectedPackingClosed (k r : ℕ) : Prop :=
  (k = 5 ∧ 1 ≤ r ∧ r ≤ 2) ∨
  (k = 7 ∧ 1 ≤ r ∧ r ≤ 3) ∨
  (k = 9 ∧ 1 ≤ r ∧ r ≤ 4) ∨
  (k = 11 ∧ 1 ≤ r ∧ r ≤ 3)

/-- Exact-arithmetic cutoff certificate for the 12 closed reflected pairs. -/
theorem target_reflected_packing_cutoff_certificate
    {k r : ℕ} (hclosed : targetReflectedPackingClosed k r) :
    targetReflectedCenterCubeBound k ^ 2 *
        targetReflectedDeterminantBound k r ^ 3 *
        targetAggregateLoss k ^ 12 < 10 ^ 120 := by
  rcases hclosed with ⟨rfl, hr1, hru⟩ | ⟨rfl, hr1, hru⟩ |
      ⟨rfl, hr1, hru⟩ | ⟨rfl, hr1, hru⟩ <;>
    interval_cases r <;>
    norm_num [targetReflectedCenterCubeBound,
      targetReflectedDeterminantBound, targetReflectedResidualCeiling,
      secondCoefficientTable, thirdCoefficientTable, targetAggregateLoss] at *

/-- At the upgraded `10^1000` odd-tail cutoff, every one of the 27
center/reflected pairs satisfies the determinant-packing numerical bound.
The finite calculation first proves the stronger uniform bound `10^200`. -/
theorem target_reflected_packing_cutoff_certificate_tail1000
    {k r : ℕ}
    (hk : k = 5 ∨ k = 7 ∨ k = 9 ∨ k = 11 ∨ k = 13 ∨ k = 15)
    (hr : 1 ≤ r ∧ r < (k + 1) / 2) :
    targetReflectedCenterCubeBound k ^ 2 *
        targetReflectedDeterminantBound k r ^ 3 *
        targetAggregateLoss k ^ 12 < 10 ^ 1000 := by
  have hsmall : targetReflectedCenterCubeBound k ^ 2 *
        targetReflectedDeterminantBound k r ^ 3 *
        targetAggregateLoss k ^ 12 < 10 ^ 200 := by
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hr with ⟨hr1, hrlt⟩ <;>
      interval_cases r <;>
      norm_num [targetReflectedCenterCubeBound,
        targetReflectedDeterminantBound, targetReflectedResidualCeiling,
        secondCoefficientTable, thirdCoefficientTable, targetAggregateLoss] at *
  exact lt_of_lt_of_le hsmall
    (Nat.pow_le_pow_right (by norm_num : 0 < 10) (by omega))

/-- Pure packing step: a center cubic bound and a reflected endpoint-square
bound contradict the target cutoff. -/
theorem no_reflected_three_bucket_of_packing_bounds
    {d g P Q R H K G target : ℕ}
    (hd : 0 < d) (hg : 0 < g) (hP : 0 < P) (hQ : 0 < Q) (hR : 0 < R)
    (hgap : d = g * P * Q * R)
    (hcenter : P ^ 3 < H * d)
    (hendpoints : Q ^ 2 * R ^ 2 < K * g ^ 2 * d)
    (hloss : g ≤ G)
    (hcutoff : H ^ 2 * K ^ 3 * G ^ 12 < target)
    (htarget : target ≤ d) : False := by
  have hcenterSq := Nat.pow_lt_pow_left hcenter (by norm_num : 2 ≠ 0)
  have hcenterSq' : P ^ 6 < (H * d) ^ 2 := by
    convert hcenterSq using 1 <;> ring
  have hendpointsCube :=
    Nat.pow_lt_pow_left hendpoints (by norm_num : 3 ≠ 0)
  have hprod :
      P ^ 6 * (Q ^ 2 * R ^ 2) ^ 3 <
        (H * d) ^ 2 * (K * g ^ 2 * d) ^ 3 := by
    exact mul_lt_mul hcenterSq' (Nat.le_of_lt hendpointsCube)
      (pow_pos (Nat.mul_pos (pow_pos hQ 2) (pow_pos hR 2)) 3)
      (Nat.zero_le _)
  have hgScaled := Nat.mul_lt_mul_of_pos_left hprod (pow_pos hg 6)
  have hdPower : d ^ 6 < H ^ 2 * K ^ 3 * g ^ 12 * d ^ 5 := by
    calc
      d ^ 6 = g ^ 6 * (P ^ 6 * (Q ^ 2 * R ^ 2) ^ 3) := by
        rw [hgap]
        ring
      _ < g ^ 6 * ((H * d) ^ 2 * (K * g ^ 2 * d) ^ 3) := hgScaled
      _ = H ^ 2 * K ^ 3 * g ^ 12 * d ^ 5 := by ring
  have hdBound : d < H ^ 2 * K ^ 3 * g ^ 12 := by
    apply Nat.lt_of_mul_lt_mul_right
    calc
      d * d ^ 5 = d ^ 6 := by ring
      _ < H ^ 2 * K ^ 3 * g ^ 12 * d ^ 5 := hdPower
      _ = (H ^ 2 * K ^ 3 * g ^ 12) * d ^ 5 := by ring
  have hgPow : g ^ 12 ≤ G ^ 12 := Nat.pow_le_pow_left hloss 12
  have hconst : H ^ 2 * K ^ 3 * g ^ 12 ≤ H ^ 2 * K ^ 3 * G ^ 12 :=
    Nat.mul_le_mul_left (H ^ 2 * K ^ 3) hgPow
  have : d < d :=
    lt_of_lt_of_le (lt_trans hdBound (lt_of_le_of_lt hconst hcutoff)) htarget
  exact (Nat.lt_irrefl d this)

/-- The generic reflected packing interface contradicts the upgraded odd
tail cutoff in every target center/reflected position. -/
theorem no_reflected_three_bucket_tail1000_of_packing_bounds
    {k r d g P Q R : ℕ}
    (hk : k = 5 ∨ k = 7 ∨ k = 9 ∨ k = 11 ∨ k = 13 ∨ k = 15)
    (hr : 1 ≤ r ∧ r < (k + 1) / 2)
    (hd : 0 < d) (hg : 0 < g) (hP : 0 < P) (hQ : 0 < Q) (hR : 0 < R)
    (hgap : d = g * P * Q * R)
    (hcenter : P ^ 3 < targetReflectedCenterCubeBound k * d)
    (hendpoints : Q ^ 2 * R ^ 2 <
      targetReflectedDeterminantBound k r * g ^ 2 * d)
    (hloss : g ≤ targetAggregateLoss k)
    (htail : 10 ^ 1000 ≤ d) : False := by
  exact no_reflected_three_bucket_of_packing_bounds
    hd hg hP hQ hR hgap hcenter hendpoints hloss
    (target_reflected_packing_cutoff_certificate_tail1000 hk hr) htail

/-- The equation and a supplied center/reflected three-bucket decomposition
produce both endpoint square divisibilities; these are not assumptions of the
final packing theorem. -/
theorem target_reflected_endpoint_third_divisibilities_tail1000
    {k n d r g P Q R a b c : ℕ}
    (hk : k = 5 ∨ k = 7 ∨ k = 9 ∨ k = 11 ∨ k = 13 ∨ k = 15)
    (hr : 1 ≤ r ∧ r < (k + 1) / 2)
    (htail : 10 ^ 1000 ≤ d)
    (hQpos : 0 < Q) (hRpos : 0 < R)
    (hgap : d = g * P * Q * R)
    (hcenterRes : localResidual n d ((k + 1) / 2) = a * P ^ 2)
    (hleftRes : localResidual n d ((k + 1) / 2 - r) = b * Q ^ 2)
    (hrightRes : localResidual n d ((k + 1) / 2 + r) = c * R ^ 2)
    (hleftFactor : Q ∣ n + ((k + 1) / 2 - r))
    (hrightFactor : R ∣ n + ((k + 1) / 2 + r))
    (heq : blockProduct k (n + d) = 4 * blockProduct k n) :
    let left := (k + 1) / 2 - r
    let C := localSecondConstant k left
    let D := localSecondLinear k left
    let E := localThirdQuadratic k left
    (Q : ℤ) ^ 2 ∣ reflectedLeftThird C D E (a * b * c) g r d ∧
      (R : ℤ) ^ 2 ∣ reflectedRightThird C D E (a * b * c) g r d := by
  let center := (k + 1) / 2
  let left := center - r
  let right := center + r
  have hcenterIdx : center ∈ Finset.Icc 1 k := by
    dsimp [center]
    rw [Finset.mem_Icc]
    constructor <;> omega
  have hleftIdx : left ∈ Finset.Icc 1 k := by
    dsimp [left, center]
    rw [Finset.mem_Icc]
    constructor <;> omega
  have hrightIdx : right ∈ Finset.Icc 1 k := by
    dsimp [right, center]
    rw [Finset.mem_Icc]
    constructor <;> omega
  have hcenterPos :=
    (target_reflected_residual_window_tail1000 hk hcenterIdx htail heq).1
  have hleftPos :=
    (target_reflected_residual_window_tail1000 hk hleftIdx htail heq).1
  have hrightPos :=
    (target_reflected_residual_window_tail1000 hk hrightIdx htail heq).1
  have hcenterCast :
      3 * ((n + center : ℕ) : ℤ) - (d : ℤ) =
        (a : ℤ) * (P : ℤ) ^ 2 := by
    have hdle : d ≤ 3 * (n + center) := by
      unfold localResidual at hcenterPos
      omega
    have hcast : ((localResidual n d center : ℕ) : ℤ) =
        3 * ((n + center : ℕ) : ℤ) - (d : ℤ) := by
      unfold localResidual
      rw [Int.ofNat_sub hdle]
      push_cast
      ring
    rw [← hcast]
    exact_mod_cast hcenterRes
  have hleftCast :
      3 * ((n + left : ℕ) : ℤ) - (d : ℤ) =
        (b : ℤ) * (Q : ℤ) ^ 2 := by
    have hdle : d ≤ 3 * (n + left) := by
      unfold localResidual at hleftPos
      omega
    have hcast : ((localResidual n d left : ℕ) : ℤ) =
        3 * ((n + left : ℕ) : ℤ) - (d : ℤ) := by
      unfold localResidual
      rw [Int.ofNat_sub hdle]
      push_cast
      ring
    rw [← hcast]
    exact_mod_cast hleftRes
  have hrightCast :
      3 * ((n + right : ℕ) : ℤ) - (d : ℤ) =
        (c : ℤ) * (R : ℤ) ^ 2 := by
    have hdle : d ≤ 3 * (n + right) := by
      unfold localResidual at hrightPos
      omega
    have hcast : ((localResidual n d right : ℕ) : ℤ) =
        3 * ((n + right : ℕ) : ℤ) - (d : ℤ) := by
      unfold localResidual
      rw [Int.ofNat_sub hdle]
      push_cast
      ring
    rw [← hcast]
    exact_mod_cast hrightRes
  have hgapQ : d = Q * (g * P * R) := by rw [hgap]; ring
  have hgapR : d = R * (g * P * Q) := by rw [hgap]; ring
  have hthirdQ := third_order_local_lift
    (k := k) (n := n) (d := d) (i := left)
    (h := Q) (m := g * P * R) (a := b)
    hleftIdx hQpos hgapQ hleftFactor hleftCast heq
  have hthirdR := third_order_local_lift
    (k := k) (n := n) (d := d) (i := right)
    (h := R) (m := g * P * Q) (a := c)
    hrightIdx hRpos hgapR hrightFactor hrightCast heq
  have hleftCenter : (left : ℤ) - (center : ℤ) = -(r : ℤ) := by
    dsimp [left]
    push_cast
    omega
  have hleftRight : (left : ℤ) - (right : ℤ) = -2 * (r : ℤ) := by
    dsimp [left, right]
    push_cast
    omega
  have hrightCenter : (right : ℤ) - (center : ℤ) = (r : ℤ) := by
    dsimp [right]
    push_cast
    omega
  have hrightLeft : (right : ℤ) - (left : ℤ) = 2 * (r : ℤ) := by
    dsimp [right, left]
    push_cast
    omega
  have hleftDiffCenter :
      (b : ℤ) * (Q : ℤ) ^ 2 - (a : ℤ) * (P : ℤ) ^ 2 =
        3 * ((left : ℤ) - (center : ℤ)) := by
    rw [← hleftCast, ← hcenterCast]
    push_cast
    ring
  have hleftDiffRight :
      (b : ℤ) * (Q : ℤ) ^ 2 - (c : ℤ) * (R : ℤ) ^ 2 =
        3 * ((left : ℤ) - (right : ℤ)) := by
    rw [← hleftCast, ← hrightCast]
    push_cast
    ring
  have hrightDiffCenter :
      (c : ℤ) * (R : ℤ) ^ 2 - (a : ℤ) * (P : ℤ) ^ 2 =
        3 * ((right : ℤ) - (center : ℤ)) := by
    rw [← hrightCast, ← hcenterCast]
    push_cast
    ring
  have hrightDiffLeft :
      (c : ℤ) * (R : ℤ) ^ 2 - (b : ℤ) * (Q : ℤ) ^ 2 =
        3 * ((right : ℤ) - (left : ℤ)) := by
    rw [← hrightCast, ← hleftCast]
    push_cast
    ring
  have hcompQ := three_bucket_third_obstruction_dvd_sq
    (P := (Q : ℤ)) (Q := (P : ℤ)) (R := (R : ℤ))
    (a := (b : ℤ)) (b := (a : ℤ)) (c := (c : ℤ))
    (g := (g : ℤ))
    (C := localSecondConstant k left)
    (D := localSecondLinear k left)
    (E := localThirdQuadratic k left)
    (deltaLeft := (left : ℤ) - (center : ℤ))
    (deltaRight := (left : ℤ) - (right : ℤ))
    hthirdQ hleftDiffCenter hleftDiffRight
  have hcompR := three_bucket_third_obstruction_dvd_sq
    (P := (R : ℤ)) (Q := (P : ℤ)) (R := (Q : ℤ))
    (a := (c : ℤ)) (b := (a : ℤ)) (c := (b : ℤ))
    (g := (g : ℤ))
    (C := localSecondConstant k right)
    (D := localSecondLinear k right)
    (E := localThirdQuadratic k right)
    (deltaLeft := (right : ℤ) - (center : ℤ))
    (deltaRight := (right : ℤ) - (left : ℤ))
    hthirdR hrightDiffCenter hrightDiffLeft
  have hgapCast : (d : ℤ) = (g : ℤ) * (P : ℤ) * (Q : ℤ) * (R : ℤ) := by
    exact_mod_cast hgap
  have hgapQCast : (g : ℤ) * (Q : ℤ) * (P : ℤ) * (R : ℤ) = (d : ℤ) := by
    rw [hgapCast]
    ring
  have hgapRCast : (g : ℤ) * (R : ℤ) * (P : ℤ) * (Q : ℤ) = (d : ℤ) := by
    rw [hgapCast]
    ring
  have hsym := target_reflected_coefficient_symmetry hk hr
  dsimp [left, right, center] at hsym ⊢
  constructor
  · convert hcompQ using 1 <;>
      rw [hleftCenter, hleftRight, hgapQCast] <;>
      simp [threeBucketThirdObstruction, threeBucketSecondObstruction,
        reflectedLeftThird, left, center] <;> ring
  · rw [hsym.1, hsym.2.1, hsym.2.2] at hcompR
    convert hcompR using 1 <;>
      rw [hrightCenter, hrightLeft, hgapRCast] <;>
      simp [threeBucketThirdObstruction, threeBucketSecondObstruction,
        reflectedRightThird] <;> ring

/-- No target-row quotient-four equation at the upgraded odd-tail scale can
carry a supplied exact cleaned decomposition whose three buckets lie at the
center and one reflected owner pair.  The center and endpoint packing bounds
are derived here from the equation and local lifts. -/
theorem no_four_solution_of_exact_center_reflected_three_bucket_tail1000
    {k n d r g P Q R a b c : ℕ}
    (hk : k = 5 ∨ k = 7 ∨ k = 9 ∨ k = 11 ∨ k = 13 ∨ k = 15)
    (hr : 1 ≤ r ∧ r < (k + 1) / 2)
    (htail : 10 ^ 1000 ≤ d)
    (hgpos : 0 < g) (hPpos : 0 < P) (hQpos : 0 < Q) (hRpos : 0 < R)
    (hgap : d = g * P * Q * R)
    (hloss : g ≤ targetAggregateLoss k)
    (hcenterFactor : P ∣ n + (k + 1) / 2)
    (hleftFactor : Q ∣ n + ((k + 1) / 2 - r))
    (hrightFactor : R ∣ n + ((k + 1) / 2 + r))
    (hcenterRes : localResidual n d ((k + 1) / 2) = a * P ^ 2)
    (hleftRes : localResidual n d ((k + 1) / 2 - r) = b * Q ^ 2)
    (hrightRes : localResidual n d ((k + 1) / 2 + r) = c * R ^ 2)
    (heq : blockProduct k (n + d) = 4 * blockProduct k n) : False := by
  let center := (k + 1) / 2
  let left := center - r
  let right := center + r
  let X := localResidual n d center
  let C := localSecondConstant k left
  let D := localSecondLinear k left
  let E := localThirdQuadratic k left
  let t := a * b * c
  let inner : ℤ := C * (t : ℤ) -
    8 * D * (X : ℤ) * (g : ℤ) ^ 2 * (r : ℤ) -
    40 * E * (g : ℤ) ^ 2 * (r : ℤ) ^ 2 * (d : ℤ)
  let det : ℤ :=
    ((X : ℤ) - 3 * (r : ℤ)) *
        reflectedRightThird C D E (t : ℤ) (g : ℤ) (r : ℤ) (d : ℤ) -
      ((X : ℤ) + 3 * (r : ℤ)) *
        reflectedLeftThird C D E (t : ℤ) (g : ℤ) (r : ℤ) (d : ℤ)
  have hcenterIdx : center ∈ Finset.Icc 1 k := by
    dsimp [center]
    rw [Finset.mem_Icc]
    constructor <;> omega
  have hleftIdx : left ∈ Finset.Icc 1 k := by
    dsimp [left, center]
    rw [Finset.mem_Icc]
    constructor <;> omega
  have hrightIdx : right ∈ Finset.Icc 1 k := by
    dsimp [right, center]
    rw [Finset.mem_Icc]
    constructor <;> omega
  have hcenterWindow :=
    target_reflected_residual_window_tail1000 hk hcenterIdx htail heq
  have hleftWindow :=
    target_reflected_residual_window_tail1000 hk hleftIdx htail heq
  have hrightWindow :=
    target_reflected_residual_window_tail1000 hk hrightIdx htail heq
  have hresidualCast : ∀ i, i ∈ Finset.Icc 1 k →
      ((localResidual n d i : ℕ) : ℤ) =
        3 * ((n + i : ℕ) : ℤ) - (d : ℤ) := by
    intro i hi
    have hpos := (target_reflected_residual_window_tail1000 hk hi htail heq).1
    have hdle : d ≤ 3 * (n + i) := by
      unfold localResidual at hpos
      omega
    unfold localResidual
    rw [Int.ofNat_sub hdle]
    push_cast
    ring
  have hcenterCast : (X : ℤ) = (a : ℤ) * (P : ℤ) ^ 2 := by
    exact_mod_cast hcenterRes
  have hcenterFormula := hresidualCast center hcenterIdx
  have hleftFormula := hresidualCast left hleftIdx
  have hrightFormula := hresidualCast right hrightIdx
  have hleftDecomp : ((localResidual n d left : ℕ) : ℤ) =
      (b : ℤ) * (Q : ℤ) ^ 2 := by
    exact_mod_cast hleftRes
  have hrightDecomp : ((localResidual n d right : ℕ) : ℤ) =
      (c : ℤ) * (R : ℤ) ^ 2 := by
    exact_mod_cast hrightRes
  have hleftCast :
      (X : ℤ) - 3 * (r : ℤ) = (b : ℤ) * (Q : ℤ) ^ 2 := by
    have hrel : (center : ℤ) - (left : ℤ) = (r : ℤ) := by
      dsimp [left]
      push_cast
      omega
    calc
      (X : ℤ) - 3 * (r : ℤ) =
          ((localResidual n d center : ℕ) : ℤ) - 3 * (r : ℤ) := by rfl
      _ = ((localResidual n d left : ℕ) : ℤ) := by
        rw [hcenterFormula, hleftFormula]
        push_cast
        linear_combination 3 * hrel
      _ = (b : ℤ) * (Q : ℤ) ^ 2 := hleftDecomp
  have hrightCast :
      (X : ℤ) + 3 * (r : ℤ) = (c : ℤ) * (R : ℤ) ^ 2 := by
    have hrel : (right : ℤ) - (center : ℤ) = (r : ℤ) := by
      dsimp [right]
      push_cast
      omega
    calc
      (X : ℤ) + 3 * (r : ℤ) =
          ((localResidual n d center : ℕ) : ℤ) + 3 * (r : ℤ) := by rfl
      _ = ((localResidual n d right : ℕ) : ℤ) := by
        rw [hcenterFormula, hrightFormula]
        push_cast
        linear_combination -3 * hrel
      _ = (c : ℤ) * (R : ℤ) ^ 2 := hrightDecomp
  have hgapCast : (d : ℤ) = (g : ℤ) * (P : ℤ) * (Q : ℤ) * (R : ℤ) := by
    exact_mod_cast hgap
  have hproduct : (t : ℤ) * (d : ℤ) ^ 2 =
      (g : ℤ) ^ 2 * (X : ℤ) *
        ((X : ℤ) ^ 2 - 9 * (r : ℤ) ^ 2) := by
    simpa [t] using reflected_three_bucket_product_identity
      hcenterCast hleftCast hrightCast hgapCast
  have hcenterNat : X = a * P ^ 2 := by simpa [X, center] using hcenterRes
  have hleftNat : localResidual n d left = b * Q ^ 2 := by
    simpa [left, center] using hleftRes
  have hrightNat : localResidual n d right = c * R ^ 2 := by
    simpa [right, center] using hrightRes
  have hleftLinear : localResidual n d left + 3 * r = X := by
    have hcast : ((localResidual n d left : ℕ) : ℤ) + 3 * (r : ℤ) =
        (X : ℤ) := by
      rw [hleftDecomp]
      linarith [hleftCast]
    exact_mod_cast hcast
  have hrightLinear : localResidual n d right = X + 3 * r := by
    have hcast : ((localResidual n d right : ℕ) : ℤ) =
        (X : ℤ) + 3 * (r : ℤ) := by
      rw [hrightDecomp]
      linarith [hrightCast]
    exact_mod_cast hcast
  have hpair :
      localResidual n d left * localResidual n d right ≤ X ^ 2 := by
    have heqPair :
        localResidual n d left * localResidual n d right + (3 * r) ^ 2 =
          X ^ 2 := by
      rw [hrightLinear, ← hleftLinear]
      ring
    omega
  have hproductNat : t * d ^ 2 =
      g ^ 2 * X *
        (localResidual n d left * localResidual n d right) := by
    calc
      t * d ^ 2 = (a * b * c) * (g * P * Q * R) ^ 2 := by
        rw [hgap]
      _ = g ^ 2 * (a * P ^ 2) * ((b * Q ^ 2) * (c * R ^ 2)) := by ring
      _ = g ^ 2 * X *
          (localResidual n d left * localResidual n d right) := by
        rw [hcenterNat, hleftNat, hrightNat]
  have hproductLe : t * d ^ 2 ≤ g ^ 2 * X ^ 3 := by
    rw [hproductNat]
    have hscaled := Nat.mul_le_mul_left (g ^ 2 * X) hpair
    convert hscaled using 1 <;> ring
  have hdpos : 0 < d := lt_of_lt_of_le (by norm_num) htail
  have htBound : t < g ^ 2 * targetReflectedResidualCeiling k ^ 3 * d :=
    reflected_cofactor_product_lt hgpos hdpos
      (by simpa [X, center] using hcenterWindow.2) hproductLe
  have hd120 : 10 ^ 120 ≤ d := by
    exact le_trans
      (Nat.pow_le_pow_right (by norm_num : 0 < 10) (by omega : 120 ≤ 1000))
      htail
  have hinnerNe : inner ≠ 0 := by
    have hraw := target_reflected_third_inner_ne_zero hk hr hd120 hgpos heq
      (by simpa [X, center] using hcenterWindow.2) hproduct
    simpa only [inner, C, D, E, t, X, left, center] using hraw
  have hCpos : 0 < Int.natAbs C := by
    have hcert := target_reflected_cubic_coefficient_certificate hk hr
    simpa only [C, left, center] using hcert.1
  have hinnerSize : Int.natAbs inner <
      (Int.natAbs C * targetReflectedResidualCeiling k ^ 3 +
        8 * Int.natAbs D * targetReflectedResidualCeiling k * r +
        40 * Int.natAbs E * r ^ 2) * g ^ 2 * d := by
    simpa [inner, C, D, E, t, X] using
      (reflected_third_inner_abs_lt hCpos
        (by simpa [X, center] using hcenterWindow.2) htBound)
  have hthird := target_reflected_endpoint_third_divisibilities_tail1000
    hk hr htail hQpos hRpos hgap hcenterRes hleftRes hrightRes
      hleftFactor hrightFactor heq
  have hdiv : (Q : ℤ) ^ 2 * (R : ℤ) ^ 2 ∣ det := by
    have hraw := reflected_third_determinant_dvd_endpoint_squares
      hleftCast hrightCast hthird.1 hthird.2
    simpa [det, C, D, E, t] using hraw
  have hdetIdentity : det = 54 * (r : ℤ) * inner := by
    simpa [det, inner, C, D, E, t] using
      reflected_third_determinant_identity C D E (t : ℤ) (g : ℤ)
        (r : ℤ) (d : ℤ) (X : ℤ)
  have hdetNe : det ≠ 0 := by
    rw [hdetIdentity]
    exact mul_ne_zero (mul_ne_zero (by norm_num)
      (by exact_mod_cast (Nat.ne_of_gt hr.1))) hinnerNe
  have hdetSize : Int.natAbs det <
      targetReflectedDeterminantBound k r * g ^ 2 * d := by
    have hscale : (54 * r) * Int.natAbs inner <
        (54 * r) *
          ((Int.natAbs C * targetReflectedResidualCeiling k ^ 3 +
            8 * Int.natAbs D * targetReflectedResidualCeiling k * r +
            40 * Int.natAbs E * r ^ 2) * g ^ 2 * d) :=
      Nat.mul_lt_mul_of_pos_left hinnerSize
        (Nat.mul_pos (by norm_num : 0 < 54) hr.1)
    rw [target_reflected_determinant_bound_eq hk hr]
    rw [hdetIdentity, Int.natAbs_mul, Int.natAbs_mul]
    norm_num
    simpa [mul_assoc] using hscale
  have hendpoints : Q ^ 2 * R ^ 2 <
      targetReflectedDeterminantBound k r * g ^ 2 * d :=
    reflected_endpoint_square_product_lt_of_determinant hdiv hdetNe hdetSize
  have hcenterBound : P ^ 3 < targetReflectedCenterCubeBound k * d :=
    target_reflected_center_cube_bound_tail1000 hk htail hgap hcenterFactor heq
  exact no_reflected_three_bucket_tail1000_of_packing_bounds
    hk hr hdpos hgpos hPpos hQpos hRpos hgap hcenterBound hendpoints hloss htail

#print axioms three_bucket_reduced_fifth_center_reflected
#print axioms reflected_third_determinant_identity
#print axioms reflected_third_determinant_dvd_endpoint_squares
#print axioms reflected_three_bucket_product_identity
#print axioms reflected_inner_zero_forces_cubic_zero
#print axioms reflected_cubic_abs_domination_nat
#print axioms reflected_cubic_ne_zero_of_abs_domination
#print axioms target_reflected_cubic_coefficient_certificate
#print axioms target_reflected_cubic_ne_zero
#print axioms target_reflected_third_inner_ne_zero
#print axioms reflected_cofactor_product_lt
#print axioms reflected_third_inner_abs_lt
#print axioms reflected_endpoint_square_product_lt_of_determinant
#print axioms target_reflected_packing_cutoff_certificate
#print axioms no_reflected_three_bucket_of_packing_bounds
#print axioms target_reflected_packing_cutoff_certificate_tail1000
#print axioms no_reflected_three_bucket_tail1000_of_packing_bounds
#print axioms target_reflected_residual_window_tail1000
#print axioms target_reflected_coefficient_symmetry
#print axioms target_reflected_determinant_bound_eq
#print axioms target_reflected_center_cube_bound_tail1000
#print axioms target_reflected_endpoint_third_divisibilities_tail1000
#print axioms no_four_solution_of_exact_center_reflected_three_bucket_tail1000

end Erdos686Variant
end Erdos686
