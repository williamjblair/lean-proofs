/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import ErdosProblems.Erdos686AllOwnerAssembly
import ErdosProblems.Erdos686ShortWindowQuotient
import ErdosProblems.Erdos686ThreeBucketZeroExclusion

/-!
# Erdős 686: equation-level nonvanishing of third obstructions

The previously banked quotient analysis retained zero branches because it
used only the coarse interval `5d < X_i < A_k d`.  The exact ratio window is
stronger.  In each of the six target rows it gives a row-specific lower
multiple for every local residual.  For three cleaned components this makes
the product cofactor `abc` large enough that the leading term of the composed
third obstruction strictly dominates both Taylor corrections.

The same product argument is even stronger on the complete owner grid.  This
module proves the exact finite coefficient certificate and the generic
integer arithmetic.  It does not claim that nonvanishing alone closes the
remaining short-window branch.
-/

namespace Erdos686
namespace Erdos686Variant

open scoped BigOperators

/-- Row-specific lower multiple forced for `3(n+i)-d` by the exact ratio
window at target size. -/
def targetThirdResidualFloor : ℕ → ℕ
  | 5 => 8
  | 7 => 12
  | 9 => 15
  | 11 => 20
  | 13 => 23
  | 15 => 29
  | _ => 0

/-- Computable finite certificate for domination of both correction terms in
the composed third obstruction. -/
def thirdObstructionNonzeroRowCertificateBool (k : ℕ) : Bool :=
  (List.range (k + 1)).all fun owner =>
    (List.range (k + 1)).all fun left =>
      (List.range (k + 1)).all fun right =>
        decide (
          1 ≤ owner → 1 ≤ left → 1 ≤ right →
          owner ≠ left → owner ≠ right → left ≠ right →
          let C := (secondCoefficientTable k owner).1
          let D := (secondCoefficientTable k owner).2
          let E := thirdCoefficientTable k owner
          let delta := threeBucketOwnerDelta owner left right
          let main := 9 * Int.natAbs C * targetThirdResidualFloor k ^ 3
          let linear := 180 * Int.natAbs (E * delta)
          linear < main ∧
            108 * Int.natAbs (D * delta) <
              10 ^ 120 * (main - linear))

/-- One ordinary-kernel computation checks all 6,210 ordered distinct target
triples. -/
theorem target_third_obstruction_nonzero_table_certificate :
    thirdObstructionNonzeroRowCertificateBool 5 = true ∧
      thirdObstructionNonzeroRowCertificateBool 7 = true ∧
      thirdObstructionNonzeroRowCertificateBool 9 = true ∧
      thirdObstructionNonzeroRowCertificateBool 11 = true ∧
      thirdObstructionNonzeroRowCertificateBool 13 = true ∧
      thirdObstructionNonzeroRowCertificateBool 15 = true := by
  decide

private theorem target_third_obstruction_coefficient_certificate_of_row
    {k owner left right : ℕ}
    (hk : k = 5 ∨ k = 7 ∨ k = 9 ∨ k = 11 ∨ k = 13 ∨ k = 15)
    (hcert : thirdObstructionNonzeroRowCertificateBool k = true)
    (howner : owner ∈ Finset.Icc 1 k)
    (hleft : left ∈ Finset.Icc 1 k)
    (hright : right ∈ Finset.Icc 1 k)
    (hol : owner ≠ left) (hor : owner ≠ right) (hlr : left ≠ right) :
    let C := localSecondConstant k owner
    let D := localSecondLinear k owner
    let E := localThirdQuadratic k owner
    let delta := threeBucketOwnerDelta owner left right
    let main := 9 * Int.natAbs C * targetThirdResidualFloor k ^ 3
    let linear := 180 * Int.natAbs (E * delta)
    linear < main ∧
      108 * Int.natAbs (D * delta) < 10 ^ 120 * (main - linear) := by
  have hownerBounds := Finset.mem_Icc.mp howner
  have hleftBounds := Finset.mem_Icc.mp hleft
  have hrightBounds := Finset.mem_Icc.mp hright
  simp only [thirdObstructionNonzeroRowCertificateBool, List.all_eq_true,
    List.mem_range, decide_eq_true_eq] at hcert
  have hfin := hcert owner (by omega) left (by omega) right (by omega)
    hownerBounds.1 hleftBounds.1 hrightBounds.1 hol hor hlr
  simpa [localSecondConstant_eq_table hk howner,
    localSecondLinear_eq_table hk howner,
    localThirdQuadratic_eq_table hk howner] using hfin

/-- Finite target-row coefficient domination in the definitions used by the
local Taylor lifts. -/
theorem target_third_obstruction_coefficient_certificate
    {k owner left right : ℕ}
    (hk : k = 5 ∨ k = 7 ∨ k = 9 ∨ k = 11 ∨ k = 13 ∨ k = 15)
    (howner : owner ∈ Finset.Icc 1 k)
    (hleft : left ∈ Finset.Icc 1 k)
    (hright : right ∈ Finset.Icc 1 k)
    (hol : owner ≠ left) (hor : owner ≠ right) (hlr : left ≠ right) :
    let C := localSecondConstant k owner
    let D := localSecondLinear k owner
    let E := localThirdQuadratic k owner
    let delta := threeBucketOwnerDelta owner left right
    let main := 9 * Int.natAbs C * targetThirdResidualFloor k ^ 3
    let linear := 180 * Int.natAbs (E * delta)
    linear < main ∧
      108 * Int.natAbs (D * delta) < 10 ^ 120 * (main - linear) := by
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl
  · exact target_third_obstruction_coefficient_certificate_of_row
      (by omega) target_third_obstruction_nonzero_table_certificate.1
      howner hleft hright hol hor hlr
  · exact target_third_obstruction_coefficient_certificate_of_row
      (by omega) target_third_obstruction_nonzero_table_certificate.2.1
      howner hleft hright hol hor hlr
  · exact target_third_obstruction_coefficient_certificate_of_row
      (by omega) target_third_obstruction_nonzero_table_certificate.2.2.1
      howner hleft hright hol hor hlr
  · exact target_third_obstruction_coefficient_certificate_of_row
      (by omega) target_third_obstruction_nonzero_table_certificate.2.2.2.1
      howner hleft hright hol hor hlr
  · exact target_third_obstruction_coefficient_certificate_of_row
      (by omega) target_third_obstruction_nonzero_table_certificate.2.2.2.2.1
      howner hleft hright hol hor hlr
  · exact target_third_obstruction_coefficient_certificate_of_row
      (by omega) target_third_obstruction_nonzero_table_certificate.2.2.2.2.2
      howner hleft hright hol hor hlr

/-- Three residual lower bounds and the exact cleaned gap decomposition give
the required cofactor-product lower bound without division. -/
theorem three_component_cofactor_product_lower
    {L a b c P Q R g d : ℕ}
    (hdpos : 0 < d)
    (hdecomp : d = g * P * Q * R)
    (hP : L * d ≤ a * P ^ 2)
    (hQ : L * d ≤ b * Q ^ 2)
    (hR : L * d ≤ c * R ^ 2) :
    L ^ 3 * g ^ 2 * d ≤ a * b * c := by
  have hprod : (L * d) ^ 3 ≤
      (a * P ^ 2) * (b * Q ^ 2) * (c * R ^ 2) := by
    nlinarith [Nat.mul_le_mul (Nat.mul_le_mul hP hQ) hR]
  have hscaled := Nat.mul_le_mul_left (g ^ 2) hprod
  have hcancel : (L ^ 3 * g ^ 2 * d) * d ^ 2 ≤
      (a * b * c) * d ^ 2 := by
    calc
      (L ^ 3 * g ^ 2 * d) * d ^ 2 = g ^ 2 * (L * d) ^ 3 := by ring
      _ ≤ g ^ 2 * ((a * P ^ 2) * (b * Q ^ 2) * (c * R ^ 2)) := hscaled
      _ = (a * b * c) * d ^ 2 := by rw [hdecomp]; ring
  exact Nat.le_of_mul_le_mul_right hcancel (pow_pos hdpos 2)

/-- Generic signed domination: a row certificate and a sufficiently large
cofactor product force the composed third obstruction to be nonzero. -/
theorem third_obstruction_ne_zero_of_cofactor_lower
    {L A g d : ℕ} {C D E delta : ℤ}
    (hgpos : 0 < g)
    (hd : 10 ^ 120 ≤ d)
    (hA : L ^ 3 * g ^ 2 * d ≤ A)
    (hlinear :
      180 * Int.natAbs (E * delta) <
        9 * Int.natAbs C * L ^ 3)
    (hcorrection :
      108 * Int.natAbs (D * delta) <
        10 ^ 120 *
          (9 * Int.natAbs C * L ^ 3 -
            180 * Int.natAbs (E * delta))) :
    -9 * C * (A : ℤ) +
        180 * E * (g : ℤ) ^ 2 * delta * (d : ℤ) +
        108 * D * (g : ℤ) ^ 2 * delta ≠ 0 := by
  intro hzero
  let M : ℕ := 9 * Int.natAbs C * L ^ 3
  let U : ℕ := 180 * Int.natAbs (E * delta)
  let V : ℕ := 108 * Int.natAbs (D * delta)
  have hUM : U < M := by simpa [U, M] using hlinear
  have htarget : V < 10 ^ 120 * (M - U) := by
    simpa [V, M, U] using hcorrection
  have htargetLe : 10 ^ 120 * (M - U) ≤ d * (M - U) := by
    exact Nat.mul_le_mul_right (M - U) hd
  have hV : V < d * (M - U) := lt_of_lt_of_le htarget htargetLe
  have hUV : U * d + V < M * d := by
    calc
      U * d + V < U * d + d * (M - U) := Nat.add_lt_add_left hV _
      _ = (U + (M - U)) * d := by ring
      _ = M * d := by rw [Nat.add_sub_of_le (Nat.le_of_lt hUM)]
  have hUVg : (U * d + V) * g ^ 2 < (M * d) * g ^ 2 :=
    Nat.mul_lt_mul_of_pos_right hUV (pow_pos hgpos 2)
  have heq :
      9 * C * (A : ℤ) =
        180 * E * (g : ℤ) ^ 2 * delta * (d : ℤ) +
          108 * D * (g : ℤ) ^ 2 * delta := by
    linarith
  have habsEq := congrArg Int.natAbs heq
  have habsLe := Int.natAbs_add_le
    (180 * E * (g : ℤ) ^ 2 * delta * (d : ℤ))
    (108 * D * (g : ℤ) ^ 2 * delta)
  have hleft :
      Int.natAbs (9 * C * (A : ℤ)) = 9 * Int.natAbs C * A := by
    simp [Int.natAbs_mul]
  have hright :
      Int.natAbs
          (180 * E * (g : ℤ) ^ 2 * delta * (d : ℤ) +
            108 * D * (g : ℤ) ^ 2 * delta) ≤
        (U * d + V) * g ^ 2 := by
    calc
      Int.natAbs
          (180 * E * (g : ℤ) ^ 2 * delta * (d : ℤ) +
            108 * D * (g : ℤ) ^ 2 * delta) ≤
          Int.natAbs (180 * E * (g : ℤ) ^ 2 * delta * (d : ℤ)) +
            Int.natAbs (108 * D * (g : ℤ) ^ 2 * delta) := habsLe
      _ = (U * d + V) * g ^ 2 := by
        simp [U, V, Int.natAbs_mul, Int.natAbs_pow]
        ring
  have hmainLe : (M * d) * g ^ 2 ≤ 9 * Int.natAbs C * A := by
    dsimp [M]
    have := Nat.mul_le_mul_left (9 * Int.natAbs C) hA
    nlinarith
  have hbad : 9 * Int.natAbs C * A < 9 * Int.natAbs C * A := by
    calc
      9 * Int.natAbs C * A =
          Int.natAbs (9 * C * (A : ℤ)) := hleft.symm
      _ = Int.natAbs
          (180 * E * (g : ℤ) ^ 2 * delta * (d : ℤ) +
            108 * D * (g : ℤ) ^ 2 * delta) := habsEq
      _ ≤ (U * d + V) * g ^ 2 := hright
      _ < (M * d) * g ^ 2 := hUVg
      _ ≤ 9 * Int.natAbs C * A := hmainLe
  exact (Nat.lt_irrefl _ hbad)

/-- A supplied three-component target-row decomposition has a nonzero
composed third obstruction at its first owner once the three exact residual
floors are available. -/
theorem target_three_bucket_third_obstruction_ne_zero_of_residual_floors
    {k i j l P Q R g d a b c : ℕ}
    (hk : k = 5 ∨ k = 7 ∨ k = 9 ∨ k = 11 ∨ k = 13 ∨ k = 15)
    (hi : i ∈ Finset.Icc 1 k)
    (hj : j ∈ Finset.Icc 1 k)
    (hl : l ∈ Finset.Icc 1 k)
    (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l)
    (hgpos : 0 < g)
    (hdlarge : 10 ^ 120 ≤ d)
    (hdecomp : d = g * P * Q * R)
    (hPi : targetThirdResidualFloor k * d ≤ a * P ^ 2)
    (hQj : targetThirdResidualFloor k * d ≤ b * Q ^ 2)
    (hRl : targetThirdResidualFloor k * d ≤ c * R ^ 2) :
    targetThreeBucketThirdObstruction k i j l a b c g d ≠ 0 := by
  have hdpos : 0 < d := lt_of_lt_of_le (by norm_num) hdlarge
  have hproduct := three_component_cofactor_product_lower
    hdpos hdecomp hPi hQj hRl
  have hcoeff := target_third_obstruction_coefficient_certificate
    hk hi hj hl hij hil hjl
  have hne := third_obstruction_ne_zero_of_cofactor_lower
    (L := targetThirdResidualFloor k)
    (A := a * b * c) (g := g) (d := d)
    (C := localSecondConstant k i)
    (D := localSecondLinear k i)
    (E := localThirdQuadratic k i)
    (delta := threeBucketOwnerDelta i j l)
    hgpos hdlarge hproduct hcoeff.1 hcoeff.2
  intro hzero
  apply hne
  dsimp [targetThreeBucketThirdObstruction,
    targetThreeBucketSecondObstruction] at hzero ⊢
  linear_combination hzero

/-- Cyclic form: all three composed third obstructions are nonzero under the
same exact residual-floor hypotheses. -/
theorem target_three_bucket_all_third_obstructions_nonzero_of_residual_floors
    {k i j l P Q R g d a b c : ℕ}
    (hk : k = 5 ∨ k = 7 ∨ k = 9 ∨ k = 11 ∨ k = 13 ∨ k = 15)
    (hi : i ∈ Finset.Icc 1 k)
    (hj : j ∈ Finset.Icc 1 k)
    (hl : l ∈ Finset.Icc 1 k)
    (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l)
    (hgpos : 0 < g)
    (hdlarge : 10 ^ 120 ≤ d)
    (hdecomp : d = g * P * Q * R)
    (hPi : targetThirdResidualFloor k * d ≤ a * P ^ 2)
    (hQj : targetThirdResidualFloor k * d ≤ b * Q ^ 2)
    (hRl : targetThirdResidualFloor k * d ≤ c * R ^ 2) :
    targetThreeBucketThirdObstruction k i j l a b c g d ≠ 0 ∧
      targetThreeBucketThirdObstruction k j i l a b c g d ≠ 0 ∧
      targetThreeBucketThirdObstruction k l i j a b c g d ≠ 0 := by
  have hdQPR : d = g * Q * P * R := by rw [hdecomp]; ring
  have hdRPQ : d = g * R * P * Q := by rw [hdecomp]; ring
  constructor
  · exact target_three_bucket_third_obstruction_ne_zero_of_residual_floors
      hk hi hj hl hij hil hjl hgpos hdlarge hdecomp hPi hQj hRl
  constructor
  · have hJ := target_three_bucket_third_obstruction_ne_zero_of_residual_floors
      (a := b) (b := a) (c := c)
      hk hj hi hl hij.symm hjl hil hgpos hdlarge hdQPR hQj hPi hRl
    simpa [targetThreeBucketThirdObstruction,
      targetThreeBucketSecondObstruction, mul_comm, mul_left_comm,
      mul_assoc] using hJ
  · have hL := target_three_bucket_third_obstruction_ne_zero_of_residual_floors
      (a := c) (b := a) (c := b)
      hk hl hi hj hil.symm hjl.symm hij hgpos hdlarge hdRPQ hRl hPi hQj
    simpa [targetThreeBucketThirdObstruction,
      targetThreeBucketSecondObstruction, mul_comm, mul_left_comm,
      mul_assoc] using hL

/-- Uniform coefficient ceiling for the linear-in-gap correction in a
multi-owner third obstruction. -/
def multiOwnerThirdCoefficientBound : ℕ :=
  56 * 10 ^ 12 * 3 ^ 14 * 15 ^ 14 + 1

/-- Four or more target-size residuals make the cofactor product dominate
the complete third-obstruction correction, including its factor of `d`. -/
theorem multi_owner_target_cofactor_product_gt_third_bound
    {α : Type*}
    {owners : Finset α} {a P : α → ℕ} {d g : ℕ}
    (hcard : 4 ≤ owners.card)
    (hd : 10 ^ 120 ≤ d)
    (hgpos : 0 < g)
    (hdecomp : d = g * ∏ j ∈ owners, P j)
    (hresidual : ∀ j ∈ owners, 5 * d < a j * (P j) ^ 2) :
    multiOwnerThirdCoefficientBound * g ^ 2 * d <
      ∏ j ∈ owners, a j := by
  have hdpos : 0 < d := lt_of_lt_of_le (by norm_num) hd
  have howners : owners.Nonempty := Finset.card_pos.mp (by omega)
  have hscaled := multi_owner_cofactor_product_scaled_lower
    howners hdpos hgpos hdecomp hresidual
  have hnumeric :
      multiOwnerThirdCoefficientBound < 625 * 10 ^ 120 := by
    norm_num [multiOwnerThirdCoefficientBound]
  have hKd : multiOwnerThirdCoefficientBound < 625 * d :=
    lt_of_lt_of_le hnumeric (Nat.mul_le_mul_left 625 hd)
  have hfour :
      multiOwnerThirdCoefficientBound * d ^ 3 < (5 * d) ^ 4 := by
    calc
      multiOwnerThirdCoefficientBound * d ^ 3 <
          (625 * d) * d ^ 3 :=
        Nat.mul_lt_mul_of_pos_right hKd (pow_pos hdpos 3)
      _ = (5 * d) ^ 4 := by ring
  have hpow : (5 * d) ^ 4 ≤ (5 * d) ^ owners.card :=
    pow_le_pow_right' (by omega : 1 ≤ 5 * d) hcard
  have hgBound := Nat.mul_lt_mul_of_pos_left
    (lt_of_lt_of_le hfour hpow) (pow_pos hgpos 2)
  have hcancel :
      (multiOwnerThirdCoefficientBound * g ^ 2 * d) * d ^ 2 <
        (∏ j ∈ owners, a j) * d ^ 2 := by
    calc
      (multiOwnerThirdCoefficientBound * g ^ 2 * d) * d ^ 2 =
          g ^ 2 * (multiOwnerThirdCoefficientBound * d ^ 3) := by ring
      _ < g ^ 2 * (5 * d) ^ owners.card := hgBound
      _ < (∏ j ∈ owners, a j) * d ^ 2 := hscaled
  exact (Nat.mul_lt_mul_right (pow_pos hdpos 2)).mp hcancel

/-- Uniform absolute-value bound for the signed coefficient multiplying
`g^2` in a multi-owner third obstruction. -/
theorem multi_owner_third_coefficient_natAbs_lt
    {D E delta : ℤ} {r d : ℕ}
    (hdpos : 0 < d)
    (hD : Int.natAbs D < 10 ^ 12)
    (hE : Int.natAbs E < 10 ^ 12)
    (hr : r ≤ 14)
    (hdelta : Int.natAbs delta ≤ 15 ^ 14) :
    Int.natAbs
        ((12 * D + 20 * E * (d : ℤ)) * (-3) ^ r * delta) <
      multiOwnerThirdCoefficientBound * d := by
  have hDle : Int.natAbs D ≤ 10 ^ 12 := Nat.le_of_lt hD
  have hEle : Int.natAbs E ≤ 10 ^ 12 := Nat.le_of_lt hE
  have hsum := Int.natAbs_add_le (12 * D) (20 * E * (d : ℤ))
  have hsumBound :
      Int.natAbs (12 * D + 20 * E * (d : ℤ)) ≤ 56 * 10 ^ 12 * d := by
    calc
      Int.natAbs (12 * D + 20 * E * (d : ℤ)) ≤
          Int.natAbs (12 * D) + Int.natAbs (20 * E * (d : ℤ)) := hsum
      _ = 12 * Int.natAbs D + 20 * Int.natAbs E * d := by
        simp [Int.natAbs_mul]
      _ ≤ 12 * 10 ^ 12 + 20 * 10 ^ 12 * d := by
        exact Nat.add_le_add
          (Nat.mul_le_mul_left 12 hDle)
          (Nat.mul_le_mul_right d (Nat.mul_le_mul_left 20 hEle))
      _ ≤ 56 * 10 ^ 12 * d := by nlinarith
  have hpow : 3 ^ r ≤ 3 ^ 14 :=
    pow_le_pow_right' (by norm_num : 1 ≤ (3 : ℕ)) hr
  have hproduct :
      Int.natAbs (12 * D + 20 * E * (d : ℤ)) * 3 ^ r *
          Int.natAbs delta ≤
        (56 * 10 ^ 12 * d) * 3 ^ 14 * 15 ^ 14 := by
    exact Nat.mul_le_mul (Nat.mul_le_mul hsumBound hpow) hdelta
  calc
    Int.natAbs
        ((12 * D + 20 * E * (d : ℤ)) * (-3) ^ r * delta) =
        Int.natAbs (12 * D + 20 * E * (d : ℤ)) * 3 ^ r *
          Int.natAbs delta := by
      simp [Int.natAbs_mul, Int.natAbs_pow]
    _ ≤ (56 * 10 ^ 12 * d) * 3 ^ 14 * 15 ^ 14 := hproduct
    _ < multiOwnerThirdCoefficientBound * d := by
      dsimp [multiOwnerThirdCoefficientBound]
      nlinarith

/-- Once the cofactor product dominates the uniform linear-in-gap
coefficient, a bounded multi-owner third obstruction cannot vanish. -/
theorem bounded_multi_owner_third_obstruction_ne_zero
    {A g d r : ℕ} {C D E delta : ℤ}
    (hgpos : 0 < g)
    (hdpos : 0 < d)
    (hC : C ≠ 0)
    (hD : Int.natAbs D < 10 ^ 12)
    (hE : Int.natAbs E < 10 ^ 12)
    (hr : r ≤ 14)
    (hdelta : Int.natAbs delta ≤ 15 ^ 14)
    (hA : multiOwnerThirdCoefficientBound * g ^ 2 * d < A) :
    -9 * C * (A : ℤ) +
        (12 * D + 20 * E * (d : ℤ)) * (g : ℤ) ^ 2 *
          (-3) ^ r * delta ≠ 0 := by
  intro hzero
  let coeff : ℤ :=
    (12 * D + 20 * E * (d : ℤ)) * (-3) ^ r * delta
  have heq : 9 * C * (A : ℤ) = coeff * (g : ℤ) ^ 2 := by
    dsimp [coeff]
    linarith
  have habs := congrArg Int.natAbs heq
  have habsEq :
      9 * Int.natAbs C * A = Int.natAbs coeff * g ^ 2 := by
    simpa [Int.natAbs_mul, Int.natAbs_pow] using habs
  have hcoeff : Int.natAbs coeff < multiOwnerThirdCoefficientBound * d := by
    dsimp [coeff]
    exact multi_owner_third_coefficient_natAbs_lt
      hdpos hD hE hr hdelta
  have hcoeffScaled :
      Int.natAbs coeff * g ^ 2 <
        (multiOwnerThirdCoefficientBound * d) * g ^ 2 :=
    Nat.mul_lt_mul_of_pos_right hcoeff (pow_pos hgpos 2)
  have hCpos : 0 < Int.natAbs C := Int.natAbs_pos.mpr hC
  have hAle : A ≤ 9 * Int.natAbs C * A := by nlinarith
  have hbad : A < A := by
    calc
      A ≤ 9 * Int.natAbs C * A := hAle
      _ = Int.natAbs coeff * g ^ 2 := habsEq
      _ < (multiOwnerThirdCoefficientBound * d) * g ^ 2 := hcoeffScaled
      _ = multiOwnerThirdCoefficientBound * g ^ 2 * d := by ring
      _ < A := hA
  exact Nat.lt_irrefl _ hbad

/-- Uniform target-size nonvanishing of the composed third obstruction for
every owner family of cardinality `4..15`. -/
theorem target_multi_owner_third_obstruction_ne_zero
    {owners : Finset ℤ} {i C D E : ℤ}
    {a P : ℤ → ℕ} {d g : ℕ}
    (hi : i ∈ owners)
    (hcard4 : 4 ≤ owners.card)
    (hcard15 : owners.card ≤ 15)
    (hrange : ∀ j ∈ owners, 1 ≤ j ∧ j ≤ 15)
    (hd : 10 ^ 120 ≤ d)
    (hgpos : 0 < g)
    (hdecomp : d = g * ∏ j ∈ owners, P j)
    (hresidual : ∀ j ∈ owners, 5 * d < a j * (P j) ^ 2)
    (hC : C ≠ 0)
    (hD : Int.natAbs D < 10 ^ 12)
    (hE : Int.natAbs E < 10 ^ 12) :
    multiOwnerThirdObstruction owners i C D E (g : ℤ) (d : ℤ)
      (fun j => (a j : ℤ)) ≠ 0 := by
  have hdpos : 0 < d := lt_of_lt_of_le (by norm_num) hd
  have hA := multi_owner_target_cofactor_product_gt_third_bound
    hcard4 hd hgpos hdecomp hresidual
  have hcardErase : (owners.erase i).card ≤ 14 := by
    rw [Finset.card_erase_of_mem hi]
    omega
  have hdeltaBase := multi_owner_delta_natAbs_le_pow hi hrange
  have hpow : 15 ^ (owners.erase i).card ≤ 15 ^ 14 :=
    pow_le_pow_right' (by norm_num : 1 ≤ (15 : ℕ)) hcardErase
  have hdelta : Int.natAbs (multiOwnerDelta owners i) ≤ 15 ^ 14 :=
    le_trans hdeltaBase hpow
  have hne := bounded_multi_owner_third_obstruction_ne_zero
    hgpos hdpos hC hD hE hcardErase hdelta hA
  intro hzero
  apply hne
  have hcast :
      (((∏ j ∈ owners, a j) : ℕ) : ℤ) =
        ∏ j ∈ owners, (a j : ℤ) := by
    push_cast
    rfl
  dsimp [multiOwnerThirdObstruction, multiOwnerSecondObstruction,
    multiOwnerCofactorProduct] at hzero ⊢
  rw [hcast]
  linear_combination hzero

/-- At target scale every composed full-grid third obstruction attached to a
certified owner assignment is nonzero.  This is the equation-facing bridge
from the uniform multi-owner estimate back to the complete residual grid. -/
theorem allOwner_third_obstruction_ne_zero
    {k n d i : ℕ} {owner : ℕ → ℕ}
    (hk : k = 5 ∨ k = 7 ∨ k = 9 ∨ k = 11 ∨ k = 13 ∨ k = 15)
    (hdTarget : 10 ^ 120 ≤ d)
    (hi : i ∈ allOwnerGrid k)
    (hassign : GlobalResidualOwnerAssignment k n d owner)
    (heq : blockProduct k (n + d) = 4 * blockProduct k n) :
    multiOwnerThirdObstruction (allOwnerIntGrid k) (i : ℤ)
      (localSecondConstant k i) (localSecondLinear k i)
      (localThirdQuadratic k i)
      (globalResidualGroupedLoss k d : ℤ) (d : ℤ)
      (fun z => (allOwnerCofactorInt k n d owner z : ℤ)) ≠ 0 := by
  have hk5 : 5 ≤ k := by
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> omega
  have hk15 : k ≤ 15 := by
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> omega
  have hkd : k ≤ d := le_trans hk15 (le_trans (by norm_num) hdTarget)
  have hd : 0 < d := lt_of_lt_of_le (by norm_num) hdTarget
  apply target_multi_owner_third_obstruction_ne_zero
      (a := allOwnerCofactorInt k n d owner)
      (P := allOwnerBucketInt k d owner)
  · exact allOwner_natCast_mem_intGrid hi
  · rw [allOwnerIntGrid_card]
    omega
  · rw [allOwnerIntGrid_card]
    exact hk15
  · exact allOwnerIntGrid_target_range hk15
  · exact hdTarget
  · exact allOwnerLoss_pos k d
  · exact allOwnerIntGrid_gap_decomposition hd hassign
  · exact allOwnerIntGrid_residual_gt_five_gap hk5 hkd hassign heq
  · exact allOwner_localSecondConstant_ne_zero hi
  · exact (target_local_taylor_bounds hk hi).2.1
  · exact (target_local_taylor_bounds hk hi).2.2.1

/-- Complete all-owner assembly augmented with the newly proved nonvanishing
of every third obstruction.  The base certificate still records all exact
factorizations and divisibilities. -/
structure AllOwnerAssemblyThirdNonzeroCertificate (k n d : ℕ) where
  base : AllOwnerAssemblyCertificate k n d
  nonzeroThirdObstructions : ∀ i ∈ allOwnerGrid k,
    multiOwnerThirdObstruction (allOwnerIntGrid k) (i : ℤ)
      (localSecondConstant k i) (localSecondLinear k i)
      (localThirdQuadratic k i)
      (globalResidualGroupedLoss k d : ℤ) (d : ℤ)
      (fun z => (allOwnerCofactorInt k n d base.owner z : ℤ)) ≠ 0

/-- Package a supplied owner assignment with both nonzero second and nonzero
third full-grid obstruction certificates. -/
def allOwnerAssemblyThirdNonzeroCertificate_of_assignment
    {k n d : ℕ} {owner : ℕ → ℕ}
    (hk : k = 5 ∨ k = 7 ∨ k = 9 ∨ k = 11 ∨ k = 13 ∨ k = 15)
    (hdTarget : 10 ^ 120 ≤ d)
    (hassign : GlobalResidualOwnerAssignment k n d owner)
    (heq : blockProduct k (n + d) = 4 * blockProduct k n) :
    AllOwnerAssemblyThirdNonzeroCertificate k n d := by
  refine {
    base := allOwnerAssemblyCertificate_of_assignment
      hk hdTarget hassign heq
    nonzeroThirdObstructions := ?_ }
  intro i hi
  exact allOwner_third_obstruction_ne_zero
    hk hdTarget hi hassign heq

/-- Every target-scale solution has a complete all-owner certificate in which
all composed second and third obstructions are explicitly nonzero.  This
remains a reduction of the joint nonzero branch, not a contradiction. -/
theorem exists_allOwnerAssemblyThirdNonzeroCertificate
    {k n d : ℕ}
    (hk : k = 5 ∨ k = 7 ∨ k = 9 ∨ k = 11 ∨ k = 13 ∨ k = 15)
    (hdTarget : 10 ^ 120 ≤ d)
    (heq : blockProduct k (n + d) = 4 * blockProduct k n) :
    Nonempty (AllOwnerAssemblyThirdNonzeroCertificate k n d) := by
  have hk5 : 5 ≤ k := by
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> omega
  have hk15 : k ≤ 15 := by
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> omega
  have hkd : k ≤ d := le_trans hk15 (le_trans (by norm_num) hdTarget)
  obtain ⟨owner, hassign⟩ :=
    exists_globalResidualOwnerAssignment hk5 hkd heq
  exact ⟨allOwnerAssemblyThirdNonzeroCertificate_of_assignment
    hk hdTarget hassign heq⟩

#print axioms target_third_obstruction_nonzero_table_certificate
#print axioms target_third_obstruction_coefficient_certificate
#print axioms three_component_cofactor_product_lower
#print axioms third_obstruction_ne_zero_of_cofactor_lower
#print axioms target_three_bucket_third_obstruction_ne_zero_of_residual_floors
#print axioms target_three_bucket_all_third_obstructions_nonzero_of_residual_floors
#print axioms multi_owner_target_cofactor_product_gt_third_bound
#print axioms multi_owner_third_coefficient_natAbs_lt
#print axioms bounded_multi_owner_third_obstruction_ne_zero
#print axioms target_multi_owner_third_obstruction_ne_zero
#print axioms allOwner_third_obstruction_ne_zero
#print axioms exists_allOwnerAssemblyThirdNonzeroCertificate

end Erdos686Variant
end Erdos686
