/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import ErdosProblems.Erdos686ThirdObstructionNonzero

/-!
# Erdős 686: exact-ratio-window control of three-bucket third quotients

The earlier three-bucket sign scan used only the coarse residual window
`5*d < X_s < A_k*d`.  The equation supplies the much sharper ratio window.
For a rational upper bracket `A/B > 4^(1/k)`, its upper side gives

`B*d < (A-B)*(n+k)`.

For the six odd target rows we use denominator `100000`.  After absorbing the
at-most-fourteen row offset at `d >= 10^120`, every local residual satisfies

`R_k*d < H_k*localResidual n d i`,

where `H_k=A_k-100000` and `R_k=400000-A_k-1`.  The product version below is
the archimedean input that fixes the signs of all three third quotients in an
exactly-three cleaned-bucket tuple.  This module deliberately stops before
the remaining all-nonzero cancellation problem.
-/

namespace Erdos686
namespace Erdos686Variant

/-- Common denominator for the six exact rational upper-root brackets. -/
def exactRatioBracketDenominator : ℕ := 100000

/-- A strict rational upper bracket for `4^(1/k)` in every odd target row. -/
def exactRatioBracketNumerator : ℕ → ℕ
  | 5 => 131951
  | 7 => 121902
  | 9 => 116653
  | 11 => 113432
  | 13 => 111254
  | 15 => 109683
  | _ => 0

/-- Denominator of the induced lower bound for the centered residual. -/
def exactRatioResidualDenominator (k : ℕ) : ℕ :=
  exactRatioBracketNumerator k - exactRatioBracketDenominator

/-- Numerator of the induced lower bound for the centered residual.  The
subtracted one absorbs every finite row offset at the target cutoff. -/
def exactRatioResidualNumerator (k : ℕ) : ℕ :=
  4 * exactRatioBracketDenominator - exactRatioBracketNumerator k - 1

/-- A convenient integral floor below the sharper rational residual bound. -/
def exactRatioThirdResidualFloor : ℕ → ℕ
  | 5 => 8
  | 7 => 12
  | 9 => 15
  | 11 => 20
  | 13 => 23
  | 15 => 29
  | _ => 0

/-- The six rational brackets are strict upper brackets, checked by exact
integer arithmetic. -/
theorem target_exactRatioBracket_certificate
    {k : ℕ}
    (hk : k = 5 ∨ k = 7 ∨ k = 9 ∨ k = 11 ∨ k = 13 ∨ k = 15) :
    4 * exactRatioBracketDenominator ^ k <
      exactRatioBracketNumerator k ^ k := by
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    norm_num [exactRatioBracketDenominator, exactRatioBracketNumerator]

/-- Linear consequence of the upper half of the exact ratio window. -/
theorem target_exactRatio_lower_linear
    {k n d : ℕ}
    (hk : k = 5 ∨ k = 7 ∨ k = 9 ∨ k = 11 ∨ k = 13 ∨ k = 15)
    (hup : (n + d + k) ^ k ≤ 4 * (n + k) ^ k) :
    exactRatioBracketDenominator * d <
      exactRatioResidualDenominator k * (n + k) := by
  have hk1 : 1 ≤ k := by omega
  have hlin := ratio_window_linearize_of_pow_bracket
    (N := 4) (A := exactRatioBracketNumerator k)
    (B := exactRatioBracketDenominator) (k := k) (n := n) (d := d)
    hk1
    (target_exactRatioBracket_certificate hk) hup
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    norm_num [exactRatioResidualDenominator, exactRatioBracketNumerator,
      exactRatioBracketDenominator] at hlin ⊢ <;> omega

/-- At target scale the finite owner offset is smaller than one unit of the
chosen residual numerator. -/
theorem target_exactRatio_offset_lt_gap
    {k i d : ℕ}
    (hk : k = 5 ∨ k = 7 ∨ k = 9 ∨ k = 11 ∨ k = 13 ∨ k = 15)
    (hi : i ∈ Finset.Icc 1 k)
    (hd : 10 ^ 120 ≤ d) :
    3 * exactRatioResidualDenominator k * (k - i) < d := by
  rw [Finset.mem_Icc] at hi
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    norm_num [exactRatioResidualDenominator, exactRatioBracketNumerator,
      exactRatioBracketDenominator] at * <;> omega

/-- The exact equation window gives a sharp, row-uniform lower bound for
every positive local residual. -/
theorem target_exactRatio_localResidual_lower
    {k n d i : ℕ}
    (hk : k = 5 ∨ k = 7 ∨ k = 9 ∨ k = 11 ∨ k = 13 ∨ k = 15)
    (hi : i ∈ Finset.Icc 1 k)
    (hd : 10 ^ 120 ≤ d)
    (heq : blockProduct k (n + d) = 4 * blockProduct k n) :
    exactRatioResidualNumerator k * d <
      exactRatioResidualDenominator k * localResidual n d i := by
  have hlin := target_exactRatio_lower_linear hk (ratio_window_four_nat heq).1
  have hoff := target_exactRatio_offset_lt_gap hk hi hd
  rw [Finset.mem_Icc] at hi
  unfold localResidual
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    norm_num [exactRatioResidualNumerator, exactRatioResidualDenominator,
      exactRatioBracketNumerator, exactRatioBracketDenominator] at * <;>
    omega

/-- Integral row floors consumed by the three-component cofactor-product
argument.  Unlike the earlier coarse-window assumption, these floors are
derived directly from the exact block equation. -/
theorem target_exactRatio_localResidual_floor
    {k n d i : ℕ}
    (hk : k = 5 ∨ k = 7 ∨ k = 9 ∨ k = 11 ∨ k = 13 ∨ k = 15)
    (hi : i ∈ Finset.Icc 1 k)
    (hd : 10 ^ 120 ≤ d)
    (heq : blockProduct k (n + d) = 4 * blockProduct k n) :
    exactRatioThirdResidualFloor k * d ≤ localResidual n d i := by
  have hsharp := target_exactRatio_localResidual_lower hk hi hd heq
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    norm_num [exactRatioThirdResidualFloor, exactRatioResidualNumerator,
      exactRatioResidualDenominator, exactRatioBracketNumerator,
      exactRatioBracketDenominator] at hsharp ⊢ <;> omega

/- Multiplying the three exact-ratio residual bounds retains strictness and
produces the scale used by the third-quotient sign certificate. -/
set_option maxRecDepth 100000 in
theorem target_exactRatio_threeResidual_product_lower
    {k n d i j l : ℕ}
    (hk : k = 5 ∨ k = 7 ∨ k = 9 ∨ k = 11 ∨ k = 13 ∨ k = 15)
    (hi : i ∈ Finset.Icc 1 k)
    (hj : j ∈ Finset.Icc 1 k)
    (hl : l ∈ Finset.Icc 1 k)
    (hd : 10 ^ 120 ≤ d)
    (heq : blockProduct k (n + d) = 4 * blockProduct k n) :
    (exactRatioResidualNumerator k) ^ 3 * d ^ 3 <
      (exactRatioResidualDenominator k) ^ 3 *
        (localResidual n d i * localResidual n d j *
          localResidual n d l) := by
  have hdi := target_exactRatio_localResidual_lower hk hi hd heq
  have hdj := target_exactRatio_localResidual_lower hk hj hd heq
  have hdl := target_exactRatio_localResidual_lower hk hl hd heq
  have hRpos : 0 < exactRatioResidualNumerator k := by
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
      norm_num [exactRatioResidualNumerator, exactRatioBracketNumerator,
        exactRatioBracketDenominator]
  have hdpos : 0 < d := lt_of_lt_of_le (by norm_num) hd
  have hbasePos : 0 < exactRatioResidualNumerator k * d :=
    Nat.mul_pos hRpos hdpos
  have hXiPos : 0 < exactRatioResidualDenominator k * localResidual n d i :=
    lt_trans hbasePos hdi
  have hXjPos : 0 < exactRatioResidualDenominator k * localResidual n d j :=
    lt_trans hbasePos hdj
  have hfirst :
      (exactRatioResidualNumerator k * d) ^ 2 <
        (exactRatioResidualDenominator k * localResidual n d i) *
          (exactRatioResidualDenominator k * localResidual n d j) := by
    calc
      (exactRatioResidualNumerator k * d) ^ 2 =
          (exactRatioResidualNumerator k * d) *
            (exactRatioResidualNumerator k * d) := by ring
      _ < (exactRatioResidualDenominator k * localResidual n d i) *
            (exactRatioResidualNumerator k * d) :=
          Nat.mul_lt_mul_of_pos_right hdi hbasePos
      _ < (exactRatioResidualDenominator k * localResidual n d i) *
            (exactRatioResidualDenominator k * localResidual n d j) :=
          Nat.mul_lt_mul_of_pos_left hdj hXiPos
  have hthird :
      (exactRatioResidualNumerator k * d) ^ 3 <
        (exactRatioResidualDenominator k * localResidual n d i) *
          (exactRatioResidualDenominator k * localResidual n d j) *
          (exactRatioResidualDenominator k * localResidual n d l) := by
    calc
      (exactRatioResidualNumerator k * d) ^ 3 =
          (exactRatioResidualNumerator k * d) ^ 2 *
            (exactRatioResidualNumerator k * d) := by ring
      _ < ((exactRatioResidualDenominator k * localResidual n d i) *
            (exactRatioResidualDenominator k * localResidual n d j)) *
            (exactRatioResidualNumerator k * d) :=
          Nat.mul_lt_mul_of_pos_right hfirst hbasePos
      _ < ((exactRatioResidualDenominator k * localResidual n d i) *
            (exactRatioResidualDenominator k * localResidual n d j)) *
            (exactRatioResidualDenominator k * localResidual n d l) :=
          Nat.mul_lt_mul_of_pos_left hdl (Nat.mul_pos hXiPos hXjPos)
  calc
    (exactRatioResidualNumerator k) ^ 3 * d ^ 3 =
        (exactRatioResidualNumerator k * d) ^ 3 := by rw [mul_pow]
    _ < (exactRatioResidualDenominator k * localResidual n d i) *
          (exactRatioResidualDenominator k * localResidual n d j) *
          (exactRatioResidualDenominator k * localResidual n d l) := hthird
    _ = (exactRatioResidualDenominator k) ^ 3 *
          (localResidual n d i * localResidual n d j *
            localResidual n d l) := by
      ring

/-- Equation-facing exactly-three wrapper.  The exact ratio window supplies
the three residual floors, so every composed third obstruction is nonzero.
This removes the one-zero and multi-zero quotient branches, but it does not
bound the remaining all-nonzero cancellation. -/
theorem exactRatio_target_three_bucket_all_third_obstructions_nonzero
    {k n d i j l P Q R g a b c : ℕ}
    (hk : k = 5 ∨ k = 7 ∨ k = 9 ∨ k = 11 ∨ k = 13 ∨ k = 15)
    (hi : i ∈ Finset.Icc 1 k)
    (hj : j ∈ Finset.Icc 1 k)
    (hl : l ∈ Finset.Icc 1 k)
    (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l)
    (hgpos : 0 < g)
    (hdlarge : 10 ^ 120 ≤ d)
    (hdecomp : d = g * P * Q * R)
    (hPi : localResidual n d i = a * P ^ 2)
    (hQj : localResidual n d j = b * Q ^ 2)
    (hRl : localResidual n d l = c * R ^ 2)
    (heq : blockProduct k (n + d) = 4 * blockProduct k n) :
    targetThreeBucketThirdObstruction k i j l a b c g d ≠ 0 ∧
      targetThreeBucketThirdObstruction k j i l a b c g d ≠ 0 ∧
      targetThreeBucketThirdObstruction k l i j a b c g d ≠ 0 := by
  have hfloorI := target_exactRatio_localResidual_floor hk hi hdlarge heq
  have hfloorJ := target_exactRatio_localResidual_floor hk hj hdlarge heq
  have hfloorL := target_exactRatio_localResidual_floor hk hl hdlarge heq
  have hfloorEq : exactRatioThirdResidualFloor k = targetThirdResidualFloor k := by
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rfl
  rw [hPi, hfloorEq] at hfloorI
  rw [hQj, hfloorEq] at hfloorJ
  rw [hRl, hfloorEq] at hfloorL
  exact target_three_bucket_all_third_obstructions_nonzero_of_residual_floors
    hk hi hj hl hij hil hjl hgpos hdlarge hdecomp
    hfloorI hfloorJ hfloorL

/-- Equation-facing full-grid wrapper for the new multi-owner domination
theorem.  Every full-grid third obstruction is nonzero, including unit
owner buckets.  The theorem does not turn the resulting simultaneous
nonzero divisibilities into a cutoff. -/
theorem exactRatio_allOwner_third_obstruction_ne_zero
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

#print axioms target_exactRatioBracket_certificate
#print axioms target_exactRatio_lower_linear
#print axioms target_exactRatio_offset_lt_gap
#print axioms target_exactRatio_localResidual_lower
#print axioms target_exactRatio_localResidual_floor
#print axioms target_exactRatio_threeResidual_product_lower
#print axioms exactRatio_target_three_bucket_all_third_obstructions_nonzero
#print axioms exactRatio_allOwner_third_obstruction_ne_zero

end Erdos686Variant
end Erdos686
