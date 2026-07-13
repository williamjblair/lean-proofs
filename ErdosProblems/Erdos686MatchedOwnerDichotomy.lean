/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import ErdosProblems.Erdos686CenteredRatioWindowSharp
import ErdosProblems.Erdos686ReflectedAlignmentSquareLift
import ErdosProblems.Erdos686ReflectedHarmonicBridge

/-!
# A matched-owner dichotomy for Erdős 686

This module keeps one exact large-base component on a supplied lower owner
and its equation-forced upper match.  A nonzero matched linear residual gives
an explicit cofactor-sensitive gap bound.  If that residual vanishes, the
next fixed coefficient is nonzero and absorbs the complete normalization
parameter.

No owner-supply assertion is made here.
-/

namespace Erdos686
namespace Erdos686Variant

open scoped BigOperators

/-- The fixed quadratic coefficient after the matched constant and linear
terms have cancelled. -/
def matchedOwnerQuadraticCoefficient
    (k i j A B : ℕ) : ℤ :=
  (A : ℤ) ^ 2 * localSecondLinear k j -
    4 * (B : ℤ) ^ 2 * localSecondLinear k i

/-- The first matched-owner residual after removing the common owner base. -/
def matchedOwnerLinearResidual
    (k i j a b : ℕ) : ℤ :=
  localSecondConstant k j * ((a + b : ℕ) : ℤ) -
    4 * localSecondConstant k i * (a : ℤ)

/-- The exact normalization of the signed local derivative coefficients. -/
def matchedOwnerSlopeNumerator (k i j : ℕ) : ℕ :=
  4 * localBlockCoefficientNat k i /
    Nat.gcd (4 * localBlockCoefficientNat k i)
      (localBlockCoefficientNat k j)

/-- The exact normalization denominator of the signed local derivative
coefficients. -/
def matchedOwnerSlopeDenominator (k i j : ℕ) : ℕ :=
  localBlockCoefficientNat k j /
    Nat.gcd (4 * localBlockCoefficientNat k i)
      (localBlockCoefficientNat k j)

private lemma int_mul_left_cancel_of_ne_zero
    {a b c : ℤ} (ha : a ≠ 0) (h : a * b = a * c) : b = c := by
  exact mul_left_cancel₀ ha h

lemma localBlockCoefficientNat_succ_le_of_left_half
    {k i : ℕ} (hi1 : 1 ≤ i) (hi : 2 * i ≤ k) :
    localBlockCoefficientNat k (i + 1) ≤ localBlockCoefficientNat k i := by
  have hfac : i.factorial = i * (i - 1).factorial := by
    conv_lhs => rw [show i = (i - 1) + 1 by omega, Nat.factorial_succ]
    congr 1 <;> omega
  have hkfac : (k - i).factorial =
      (k - i) * (k - i - 1).factorial := by
    conv_lhs =>
      rw [show k - i = (k - i - 1) + 1 by omega, Nat.factorial_succ]
    congr 1 <;> omega
  have hle : i ≤ k - i := by omega
  unfold localBlockCoefficientNat
  calc
    (i + 1 - 1).factorial * (k - (i + 1)).factorial =
        i.factorial * (k - i - 1).factorial := by congr 2 <;> omega
    _ = i * (i - 1).factorial * (k - i - 1).factorial := by rw [hfac]
    _ ≤ (k - i) * (i - 1).factorial * (k - i - 1).factorial := by
      exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hle)
    _ = (i - 1).factorial * (k - i).factorial := by rw [hkfac]; ring

lemma localBlockCoefficientNat_le_of_left_half
    {k i j : ℕ} (hi1 : 1 ≤ i) (hij : i ≤ j) (hj : 2 * j ≤ k) :
    localBlockCoefficientNat k j ≤ localBlockCoefficientNat k i := by
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ j hij ih =>
      exact (localBlockCoefficientNat_succ_le_of_left_half (by omega) (by omega)).trans
        (ih (by omega))

lemma localBlockCoefficientNat_le_succ_of_right_half
    {k i : ℕ} (hi : k ≤ 2 * i) (hik : i < k) :
    localBlockCoefficientNat k i ≤ localBlockCoefficientNat k (i + 1) := by
  have hfac : i.factorial = i * (i - 1).factorial := by
    conv_lhs => rw [show i = (i - 1) + 1 by omega, Nat.factorial_succ]
    congr 1 <;> omega
  have hkfac : (k - i).factorial =
      (k - i) * (k - i - 1).factorial := by
    conv_lhs =>
      rw [show k - i = (k - i - 1) + 1 by omega, Nat.factorial_succ]
    congr 1 <;> omega
  have hle : k - i ≤ i := by omega
  unfold localBlockCoefficientNat
  calc
    (i - 1).factorial * (k - i).factorial =
        (k - i) * (i - 1).factorial * (k - i - 1).factorial := by
          rw [hkfac]; ring
    _ ≤ i * (i - 1).factorial * (k - i - 1).factorial := by
      exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hle)
    _ = i.factorial * (k - i - 1).factorial := by rw [hfac]
    _ = (i + 1 - 1).factorial * (k - (i + 1)).factorial := by congr 2 <;> omega

lemma localBlockCoefficientNat_le_of_right_half
    {k i j : ℕ} (hik : i ≤ k) (hji : j ≤ i)
    (hj : k ≤ 2 * j) :
    localBlockCoefficientNat k j ≤ localBlockCoefficientNat k i := by
  induction i, hji using Nat.le_induction with
  | base => exact le_rfl
  | succ i hji ih =>
      have hhalf : k ≤ 2 * i := by omega
      have hik' : i < k := by omega
      exact (ih (by omega)).trans
        (localBlockCoefficientNat_le_succ_of_right_half hhalf hik')

lemma ownerSlope_pos_implies_left_half
    {k i : ℕ} (hi1 : 1 ≤ i) (hik : i ≤ k)
    (hpos : 0 < ownerSlope k i) :
    2 * i ≤ k := by
  by_contra hnot
  have hki : k + 1 - i ≤ i := by omega
  have hr1 : 1 ≤ k + 1 - i := by omega
  have hrk : k + 1 - i ≤ k := by omega
  have href := ownerSlope_reflect hi1 hik
  rcases eq_or_lt_of_le hki with heq | hlt
  · rw [heq] at href
    linarith
  · have hanti := ownerSlope_strictAnti hr1 hik hlt
    rw [href] at hanti
    linarith

lemma ownerSlope_neg_implies_right_half
    {k i : ℕ} (hi1 : 1 ≤ i) (hik : i ≤ k)
    (hneg : ownerSlope k i < 0) :
    k ≤ 2 * i := by
  by_contra hnot
  have hik' : i < k + 1 - i := by omega
  have hrk : k + 1 - i ≤ k := by omega
  have href := ownerSlope_reflect hi1 hik
  have hanti := ownerSlope_strictAnti hi1 hrk hik'
  rw [href] at hanti
  linarith

/-- The sharp centered equation window forces the increment cofactor `b` to
be strictly smaller than the lower cofactor `a`, quantitatively.  The modulus
is arbitrary; primality enters only when a caller extracts an owner. -/
theorem matchedOwner_sharp_cofactor_ratio
    {k n d i j q a b : ℕ}
    (hk : 16 ≤ k) (hd : k ≤ d)
    (hi : i ∈ Finset.Icc 1 k) (hj : j ∈ Finset.Icc 1 k)
    (hq : 0 < q)
    (hlower : n + i = a * q)
    (hupper : n + d + j = (a + b) * q)
    (heq : blockProduct k (n + d) = 4 * blockProduct k n) :
    1218443 * k * b < 3707904 * a := by
  have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
  have hjk : j ≤ k := (Finset.mem_Icc.mp hj).2
  have hsplit : (a + b) * q = a * q + b * q := by ring
  have hgap : d + j = i + b * q := by omega
  have hbq : b * q < 2 * d := by omega
  have hratio : 1218443 * k * d < 1853952 * n :=
    maximal_sharp_bracket_ratio_of_four_solution hk hd heq
  have hnlt : n < a * q := by omega
  have hscaled :
      (1218443 * k * b) * q < (3707904 * a) * q := by
    nlinarith
  exact (Nat.mul_lt_mul_right hq).mp hscaled

/-- The matched square lift removes one copy of the supplied owner modulus and
puts the remaining copy into the first signed residual. -/
theorem matchedOwnerLinearResidual_dvd
    {k n d i j q a b : ℕ}
    (hi : i ∈ Finset.Icc 1 k) (hj : j ∈ Finset.Icc 1 k)
    (hq : 0 < q)
    (hlower : n + i = a * q)
    (hupper : n + d + j = (a + b) * q)
    (heq : blockProduct k (n + d) = 4 * blockProduct k n) :
    (q : ℤ) ∣ matchedOwnerLinearResidual k i j a b := by
  have hlowerDvd : q ∣ n + i := by
    refine ⟨a, ?_⟩
    simpa [Nat.mul_comm] using hlower
  have hupperDvd : q ∣ n + d + j := by
    refine ⟨a + b, ?_⟩
    simpa [Nat.mul_comm] using hupper
  have hraw := matched_owner_local_coefficients_dvd_sq
    hi hj hlowerDvd hupperDvd heq
  have hidentity :
      localBlockCoefficient k j * ((n + d + j : ℕ) : ℤ) -
          4 * localBlockCoefficient k i * ((n + i : ℕ) : ℤ) =
        (q : ℤ) * matchedOwnerLinearResidual k i j a b := by
    rw [hlower, hupper]
    dsimp [matchedOwnerLinearResidual]
    rw [localSecondConstant_eq_localBlockCoefficient,
      localSecondConstant_eq_localBlockCoefficient]
    push_cast
    ring
  rw [hidentity] at hraw
  rcases hraw with ⟨W, hW⟩
  refine ⟨W, ?_⟩
  have hq0 : (q : ℤ) ≠ 0 := by exact_mod_cast (ne_of_gt hq)
  apply int_mul_left_cancel_of_ne_zero hq0
  calc
    (q : ℤ) * matchedOwnerLinearResidual k i j a b =
        (q : ℤ) ^ 2 * W := hW
    _ = (q : ℤ) * ((q : ℤ) * W) := by ring

/-- Once a supplied matched owner is written as `BZ` below and `AZ` above,
vanishing of the matched linear residual forces `Z` into the fixed quadratic
coefficient. -/
theorem matchedOwnerQuadraticCoefficient_dvd_of_normalized_match
    {k n d i j A B Z : ℕ}
    (hi : i ∈ Finset.Icc 1 k) (hj : j ∈ Finset.Icc 1 k)
    (hZ : 0 < Z)
    (hlower : n + i = B * Z)
    (hupper : n + d + j = A * Z)
    (hlinear :
      (A : ℤ) * localSecondConstant k j =
        4 * (B : ℤ) * localSecondConstant k i)
    (heq : blockProduct k (n + d) = 4 * blockProduct k n) :
    (Z : ℤ) ∣ matchedOwnerQuadraticCoefficient k i j A B := by
  let QL : ℤ := localOffsetCofactor k i (B * Z)
  let QU : ℤ := localOffsetCofactor k j (A * Z)
  let Ci : ℤ := localSecondConstant k i
  let Cj : ℤ := localSecondConstant k j
  let Di : ℤ := localSecondLinear k i
  let Dj : ℤ := localSecondLinear k j
  have hZ0 : (Z : ℤ) ≠ 0 := by exact_mod_cast (ne_of_gt hZ)
  have hQLrem : (Z : ℤ) ^ 2 ∣ QL - Ci - Di * ((B : ℤ) * Z) := by
    have hraw := localOffsetCofactor_second_order k i ((B : ℤ) * Z)
    have hpow : (Z : ℤ) ^ 2 ∣ ((B : ℤ) * Z) ^ 2 := by
      refine ⟨(B : ℤ) ^ 2, ?_⟩
      ring
    exact dvd_trans hpow (by simpa [QL, Ci, Di, mul_assoc] using hraw)
  have hQUrem : (Z : ℤ) ^ 2 ∣ QU - Cj - Dj * ((A : ℤ) * Z) := by
    have hraw := localOffsetCofactor_second_order k j ((A : ℤ) * Z)
    have hpow : (Z : ℤ) ^ 2 ∣ ((A : ℤ) * Z) ^ 2 := by
      refine ⟨(A : ℤ) ^ 2, ?_⟩
      ring
    exact dvd_trans hpow (by simpa [QU, Cj, Dj, mul_assoc] using hraw)
  have heqInt :
      intBlockProduct k ((n + d : ℕ) : ℤ) =
        4 * intBlockProduct k (n : ℤ) := by
    rw [intBlockProduct_natCast, intBlockProduct_natCast]
    exact_mod_cast heq
  have heqLocal :
      ((A : ℤ) * Z) * QU = 4 * ((B : ℤ) * Z) * QL := by
    rw [intBlockProduct_eq_factor_mul_localBlockCofactor
        ((n + d : ℕ) : ℤ) hj,
      intBlockProduct_eq_factor_mul_localBlockCofactor (n : ℤ) hi] at heqInt
    have hlowerZ : (((n + i : ℕ) : ℤ)) = (B : ℤ) * Z := by
      exact_mod_cast hlower
    have hupperZ : (((n + d + j : ℕ) : ℤ)) = (A : ℤ) * Z := by
      exact_mod_cast hupper
    have hQLcof : QL = localBlockCofactor k i (n : ℤ) := by
      dsimp [QL]
      rw [← hlowerZ, localOffsetCofactor_eq_localBlockCofactor]
    have hQUcof : QU = localBlockCofactor k j ((n + d : ℕ) : ℤ) := by
      dsimp [QU]
      rw [← hupperZ]
      simpa [Nat.add_assoc] using
        (localOffsetCofactor_eq_localBlockCofactor
          (k := k) (i := j) (n := n + d))
    rw [hQLcof, hQUcof, ← hupperZ, ← hlowerZ]
    simpa [Nat.cast_add, mul_assoc] using heqInt
  have heqReduced : (A : ℤ) * QU = 4 * (B : ℤ) * QL := by
    have hfactored :
        (Z : ℤ) * ((A : ℤ) * QU) =
          (Z : ℤ) * (4 * (B : ℤ) * QL) := by
      simpa [mul_assoc, mul_comm, mul_left_comm] using heqLocal
    exact int_mul_left_cancel_of_ne_zero hZ0 hfactored
  rcases hQLrem with ⟨EL, hEL⟩
  rcases hQUrem with ⟨EU, hEU⟩
  have hQLform : QL = Ci + Di * ((B : ℤ) * Z) + (Z : ℤ) ^ 2 * EL := by
    linarith
  have hQUform : QU = Cj + Dj * ((A : ℤ) * Z) + (Z : ℤ) ^ 2 * EU := by
    linarith
  have hquad :
      (Z : ℤ) ^ 2 ∣
        (Z : ℤ) * matchedOwnerQuadraticCoefficient k i j A B := by
    refine ⟨-(A : ℤ) * EU + 4 * (B : ℤ) * EL, ?_⟩
    dsimp [matchedOwnerQuadraticCoefficient]
    rw [hQLform, hQUform] at heqReduced
    dsimp [Ci, Cj, Di, Dj] at hlinear heqReduced ⊢
    have heqZero :
        (A : ℤ) * (localSecondConstant k j +
            localSecondLinear k j * ((A : ℤ) * Z) + Z ^ 2 * EU) -
          4 * (B : ℤ) * (localSecondConstant k i +
            localSecondLinear k i * ((B : ℤ) * Z) + Z ^ 2 * EL) = 0 :=
      sub_eq_zero.mpr heqReduced
    have hconst :
        (A : ℤ) * localSecondConstant k j -
          4 * (B : ℤ) * localSecondConstant k i = 0 :=
      sub_eq_zero.mpr hlinear
    have hzero :
        (Z : ℤ) * ((A : ℤ) ^ 2 * localSecondLinear k j -
          4 * (B : ℤ) ^ 2 * localSecondLinear k i) +
          Z ^ 2 * ((A : ℤ) * EU - 4 * (B : ℤ) * EL) = 0 := by
      calc
        _ = ((A : ℤ) * (localSecondConstant k j +
              localSecondLinear k j * ((A : ℤ) * Z) + Z ^ 2 * EU) -
            4 * (B : ℤ) * (localSecondConstant k i +
              localSecondLinear k i * ((B : ℤ) * Z) + Z ^ 2 * EL)) -
            ((A : ℤ) * localSecondConstant k j -
              4 * (B : ℤ) * localSecondConstant k i) := by ring
        _ = 0 := by rw [heqZero, hconst]; ring
    linear_combination hzero
  rcases hquad with ⟨W, hW⟩
  refine ⟨W, ?_⟩
  have hcancel :
      (Z : ℤ) * matchedOwnerQuadraticCoefficient k i j A B =
        (Z : ℤ) * ((Z : ℤ) * W) := by
    calc
      (Z : ℤ) * matchedOwnerQuadraticCoefficient k i j A B =
          (Z : ℤ) ^ 2 * W := hW
      _ = (Z : ℤ) * ((Z : ℤ) * W) := by ring
  exact int_mul_left_cancel_of_ne_zero hZ0 hcancel

lemma localSecondConstant_natAbs_eq_localBlockCoefficientNat
    {k i : ℕ} (hi : i ∈ Finset.Icc 1 k) :
    Int.natAbs (localSecondConstant k i) = localBlockCoefficientNat k i := by
  rw [localSecondConstant_eq_localBlockCoefficient,
    localBlockCoefficient_eq_sign_mul_nat hi]
  simp [Int.natAbs_mul, Int.natAbs_pow]

lemma matchedOwnerLinearResidual_natAbs_lt
    {k i j a b : ℕ}
    (hi : i ∈ Finset.Icc 1 k) (hj : j ∈ Finset.Icc 1 k)
    (hba : b < a) :
    Int.natAbs (matchedOwnerLinearResidual k i j a b) <
      2 * a * (localBlockCoefficientNat k j +
        2 * localBlockCoefficientNat k i) := by
  have htri := Int.natAbs_sub_le
    (localSecondConstant k j * ((a + b : ℕ) : ℤ))
    (4 * localSecondConstant k i * (a : ℤ))
  have hCjPos : 0 < localBlockCoefficientNat k j := by
    unfold localBlockCoefficientNat
    positivity
  calc
    Int.natAbs (matchedOwnerLinearResidual k i j a b) ≤
        Int.natAbs (localSecondConstant k j * ((a + b : ℕ) : ℤ)) +
          Int.natAbs (4 * localSecondConstant k i * (a : ℤ)) := by
      simpa [matchedOwnerLinearResidual] using htri
    _ = localBlockCoefficientNat k j * (a + b) +
        4 * localBlockCoefficientNat k i * a := by
      simp only [Int.natAbs_mul, Int.natAbs_natCast,
        localSecondConstant_natAbs_eq_localBlockCoefficientNat hi,
        localSecondConstant_natAbs_eq_localBlockCoefficientNat hj]
      norm_num
    _ < 2 * a * (localBlockCoefficientNat k j +
        2 * localBlockCoefficientNat k i) := by
      nlinarith

/-- Quantitative nonzero arm of the supplied-owner dichotomy. -/
theorem matchedOwner_nonzero_residual_gap_bound
    {k n d i j q a b : ℕ}
    (hk : 16 ≤ k) (hd : k ≤ d)
    (hi : i ∈ Finset.Icc 1 k) (hj : j ∈ Finset.Icc 1 k)
    (hq : 0 < q)
    (hlower : n + i = a * q)
    (hupper : n + d + j = (a + b) * q)
    (heq : blockProduct k (n + d) = 4 * blockProduct k n)
    (hD : matchedOwnerLinearResidual k i j a b ≠ 0) :
    1218443 * k * d <
      3707904 * a ^ 2 * (localBlockCoefficientNat k j +
        2 * localBlockCoefficientNat k i) := by
  have hcofactor := matchedOwner_sharp_cofactor_ratio
    hk hd hi hj hq hlower hupper heq
  have hapos : 0 < a := by nlinarith
  have hba : b < a := by nlinarith
  have hdvd := matchedOwnerLinearResidual_dvd hi hj hq hlower hupper heq
  have hdvdNat : q ∣ Int.natAbs (matchedOwnerLinearResidual k i j a b) := by
    have habsDvd := Int.natAbs_dvd_natAbs.mpr hdvd
    simpa using habsDvd
  have hqle : q ≤ Int.natAbs (matchedOwnerLinearResidual k i j a b) :=
    Nat.le_of_dvd (Int.natAbs_pos.mpr hD) hdvdNat
  have habslt := matchedOwnerLinearResidual_natAbs_lt hi hj hba
  have hratio : 1218443 * k * d < 1853952 * n :=
    maximal_sharp_bracket_ratio_of_four_solution hk hd heq
  have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
  have hnlt : n < a * q := by omega
  calc
    1218443 * k * d < 1853952 * n := hratio
    _ < 1853952 * (a * q) :=
      Nat.mul_lt_mul_of_pos_left hnlt (by norm_num)
    _ ≤ 1853952 * (a * Int.natAbs (matchedOwnerLinearResidual k i j a b)) := by
      exact Nat.mul_le_mul_left 1853952 (Nat.mul_le_mul_left a hqle)
    _ < 1853952 * (a *
        (2 * a * (localBlockCoefficientNat k j +
          2 * localBlockCoefficientNat k i))) := by
      exact Nat.mul_lt_mul_of_pos_left
        (Nat.mul_lt_mul_of_pos_left habslt hapos) (by norm_num)
    _ = 3707904 * a ^ 2 * (localBlockCoefficientNat k j +
        2 * localBlockCoefficientNat k i) := by ring

/-- In the sharp normalized range `B < A < 2B`, the fixed quadratic
coefficient cannot vanish.  The upper bound is essential: at a central owner
the formal equality can instead force the excluded ratio `A / B = 4`. -/
theorem matchedOwnerQuadraticCoefficient_ne_zero_of_ratio_lt_two
    {k i j A B : ℕ}
    (hi : i ∈ Finset.Icc 1 k) (hj : j ∈ Finset.Icc 1 k)
    (hB : 0 < B) (hBA : B < A) (hA2 : A < 2 * B)
    (hlinear :
      (A : ℤ) * localSecondConstant k j =
        4 * (B : ℤ) * localSecondConstant k i) :
    matchedOwnerQuadraticCoefficient k i j A B ≠ 0 := by
  intro hzero
  have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
  have hik : i ≤ k := (Finset.mem_Icc.mp hi).2
  have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
  have hjk : j ≤ k := (Finset.mem_Icc.mp hj).2
  have hA : 0 < A := lt_trans hB hBA
  have hCi0 : localSecondConstant k i ≠ 0 :=
    localSecondConstant_ne_zero_of_mem_Icc hi
  have hlinearQ :
      (A : ℚ) * (localSecondConstant k j : ℚ) =
        4 * (B : ℚ) * (localSecondConstant k i : ℚ) := by
    exact_mod_cast hlinear
  have hquadraticQ :
      (A : ℚ) ^ 2 * (localSecondLinear k j : ℚ) -
          4 * (B : ℚ) ^ 2 * (localSecondLinear k i : ℚ) = 0 := by
    exact_mod_cast hzero
  rw [localSecondLinear_cast_eq_constant_mul_ownerSlope,
    localSecondLinear_cast_eq_constant_mul_ownerSlope] at hquadraticQ
  have hfactor :
      (4 * (B : ℚ) * (localSecondConstant k i : ℚ)) *
          ((A : ℚ) * ownerSlope k j - (B : ℚ) * ownerSlope k i) = 0 := by
    linear_combination hquadraticQ -
      ((A : ℚ) * ownerSlope k j) * hlinearQ
  have hfactor0 :
      4 * (B : ℚ) * (localSecondConstant k i : ℚ) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast (ne_of_gt hB)))
      (by exact_mod_cast hCi0)
  have hslope :
      (A : ℚ) * ownerSlope k j = (B : ℚ) * ownerSlope k i := by
    exact sub_eq_zero.mp ((mul_eq_zero.mp hfactor).resolve_left hfactor0)
  have hmag :
      A * localBlockCoefficientNat k j =
        4 * B * localBlockCoefficientNat k i := by
    have habs := congrArg Int.natAbs hlinear
    simpa [Int.natAbs_mul,
      localSecondConstant_natAbs_eq_localBlockCoefficientNat hi,
      localSecondConstant_natAbs_eq_localBlockCoefficientNat hj] using habs
  have hcoeffLe :
      localBlockCoefficientNat k j ≤ localBlockCoefficientNat k i := by
    rcases lt_trichotomy (ownerSlope k i) 0 with hsiNeg | hsiZero | hsiPos
    · have hsjNeg : ownerSlope k j < 0 := by
        have hAQ : (0 : ℚ) < A := by exact_mod_cast hA
        have hBQ : (0 : ℚ) < B := by exact_mod_cast hB
        nlinarith [hslope]
      have hsij : ownerSlope k i < ownerSlope k j := by
        have hAQ : (0 : ℚ) < A := by exact_mod_cast hA
        have hBAQ : (B : ℚ) < A := by exact_mod_cast hBA
        nlinarith [hslope]
      have hji : j < i := by
        rcases lt_trichotomy j i with hlt | heq | hgt
        · exact hlt
        · subst j
          linarith
        · have hanti := ownerSlope_strictAnti hi1 hjk hgt
          linarith
      have hjhalf := ownerSlope_neg_implies_right_half hj1 hjk hsjNeg
      exact localBlockCoefficientNat_le_of_right_half hik
        (Nat.le_of_lt hji) hjhalf
    · have hsjZero : ownerSlope k j = 0 := by
        have hAQ : (0 : ℚ) < A := by exact_mod_cast hA
        have hBQ : (0 : ℚ) < B := by exact_mod_cast hB
        nlinarith [hslope]
      have hij : i = j := by
        rcases lt_trichotomy i j with hlt | heq | hgt
        · have hanti := ownerSlope_strictAnti hi1 hjk hlt
          linarith
        · exact heq
        · have hanti := ownerSlope_strictAnti hj1 hik hgt
          linarith
      subst j
      exact le_rfl
    · have hsjPos : 0 < ownerSlope k j := by
        have hAQ : (0 : ℚ) < A := by exact_mod_cast hA
        have hBQ : (0 : ℚ) < B := by exact_mod_cast hB
        nlinarith [hslope]
      have hsji : ownerSlope k j < ownerSlope k i := by
        have hAQ : (0 : ℚ) < A := by exact_mod_cast hA
        have hBAQ : (B : ℚ) < A := by exact_mod_cast hBA
        nlinarith [hslope]
      have hij : i < j := by
        rcases lt_trichotomy i j with hlt | heq | hgt
        · exact hlt
        · subst j
          linarith
        · have hanti := ownerSlope_strictAnti hj1 hik hgt
          linarith
      have hjhalf := ownerSlope_pos_implies_left_half hj1 hjk hsjPos
      exact localBlockCoefficientNat_le_of_left_half hi1
        (Nat.le_of_lt hij) hjhalf
  have hCjPos : 0 < localBlockCoefficientNat k j := by
    unfold localBlockCoefficientNat
    positivity
  have hmul :
      4 * B * localBlockCoefficientNat k j ≤
        A * localBlockCoefficientNat k j := by
    calc
      4 * B * localBlockCoefficientNat k j ≤
          4 * B * localBlockCoefficientNat k i :=
        Nat.mul_le_mul_left (4 * B) hcoeffLe
      _ = A * localBlockCoefficientNat k j := hmag.symm
  have hfour : 4 * B ≤ A :=
    Nat.le_of_mul_le_mul_right hmul hCjPos
  omega

/-- The normalized zero-residual branch has a completely fixed bound: the
scale `Z` divides a nonzero coefficient depending only on `k,i,j,A,B`, and the
original gap is bounded by that coefficient. -/
theorem matchedOwner_zero_residual_fixed_coefficient_bound
    {k n d i j A B Z : ℕ}
    (hi : i ∈ Finset.Icc 1 k) (hj : j ∈ Finset.Icc 1 k)
    (hZ : 0 < Z) (hB : 0 < B) (hBA : B < A) (hA2 : A < 2 * B)
    (hlower : n + i = B * Z)
    (hupper : n + d + j = A * Z)
    (hlinear :
      (A : ℤ) * localSecondConstant k j =
        4 * (B : ℤ) * localSecondConstant k i)
    (heq : blockProduct k (n + d) = 4 * blockProduct k n) :
    Z ≤ Int.natAbs (matchedOwnerQuadraticCoefficient k i j A B) ∧
      d ≤ (A - B) *
          Int.natAbs (matchedOwnerQuadraticCoefficient k i j A B) + k - 1 := by
  have hdvd := matchedOwnerQuadraticCoefficient_dvd_of_normalized_match
    hi hj hZ hlower hupper hlinear heq
  have hne := matchedOwnerQuadraticCoefficient_ne_zero_of_ratio_lt_two
    hi hj hB hBA hA2 hlinear
  have hdvdNat :
      Z ∣ Int.natAbs (matchedOwnerQuadraticCoefficient k i j A B) := by
    have habsDvd := Int.natAbs_dvd_natAbs.mpr hdvd
    simpa using habsDvd
  have hZle :
      Z ≤ Int.natAbs (matchedOwnerQuadraticCoefficient k i j A B) :=
    Nat.le_of_dvd (Int.natAbs_pos.mpr hne) hdvdNat
  have hAZ : A * Z = B * Z + (A - B) * Z := by
    calc
      A * Z = ((A - B) + B) * Z := by rw [Nat.sub_add_cancel (Nat.le_of_lt hBA)]
      _ = B * Z + (A - B) * Z := by ring
  have hgapEq : d + j = (A - B) * Z + i := by
    omega
  have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
  have hik : i ≤ k := (Finset.mem_Icc.mp hi).2
  have hgapZ : d ≤ (A - B) * Z + k - 1 := by
    omega
  have hscaled :
      (A - B) * Z ≤
        (A - B) * Int.natAbs (matchedOwnerQuadraticCoefficient k i j A B) :=
    Nat.mul_le_mul_left (A - B) hZle
  constructor
  · exact hZle
  · omega

/-- A raw vanishing first residual has the promised gcd normalization.  This
is the bridge from the supplied-owner variables `a,b,q` to the fixed
coefficient theorem above. -/
theorem matchedOwner_zero_residual_gcd_normalization
    {k n d i j q a b : ℕ}
    (hk : 16 ≤ k) (hd : k ≤ d)
    (hi : i ∈ Finset.Icc 1 k) (hj : j ∈ Finset.Icc 1 k)
    (hq : 0 < q)
    (hlower : n + i = a * q)
    (hupper : n + d + j = (a + b) * q)
    (heq : blockProduct k (n + d) = 4 * blockProduct k n)
    (hDzero : matchedOwnerLinearResidual k i j a b = 0) :
    ∃ A B w Z : ℕ,
      A = matchedOwnerSlopeNumerator k i j ∧
      B = matchedOwnerSlopeDenominator k i j ∧
      0 < w ∧ Z = w * q ∧
      a = B * w ∧ a + b = A * w ∧
      0 < B ∧ B < A ∧ A < 2 * B ∧
      Z ≤ Int.natAbs (matchedOwnerQuadraticCoefficient k i j A B) ∧
      d ≤ (A - B) *
          Int.natAbs (matchedOwnerQuadraticCoefficient k i j A B) + k - 1 := by
  have hcofactor := matchedOwner_sharp_cofactor_ratio
    hk hd hi hj hq hlower hupper heq
  have hapos : 0 < a := by nlinarith
  have hba : b < a := by nlinarith
  have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
  have hik : i ≤ k := (Finset.mem_Icc.mp hi).2
  have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
  have hsplit : (a + b) * q = a * q + b * q := by ring
  have hgap : d + j = i + b * q := by omega
  have hbpos : 0 < b := by
    have hbqpos : 0 < b * q := by omega
    exact pos_of_mul_pos_left hbqpos (Nat.zero_le q)
  have hsigned :
      localSecondConstant k j * ((a + b : ℕ) : ℤ) =
        4 * localSecondConstant k i * (a : ℤ) := by
    change localSecondConstant k j * ((a + b : ℕ) : ℤ) -
      4 * localSecondConstant k i * (a : ℤ) = 0 at hDzero
    exact sub_eq_zero.mp hDzero
  have hmag :
      localBlockCoefficientNat k j * (a + b) =
        4 * localBlockCoefficientNat k i * a := by
    have habs := congrArg Int.natAbs hsigned
    simp only [Int.natAbs_mul, Int.natAbs_natCast,
      localSecondConstant_natAbs_eq_localBlockCoefficientNat hi,
      localSecondConstant_natAbs_eq_localBlockCoefficientNat hj] at habs
    norm_num at habs
    exact habs
  let M : ℕ := 4 * localBlockCoefficientNat k i
  let N : ℕ := localBlockCoefficientNat k j
  let g : ℕ := Nat.gcd M N
  let A : ℕ := M / g
  let B : ℕ := N / g
  have hMpos : 0 < M := by
    dsimp [M, localBlockCoefficientNat]
    positivity
  have hNpos : 0 < N := by
    dsimp [N, localBlockCoefficientNat]
    positivity
  have hgpos : 0 < g := by
    dsimp [g]
    exact Nat.gcd_pos_of_pos_left N hMpos
  have hgA : g * A = M := by
    dsimp [A, g]
    exact Nat.mul_div_cancel' (Nat.gcd_dvd_left M N)
  have hgB : g * B = N := by
    dsimp [B, g]
    exact Nat.mul_div_cancel' (Nat.gcd_dvd_right M N)
  have hApos : 0 < A := by nlinarith
  have hBpos : 0 < B := by nlinarith
  have hredScaled : g * (B * (a + b)) = g * (A * a) := by
    calc
      g * (B * (a + b)) = (g * B) * (a + b) := by ring
      _ = N * (a + b) := by rw [hgB]
      _ = M * a := by simpa [M, N] using hmag
      _ = (g * A) * a := by rw [hgA]
      _ = g * (A * a) := by ring
  have hred : B * (a + b) = A * a :=
    Nat.eq_of_mul_eq_mul_left hgpos hredScaled
  have hcop : A.Coprime B := by
    dsimp [A, B, g]
    exact Nat.coprime_div_gcd_div_gcd hgpos
  have hAdvdMul : A ∣ B * (a + b) := by
    rw [hred]
    exact dvd_mul_right A a
  have hAdvd : A ∣ a + b := hcop.dvd_of_dvd_mul_left hAdvdMul
  rcases hAdvd with ⟨w, hw⟩
  have hABw : A * (B * w) = A * a := by
    calc
      A * (B * w) = B * (A * w) := by ring
      _ = B * (a + b) := by rw [hw]
      _ = A * a := hred
  have hBw : B * w = a := Nat.eq_of_mul_eq_mul_left hApos hABw
  have haBw : a = B * w := hBw.symm
  have hwpos : 0 < w := by
    by_contra hnot
    have hwzero : w = 0 := by omega
    rw [hwzero, mul_zero] at haBw
    omega
  have hBA : B < A := by
    apply (Nat.mul_lt_mul_right hwpos).mp
    rw [← haBw, ← hw]
    omega
  have hA2 : A < 2 * B := by
    apply (Nat.mul_lt_mul_right hwpos).mp
    rw [← hw]
    have htwice : (2 * B) * w = 2 * (B * w) := by ring
    rw [htwice, ← haBw]
    omega
  have hwCast : (((a + b : ℕ) : ℤ)) = (A : ℤ) * w := by
    exact_mod_cast hw
  have haCast : (a : ℤ) = (B : ℤ) * w := by
    exact_mod_cast haBw
  have hw0 : (w : ℤ) ≠ 0 := by exact_mod_cast (ne_of_gt hwpos)
  have hlinearScaled :
      (w : ℤ) * ((A : ℤ) * localSecondConstant k j) =
        (w : ℤ) * (4 * (B : ℤ) * localSecondConstant k i) := by
    calc
      _ = localSecondConstant k j * (((a + b : ℕ) : ℤ)) := by
        rw [hwCast]
        ring
      _ = 4 * localSecondConstant k i * (a : ℤ) := hsigned
      _ = (w : ℤ) * (4 * (B : ℤ) * localSecondConstant k i) := by
        rw [haCast]
        ring
  have hlinear :
      (A : ℤ) * localSecondConstant k j =
        4 * (B : ℤ) * localSecondConstant k i :=
    int_mul_left_cancel_of_ne_zero hw0 hlinearScaled
  let Z : ℕ := w * q
  have hZpos : 0 < Z := by
    dsimp [Z]
    positivity
  have hlowerNorm : n + i = B * Z := by
    rw [hlower, haBw]
    dsimp [Z]
    ring
  have hupperNorm : n + d + j = A * Z := by
    rw [hupper, hw]
    dsimp [Z]
    ring
  have hfixed := matchedOwner_zero_residual_fixed_coefficient_bound
    hi hj hZpos hBpos hBA hA2 hlowerNorm hupperNorm hlinear heq
  refine ⟨A, B, w, Z, ?_, ?_, hwpos, rfl, haBw, hw, hBpos, hBA, hA2,
    hfixed.1, hfixed.2⟩
  · simp [A, M, N, g, matchedOwnerSlopeNumerator]
  · simp [B, N, g, M, matchedOwnerSlopeDenominator]

/-- Final arbitrary-modulus supplied-owner dichotomy.  It does not assert that
such an owner exists; any prime-power owner dispatcher may instantiate
`q = p^e` without changing this algebraic core. -/
theorem suppliedOwner_matched_residual_dichotomy
    {k n d i j q a b : ℕ}
    (hk : 16 ≤ k) (hd : k ≤ d)
    (hi : i ∈ Finset.Icc 1 k) (hj : j ∈ Finset.Icc 1 k)
    (hq : 0 < q)
    (hlower : n + i = a * q)
    (hupper : n + d + j = (a + b) * q)
    (heq : blockProduct k (n + d) = 4 * blockProduct k n) :
    (matchedOwnerLinearResidual k i j a b ≠ 0 ∧
      1218443 * k * d <
        3707904 * a ^ 2 * (localBlockCoefficientNat k j +
          2 * localBlockCoefficientNat k i)) ∨
    (matchedOwnerLinearResidual k i j a b = 0 ∧
      ∃ A B w Z : ℕ,
        A = matchedOwnerSlopeNumerator k i j ∧
        B = matchedOwnerSlopeDenominator k i j ∧
        0 < w ∧ Z = w * q ∧
        a = B * w ∧ a + b = A * w ∧
        0 < B ∧ B < A ∧ A < 2 * B ∧
        Z ≤ Int.natAbs (matchedOwnerQuadraticCoefficient k i j A B) ∧
        d ≤ (A - B) *
            Int.natAbs (matchedOwnerQuadraticCoefficient k i j A B) + k - 1) := by
  by_cases hD : matchedOwnerLinearResidual k i j a b = 0
  · exact Or.inr ⟨hD, matchedOwner_zero_residual_gcd_normalization
      hk hd hi hj hq hlower hupper heq hD⟩
  · exact Or.inl ⟨hD, matchedOwner_nonzero_residual_gap_bound
      hk hd hi hj hq hlower hupper heq hD⟩

#print axioms matchedOwnerQuadraticCoefficient_dvd_of_normalized_match
#print axioms matchedOwnerQuadraticCoefficient_ne_zero_of_ratio_lt_two
#print axioms matchedOwner_zero_residual_fixed_coefficient_bound
#print axioms matchedOwner_zero_residual_gcd_normalization
#print axioms suppliedOwner_matched_residual_dichotomy

end Erdos686Variant
end Erdos686
