/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import ErdosProblems.Erdos686.K5.IntegralLift

/-!
# Erdős 686, k=5: exact fifth-root approximation on the surviving tail

This module turns the centered equation into a sharp rational approximation
to `4^(1/5)`.  The rational lower bracket

`1319507 / 1000000 < v/u`

is deliberately much tighter than the coarse `131/100` bracket.  It is
already valid for `u ≥ 1425`, so in particular throughout the only surviving
tail `u ≥ 10^1000`.
-/

namespace Erdos686
namespace Erdos686Variant

/-- The positive real fifth root of four. -/
noncomputable def k5Alpha : ℝ :=
  (4 : ℝ) ^ ((5 : ℝ)⁻¹)

lemma k5Alpha_fifth : k5Alpha ^ 5 = 4 := by
  simpa [k5Alpha] using
    (Real.rpow_inv_natCast_pow (x := (4 : ℝ)) (n := 5) (by norm_num) (by norm_num))

lemma k5Alpha_pos : 0 < k5Alpha := by
  dsimp [k5Alpha]
  positivity

/-- A seven-decimal rational lower certificate for the fifth root of four. -/
lemma k5Alpha_gt_1319507_over_million :
    (1319507 : ℝ) / 1000000 < k5Alpha := by
  have ha0 : (0 : ℝ) ≤ (1319507 : ℝ) / 1000000 := by norm_num
  have hp :
      ((1319507 : ℝ) / 1000000) ^ 5 < k5Alpha ^ 5 := by
    rw [k5Alpha_fifth]
    norm_num
  by_contra h
  have hle : k5Alpha ≤ (1319507 : ℝ) / 1000000 := le_of_not_gt h
  have := pow_le_pow_left₀ (le_of_lt k5Alpha_pos) hle 5
  linarith

/-- The centered equation forces a much sharper rational lower bracket than
the coarse interval used by the original Thue certificate. -/
theorem k5_integral_ratio_lower_sharp
    {u v : ℕ} (hu : 1425 ≤ u) (hsol : K5CenteredEq v u) :
    1319507 * u < 1000000 * v := by
  obtain ⟨_, hv2u⟩ := k5_integral_solution_window (by omega) hsol
  by_contra hnot
  have hratio : 1000000 * v ≤ 1319507 * u := Nat.le_of_not_gt hnot
  have hpow := Nat.pow_le_pow_left hratio 5
  rw [mul_pow, mul_pow] at hpow
  have heq :
      4 * u ^ 5 ≤ v ^ 5 + 20 * u ^ 3 + 4 * v := by
    unfold K5CenteredEq at hsol
    omega
  have hrem : 20 * u ^ 3 + 4 * v ≤ 28 * u ^ 3 := by
    have huCube : u ≤ u ^ 3 := by
      have hp := Nat.pow_le_pow_right (by omega : 0 < u) (by norm_num : 1 ≤ 3)
      simpa using hp
    nlinarith
  have hscaled :
      1000000 ^ 5 * (4 * u ^ 5) ≤
        1000000 ^ 5 * (v ^ 5 + 20 * u ^ 3 + 4 * v) :=
    Nat.mul_le_mul_left _ heq
  have hdefect :
      (4 * 1000000 ^ 5 - 1319507 ^ 5) * u ^ 5 ≤
        28 * 1000000 ^ 5 * u ^ 3 := by
    norm_num at hscaled hpow ⊢
    nlinarith
  have hsq : 1425 ^ 2 ≤ u ^ 2 := Nat.pow_le_pow_left hu 2
  have hlarge :
      28 * 1000000 ^ 5 <
        (4 * 1000000 ^ 5 - 1319507 ^ 5) * u ^ 2 := by
    calc
      28 * 1000000 ^ 5 <
          (4 * 1000000 ^ 5 - 1319507 ^ 5) * 1425 ^ 2 := by norm_num
      _ ≤ (4 * 1000000 ^ 5 - 1319507 ^ 5) * u ^ 2 :=
        Nat.mul_le_mul_left _ hsq
  have huCubePos : 0 < u ^ 3 := pow_pos (by omega) 3
  have hcontra :
      28 * 1000000 ^ 5 * u ^ 3 <
        (4 * 1000000 ^ 5 - 1319507 ^ 5) * u ^ 5 := by
    calc
      28 * 1000000 ^ 5 * u ^ 3 <
          ((4 * 1000000 ^ 5 - 1319507 ^ 5) * u ^ 2) * u ^ 3 :=
        Nat.mul_lt_mul_of_pos_right hlarge huCubePos
      _ = (4 * 1000000 ^ 5 - 1319507 ^ 5) * u ^ 5 := by ring
  omega

/-- Exact signed fifth-power defect. -/
lemma k5_fifth_defect_eq
    {u v : ℕ} (hsol : K5CenteredEq v u) :
    (4 : ℤ) * (u : ℤ) ^ 5 - (v : ℤ) ^ 5 =
      20 * (u : ℤ) ^ 3 - 5 * (v : ℤ) ^ 3 -
        16 * (u : ℤ) + 4 * (v : ℤ) := by
  have hz :
      (v : ℤ) ^ 5 + 4 * (v : ℤ) + 20 * (u : ℤ) ^ 3 =
        4 * (u : ℤ) ^ 5 + 16 * (u : ℤ) + 5 * (v : ℤ) ^ 3 := by
    exact_mod_cast hsol
  linarith

/-- On the sharp ratio window, the fifth-power defect is positive and has
the exact cubic upper bound used in the real approximation theorem. -/
theorem k5_fifth_defect_bounds
    {u v : ℕ} (hu : 1425 ≤ u) (hsol : K5CenteredEq v u) :
    0 < (4 : ℤ) * (u : ℤ) ^ 5 - (v : ℤ) ^ 5 ∧
      1000000 ^ 3 *
          ((4 : ℤ) * (u : ℤ) ^ 5 - (v : ℤ) ^ 5) <
        (20 * 1000000 ^ 3 - 5 * 1319507 ^ 3) * (u : ℤ) ^ 3 := by
  have hsharp := k5_integral_ratio_lower_sharp hu hsol
  obtain ⟨_, hv2u⟩ := k5_integral_solution_window (by omega) hsol
  have hsharpZ : (1319507 : ℤ) * u < 1000000 * v := by exact_mod_cast hsharp
  have hv2uZ : (v : ℤ) < 2 * u := by exact_mod_cast hv2u
  have huZ : (1425 : ℤ) ≤ u := by exact_mod_cast hu
  have hcube :
      (1319507 : ℤ) ^ 3 * (u : ℤ) ^ 3 <
        1000000 ^ 3 * (v : ℤ) ^ 3 := by
    have hp := pow_lt_pow_left₀ hsharpZ (by positivity) (by norm_num : 3 ≠ 0)
    simpa [mul_pow] using hp
  have hdef := k5_fifth_defect_eq hsol
  constructor
  · have hupperCoarse := k5_bracket_upper hsol (by omega)
    have hupperZ : (100 : ℤ) * v < 132 * u := by exact_mod_cast hupperCoarse
    have hc :
        (100 : ℤ) ^ 3 * (v : ℤ) ^ 3 <
          132 ^ 3 * (u : ℤ) ^ 3 := by
      have hp := pow_lt_pow_left₀ hupperZ (by positivity) (by norm_num : 3 ≠ 0)
      simpa [mul_pow] using hp
    have hvCubeSmall : 5 * (v : ℤ) ^ 3 < 12 * (u : ℤ) ^ 3 := by
      nlinarith
    have huLinearSmall : 16 * (u : ℤ) < (u : ℤ) ^ 3 := by
      have hu0 : (0 : ℤ) < (u : ℤ) := by omega
      have hsq : (16 : ℤ) < (u : ℤ) ^ 2 := by nlinarith
      have hm := mul_lt_mul_of_pos_left hsq hu0
      nlinarith
    nlinarith
  · nlinarith

/-- The exact rational approximation constant obtained from the seven-decimal
lower bracket.  Numerically it is about `0.5616527476`. -/
def k5ApproximationConstant : ℚ :=
  1702608047245783157000000 / 3031424763402858403856401

/-- Every centered solution in the surviving range is a one-sided
`C/u²` approximation to `4^(1/5)`, with an exact rational `C < 0.562`. -/
theorem k5_alpha_approximation
    {u v : ℕ} (hu : 1425 ≤ u) (hsol : K5CenteredEq v u) :
    |(v : ℝ) / (u : ℝ) - k5Alpha| <
      (k5ApproximationConstant : ℝ) / (u : ℝ) ^ 2 := by
  let ur : ℝ := u
  let vr : ℝ := v
  let q : ℝ := (1319507 : ℝ) / 1000000
  let S : ℝ :=
    (k5Alpha * ur) ^ 4 +
      (k5Alpha * ur) ^ 3 * vr +
      (k5Alpha * ur) ^ 2 * vr ^ 2 +
      (k5Alpha * ur) * vr ^ 3 + vr ^ 4
  let D : ℝ := 4 * ur ^ 5 - vr ^ 5
  have hu0 : 0 < ur := by dsimp [ur]; positivity
  have hv0 : 0 ≤ vr := by dsimp [vr]; positivity
  have hq0 : 0 < q := by norm_num [q]
  have hsharpN := k5_integral_ratio_lower_sharp hu hsol
  have hsharp : q * ur < vr := by
    dsimp [q, ur, vr]
    rw [div_mul_eq_mul_div]
    apply (div_lt_iff₀ (by norm_num : (0 : ℝ) < 1000000)).2
    have hz :
        (1319507 : ℝ) * (u : ℝ) < 1000000 * (v : ℝ) := by
      exact_mod_cast hsharpN
    simpa [mul_comm] using hz
  have hdefZ := k5_fifth_defect_bounds hu hsol
  have hDpos : 0 < D := by
    dsimp [D, ur, vr]
    exact_mod_cast hdefZ.1
  have hDupper :
      (1000000 : ℝ) ^ 3 * D <
        (20 * (1000000 : ℝ) ^ 3 - 5 * (1319507 : ℝ) ^ 3) * ur ^ 3 := by
    dsimp [D, ur, vr]
    exact_mod_cast hdefZ.2
  have hfactor :
      D = (k5Alpha * ur - vr) * S := by
    calc
      D = (k5Alpha * ur) ^ 5 - vr ^ 5 := by
        dsimp [D]
        rw [mul_pow, k5Alpha_fifth]
      _ = (k5Alpha * ur - vr) * S := by
        dsimp [S]
        ring
  have hxv : 0 < k5Alpha * ur - vr := by
    have hp :
        vr ^ 5 < (k5Alpha * ur) ^ 5 := by
      dsimp [D] at hDpos
      rw [mul_pow, k5Alpha_fifth]
      nlinarith
    have hxu0 : 0 ≤ k5Alpha * ur :=
      le_of_lt (mul_pos k5Alpha_pos hu0)
    have hlt := lt_of_pow_lt_pow_left₀ 5 hxu0 hp
    linarith
  have hSgtV :
      5 * vr ^ 4 < S := by
    have hxu0 : 0 < k5Alpha * ur := mul_pos k5Alpha_pos hu0
    have hinner :
        0 <
          (k5Alpha * ur) ^ 3 +
            2 * (k5Alpha * ur) ^ 2 * vr +
            3 * (k5Alpha * ur) * vr ^ 2 + 4 * vr ^ 3 := by
      positivity
    have hpos :
        0 <
          (k5Alpha * ur - vr) *
            ((k5Alpha * ur) ^ 3 +
              2 * (k5Alpha * ur) ^ 2 * vr +
              3 * (k5Alpha * ur) * vr ^ 2 + 4 * vr ^ 3) := by
      exact mul_pos hxv hinner
    dsimp [S]
    nlinarith [hpos]
  have hqpow :
      q ^ 4 * ur ^ 4 < vr ^ 4 := by
    have hqu0 : 0 ≤ q * ur := le_of_lt (mul_pos hq0 hu0)
    have hp := pow_lt_pow_left₀ hsharp hqu0 (by norm_num : 4 ≠ 0)
    simpa [mul_pow] using hp
  have hSlower :
      5 * q ^ 4 * ur ^ 4 < S := by nlinarith
  have hSpos : 0 < S := lt_trans (by positivity) hSlower
  have hnumPos :
      0 <
        (20 * (1000000 : ℝ) ^ 3 - 5 * (1319507 : ℝ) ^ 3) * ur ^ 3 := by
    have : (0 : ℝ) <
        20 * (1000000 : ℝ) ^ 3 - 5 * (1319507 : ℝ) ^ 3 := by norm_num
    positivity
  have hDquot :
      D <
        ((20 * (1000000 : ℝ) ^ 3 - 5 * (1319507 : ℝ) ^ 3) * ur ^ 3) /
          (1000000 : ℝ) ^ 3 := by
    apply (lt_div_iff₀ (by positivity : (0 : ℝ) < (1000000 : ℝ) ^ 3)).2
    nlinarith
  have hxvQuot :
      k5Alpha * ur - vr <
        (((20 * (1000000 : ℝ) ^ 3 - 5 * (1319507 : ℝ) ^ 3) * ur ^ 3) /
            (1000000 : ℝ) ^ 3) /
          (5 * q ^ 4 * ur ^ 4) := by
    have hxvEq : k5Alpha * ur - vr = D / S := by
      apply (eq_div_iff hSpos.ne').2
      exact hfactor.symm
    rw [hxvEq]
    calc
      D / S <
          (((20 * (1000000 : ℝ) ^ 3 - 5 * (1319507 : ℝ) ^ 3) * ur ^ 3) /
            (1000000 : ℝ) ^ 3) / S := by
              gcongr
      _ < (((20 * (1000000 : ℝ) ^ 3 - 5 * (1319507 : ℝ) ^ 3) * ur ^ 3) /
            (1000000 : ℝ) ^ 3) / (5 * q ^ 4 * ur ^ 4) := by
              apply div_lt_div_of_pos_left
              · positivity
              · positivity
              · exact hSlower
  have hconstant :
      (((20 * (1000000 : ℝ) ^ 3 - 5 * (1319507 : ℝ) ^ 3) * ur ^ 3) /
            (1000000 : ℝ) ^ 3) /
          (5 * q ^ 4 * ur ^ 4) =
        (k5ApproximationConstant : ℝ) / ur := by
    dsimp [q, k5ApproximationConstant]
    field_simp
    ring
  rw [hconstant] at hxvQuot
  have hratio :
      k5Alpha - vr / ur <
        (k5ApproximationConstant : ℝ) / ur ^ 2 := by
    rw [show k5Alpha - vr / ur = (k5Alpha * ur - vr) / ur by
      field_simp]
    rw [div_lt_iff₀ hu0]
    have hc :
        (k5ApproximationConstant : ℝ) / ur ^ 2 * ur =
          (k5ApproximationConstant : ℝ) / ur := by
      field_simp
    rw [hc]
    exact hxvQuot
  have hsign : vr / ur - k5Alpha < 0 := by
    have : vr < k5Alpha * ur := by linarith
    have hdiv : vr / ur < k5Alpha := (div_lt_iff₀ hu0).2 this
    linarith
  rw [abs_of_nonpos (le_of_lt hsign)]
  simpa [ur, vr] using hratio

#print axioms k5_integral_ratio_lower_sharp
#print axioms k5_fifth_defect_bounds
#print axioms k5_alpha_approximation

end Erdos686Variant
end Erdos686
