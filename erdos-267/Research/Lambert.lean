import Research.TwoOverlap

/-!
# Exact Lambert expansion of a reciprocal Fibonacci number
-/

namespace Research

open Filter Topology
open Real goldenRatio
open scoped BigOperators

/-- Exact signed `φ`-power expansion of one reciprocal Fibonacci number. -/
theorem hasSum_inv_fib_lambert (n : ℕ) (hn : 0 < n) :
    HasSum
      (fun j : ℕ =>
        √5 * ((-1 : ℝ) ^ (n * j) *
          (φ⁻¹) ^ ((2 * j + 1) * n)))
      (Nat.fib n : ℝ)⁻¹ := by
  let r : ℝ := φ⁻¹
  let q : ℝ := (-1 : ℝ) ^ n * r ^ (2 * n)
  have hr0 : 0 ≤ r := by dsimp [r]; exact (inv_pos.mpr Real.goldenRatio_pos).le
  have hr1 : r < 1 := by dsimp [r]; exact inv_lt_one_of_one_lt₀ Real.one_lt_goldenRatio
  have hrabs : |r| < 1 := by simpa [abs_of_nonneg hr0] using hr1
  have hqabs : |q| < 1 := by
    dsimp [q]
    rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
      abs_pow, abs_of_nonneg hr0]
    exact pow_lt_one₀ hr0 hr1 (by omega)
  have hgeom := (hasSum_geometric_of_abs_lt_one hqabs).const_smul (√5 * r ^ n)
  have hseries :
      HasSum (fun j : ℕ =>
        √5 * ((-1 : ℝ) ^ (n * j) * r ^ ((2 * j + 1) * n)))
        ((√5 * r ^ n) * (1 - q)⁻¹) := by
    convert hgeom using 1
    · ext j
      dsimp [q]
      rw [mul_pow, ← pow_mul, ← pow_mul]
      ring_nf
    · rfl
  have hpsi : ψ = -r := by
    dsimp [r]
    linarith [Real.inv_goldenRatio]
  have hpsi_pow : ψ ^ n = (-1 : ℝ) ^ n * r ^ n := by
    rw [hpsi, neg_pow]
  have hunit : φ ^ n * r ^ n = 1 := by
    dsimp [r]
    rw [inv_pow, mul_inv_cancel₀ (pow_ne_zero _ Real.goldenRatio_ne_zero)]
  have hqne : 1 - q ≠ 0 := by
    have habsne : |q| ≠ 1 := ne_of_lt hqabs
    intro h
    have hq : q = 1 := (sub_eq_zero.mp h).symm
    exact habsne (by rw [hq, abs_one])
  have hsqrt : √5 ≠ 0 := by positivity
  have hden : 1 - ((-1 : ℝ) ^ n * r ^ (2 * n)) ≠ 0 := by
    simpa [q] using hqne
  have hrr : r ^ n * r ^ n = r ^ (2 * n) := by
    rw [← pow_add]
    congr 1
    omega
  have hvalue : ((√5 * r ^ n) * (1 - q)⁻¹) = (Nat.fib n : ℝ)⁻¹ := by
    symm
    apply inv_eq_of_mul_eq_one_right
    rw [Real.coe_fib_eq, hpsi_pow]
    dsimp [q]
    field_simp [hden, hsqrt]
    rw [mul_sub, show r ^ n * φ ^ n = 1 by simpa [mul_comm] using hunit,
      show r ^ n * ((-1 : ℝ) ^ n * r ^ n) =
        (-1 : ℝ) ^ n * r ^ (2 * n) by rw [← hrr]; ring]
  rw [hvalue] at hseries
  simpa [r] using hseries

/-- Residue-class description of the coefficient contributed by `1/F_n` in
its exact Lambert expansion.  It has period dividing `4n`. -/
def fibLambertCoeff (n m : ℕ) : ℤ :=
  if Even n then
    if m % (2 * n) = n then 1 else 0
  else
    if m % (4 * n) = n then 1
    else if m % (4 * n) = 3 * n then -1 else 0

/-- Every individual reciprocal-Fibonacci coefficient pattern is periodic with
period `4n`. -/
theorem fibLambertCoeff_add_four_mul (n m : ℕ) :
    fibLambertCoeff n (m + 4 * n) = fibLambertCoeff n m := by
  have h4 : (m + 4 * n) % (4 * n) = m % (4 * n) := by simp
  have h2 : (m + 4 * n) % (2 * n) = m % (2 * n) := by
    rw [show 4 * n = 2 * (2 * n) by omega]
    simp
  unfold fibLambertCoeff
  rw [h2, h4]

/-- The coefficient contributed by one summand is always `-1`, `0`, or `1`. -/
theorem abs_fibLambertCoeff_le_one (n m : ℕ) :
    |fibLambertCoeff n m| ≤ 1 := by
  unfold fibLambertCoeff
  split_ifs <;> norm_num

end Research
