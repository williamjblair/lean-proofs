import Research.GoldenNorm

/-!
# Summing the collected Lambert coefficient series
-/

namespace Research

open Filter Topology
open Real goldenRatio
open scoped BigOperators

set_option maxHeartbeats 800000

private theorem even_coefficient_period_sum
    (n : ℕ) (hn : 0 < n) (he : Even n) (j : ℕ) (r : ℝ) :
    (∑ x : Fin (2 * n),
      (fibLambertCoeff n (j * (2 * n) + x) : ℝ) *
        r ^ (j * (2 * n) + x)) =
      r ^ (j * (2 * n) + n) := by
  have hnlt : n < 2 * n := by omega
  let y : Fin (2 * n) := ⟨n, hnlt⟩
  have hmod (x : Fin (2 * n)) :
      (j * (2 * n) + (x : ℕ)) % (2 * n) = x :=
    Nat.mul_add_mod_of_lt x.isLt
  have hcond (x : Fin (2 * n)) : ((x : ℕ) = n) ↔ x = y := by
    simp [y, Fin.ext_iff]
  simp only [fibLambertCoeff, if_pos he]
  simp_rw [hmod, hcond]
  simp only [Int.cast_ite, Int.cast_one, Int.cast_zero, ite_mul, one_mul, zero_mul]
  rw [Fintype.sum_ite_eq' y]

private theorem odd_coefficient_period_sum
    (n : ℕ) (hn : 0 < n) (ho : ¬ Even n) (j : ℕ) (r : ℝ) :
    (∑ x : Fin (4 * n),
      (fibLambertCoeff n (j * (4 * n) + x) : ℝ) *
        r ^ (j * (4 * n) + x)) =
      r ^ (j * (4 * n) + n) - r ^ (j * (4 * n) + 3 * n) := by
  have hnlt : n < 4 * n := by omega
  have h3nlt : 3 * n < 4 * n := by omega
  let y : Fin (4 * n) := ⟨n, hnlt⟩
  let z : Fin (4 * n) := ⟨3 * n, h3nlt⟩
  have hmod (x : Fin (4 * n)) :
      (j * (4 * n) + (x : ℕ)) % (4 * n) = x :=
    Nat.mul_add_mod_of_lt x.isLt
  have hcond (x : Fin (4 * n)) : ((x : ℕ) = n) ↔ x = y := by
    simp [y, Fin.ext_iff]
  have hcond3 (x : Fin (4 * n)) : ((x : ℕ) = 3 * n) ↔ x = z := by
    simp [z, Fin.ext_iff]
  simp only [fibLambertCoeff, if_neg ho]
  simp_rw [hmod, hcond, hcond3]
  simp only [Int.cast_ite, Int.cast_one, Int.cast_zero, Int.cast_neg, ite_mul,
    one_mul, zero_mul, neg_mul]
  have hyz : y ≠ z := by
    intro h
    have hv := congrArg Fin.val h
    dsimp [y, z] at hv
    omega
  calc
    (∑ x, if x = y then r ^ (j * (4 * n) + (x : ℕ))
      else if x = z then -r ^ (j * (4 * n) + (x : ℕ)) else 0) =
        (∑ x, if x = y then r ^ (j * (4 * n) + (x : ℕ)) else 0) +
        (∑ x, if x = z then -r ^ (j * (4 * n) + (x : ℕ)) else 0) := by
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro x hx
          by_cases hxy : x = y
          · simp [hxy, hyz]
          · by_cases hxz : x = z <;> simp [hxy, hxz, Ne.symm hyz]
    _ = r ^ (j * (4 * n) + n) - r ^ (j * (4 * n) + 3 * n) := by
      rw [Fintype.sum_ite_eq' y, Fintype.sum_ite_eq' z]
      rfl

/-- The residue-class coefficient series for one reciprocal Fibonacci summand
is absolutely summable. -/
theorem summable_fibLambertCoeff_mul_invPhi_pow (n : ℕ) :
    Summable (fun m : ℕ =>
      (fibLambertCoeff n m : ℝ) * (φ⁻¹) ^ m) := by
  let r : ℝ := φ⁻¹
  have hr0 : 0 ≤ r := by
    dsimp [r]
    exact (inv_pos.mpr Real.goldenRatio_pos).le
  have hr1 : r < 1 := by
    dsimp [r]
    exact inv_lt_one_of_one_lt₀ Real.one_lt_goldenRatio
  change Summable (fun m : ℕ =>
    (fibLambertCoeff n m : ℝ) * r ^ m)
  have hgeom : Summable (fun m : ℕ => r ^ m) :=
    summable_geometric_of_norm_lt_one (by
      simpa [Real.norm_eq_abs, abs_of_nonneg hr0] using hr1)
  apply Summable.of_norm_bounded hgeom
  intro m
  have hc : |(fibLambertCoeff n m : ℝ)| ≤ 1 := by
    exact_mod_cast abs_fibLambertCoeff_le_one n m
  rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg hr0]
  simpa [r] using mul_le_mul_of_nonneg_right hc (pow_nonneg hr0 m)

/-- Closed form of the coefficient generating series for one selected index. -/
theorem hasSum_fibLambertCoeff_mul_invPhi_pow
    (n : ℕ) (hn : 0 < n) :
    HasSum (fun m : ℕ =>
      (fibLambertCoeff n m : ℝ) * (φ⁻¹) ^ m)
      ((φ⁻¹) ^ n *
        (1 - (-1 : ℝ) ^ n * (φ⁻¹) ^ (2 * n))⁻¹) := by
  let r : ℝ := φ⁻¹
  have hr0 : 0 ≤ r := by
    dsimp [r]
    exact (inv_pos.mpr Real.goldenRatio_pos).le
  have hr1 : r < 1 := by
    dsimp [r]
    exact inv_lt_one_of_one_lt₀ Real.one_lt_goldenRatio
  have hf : Summable (fun m : ℕ =>
      (fibLambertCoeff n m : ℝ) * r ^ m) := by
    simpa [r] using summable_fibLambertCoeff_mul_invPhi_pow n
  by_cases he : Even n
  · letI : NeZero (2 * n) := ⟨by omega⟩
    have hprod : HasSum
        (fun p : ℕ × Fin (2 * n) =>
          (fibLambertCoeff n (p.1 * (2 * n) + p.2) : ℝ) *
            r ^ (p.1 * (2 * n) + p.2))
        (∑' m : ℕ, (fibLambertCoeff n m : ℝ) * r ^ m) := by
      exact (Nat.divModEquiv (2 * n)).symm.hasSum_iff.mpr hf.hasSum
    have hrows : HasSum (fun j : ℕ => r ^ (j * (2 * n) + n))
        (∑' m : ℕ, (fibLambertCoeff n m : ℝ) * r ^ m) := by
      apply hprod.prod_fiberwise
      intro j
      convert hasSum_fintype (fun x : Fin (2 * n) =>
        (fibLambertCoeff n (j * (2 * n) + x) : ℝ) *
          r ^ (j * (2 * n) + x)) using 1
      exact (even_coefficient_period_sum n hn he j r).symm
    have hgeom : HasSum (fun j : ℕ => r ^ (j * (2 * n) + n))
        (r ^ n * (1 - r ^ (2 * n))⁻¹) := by
      have hg := (hasSum_geometric_of_abs_lt_one
        (show |r ^ (2 * n)| < 1 by
          rw [abs_pow, abs_of_nonneg hr0]
          exact pow_lt_one₀ hr0 hr1 (by omega))).mul_left (r ^ n)
      simpa only [← pow_mul, ← pow_add, Nat.mul_comm, Nat.add_comm] using hg
    have hv := hrows.unique hgeom
    rw [Even.neg_one_pow he, one_mul]
    rw [← hv]
    simpa [r] using hf.hasSum
  · have ho : Odd n := Nat.not_even_iff_odd.mp he
    letI : NeZero (4 * n) := ⟨by omega⟩
    have hprod : HasSum
        (fun p : ℕ × Fin (4 * n) =>
          (fibLambertCoeff n (p.1 * (4 * n) + p.2) : ℝ) *
            r ^ (p.1 * (4 * n) + p.2))
        (∑' m : ℕ, (fibLambertCoeff n m : ℝ) * r ^ m) := by
      exact (Nat.divModEquiv (4 * n)).symm.hasSum_iff.mpr hf.hasSum
    have hrows : HasSum
        (fun j : ℕ => r ^ (j * (4 * n) + n) -
          r ^ (j * (4 * n) + 3 * n))
        (∑' m : ℕ, (fibLambertCoeff n m : ℝ) * r ^ m) := by
      apply hprod.prod_fiberwise
      intro j
      convert hasSum_fintype (fun x : Fin (4 * n) =>
        (fibLambertCoeff n (j * (4 * n) + x) : ℝ) *
          r ^ (j * (4 * n) + x)) using 1
      exact (odd_coefficient_period_sum n hn he j r).symm
    have hgeom : HasSum
        (fun j : ℕ => r ^ (j * (4 * n) + n) -
          r ^ (j * (4 * n) + 3 * n))
        ((r ^ n - r ^ (3 * n)) * (1 - r ^ (4 * n))⁻¹) := by
      have hg := (hasSum_geometric_of_abs_lt_one
        (show |r ^ (4 * n)| < 1 by
          rw [abs_pow, abs_of_nonneg hr0]
          exact pow_lt_one₀ hr0 hr1 (by omega))).mul_left
            (r ^ n - r ^ (3 * n))
      simpa only [sub_mul, ← pow_mul, ← pow_add, Nat.mul_comm,
        Nat.add_comm] using hg
    have hv := hrows.unique hgeom
    have h2lt : r ^ (2 * n) < 1 := pow_lt_one₀ hr0 hr1 (by omega)
    have hplus : 1 + r ^ (2 * n) ≠ 0 := by positivity
    have hminus : 1 - r ^ (4 * n) ≠ 0 := by
      have : r ^ (4 * n) < 1 := pow_lt_one₀ hr0 hr1 (by omega)
      linarith
    rw [Odd.neg_one_pow ho, neg_mul, sub_neg_eq_add, one_mul]
    change HasSum (fun m : ℕ =>
      (fibLambertCoeff n m : ℝ) * r ^ m)
      (r ^ n * (1 + r ^ (2 * n))⁻¹)
    have hclosed :
        (r ^ n - r ^ (3 * n)) * (1 - r ^ (4 * n))⁻¹ =
          r ^ n * (1 + r ^ (2 * n))⁻¹ := by
      field_simp [hplus, hminus]
      rw [show r ^ (3 * n) = r ^ n * r ^ (2 * n) by
        rw [← pow_add]
        congr 1
        omega,
        show r ^ (4 * n) = r ^ (2 * n) * r ^ (2 * n) by
          rw [← pow_add]
          congr 1
          omega]
      ring
    rw [← hclosed, ← hv]
    exact hf.hasSum

/-- The collected coefficient series sums to exactly `1/(√5 F_n)`. -/
theorem hasSum_fibLambertCoeff_eq_inv_sqrtFive_mul_inv_fib
    (n : ℕ) (hn : 0 < n) :
    HasSum (fun m : ℕ =>
      (fibLambertCoeff n m : ℝ) * (φ⁻¹) ^ m)
      ((√5)⁻¹ * (Nat.fib n : ℝ)⁻¹) := by
  let r : ℝ := φ⁻¹
  let q : ℝ := (-1 : ℝ) ^ n * r ^ (2 * n)
  have hcoeff := hasSum_fibLambertCoeff_mul_invPhi_pow n hn
  have hpsi : ψ = -r := by
    dsimp [r]
    linarith [Real.inv_goldenRatio]
  have hpsi_pow : ψ ^ n = (-1 : ℝ) ^ n * r ^ n := by
    rw [hpsi, neg_pow]
  have hunit : φ ^ n * r ^ n = 1 := by
    dsimp [r]
    rw [inv_pow, mul_inv_cancel₀ (pow_ne_zero _ Real.goldenRatio_ne_zero)]
  have hr0 : 0 ≤ r := by
    dsimp [r]
    exact (inv_pos.mpr Real.goldenRatio_pos).le
  have hr1 : r < 1 := by
    dsimp [r]
    exact inv_lt_one_of_one_lt₀ Real.one_lt_goldenRatio
  have hqabs : |q| < 1 := by
    dsimp [q]
    rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
      abs_pow, abs_of_nonneg hr0]
    exact pow_lt_one₀ hr0 hr1 (by omega)
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
  have hvalue :
      √5 * (r ^ n * (1 - (-1 : ℝ) ^ n * r ^ (2 * n))⁻¹) =
        (Nat.fib n : ℝ)⁻¹ := by
    symm
    apply inv_eq_of_mul_eq_one_right
    rw [Real.coe_fib_eq, hpsi_pow]
    field_simp [hden, hsqrt]
    rw [mul_sub, show r ^ n * φ ^ n = 1 by
      simpa [mul_comm] using hunit,
      show r ^ n * ((-1 : ℝ) ^ n * r ^ n) =
        (-1 : ℝ) ^ n * r ^ (2 * n) by rw [← hrr]; ring]
  have hclosed :
      r ^ n * (1 - (-1 : ℝ) ^ n * r ^ (2 * n))⁻¹ =
        (√5)⁻¹ * (Nat.fib n : ℝ)⁻¹ := by
    rw [← hvalue]
    field_simp
  change HasSum (fun m : ℕ =>
    (fibLambertCoeff n m : ℝ) * r ^ m)
    (r ^ n * (1 - (-1 : ℝ) ^ n * r ^ (2 * n))⁻¹) at hcoeff
  rw [hclosed] at hcoeff
  simpa [r] using hcoeff

end Research
