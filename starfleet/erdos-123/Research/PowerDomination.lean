import Mathlib

namespace Erdos123

open Filter Asymptotics

/-- A power of a larger natural base eventually dominates any fixed multiple
of the corresponding power of a smaller base. -/
theorem eventually_const_mul_pow_le_pow {x y C : ℕ} (hxy : x < y) :
    ∃ N : ℕ, ∀ n, N ≤ n → C * x ^ n ≤ y ^ n := by
  have hreal : (0 : ℝ) ≤ (x : ℝ) := by positivity
  have hlt : (x : ℝ) < (y : ℝ) := by exact_mod_cast hxy
  have ho := isLittleO_pow_pow_of_lt_left hreal hlt
  have hcpos : (0 : ℝ) < ((C + 1 : ℕ) : ℝ)⁻¹ := by positivity
  have hev := ho.bound hcpos
  rw [eventually_atTop] at hev
  rcases hev with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn
  have hh := hN n hn
  simp only [Real.norm_eq_abs, abs_pow,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ x),
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ y)] at hh
  have hmult : (((C + 1 : ℕ) : ℝ) * (x : ℝ) ^ n) ≤ (y : ℝ) ^ n := by
    have hcp : (0 : ℝ) < ((C + 1 : ℕ) : ℝ) := by positivity
    calc
      (((C + 1 : ℕ) : ℝ) * (x : ℝ) ^ n)
          ≤ ((C + 1 : ℕ) : ℝ) *
              (((C + 1 : ℕ) : ℝ)⁻¹ * (y : ℝ) ^ n) :=
            mul_le_mul_of_nonneg_left hh hcp.le
      _ = (y : ℝ) ^ n := by field_simp
  have hC : (((C : ℕ) : ℝ) * (x : ℝ) ^ n) ≤ (y : ℝ) ^ n := by
    apply le_trans _ hmult
    gcongr
    norm_num
  exact_mod_cast hC

/-- If `a<c`, one can choose a positive exponent for which the `c` power
beats an arbitrarily prescribed multiple of the `a` power. -/
theorem exists_positive_pow_multiple_le {a c K : ℕ} (hac : a < c) :
    ∃ v : ℕ, 0 < v ∧ K * a ^ v ≤ c ^ v := by
  rcases eventually_const_mul_pow_le_pow (C := K) hac with ⟨N, hN⟩
  let v := max N 1
  exact ⟨v, by dsimp [v]; omega, hN v (by dsimp [v]; omega)⟩

end Erdos123
