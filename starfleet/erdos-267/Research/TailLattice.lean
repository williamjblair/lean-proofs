import Research.GlobalCoefficient

/-!
# Fixed quadratic lattice for normalized rational tails
-/

namespace Research

open Real goldenRatio
open scoped BigOperators

/-- Membership in the scaled quadratic lattice `(1/q) ℤ[φ]`. -/
def InScaledGoldenLattice (q : ℕ) (x : ℝ) : Prop :=
  ∃ A B : ℤ, x = ((A : ℝ) + (B : ℝ) * φ) / (q : ℝ)

/-- The scaled golden lattice is closed under addition. -/
theorem InScaledGoldenLattice.add {q : ℕ} (hq : 0 < q) {x y : ℝ}
    (hx : InScaledGoldenLattice q x) (hy : InScaledGoldenLattice q y) :
    InScaledGoldenLattice q (x + y) := by
  obtain ⟨A, B, rfl⟩ := hx
  obtain ⟨C, D, rfl⟩ := hy
  refine ⟨A + C, B + D, ?_⟩
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hq
  push_cast
  field_simp
  ring

/-- The scaled golden lattice is closed under negation. -/
theorem InScaledGoldenLattice.neg {q : ℕ} {x : ℝ}
    (hx : InScaledGoldenLattice q x) :
    InScaledGoldenLattice q (-x) := by
  obtain ⟨A, B, rfl⟩ := hx
  refine ⟨-A, -B, ?_⟩
  push_cast
  ring

/-- The scaled golden lattice is closed under subtraction. -/
theorem InScaledGoldenLattice.sub {q : ℕ} (hq : 0 < q) {x y : ℝ}
    (hx : InScaledGoldenLattice q x) (hy : InScaledGoldenLattice q y) :
    InScaledGoldenLattice q (x - y) := by
  rw [sub_eq_add_neg]
  exact hx.add hq hy.neg

/-- Multiplication by an integer preserves the denominator. -/
theorem InScaledGoldenLattice.int_mul {q : ℕ} {x : ℝ}
    (C : ℤ) (hx : InScaledGoldenLattice q x) :
    InScaledGoldenLattice q ((C : ℝ) * x) := by
  obtain ⟨A, B, rfl⟩ := hx
  refine ⟨C * A, C * B, ?_⟩
  push_cast
  ring

/-- Multiplication by any nonnegative power of `φ` preserves the scaled
lattice. -/
theorem InScaledGoldenLattice.goldenRatio_pow_mul {q : ℕ} (_hq : 0 < q)
    {x : ℝ} (hx : InScaledGoldenLattice q x) (p : ℕ) :
    InScaledGoldenLattice q (φ ^ p * x) := by
  induction p with
  | zero => simpa using hx
  | succ p ih =>
      obtain ⟨A, B, hAB⟩ := ih
      refine ⟨B, A + B, ?_⟩
      rw [show φ ^ (p + 1) * x = φ * (φ ^ p * x) by
        rw [pow_succ]
        ring, hAB]
      have hnum :
          φ * ((A : ℝ) + (B : ℝ) * φ) =
            (B : ℝ) + ((A + B : ℤ) : ℝ) * φ := by
        push_cast
        rw [show φ * ((A : ℝ) + (B : ℝ) * φ) =
          (A : ℝ) * φ + (B : ℝ) * φ ^ 2 by ring,
          Real.goldenRatio_sq]
        ring
      rw [← mul_div_assoc, hnum]

/-- Every power of `φ` is an algebraic integer in `ℤ[φ]`. -/
theorem goldenRatio_pow_mem_lattice (p : ℕ) :
    InScaledGoldenLattice 1 (φ ^ p) := by
  have hone : InScaledGoldenLattice 1 (1 : ℝ) := by
    exact ⟨1, 0, by norm_num⟩
  simpa using hone.goldenRatio_pow_mul (by omega) p

/-- An integral golden-lattice element can be viewed with any positive
specified denominator. -/
theorem InScaledGoldenLattice.change_one_to_denominator
    {q : ℕ} (hq : 0 < q) {x : ℝ}
    (hx : InScaledGoldenLattice 1 x) :
    InScaledGoldenLattice q x := by
  obtain ⟨A, B, hAB⟩ := hx
  refine ⟨(q : ℤ) * A, (q : ℤ) * B, ?_⟩
  rw [hAB]
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hq
  push_cast
  field_simp

/-- Every integer multiple of every nonnegative power of `φ` belongs to a
chosen positive scaled lattice. -/
theorem int_mul_goldenRatio_pow_mem_scaled
    (q : ℕ) (hq : 0 < q) (C : ℤ) (p : ℕ) :
    InScaledGoldenLattice q ((C : ℝ) * φ ^ p) := by
  exact (goldenRatio_pow_mem_lattice p).int_mul C |>.change_one_to_denominator hq

/-- A finite sum of elements with one common positive denominator remains in
the same scaled lattice. -/
theorem finset_sum_mem_scaledGoldenLattice
    {ι : Type*} {q : ℕ} (hq : 0 < q) (s : Finset ι) (f : ι → ℝ)
    (hf : ∀ i ∈ s, InScaledGoldenLattice q (f i)) :
    InScaledGoldenLattice q (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      exact ⟨0, 0, by simp⟩
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact (hf a (Finset.mem_insert_self a s)).add hq
        (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

/-- Rationality of the original sum puts its `1/√5` multiple in the fixed
lattice with denominator `5b`. -/
theorem inv_sqrtFive_mul_rational_mem_scaled
    (a : ℤ) (b : ℕ) (hb : 0 < b) :
    InScaledGoldenLattice (5 * b)
      ((√5)⁻¹ * ((a : ℝ) / (b : ℝ))) := by
  refine ⟨-a, 2 * a, ?_⟩
  have hs : √(5 : ℝ) ≠ 0 := by positivity
  have hb0 : (b : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hb
  rw [show φ = (1 + √5) / 2 by rfl]
  push_cast
  field_simp
  rw [show (-1 : ℝ) + (1 + √5) = √5 by ring,
    show √5 * (a : ℝ) * √5 = (a : ℝ) * √5 ^ 2 by ring,
    Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)]

/-- Algebraic normalized prefix residual at cut `N`. -/
noncomputable def normalizedCoefficientResidual (C : ℕ → ℤ) (T : ℝ) (N : ℕ) : ℝ :=
  φ ^ N * T -
    ∑ m ∈ Finset.range N, (C m : ℝ) * φ ^ (N - m)

/-- If `T=S/√5` and `S=a/b`, every normalized prefix residual lies in one
fixed lattice `(1/(5b))ℤ[φ]`, independently of the cut. -/
theorem normalizedCoefficientResidual_mem_fixed_lattice
    (C : ℕ → ℤ) (a : ℤ) (b N : ℕ) (hb : 0 < b) :
    InScaledGoldenLattice (5 * b)
      (normalizedCoefficientResidual C
        ((√5)⁻¹ * ((a : ℝ) / (b : ℝ))) N) := by
  have hq : 0 < 5 * b := by omega
  apply InScaledGoldenLattice.sub hq
  · exact (inv_sqrtFive_mul_rational_mem_scaled a b hb).goldenRatio_pow_mul hq N
  · apply finset_sum_mem_scaledGoldenLattice hq
    intro m hm
    exact int_mul_goldenRatio_pow_mem_scaled (5 * b) hq (C m) (N - m)

end Research
