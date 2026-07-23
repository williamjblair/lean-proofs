import Research.TailAnalysis

/-!
# Conjugate normalized tails and the paired lattice
-/

namespace Research

open Real goldenRatio
open scoped BigOperators

/-- Two real numbers represented by the two embeddings of one element of
`(1/q)ℤ[φ]`. -/
def InScaledGoldenPair (q : ℕ) (x y : ℝ) : Prop :=
  ∃ A B : ℤ,
    x = ((A : ℝ) + (B : ℝ) * φ) / (q : ℝ) ∧
    y = ((A : ℝ) + (B : ℝ) * ψ) / (q : ℝ)

/-- Paired lattice closure under addition. -/
theorem InScaledGoldenPair.add {q : ℕ} (hq : 0 < q)
    {x y x' y' : ℝ} (h : InScaledGoldenPair q x y)
    (h' : InScaledGoldenPair q x' y') :
    InScaledGoldenPair q (x + x') (y + y') := by
  obtain ⟨A, B, hx, hy⟩ := h
  obtain ⟨C, D, hx', hy'⟩ := h'
  refine ⟨A + C, B + D, ?_, ?_⟩
  · rw [hx, hx']
    push_cast
    field_simp
    ring
  · rw [hy, hy']
    push_cast
    field_simp
    ring

/-- Paired lattice closure under negation. -/
theorem InScaledGoldenPair.neg {q : ℕ} {x y : ℝ}
    (h : InScaledGoldenPair q x y) :
    InScaledGoldenPair q (-x) (-y) := by
  obtain ⟨A, B, hx, hy⟩ := h
  refine ⟨-A, -B, ?_, ?_⟩
  · rw [hx]
    push_cast
    ring
  · rw [hy]
    push_cast
    ring

/-- Paired lattice closure under subtraction. -/
theorem InScaledGoldenPair.sub {q : ℕ} (hq : 0 < q)
    {x y x' y' : ℝ} (h : InScaledGoldenPair q x y)
    (h' : InScaledGoldenPair q x' y') :
    InScaledGoldenPair q (x - x') (y - y') := by
  rw [sub_eq_add_neg, sub_eq_add_neg]
  exact h.add hq h'.neg

/-- Paired lattice closure under integer scaling. -/
theorem InScaledGoldenPair.int_mul {q : ℕ} (C : ℤ) {x y : ℝ}
    (h : InScaledGoldenPair q x y) :
    InScaledGoldenPair q ((C : ℝ) * x) ((C : ℝ) * y) := by
  obtain ⟨A, B, hx, hy⟩ := h
  refine ⟨C * A, C * B, ?_, ?_⟩
  · rw [hx]
    push_cast
    ring
  · rw [hy]
    push_cast
    ring

/-- Simultaneous multiplication by corresponding powers in the two embeddings
preserves the paired lattice. -/
theorem InScaledGoldenPair.powers_mul {q : ℕ}
    {x y : ℝ} (h : InScaledGoldenPair q x y) (p : ℕ) :
    InScaledGoldenPair q (φ ^ p * x) (ψ ^ p * y) := by
  induction p with
  | zero => simpa using h
  | succ p ih =>
      obtain ⟨A, B, hx, hy⟩ := ih
      refine ⟨B, A + B, ?_, ?_⟩
      · rw [show φ ^ (p + 1) * x = φ * (φ ^ p * x) by
          rw [pow_succ]
          ring, hx]
        rw [← mul_div_assoc]
        congr 1
        push_cast
        rw [show φ * ((A : ℝ) + (B : ℝ) * φ) =
          (A : ℝ) * φ + (B : ℝ) * φ ^ 2 by ring,
          Real.goldenRatio_sq]
        ring
      · rw [show ψ ^ (p + 1) * y = ψ * (ψ ^ p * y) by
          rw [pow_succ]
          ring, hy]
        rw [← mul_div_assoc]
        congr 1
        push_cast
        rw [show ψ * ((A : ℝ) + (B : ℝ) * ψ) =
          (A : ℝ) * ψ + (B : ℝ) * ψ ^ 2 by ring,
          Real.goldenConj_sq]
        ring

/-- Paired algebraic-integer powers. -/
theorem golden_powers_mem_pair (p : ℕ) :
    InScaledGoldenPair 1 (φ ^ p) (ψ ^ p) := by
  have hone : InScaledGoldenPair 1 (1 : ℝ) (1 : ℝ) := by
    exact ⟨1, 0, by norm_num, by norm_num⟩
  simpa using hone.powers_mul p

/-- Change an integral paired element to a specified positive denominator. -/
theorem InScaledGoldenPair.change_one_to_denominator
    {q : ℕ} (hq : 0 < q) {x y : ℝ}
    (h : InScaledGoldenPair 1 x y) :
    InScaledGoldenPair q x y := by
  obtain ⟨A, B, hx, hy⟩ := h
  refine ⟨(q : ℤ) * A, (q : ℤ) * B, ?_, ?_⟩
  · rw [hx]
    push_cast
    field_simp
  · rw [hy]
    push_cast
    field_simp

/-- Paired integer multiples of corresponding powers. -/
theorem int_mul_golden_powers_mem_pair
    (q : ℕ) (hq : 0 < q) (C : ℤ) (p : ℕ) :
    InScaledGoldenPair q ((C : ℝ) * φ ^ p) ((C : ℝ) * ψ ^ p) := by
  exact (golden_powers_mem_pair p).int_mul C |>.change_one_to_denominator hq

/-- Finite sums preserve a paired denominator. -/
theorem finset_sum_mem_scaledGoldenPair
    {ι : Type*} {q : ℕ} (hq : 0 < q) (s : Finset ι)
    (f g : ι → ℝ) (hfg : ∀ i ∈ s, InScaledGoldenPair q (f i) (g i)) :
    InScaledGoldenPair q (∑ i ∈ s, f i) (∑ i ∈ s, g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, 0, by simp, by simp⟩
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      exact (hfg a (Finset.mem_insert_self a s)).add hq
        (ih fun i hi => hfg i (Finset.mem_insert_of_mem hi))

/-- The two embeddings of `(a/b)/√5` are opposite and form one paired lattice
element with denominator `5b`. -/
theorem rational_inv_sqrtFive_mem_pair
    (a : ℤ) (b : ℕ) (hb : 0 < b) :
    InScaledGoldenPair (5 * b)
      ((√5)⁻¹ * ((a : ℝ) / (b : ℝ)))
      (-((√5)⁻¹ * ((a : ℝ) / (b : ℝ)))) := by
  refine ⟨-a, 2 * a, ?_, ?_⟩
  · have hs : √(5 : ℝ) ≠ 0 := by positivity
    have hb0 : (b : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hb
    rw [show φ = (1 + √5) / 2 by rfl]
    push_cast
    field_simp
    rw [show (-1 : ℝ) + (1 + √5) = √5 by ring,
      show √5 * (a : ℝ) * √5 = (a : ℝ) * √5 ^ 2 by ring,
      Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)]
  · have hs : √(5 : ℝ) ≠ 0 := by positivity
    have hb0 : (b : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hb
    rw [show ψ = (1 - √5) / 2 by rfl]
    push_cast
    field_simp
    rw [show (-1 : ℝ) + (1 - √5) = -√5 by ring,
      show √5 * (a : ℝ) * (-√5) = -(a : ℝ) * √5 ^ 2 by ring,
      Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)]
    ring

/-- Conjugate algebraic prefix residual at a cut. -/
noncomputable def conjugateCoefficientResidual (C : ℕ → ℤ)
    (Tconj : ℝ) (N : ℕ) : ℝ :=
  ψ ^ N * Tconj -
    ∑ m ∈ Finset.range N, (C m : ℝ) * ψ ^ (N - m)

/-- Under `S=a/b`, the principal and conjugate normalized residuals are the two
embeddings of one element of the fixed lattice `(1/(5b))ℤ[φ]`. -/
theorem normalized_and_conjugate_residual_mem_pair
    (C : ℕ → ℤ) (a : ℤ) (b N : ℕ) (hb : 0 < b) :
    InScaledGoldenPair (5 * b)
      (normalizedCoefficientResidual C
        ((√5)⁻¹ * ((a : ℝ) / (b : ℝ))) N)
      (conjugateCoefficientResidual C
        (-((√5)⁻¹ * ((a : ℝ) / (b : ℝ)))) N) := by
  have hq : 0 < 5 * b := by omega
  apply InScaledGoldenPair.sub hq
  · exact (rational_inv_sqrtFive_mem_pair a b hb).powers_mul N
  · apply finset_sum_mem_scaledGoldenPair hq
    intro m hm
    exact int_mul_golden_powers_mem_pair (5 * b) hq (C m) (N - m)

/-- Paired norm lower bound in directly usable form. -/
theorem InScaledGoldenPair.norm_lower {q : ℕ} (hq : 0 < q)
    {x y : ℝ} (h : InScaledGoldenPair q x y) (hx : x ≠ 0) :
    ((q : ℝ)⁻¹) ^ 2 ≤ |x| * |y| := by
  obtain ⟨A, B, hxAB, hyAB⟩ := h
  have hAB : A ≠ 0 ∨ B ≠ 0 := by
    by_contra hz
    simp only [not_or, not_not] at hz
    rcases hz with ⟨rfl, rfl⟩
    simp at hxAB
    exact hx hxAB
  rw [hxAB, hyAB]
  exact inv_sq_le_abs_scaled_golden_mul_abs_conj A B q hq hAB

end Research
