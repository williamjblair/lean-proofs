import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Tactic

open scoped BigOperators

namespace Erdos521

lemma gaussian_weight_telescoping_pointwise {a x : ℝ} (ha : 0 < a) (hx : 0 ≤ x) :
    x * Real.exp (-a * x ^ 2) ≤
      Real.exp a / (4 * a) *
        (Real.exp (-a * (x - 1) ^ 2) - Real.exp (-a * (x + 1) ^ 2)) := by
  have hz : 0 ≤ 2 * a * x := by positivity
  have hsinh : 2 * a * x ≤ Real.sinh (2 * a * x) :=
    Real.self_le_sinh_iff.mpr hz
  have hdiff :
      2 * Real.exp (-a * (x ^ 2 + 1)) * Real.sinh (2 * a * x) =
        Real.exp (-a * (x - 1) ^ 2) - Real.exp (-a * (x + 1) ^ 2) := by
    rw [Real.sinh_eq]
    field_simp
    rw [mul_sub, ← Real.exp_add, ← Real.exp_add]
    congr 1 <;> ring
  have hfactor : 0 ≤ Real.exp a / (4 * a) := by positivity
  calc
    x * Real.exp (-a * x ^ 2) =
        Real.exp a / (4 * a) *
          (2 * Real.exp (-a * (x ^ 2 + 1)) * (2 * a * x)) := by
      have hexp : Real.exp a * Real.exp (-a * (x ^ 2 + 1)) =
          Real.exp (-a * x ^ 2) := by
        rw [← Real.exp_add]
        congr 1
        ring
      have hexp' : Real.exp (-(x ^ 2 * a)) =
          Real.exp a * Real.exp (-(a * (x ^ 2 + 1))) := by
        rw [show -(x ^ 2 * a) = -a * x ^ 2 by ring, ← hexp]
        congr 2
        ring
      field_simp
      rw [hexp']
      ring
    _ ≤ Real.exp a / (4 * a) *
        (2 * Real.exp (-a * (x ^ 2 + 1)) * Real.sinh (2 * a * x)) := by
      apply mul_le_mul_of_nonneg_left _ hfactor
      exact mul_le_mul_of_nonneg_left hsinh (by positivity)
    _ = _ := by rw [hdiff]

/-- Positive even points on a mesh of width two have the sharp telescoping Gaussian first-moment
bound. -/
lemma sum_even_pos_mul_gaussian_le (a : ℝ) (ha : 0 < a) (M : ℕ) :
    (∑ n ∈ Finset.range M,
      (2 * (n + 1) : ℝ) * Real.exp (-a * (2 * (n + 1) : ℝ) ^ 2)) ≤
      1 / (4 * a) := by
  let G : ℕ → ℝ := fun n ↦ Real.exp (-a * (2 * n + 1 : ℝ) ^ 2)
  have hpoint (n : ℕ) :
      (2 * (n + 1) : ℝ) * Real.exp (-a * (2 * (n + 1) : ℝ) ^ 2) ≤
        Real.exp a / (4 * a) * (G n - G (n + 1)) := by
    have h := gaussian_weight_telescoping_pointwise ha
      (show 0 ≤ (2 * (n + 1) : ℝ) by positivity)
    calc
      (2 * (n + 1) : ℝ) * Real.exp (-a * (2 * (n + 1) : ℝ) ^ 2) ≤
          Real.exp a / (4 * a) *
            (Real.exp (-a * ((2 * (n + 1) : ℝ) - 1) ^ 2) -
              Real.exp (-a * ((2 * (n + 1) : ℝ) + 1) ^ 2)) := h
      _ = Real.exp a / (4 * a) * (G n - G (n + 1)) := by
        congr 2 <;> dsimp [G] <;> congr 1 <;> push_cast <;> ring
  calc
    (∑ n ∈ Finset.range M,
      (2 * (n + 1) : ℝ) * Real.exp (-a * (2 * (n + 1) : ℝ) ^ 2)) ≤
        ∑ n ∈ Finset.range M,
          Real.exp a / (4 * a) * (G n - G (n + 1)) :=
      Finset.sum_le_sum fun n hn ↦ hpoint n
    _ = Real.exp a / (4 * a) * (G 0 - G M) := by
      rw [← Finset.mul_sum, Finset.sum_range_sub']
    _ ≤ Real.exp a / (4 * a) * G 0 := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      linarith [Real.exp_pos (-a * (2 * M + 1 : ℝ) ^ 2)]
    _ = 1 / (4 * a) := by
      dsimp [G]
      norm_num
      rw [show Real.exp a / (4 * a) * Real.exp (-a) =
          (Real.exp a * Real.exp (-a)) / (4 * a) by ring,
        ← Real.exp_add]
      norm_num

/-- Positive odd points on a mesh of width two have the corresponding bound, differing only by the
harmless factor `exp a`. -/
lemma sum_odd_pos_mul_gaussian_le (a : ℝ) (ha : 0 < a) (M : ℕ) :
    (∑ n ∈ Finset.range M,
      (2 * n + 1 : ℝ) * Real.exp (-a * (2 * n + 1 : ℝ) ^ 2)) ≤
      Real.exp a / (4 * a) := by
  let G : ℕ → ℝ := fun n ↦ Real.exp (-a * (2 * n : ℝ) ^ 2)
  have hpoint (n : ℕ) :
      (2 * n + 1 : ℝ) * Real.exp (-a * (2 * n + 1 : ℝ) ^ 2) ≤
        Real.exp a / (4 * a) * (G n - G (n + 1)) := by
    have h := gaussian_weight_telescoping_pointwise ha
      (show 0 ≤ (2 * n + 1 : ℝ) by positivity)
    calc
      (2 * n + 1 : ℝ) * Real.exp (-a * (2 * n + 1 : ℝ) ^ 2) ≤
          Real.exp a / (4 * a) *
            (Real.exp (-a * ((2 * n + 1 : ℝ) - 1) ^ 2) -
              Real.exp (-a * ((2 * n + 1 : ℝ) + 1) ^ 2)) := h
      _ = Real.exp a / (4 * a) * (G n - G (n + 1)) := by
        congr 2 <;> dsimp [G] <;> congr 1 <;> push_cast <;> ring
  calc
    (∑ n ∈ Finset.range M,
      (2 * n + 1 : ℝ) * Real.exp (-a * (2 * n + 1 : ℝ) ^ 2)) ≤
        ∑ n ∈ Finset.range M,
          Real.exp a / (4 * a) * (G n - G (n + 1)) :=
      Finset.sum_le_sum fun n hn ↦ hpoint n
    _ = Real.exp a / (4 * a) * (G 0 - G M) := by
      rw [← Finset.mul_sum, Finset.sum_range_sub']
    _ ≤ Real.exp a / (4 * a) * G 0 := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      linarith [Real.exp_pos (-a * (2 * M : ℝ) ^ 2)]
    _ = Real.exp a / (4 * a) := by simp [G]

noncomputable def gaussianParityMeshTerm (a : ℝ) (L n : ℕ) : ℝ :=
  |-(L : ℝ) + 2 * n| * Real.exp (-a * (-(L : ℝ) + 2 * n) ^ 2)

noncomputable def gaussianParityMeshFirstMoment (a : ℝ) (L : ℕ) : ℝ :=
  ∑ n ∈ Finset.range (L + 1), gaussianParityMeshTerm a L n

lemma gaussianParityMeshTerm_shift (a : ℝ) (L n : ℕ) :
    gaussianParityMeshTerm a (L + 2) (n + 1) = gaussianParityMeshTerm a L n := by
  unfold gaussianParityMeshTerm
  have hv : -((L + 2 : ℕ) : ℝ) + 2 * ((n + 1 : ℕ) : ℝ) =
      -(L : ℝ) + 2 * n := by push_cast; ring
  rw [hv]

lemma gaussianParityMeshTerm_left (a : ℝ) (L : ℕ) :
    gaussianParityMeshTerm a (L + 2) 0 =
      (L + 2 : ℝ) * Real.exp (-a * (L + 2 : ℝ) ^ 2) := by
  unfold gaussianParityMeshTerm
  have hv : -((L + 2 : ℕ) : ℝ) + 2 * (0 : ℕ) = -(L + 2 : ℝ) := by
    push_cast
    ring
  rw [hv, abs_neg, abs_of_nonneg (by positivity)]
  congr 1
  ring

lemma gaussianParityMeshTerm_right (a : ℝ) (L : ℕ) :
    gaussianParityMeshTerm a (L + 2) (L + 2) =
      (L + 2 : ℝ) * Real.exp (-a * (L + 2 : ℝ) ^ 2) := by
  unfold gaussianParityMeshTerm
  have hv : -((L + 2 : ℕ) : ℝ) + 2 * ((L + 2 : ℕ) : ℝ) = (L + 2 : ℝ) := by
    push_cast
    ring
  rw [hv, abs_of_nonneg (by positivity)]

lemma gaussianParityMeshFirstMoment_add_two (a : ℝ) (L : ℕ) :
    gaussianParityMeshFirstMoment a (L + 2) =
      gaussianParityMeshFirstMoment a L +
        2 * (L + 2 : ℝ) * Real.exp (-a * (L + 2 : ℝ) ^ 2) := by
  unfold gaussianParityMeshFirstMoment
  rw [show L + 2 + 1 = (L + 2) + 1 by omega,
    Finset.sum_range_succ', Finset.sum_range_succ]
  rw [show (∑ n ∈ Finset.range (L + 1),
      gaussianParityMeshTerm a (L + 2) (n + 1)) =
      ∑ n ∈ Finset.range (L + 1), gaussianParityMeshTerm a L n by
    apply Finset.sum_congr rfl
    intro n hn
    exact gaussianParityMeshTerm_shift a L n]
  rw [gaussianParityMeshTerm_left, gaussianParityMeshTerm_right]
  ring

lemma gaussianParityMeshFirstMoment_even (a : ℝ) (M : ℕ) :
    gaussianParityMeshFirstMoment a (2 * M) =
      2 * ∑ n ∈ Finset.range M,
        (2 * (n + 1) : ℝ) * Real.exp (-a * (2 * (n + 1) : ℝ) ^ 2) := by
  induction M with
  | zero => simp [gaussianParityMeshFirstMoment, gaussianParityMeshTerm]
  | succ M ih =>
      rw [show 2 * (M + 1) = 2 * M + 2 by omega,
        gaussianParityMeshFirstMoment_add_two, ih]
      have heq : ((2 * M : ℕ) : ℝ) + 2 = 2 * (M + 1 : ℝ) := by
        push_cast
        ring
      have hsum := Finset.sum_range_succ
        (fun n : ℕ ↦ (2 * (n + 1) : ℝ) *
          Real.exp (-a * (2 * (n + 1) : ℝ) ^ 2)) M
      rw [hsum, heq]
      ring

lemma gaussianParityMeshFirstMoment_odd (a : ℝ) (M : ℕ) :
    gaussianParityMeshFirstMoment a (2 * M + 1) =
      2 * ∑ n ∈ Finset.range (M + 1),
        (2 * n + 1 : ℝ) * Real.exp (-a * (2 * n + 1 : ℝ) ^ 2) := by
  induction M with
  | zero =>
      norm_num [gaussianParityMeshFirstMoment, gaussianParityMeshTerm,
        Finset.sum_range_succ]
      ring
  | succ M ih =>
      rw [show 2 * (M + 1) + 1 = (2 * M + 1) + 2 by omega,
        gaussianParityMeshFirstMoment_add_two, ih]
      have heq : ((2 * M + 1 : ℕ) : ℝ) + 2 =
          2 * ((M + 1 : ℕ) : ℝ) + 1 := by
        push_cast
        ring
      have hend : 2 * ((((2 * M + 1 : ℕ) : ℝ) + 2) *
          Real.exp (-a * (((2 * M + 1 : ℕ) : ℝ) + 2) ^ 2)) =
          2 * ((2 * ((M + 1 : ℕ) : ℝ) + 1) *
            Real.exp (-a * (2 * ((M + 1 : ℕ) : ℝ) + 1) ^ 2)) := by
        rw [heq]
      have hsum := Finset.sum_range_succ
        (fun n : ℕ ↦ (2 * n + 1 : ℝ) *
          Real.exp (-a * (2 * n + 1 : ℝ) ^ 2)) (M + 1)
      rw [hsum]
      linear_combination hend

/-- A complete finite affine parity mesh has Gaussian first moment at most
`exp(a)/(2a)`. -/
lemma gaussianParityMeshFirstMoment_le (a : ℝ) (ha : 0 < a) (L : ℕ) :
    gaussianParityMeshFirstMoment a L ≤ Real.exp a / (2 * a) := by
  rcases Nat.even_or_odd L with ⟨M, hM⟩ | ⟨M, hM⟩
  · rw [show L = 2 * M by omega, gaussianParityMeshFirstMoment_even]
    calc
      2 * (∑ n ∈ Finset.range M,
        (2 * (n + 1) : ℝ) * Real.exp (-a * (2 * (n + 1) : ℝ) ^ 2)) ≤
          2 * (1 / (4 * a)) :=
        mul_le_mul_of_nonneg_left (sum_even_pos_mul_gaussian_le a ha M) (by norm_num)
      _ ≤ Real.exp a / (2 * a) := by
        have he : 1 ≤ Real.exp a := by rw [← Real.exp_zero]; exact Real.exp_le_exp.mpr ha.le
        rw [show 2 * (1 / (4 * a)) = 1 / (2 * a) by field_simp; ring]
        exact div_le_div_of_nonneg_right he (by positivity)
  · rw [show L = 2 * M + 1 by omega, gaussianParityMeshFirstMoment_odd]
    calc
      2 * (∑ n ∈ Finset.range (M + 1),
        (2 * n + 1 : ℝ) * Real.exp (-a * (2 * n + 1 : ℝ) ^ 2)) ≤
          2 * (Real.exp a / (4 * a)) :=
        mul_le_mul_of_nonneg_left (sum_odd_pos_mul_gaussian_le a ha (M + 1)) (by norm_num)
      _ = Real.exp a / (2 * a) := by ring

end Erdos521
