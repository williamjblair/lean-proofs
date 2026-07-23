import Research.FourthCharacteristicDecay
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic

open scoped BigOperators

namespace Erdos521

lemma abs_cos_sub_gaussian_le {x : ℝ} (hx : |x| ≤ 1) :
    |Real.cos x - Real.exp (-(x ^ 2) / 2)| ≤ x ^ 4 / 4 := by
  let y : ℝ := -(x ^ 2) / 2
  have hx2abs : |x| ^ 2 ≤ 1 := by
    have := pow_le_pow_left₀ (abs_nonneg x) hx 2
    norm_num at this ⊢
    exact this
  rw [sq_abs] at hx2abs
  have hy : |y| ≤ 1 := by
    dsimp [y]
    rw [abs_div, abs_neg, abs_pow]
    norm_num
    nlinarith
  have hc := Real.cos_bound hx
  have he := Real.exp_bound (n := 2) hy (by norm_num)
  have hsum : (∑ m ∈ Finset.range 2, y ^ m / m.factorial) = 1 + y := by
    norm_num [Finset.sum_range_succ]
  rw [hsum] at he
  norm_num at he
  have htri : |Real.cos x - Real.exp y| ≤
      |Real.cos x - (1 - x ^ 2 / 2)| + |Real.exp y - (1 + y)| := by
    calc
      |Real.cos x - Real.exp y| =
          |(Real.cos x - (1 - x ^ 2 / 2)) + ((1 + y) - Real.exp y)| := by
        dsimp [y]
        congr 1
        ring
      _ ≤ |Real.cos x - (1 - x ^ 2 / 2)| + |(1 + y) - Real.exp y| := abs_add_le _ _
      _ = _ := by
        congr 1
        exact abs_sub_comm _ _
  dsimp [y] at htri ⊢
  calc
    |Real.cos x - Real.exp (-(x ^ 2) / 2)| ≤
        |Real.cos x - (1 - x ^ 2 / 2)| +
          |Real.exp (-(x ^ 2) / 2) - (1 + -(x ^ 2) / 2)| := htri
    _ ≤ |x| ^ 4 * (5 / 96) + |-(x ^ 2) / 2| ^ 2 * (3 / 4) := by
      apply add_le_add hc
      simpa [y] using he
    _ = x ^ 4 * (23 / 96) := by
      have habs4 : |x| ^ 4 = x ^ 4 := by
        rw [← abs_pow]
        exact abs_of_nonneg (by positivity)
      rw [habs4, abs_div, abs_neg, abs_pow]
      norm_num
      ring
    _ ≤ x ^ 4 / 4 := by
      have hx4 : 0 ≤ x ^ 4 := by positivity
      nlinarith

lemma abs_prod_sub_prod_le_sum {ι : Type*} [DecidableEq ι] (s : Finset ι) (a b : ι → ℝ)
    (ha : ∀ i ∈ s, |a i| ≤ 1) (hb : ∀ i ∈ s, |b i| ≤ 1) :
    |(∏ i ∈ s, a i) - ∏ i ∈ s, b i| ≤ ∑ i ∈ s, |a i - b i| := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      have hai := ha i (Finset.mem_insert_self i s)
      have hbi := hb i (Finset.mem_insert_self i s)
      have haS : ∀ j ∈ s, |a j| ≤ 1 := fun j hj ↦ ha j (Finset.mem_insert_of_mem hj)
      have hbS : ∀ j ∈ s, |b j| ≤ 1 := fun j hj ↦ hb j (Finset.mem_insert_of_mem hj)
      have hprodB : |∏ j ∈ s, b j| ≤ 1 := by
        rw [Finset.abs_prod]
        calc
          (∏ j ∈ s, |b j|) ≤ ∏ _j ∈ s, (1 : ℝ) :=
            Finset.prod_le_prod (fun _ _ ↦ abs_nonneg _) hbS
          _ = 1 := by simp
      rw [Finset.prod_insert hi, Finset.prod_insert hi, Finset.sum_insert hi]
      calc
        |a i * (∏ j ∈ s, a j) - b i * ∏ j ∈ s, b j| =
            |a i * ((∏ j ∈ s, a j) - ∏ j ∈ s, b j) +
              (a i - b i) * ∏ j ∈ s, b j| := by congr 1 <;> ring
        _ ≤ |a i * ((∏ j ∈ s, a j) - ∏ j ∈ s, b j)| +
            |(a i - b i) * ∏ j ∈ s, b j| := abs_add_le _ _
        _ = |a i| * |(∏ j ∈ s, a j) - ∏ j ∈ s, b j| +
            |a i - b i| * |∏ j ∈ s, b j| := by rw [abs_mul, abs_mul]
        _ ≤ (∑ j ∈ s, |a j - b j|) + |a i - b i| := by
          have hsum : 0 ≤ ∑ j ∈ s, |a j - b j| := Finset.sum_nonneg fun _ _ ↦ abs_nonneg _
          have hdiff : 0 ≤ |a i - b i| := abs_nonneg _
          apply add_le_add
          · exact (mul_le_of_le_one_left (abs_nonneg _) hai).trans (ih haS hbS)
          · exact mul_le_of_le_one_right hdiff hprodB
        _ = |a i - b i| + ∑ j ∈ s, |a j - b j| := by ring

lemma abs_cos_prod_sub_gaussian_prod {ι : Type*} [Fintype ι]
    (x : ι → ℝ) (hx : ∀ i, |x i| ≤ 1) :
    |(∏ i, Real.cos (x i)) - ∏ i, Real.exp (-(x i ^ 2) / 2)| ≤
      (1 / 4 : ℝ) * ∑ i, x i ^ 4 := by
  classical
  have hcos (i : ι) : |Real.cos (x i)| ≤ 1 := Real.abs_cos_le_one _
  have hexp (i : ι) : |Real.exp (-(x i ^ 2) / 2)| ≤ 1 := by
    rw [abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg (x i)])
  calc
    _ ≤ ∑ i, |Real.cos (x i) - Real.exp (-(x i ^ 2) / 2)| :=
      abs_prod_sub_prod_le_sum Finset.univ _ _ (fun i _ ↦ hcos i) (fun i _ ↦ hexp i)
    _ ≤ ∑ i, x i ^ 4 / 4 := Finset.sum_le_sum fun i _ ↦ abs_cos_sub_gaussian_le (hx i)
    _ = (1 / 4 : ℝ) * ∑ i, x i ^ 4 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring

end Erdos521
