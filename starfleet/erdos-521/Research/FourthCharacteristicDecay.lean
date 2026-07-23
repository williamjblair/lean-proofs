import Research.FourthWhitening
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

open scoped BigOperators

namespace Erdos521

lemma abs_cos_le_exp_neg_sq {x : ℝ} (hx : |x| ≤ 1) :
    |Real.cos x| ≤ Real.exp (-(2 / Real.pi ^ 2) * x ^ 2) := by
  have hpi := Real.pi_gt_three
  have hxpi : |x| ≤ Real.pi := hx.trans (by linarith)
  have hxhalf : x ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
    rw [Set.mem_Icc]
    constructor <;> linarith [le_abs_self x, neg_le_of_abs_le hx]
  rw [abs_of_nonneg (Real.cos_nonneg_of_mem_Icc hxhalf)]
  calc
    Real.cos x ≤ 1 - 2 / Real.pi ^ 2 * x ^ 2 :=
      Real.cos_le_one_sub_mul_cos_sq hxpi
    _ ≤ Real.exp (-(2 / Real.pi ^ 2) * x ^ 2) := by
      have h := Real.add_one_le_exp (-(2 / Real.pi ^ 2) * x ^ 2)
      linarith

lemma abs_cos_prod_le_exp_neg_sq_sum {ι : Type*} [Fintype ι]
    (x : ι → ℝ) (hx : ∀ i, |x i| ≤ 1) :
    |∏ i, Real.cos (x i)| ≤
      Real.exp (-(2 / Real.pi ^ 2) * ∑ i, (x i) ^ 2) := by
  rw [Finset.abs_prod]
  calc
    (∏ i, |Real.cos (x i)|) ≤
        ∏ i, Real.exp (-(2 / Real.pi ^ 2) * (x i) ^ 2) := by
      exact Finset.prod_le_prod (fun i hi ↦ abs_nonneg _) fun i hi ↦
        abs_cos_le_exp_neg_sq (hx i)
    _ = Real.exp (∑ i, (-(2 / Real.pi ^ 2) * (x i) ^ 2)) := by
      rw [Real.exp_sum]
    _ = Real.exp (-(2 / Real.pi ^ 2) * ∑ i, (x i) ^ 2) := by
      congr 1
      rw [Finset.mul_sum]

lemma linear_phase_sq_le (s t x y : ℝ) :
    (s * x + t * y) ^ 2 ≤ (s ^ 2 + t ^ 2) * (x ^ 2 + y ^ 2) := by
  nlinarith [sq_nonneg (s * y - t * x)]

lemma fourthOldPhase_abs_le_one {k q : ℕ} (hq : q ≤ k) {s t : ℝ}
    (hst : (s ^ 2 + t ^ 2) * (12 / (k + 1 : ℝ)) ≤ 1) :
    |s * fourthWhitenedX k q + t * fourthWhitenedY k q| ≤ 1 := by
  have hnorm := fourthOldLeverage_le hq
  rw [← fourthWhitened_norm_sq_eq_leverage] at hnorm
  have hphase := linear_phase_sq_le s t (fourthWhitenedX k q) (fourthWhitenedY k q)
  have hst0 : 0 ≤ s ^ 2 + t ^ 2 := by positivity
  have hnorm0 : 0 ≤ fourthWhitenedX k q ^ 2 + fourthWhitenedY k q ^ 2 := by positivity
  have hsquare : (s * fourthWhitenedX k q + t * fourthWhitenedY k q) ^ 2 ≤ 1 ^ 2 := by
    calc
      _ ≤ (s ^ 2 + t ^ 2) *
          (fourthWhitenedX k q ^ 2 + fourthWhitenedY k q ^ 2) := hphase
      _ ≤ (s ^ 2 + t ^ 2) * (12 / (k + 1 : ℝ)) := by gcongr
      _ ≤ 1 := hst
      _ = 1 ^ 2 := by norm_num
  exact abs_le_of_sq_le_sq hsquare (by norm_num)

lemma fourthNewPhase_abs_le_one (k : ℕ) {s t : ℝ}
    (hst : (s ^ 2 + t ^ 2) * (12 / (k + 1 : ℝ)) ≤ 1) :
    |t * fourthWhitenedNewY k| ≤ 1 := by
  have hnew := fourthNewLeverage_le k
  change fourthVarianceA k / fourthDet k ≤ 12 / (k + 1 : ℝ) at hnew
  rw [← fourthWhitenedNewY_sq] at hnew
  have ht : t ^ 2 ≤ s ^ 2 + t ^ 2 := by nlinarith [sq_nonneg s]
  have hnew0 : 0 ≤ fourthWhitenedNewY k ^ 2 := sq_nonneg _
  have hsquare : (t * fourthWhitenedNewY k) ^ 2 ≤ 1 ^ 2 := by
    calc
      _ = t ^ 2 * fourthWhitenedNewY k ^ 2 := by ring
      _ ≤ (s ^ 2 + t ^ 2) * fourthWhitenedNewY k ^ 2 := by gcongr
      _ ≤ (s ^ 2 + t ^ 2) * (12 / (k + 1 : ℝ)) := by gcongr
      _ ≤ 1 := hst
      _ = 1 ^ 2 := by norm_num
  exact abs_le_of_sq_le_sq hsquare (by norm_num)

lemma fourthPhase_sq_sum (k : ℕ) (s t : ℝ) :
    (∑ q ∈ Finset.range (k + 1),
      (s * fourthWhitenedX k q + t * fourthWhitenedY k q) ^ 2) +
      (t * fourthWhitenedNewY k) ^ 2 = s ^ 2 + t ^ 2 := by
  calc
    _ = (∑ q ∈ Finset.range (k + 1),
          (s ^ 2 * fourthWhitenedX k q ^ 2 +
            2 * s * t * (fourthWhitenedX k q * fourthWhitenedY k q) +
            t ^ 2 * fourthWhitenedY k q ^ 2)) +
        t ^ 2 * fourthWhitenedNewY k ^ 2 := by
      rw [show (t * fourthWhitenedNewY k) ^ 2 =
        t ^ 2 * fourthWhitenedNewY k ^ 2 by ring]
      apply congrArg (fun z : ℝ ↦ z + t ^ 2 * fourthWhitenedNewY k ^ 2)
      apply Finset.sum_congr rfl
      intro q hq
      ring
    _ = s ^ 2 * (∑ q ∈ Finset.range (k + 1), fourthWhitenedX k q ^ 2) +
        2 * s * t * (∑ q ∈ Finset.range (k + 1),
          fourthWhitenedX k q * fourthWhitenedY k q) +
        t ^ 2 * ((∑ q ∈ Finset.range (k + 1), fourthWhitenedY k q ^ 2) +
          fourthWhitenedNewY k ^ 2) := by
      simp only [Finset.sum_add_distrib]
      simp_rw [← Finset.mul_sum]
      ring
    _ = s ^ 2 + t ^ 2 := by
      rw [fourthWhitened_cov_xx, fourthWhitened_cov_xy, fourthWhitened_cov_yy]
      ring

/-- Uniform Gaussian decay of the fourth-array characteristic cosine product throughout its
covariance-scale central Fourier ball. -/
lemma fourthCharacteristicProduct_decay (k : ℕ) (s t : ℝ)
    (hst : (s ^ 2 + t ^ 2) * (12 / (k + 1 : ℝ)) ≤ 1) :
    |Real.cos (t * fourthWhitenedNewY k) *
        ∏ q : Fin (k + 1),
          Real.cos (s * fourthWhitenedX k q + t * fourthWhitenedY k q)| ≤
      Real.exp (-(2 / Real.pi ^ 2) * (s ^ 2 + t ^ 2)) := by
  have hnew := abs_cos_le_exp_neg_sq (fourthNewPhase_abs_le_one k hst)
  have hold := abs_cos_prod_le_exp_neg_sq_sum
    (fun q : Fin (k + 1) ↦
      s * fourthWhitenedX k q + t * fourthWhitenedY k q)
    (fun q ↦ fourthOldPhase_abs_le_one (Fin.le_last q) hst)
  have hsumEq :
      (∑ q : Fin (k + 1),
        (s * fourthWhitenedX k q + t * fourthWhitenedY k q) ^ 2) =
      ∑ q ∈ Finset.range (k + 1),
        (s * fourthWhitenedX k q + t * fourthWhitenedY k q) ^ 2 :=
    Fin.sum_univ_eq_sum_range
      (fun q : ℕ ↦ (s * fourthWhitenedX k q + t * fourthWhitenedY k q) ^ 2) (k + 1)
  have hphaseFin :
      (∑ q : Fin (k + 1),
        (s * fourthWhitenedX k q + t * fourthWhitenedY k q) ^ 2) +
        (t * fourthWhitenedNewY k) ^ 2 = s ^ 2 + t ^ 2 := by
    rw [hsumEq]
    exact fourthPhase_sq_sum k s t
  rw [abs_mul]
  have hmul := mul_le_mul hnew hold (abs_nonneg _) (Real.exp_pos _).le
  calc
    _ ≤ Real.exp (-(2 / Real.pi ^ 2) * (t * fourthWhitenedNewY k) ^ 2) *
        Real.exp (-(2 / Real.pi ^ 2) *
          ∑ q : Fin (k + 1),
            (s * fourthWhitenedX k q + t * fourthWhitenedY k q) ^ 2) := hmul
    _ = Real.exp (-(2 / Real.pi ^ 2) * (s ^ 2 + t ^ 2)) := by
      rw [← Real.exp_add]
      congr 1
      rw [← hphaseFin]
      ring

end Erdos521
