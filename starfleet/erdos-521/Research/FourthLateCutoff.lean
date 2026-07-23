import Research.FourthLateScale
import Mathlib.Tactic

open Filter Topology

namespace Erdos521

noncomputable def fourthLateBase (N : ℕ) : ℝ :=
  (N + 3 : ℝ) ^ 2 * Real.sqrt ((N + 3 : ℝ) * Real.log (N + 3 : ℝ))

noncomputable def fourthLateCutoff (N : ℕ) : ℕ :=
  Nat.ceil (100 * fourthLateBase N)

lemma fourthLate_log_one_le (N : ℕ) : 1 ≤ Real.log (N + 3 : ℝ) := by
  apply (Real.le_log_iff_exp_le (by positivity : (0 : ℝ) < N + 3)).2
  exact Real.exp_one_lt_three.le.trans (by
    have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    norm_num)

lemma fourthLateBase_one_le (N : ℕ) : 1 ≤ fourthLateBase N := by
  have hx : 1 ≤ (N + 3 : ℝ) := by
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le (N + 2))
  have hl := fourthLate_log_one_le N
  have hprod : 1 ≤ (N + 3 : ℝ) * Real.log (N + 3 : ℝ) := by
    simpa only [one_mul] using mul_le_mul hx hl (by norm_num) (by linarith)
  have hs : 1 ≤ Real.sqrt ((N + 3 : ℝ) * Real.log (N + 3 : ℝ)) :=
    Real.one_le_sqrt.mpr hprod
  unfold fourthLateBase
  nlinarith [show 1 ≤ (N + 3 : ℝ) ^ 2 from one_le_pow₀ hx]

lemma fourthLateCutoff_lower (N : ℕ) :
    100 * fourthLateBase N ≤ (fourthLateCutoff N : ℝ) := by
  exact Nat.le_ceil _

lemma fourthLateCutoff_upper (N : ℕ) :
    (fourthLateCutoff N : ℝ) ≤ 101 * fourthLateBase N := by
  have hb := fourthLateBase_one_le N
  have hnonneg : 0 ≤ 100 * fourthLateBase N := by nlinarith
  have hc := Nat.ceil_lt_add_one hnonneg
  unfold fourthLateCutoff
  linarith

lemma fourthLateCutoff_triple_count (N : ℕ) :
    ((2 * (3 * fourthLateCutoff N) + 1 : ℕ) : ℝ) ≤
      607 * fourthLateBase N := by
  push_cast
  have hc := fourthLateCutoff_upper N
  have hb := fourthLateBase_one_le N
  linarith

/-- At the late cutoff, the Gaussian strip has the critical `sqrt(log k)/k` order. -/
lemma fourthGaussianLateStrip_le (N : ℕ) :
    fourthGaussianStripMass (N + 2) (3 * fourthLateCutoff N) ≤
      607000000 * Real.sqrt (Real.log (N + 3 : ℝ)) / (N + 3 : ℝ) := by
  have h := fourthGaussianStripMass_le_coarse (N + 2) (3 * fourthLateCutoff N)
  have hcount := fourthLateCutoff_triple_count N
  have hx : 0 < (N + 3 : ℝ) := by positivity
  have hsx : 0 < Real.sqrt (N + 3 : ℝ) := Real.sqrt_pos.2 hx
  have hlog : 0 ≤ Real.log (N + 3 : ℝ) := (fourthLate_log_one_le N).trans' (by norm_num)
  calc
    fourthGaussianStripMass (N + 2) (3 * fourthLateCutoff N) ≤
        1000000 * ((2 * (3 * fourthLateCutoff N) + 1 : ℕ) : ℝ) /
          ((N + 3 : ℝ) ^ 3 * Real.sqrt (N + 3 : ℝ)) := by
      convert h using 1 <;> push_cast <;> ring
    _ ≤ 1000000 * (607 * fourthLateBase N) /
          ((N + 3 : ℝ) ^ 3 * Real.sqrt (N + 3 : ℝ)) := by
      gcongr
    _ = 607000000 * Real.sqrt (Real.log (N + 3 : ℝ)) / (N + 3 : ℝ) := by
      unfold fourthLateBase
      rw [Real.sqrt_mul hx.le]
      field_simp
      ring

/-- The iid fourth increment has a polynomially tiny tail at the late cutoff. -/
lemma fourthLate_increment_tail_le (N : ℕ) :
    2 * Real.exp (-((fourthLateCutoff N : ℝ) ^ 2) /
      (2 * fourthIncrementVarianceB (N + 2))) ≤
      2 / (N + 3 : ℝ) ^ 4 := by
  let x : ℝ := N + 3
  have hx : 0 < x := by dsimp [x]; positivity
  have hlog : 0 ≤ Real.log x := by
    dsimp [x]
    linarith [fourthLate_log_one_le N]
  have hBpos : 0 < fourthIncrementVarianceB (N + 2) := by
    unfold fourthIncrementVarianceB
    positivity
  have hB := fourthIncrementVarianceB_upper_power (N + 2)
  have hU := fourthLateCutoff_lower N
  have hbaseSq :
      (100 * fourthLateBase N) ^ 2 = 10000 * x ^ 5 * Real.log x := by
    unfold fourthLateBase
    dsimp [x]
    rw [mul_pow, mul_pow, Real.sq_sqrt (mul_nonneg hx.le hlog)]
    ring
  have hU2 : 10000 * x ^ 5 * Real.log x ≤ (fourthLateCutoff N : ℝ) ^ 2 := by
    rw [← hbaseSq]
    exact (sq_le_sq₀ (by nlinarith [fourthLateBase_one_le N])
      (by positivity)).2 hU
  have hB' : fourthIncrementVarianceB (N + 2) ≤ 24 * x ^ 5 := by
    convert hB using 1 <;> push_cast <;> dsimp [x] <;> ring
  have hmul := mul_le_mul_of_nonneg_right hB' hlog
  have hratio : 4 * Real.log x ≤
      (fourthLateCutoff N : ℝ) ^ 2 /
        (2 * fourthIncrementVarianceB (N + 2)) := by
    apply (le_div_iff₀ (mul_pos (by norm_num) hBpos)).2
    calc
      4 * Real.log x * (2 * fourthIncrementVarianceB (N + 2)) ≤
          4 * Real.log x * (2 * (24 * x ^ 5)) := by gcongr
      _ ≤ 10000 * x ^ 5 * Real.log x := by
        have hp : 0 ≤ x ^ 5 * Real.log x := mul_nonneg (by positivity) hlog
        ring_nf
        nlinarith
      _ ≤ _ := hU2
  have hexp : Real.exp (-(fourthLateCutoff N : ℝ) ^ 2 /
      (2 * fourthIncrementVarianceB (N + 2))) ≤ Real.exp (-4 * Real.log x) := by
    apply Real.exp_le_exp.mpr
    calc
      -(fourthLateCutoff N : ℝ) ^ 2 /
          (2 * fourthIncrementVarianceB (N + 2)) =
        -((fourthLateCutoff N : ℝ) ^ 2 /
          (2 * fourthIncrementVarianceB (N + 2))) := by ring
      _ ≤ -4 * Real.log x := by
        simpa only [neg_mul] using neg_le_neg hratio
  have heq : Real.exp (-4 * Real.log x) = 1 / x ^ 4 := by
    rw [show -4 * Real.log x =
      -(Real.log x + Real.log x + Real.log x + Real.log x) by ring,
      Real.exp_neg, Real.exp_add, Real.exp_add, Real.exp_add, Real.exp_log hx]
    ring
  rw [heq] at hexp
  calc
    2 * Real.exp (-((fourthLateCutoff N : ℝ) ^ 2) /
        (2 * fourthIncrementVarianceB (N + 2))) ≤ 2 * (1 / x ^ 4) := by gcongr
    _ = 2 / (N + 3 : ℝ) ^ 4 := by dsimp [x]; ring

end Erdos521
