import Research.FourthLateCutoff
import Mathlib.Tactic

open Filter Topology

namespace Erdos521

lemma sqrt_log_le_two_rpow_third {x : ℝ} (hx : 1 ≤ x) :
    Real.sqrt (Real.log x) ≤ 2 * x ^ ((1 : ℝ) / 3) := by
  have hx0 : 0 ≤ x := hx.trans' (by norm_num)
  have hlog : 0 ≤ Real.log x := Real.log_nonneg hx
  have hbase := Real.log_le_rpow_div hx0 (by norm_num : (0 : ℝ) < 2 / 3)
  have hr : (x ^ ((1 : ℝ) / 3)) ^ 2 = x ^ ((2 : ℝ) / 3) := by
    calc
      (x ^ ((1 : ℝ) / 3)) ^ 2 =
          (x ^ ((1 : ℝ) / 3)) ^ (2 : ℝ) :=
            (Real.rpow_natCast (x ^ ((1 : ℝ) / 3)) 2).symm
      _ = x ^ (((1 : ℝ) / 3) * 2) := (Real.rpow_mul hx0 _ _).symm
      _ = x ^ ((2 : ℝ) / 3) := by ring_nf
  rw [Real.sqrt_le_iff]
  constructor
  · positivity
  · rw [mul_pow, hr]
    have hrnonneg : 0 ≤ x ^ ((2 : ℝ) / 3) := Real.rpow_nonneg hx0 _
    calc
      Real.log x ≤ x ^ ((2 : ℝ) / 3) / ((2 : ℝ) / 3) := hbase
      _ ≤ 2 ^ 2 * x ^ ((2 : ℝ) / 3) := by nlinarith

lemma fourthLateCutoff_single_count (N : ℕ) :
    ((2 * fourthLateCutoff N + 1 : ℕ) : ℝ) ≤ 203 * fourthLateBase N := by
  push_cast
  have hc := fourthLateCutoff_upper N
  have hb := fourthLateBase_one_le N
  linarith

lemma fourthLateBase_sq (N : ℕ) :
    fourthLateBase N ^ 2 =
      (N + 3 : ℝ) ^ 5 * Real.log (N + 3 : ℝ) := by
  have hx : 0 ≤ (N + 3 : ℝ) := by positivity
  have hl : 0 ≤ Real.log (N + 3 : ℝ) := Real.log_nonneg (by
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le (N + 2)))
  unfold fourthLateBase
  rw [mul_pow, Real.sq_sqrt (mul_nonneg hx hl)]
  ring

/-- The number of central-strip atoms at the late cutoff is small relative to the older
`N^(8/3)` local-limit cutoff, with exactly the spare cube-root needed for the logarithm. -/
lemma fourthLate_central_count_le (N : ℕ) :
    (((2 * (3 * fourthLateCutoff N) + 1) *
      (2 * fourthLateCutoff N + 1) : ℕ) : ℝ) ≤
      250000 * Real.sqrt (Real.log (N + 3 : ℝ)) *
        (fourthCrossingCutoff N : ℝ) ^ 2 := by
  let x : ℝ := N + 3
  have hx : 1 ≤ x := by
    dsimp [x]
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le (N + 2))
  have hlog : 0 ≤ Real.log x := Real.log_nonneg hx
  have hslog : Real.sqrt (Real.log x) ≤ 2 * x ^ ((1 : ℝ) / 3) :=
    sqrt_log_le_two_rpow_third hx
  have htriple := fourthLateCutoff_triple_count N
  have hsingle := fourthLateCutoff_single_count N
  have hcounts :
      (((2 * (3 * fourthLateCutoff N) + 1) *
        (2 * fourthLateCutoff N + 1) : ℕ) : ℝ) ≤
        (607 * fourthLateBase N) * (203 * fourthLateBase N) := by
    push_cast at htriple hsingle ⊢
    exact mul_le_mul htriple hsingle (by nlinarith [fourthLateBase_one_le N])
      (by nlinarith [fourthLateBase_one_le N])
  have hbase := fourthLateBase_sq N
  have hsqrt_sq : Real.sqrt (Real.log x) ^ 2 = Real.log x := Real.sq_sqrt hlog
  have hradd : x ^ 5 * x ^ ((1 : ℝ) / 3) = x ^ ((16 : ℝ) / 3) := by
    rw [← Real.rpow_natCast x 5, ← Real.rpow_add (by positivity)]
    congr 2
    ring
  have hcut := fourthCrossingCutoff_sq_lower N
  calc
    (((2 * (3 * fourthLateCutoff N) + 1) *
      (2 * fourthLateCutoff N + 1) : ℕ) : ℝ) ≤
        (607 * fourthLateBase N) * (203 * fourthLateBase N) := hcounts
    _ = (607 * 203 : ℝ) * (x ^ 5 * Real.log x) := by
      rw [← hbase]
      ring
    _ = (607 * 203 : ℝ) *
        (x ^ 5 * (Real.sqrt (Real.log x) ^ 2)) := by rw [hsqrt_sq]
    _ ≤ (607 * 203 : ℝ) *
        (x ^ 5 * (Real.sqrt (Real.log x) * (2 * x ^ ((1 : ℝ) / 3)))) := by
      gcongr
      simpa [pow_two] using
        mul_le_mul_of_nonneg_left hslog (Real.sqrt_nonneg (Real.log x))
    _ = (2 * 607 * 203 : ℝ) * Real.sqrt (Real.log x) *
        x ^ ((16 : ℝ) / 3) := by
      rw [show x ^ 5 * (Real.sqrt (Real.log x) * (2 * x ^ ((1 : ℝ) / 3))) =
        2 * Real.sqrt (Real.log x) * (x ^ 5 * x ^ ((1 : ℝ) / 3)) by ring,
        hradd]
      ring
    _ ≤ 250000 * Real.sqrt (Real.log x) *
        (fourthCrossingCutoff N : ℝ) ^ 2 := by
      have hsnonneg : 0 ≤ Real.sqrt (Real.log x) := Real.sqrt_nonneg _
      nlinarith [mul_le_mul_of_nonneg_left hcut hsnonneg]

lemma eventually_fourthLate_atom_error_le :
    ∀ᶠ N : ℕ in atTop,
      (((2 * (3 * fourthLateCutoff N) + 1) *
        (2 * fourthLateCutoff N + 1) : ℕ) : ℝ) * fourthFullAtomError N ≤
        250000 * Real.sqrt (Real.log (N + 3 : ℝ)) / (N + 3 : ℝ) := by
  have hnorm : ∀ᶠ N : ℕ in atTop,
      (N + 3 : ℝ) * (fourthCrossingCutoff N : ℝ) ^ 2 *
        fourthFullAtomError N ≤ 1 :=
    tendsto_fourthNormalizedFullAtomError_zero.eventually_le_const (by norm_num)
  filter_upwards [hnorm, eventually_ge_atTop (21 : ℕ)] with N hnormN hN
  have hcount := fourthLate_central_count_le N
  have herr : 0 ≤ fourthFullAtomError N := fourthFullAtomError_nonneg N hN
  have hx : 0 < (N + 3 : ℝ) := by positivity
  calc
    (((2 * (3 * fourthLateCutoff N) + 1) *
      (2 * fourthLateCutoff N + 1) : ℕ) : ℝ) * fourthFullAtomError N ≤
        (250000 * Real.sqrt (Real.log (N + 3 : ℝ)) *
          (fourthCrossingCutoff N : ℝ) ^ 2) * fourthFullAtomError N :=
      mul_le_mul_of_nonneg_right hcount herr
    _ = (250000 * Real.sqrt (Real.log (N + 3 : ℝ)) / (N + 3 : ℝ)) *
        ((N + 3 : ℝ) * (fourthCrossingCutoff N : ℝ) ^ 2 *
          fourthFullAtomError N) := by field_simp
    _ ≤ 250000 * Real.sqrt (Real.log (N + 3 : ℝ)) / (N + 3 : ℝ) := by
      have hfactor : 0 ≤ 250000 * Real.sqrt (Real.log (N + 3 : ℝ)) /
          (N + 3 : ℝ) := by
        exact div_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _)) hx.le
      nlinarith

/-- Full iid small-ball rate at the late cutoff, including atom error and increment truncation. -/
lemma eventually_fourthSignedLateStrip_rate :
    ∀ᶠ N : ℕ in atTop,
      fourthSignedStripProbability (N + 2) (3 * fourthLateCutoff N) ≤
        608000000 * Real.sqrt (Real.log (N + 3 : ℝ)) / (N + 3 : ℝ) := by
  filter_upwards [eventually_fourthLate_atom_error_le,
    eventually_ge_atTop (21 : ℕ)] with N herr hN
  have hmaster := fourthSignedStripProbability_le_truncated N
    (3 * fourthLateCutoff N) (fourthLateCutoff N) hN
  have hgauss := fourthGaussianLateStrip_le N
  have htail := fourthLate_increment_tail_le N
  have hx : 1 ≤ (N + 3 : ℝ) := by
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le (N + 2))
  have hslog : 1 ≤ Real.sqrt (Real.log (N + 3 : ℝ)) :=
    Real.one_le_sqrt.mpr (fourthLate_log_one_le N)
  have hsmall : 2 / (N + 3 : ℝ) ^ 4 ≤
      2 * Real.sqrt (Real.log (N + 3 : ℝ)) / (N + 3 : ℝ) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).2
    have hx4 : (N + 3 : ℝ) ≤ (N + 3 : ℝ) ^ 4 := by
      calc
        (N + 3 : ℝ) = (N + 3 : ℝ) * 1 := by ring
        _ ≤ (N + 3 : ℝ) * (N + 3 : ℝ) ^ 3 :=
          mul_le_mul_of_nonneg_left (one_le_pow₀ hx) (by positivity)
        _ = _ := by ring
    have hs4 := mul_le_mul_of_nonneg_right hslog
      (show 0 ≤ (N + 3 : ℝ) ^ 4 by positivity)
    nlinarith
  calc
    fourthSignedStripProbability (N + 2) (3 * fourthLateCutoff N) ≤
        fourthGaussianStripMass (N + 2) (3 * fourthLateCutoff N) +
          (((2 * (3 * fourthLateCutoff N) + 1) *
            (2 * fourthLateCutoff N + 1) : ℕ) : ℝ) * fourthFullAtomError N +
          2 * Real.exp (-((fourthLateCutoff N : ℝ) ^ 2) /
            (2 * fourthIncrementVarianceB (N + 2))) := hmaster
    _ ≤ 607000000 * Real.sqrt (Real.log (N + 3 : ℝ)) / (N + 3 : ℝ) +
        250000 * Real.sqrt (Real.log (N + 3 : ℝ)) / (N + 3 : ℝ) +
        2 / (N + 3 : ℝ) ^ 4 := by linarith
    _ ≤ 608000000 * Real.sqrt (Real.log (N + 3 : ℝ)) / (N + 3 : ℝ) := by
      let f := Real.sqrt (Real.log (N + 3 : ℝ)) / (N + 3 : ℝ)
      have hfac : 0 ≤ f := by dsimp [f]; positivity
      have hs : 2 / (N + 3 : ℝ) ^ 4 ≤ 2 * f := by
        calc
          _ ≤ 2 * Real.sqrt (Real.log (N + 3 : ℝ)) / (N + 3 : ℝ) := hsmall
          _ = 2 * f := by dsimp [f]; ring
      have h607 : 607000000 * Real.sqrt (Real.log (N + 3 : ℝ)) /
          (N + 3 : ℝ) = 607000000 * f := by dsimp [f]; ring
      have h250 : 250000 * Real.sqrt (Real.log (N + 3 : ℝ)) /
          (N + 3 : ℝ) = 250000 * f := by dsimp [f]; ring
      have h608 : 608000000 * Real.sqrt (Real.log (N + 3 : ℝ)) /
          (N + 3 : ℝ) = 608000000 * f := by dsimp [f]; ring
      rw [h607, h250, h608]
      nlinarith

end Erdos521
