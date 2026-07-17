/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import ErdosProblems.Erdos686MatchingTailChebyshev

/-!
# Erdős 686: a contiguous exact Chebyshev prime-counting tail

The square-root split in the standard elementary Chebyshev bound loses too
much at `10^6`.  Here the logarithmic integral is instead bounded on the
eight dyadic intervals from `2` to `512`, then propagated by a differential
comparison.  This gives

`∫₂ˣ dt / log(t)^2 ≤ (5/2) x / log(x)^2`

for every `x ≥ 512`.  Substitution into Abel summation, together with the
exact inequality `2^33 < 10^10`, proves `8 * π(k) < k` for every
`k ≥ 10^6`.  All acceptance conditions are exact.
-/

namespace Erdos686
namespace Erdos686Variant

open MeasureTheory

private theorem intervalIntegrable_one_div_log_sq_refined {a b : ℝ}
    (one_lt_a : 1 < a) (one_lt_b : 1 < b) :
    IntervalIntegrable (fun x ↦ 1 / Real.log x ^ 2) volume a b := by
  refine ContinuousOn.intervalIntegrable fun x hx ↦ ContinuousAt.continuousWithinAt ?_
  rw [Set.mem_uIcc] at hx
  have : x ≠ 0 := by grind
  have : Real.log x ^ 2 ≠ 0 := pow_ne_zero _ (Real.log_ne_zero.mpr (by grind))
  fun_prop (disch := assumption)

private theorem integral_1_div_log_sq_le {a b : ℝ}
    (hab : a ≤ b) (one_lt : 1 < a) :
    ∫ x in a..b, 1 / Real.log x ^ 2 ≤ (b - a) / Real.log a ^ 2 := by
  calc
    _ ≤ ∫ x in a..b, 1 / Real.log a ^ 2 := by
      refine intervalIntegral.integral_mono_on hab ?_ (by simp) fun x ⟨hx, _⟩ ↦ by
        gcongr <;> bound
      apply intervalIntegrable_one_div_log_sq_refined <;> linarith
    _ = _ := by simp [field]

theorem integral_one_div_log_sq_le_at_512 :
    ∫ x in (2 : ℝ)..512, 1 / Real.log x ^ 2 ≤
      (5 / 2 : ℝ) * 512 / Real.log 512 ^ 2 := by
  have h2 := integral_1_div_log_sq_le (a := (2 : ℝ)) (b := 4) (by norm_num) (by norm_num)
  have h4 := integral_1_div_log_sq_le (a := (4 : ℝ)) (b := 8) (by norm_num) (by norm_num)
  have h8 := integral_1_div_log_sq_le (a := (8 : ℝ)) (b := 16) (by norm_num) (by norm_num)
  have h16 := integral_1_div_log_sq_le (a := (16 : ℝ)) (b := 32) (by norm_num) (by norm_num)
  have h32 := integral_1_div_log_sq_le (a := (32 : ℝ)) (b := 64) (by norm_num) (by norm_num)
  have h64 := integral_1_div_log_sq_le (a := (64 : ℝ)) (b := 128) (by norm_num) (by norm_num)
  have h128 := integral_1_div_log_sq_le (a := (128 : ℝ)) (b := 256) (by norm_num) (by norm_num)
  have h256 := integral_1_div_log_sq_le (a := (256 : ℝ)) (b := 512) (by norm_num) (by norm_num)
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := (4 : ℝ)),
    ← intervalIntegral.integral_add_adjacent_intervals (a := (4 : ℝ)) (b := 8),
    ← intervalIntegral.integral_add_adjacent_intervals (a := (8 : ℝ)) (b := 16),
    ← intervalIntegral.integral_add_adjacent_intervals (a := (16 : ℝ)) (b := 32),
    ← intervalIntegral.integral_add_adjacent_intervals (a := (32 : ℝ)) (b := 64),
    ← intervalIntegral.integral_add_adjacent_intervals (a := (64 : ℝ)) (b := 128),
    ← intervalIntegral.integral_add_adjacent_intervals (a := (128 : ℝ)) (b := 256)]
  · grw [h2, h4, h8, h16, h32, h64, h128, h256]
    have hlog2 : Real.log (2 : ℝ) ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow,
      show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow,
      show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow,
      show (32 : ℝ) = 2 ^ 5 by norm_num, Real.log_pow,
      show (64 : ℝ) = 2 ^ 6 by norm_num, Real.log_pow,
      show (128 : ℝ) = 2 ^ 7 by norm_num, Real.log_pow,
      show (256 : ℝ) = 2 ^ 8 by norm_num, Real.log_pow,
      show (512 : ℝ) = 2 ^ 9 by norm_num, Real.log_pow]
    field_simp
    norm_num
  all_goals
    apply intervalIntegrable_one_div_log_sq_refined <;> norm_num

theorem integral_one_div_log_sq_le_five_halves {x : ℝ} (hx : 512 ≤ x) :
    ∫ t in (2 : ℝ)..x, 1 / Real.log t ^ 2 ≤
      (5 / 2 : ℝ) * x / Real.log x ^ 2 := by
  have hlog512 : (10 / 3 : ℝ) < Real.log 512 := by
    have h512 : Real.log (512 : ℝ) = 9 * Real.log 2 := by
      convert Real.log_pow (2 : ℝ) 9 using 1 <;> norm_num
    rw [h512]
    nlinarith [Real.log_two_gt_d9]
  have hlogx : (10 / 3 : ℝ) < Real.log x := by
    have hxpos : (0 : ℝ) < x := lt_of_lt_of_le (by norm_num) hx
    exact lt_of_lt_of_le hlog512
      (Real.strictMonoOn_log.monotoneOn (by norm_num) hxpos hx)
  have hsplit :
      ∫ t in (2 : ℝ)..x, 1 / Real.log t ^ 2 =
        (∫ t in (2 : ℝ)..512, 1 / Real.log t ^ 2) +
        ∫ t in (512 : ℝ)..x, 1 / Real.log t ^ 2 := by
    symm
    apply intervalIntegral.integral_add_adjacent_intervals
    · apply intervalIntegrable_one_div_log_sq_refined <;> norm_num
    · apply intervalIntegrable_one_div_log_sq_refined <;> linarith
  rw [hsplit]
  have htail :
      ∫ t in (512 : ℝ)..x, 1 / Real.log t ^ 2 ≤
        (5 / 2 : ℝ) * x / Real.log x ^ 2 -
        (5 / 2 : ℝ) * 512 / Real.log 512 ^ 2 := by
    let F : ℝ → ℝ := fun y ↦ (5 / 2 : ℝ) * y / Real.log y ^ 2
    let F' : ℝ → ℝ := fun y ↦
      (5 / 2 : ℝ) * (Real.log y - 2) / Real.log y ^ 3
    have hderiv : ∀ y ∈ Set.uIcc (512 : ℝ) x, HasDerivAt F (F' y) y := by
      intro y hy
      have hyI : y ∈ Set.Icc (512 : ℝ) x := by
        simpa [Set.uIcc_of_le hx] using hy
      have hypos : 0 < y := by linarith [hyI.1]
      have hyone : 1 < y := lt_of_lt_of_le (by norm_num) hyI.1
      have hlogpos : 0 < Real.log y := Real.log_pos hyone
      have hlogne : Real.log y ^ 2 ≠ 0 := pow_ne_zero _ (ne_of_gt hlogpos)
      dsimp [F, F']
      have hd := (hasDerivAt_id y).div
        ((Real.hasDerivAt_log hypos.ne').pow 2) hlogne
      convert HasDerivAt.const_mul (5 / 2 : ℝ) hd using 1
      · funext z
        simp only [Pi.mul_apply, Pi.inv_apply, id_eq, Pi.pow_apply, div_eq_mul_inv]
        ring
      · simp only [id_eq, Pi.pow_apply]
        field_simp [ne_of_gt hlogpos]
        ring
    have hFint : IntervalIntegrable F' volume (512 : ℝ) x := by
      refine ContinuousOn.intervalIntegrable fun y hy ↦
        ContinuousAt.continuousWithinAt ?_
      rw [Set.mem_uIcc] at hy
      have hypos : 0 < y := by rcases hy with hy | hy <;> linarith
      have hyone : 1 < y := by rcases hy with hy | hy <;> linarith
      have hyne : y ≠ 0 := ne_of_gt hypos
      have hlogne : Real.log y ≠ 0 := ne_of_gt (Real.log_pos hyone)
      have hlogpowne : Real.log y ^ 3 ≠ 0 := pow_ne_zero _ hlogne
      dsimp [F']
      fun_prop (disch := assumption)
    have hbaseInt : IntervalIntegrable (fun y : ℝ ↦ 1 / Real.log y ^ 2)
        volume (512 : ℝ) x :=
      intervalIntegrable_one_div_log_sq_refined (by norm_num) (by linarith)
    have hmono : ∀ y ∈ Set.Icc (512 : ℝ) x,
        1 / Real.log y ^ 2 ≤ F' y := by
      intro y hy
      have hypos : 0 < y := by linarith [hy.1]
      have hlogLower : (10 / 3 : ℝ) < Real.log y := by
        exact lt_of_lt_of_le hlog512
          (Real.strictMonoOn_log.monotoneOn (by norm_num) hypos hy.1)
      have hlogpos : 0 < Real.log y := by linarith
      dsimp [F']
      apply (div_le_div_iff₀ (pow_pos hlogpos 2) (pow_pos hlogpos 3)).2
      nlinarith [sq_pos_of_pos hlogpos]
    calc
      ∫ t in (512 : ℝ)..x, 1 / Real.log t ^ 2
          ≤ ∫ t in (512 : ℝ)..x, F' t :=
        intervalIntegral.integral_mono_on hx hbaseInt hFint hmono
      _ = F x - F 512 :=
        intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hFint
      _ = _ := by rfl
  linarith [integral_one_div_log_sq_le_at_512, htail]

theorem integral_theta_div_log_sq_le_five_halves {x : ℝ} (hx : 512 ≤ x) :
    ∫ t in (2 : ℝ)..x, Chebyshev.theta t / (t * Real.log t ^ 2) ≤
      Real.log 4 * ((5 / 2 : ℝ) * x / Real.log x ^ 2) := by
  have hx2 : (2 : ℝ) ≤ x := by linarith
  calc
    ∫ t in (2 : ℝ)..x, Chebyshev.theta t / (t * Real.log t ^ 2)
        ≤ ∫ t in (2 : ℝ)..x, Real.log 4 * (1 / Real.log t ^ 2) := by
      refine intervalIntegral.integral_mono_on hx2 ?hf ?hg fun t ⟨ht, _⟩ ↦ ?hh
      case hf =>
        refine intervalIntegrable_iff.mpr ?_
        rw [Set.uIoc_of_le hx2, ← integrableOn_Icc_iff_integrableOn_Ioc]
        exact Chebyshev.integrableOn_theta_div_id_mul_log_sq x
      case hg =>
        exact (intervalIntegrable_one_div_log_sq_refined
          (by norm_num) (by linarith)).const_mul _
      case hh =>
        calc
          Chebyshev.theta t / (t * Real.log t ^ 2)
              ≤ Real.log 4 * t / (t * Real.log t ^ 2) := by
            gcongr
            exact Chebyshev.theta_le_log4_mul_x (by linarith)
          _ = Real.log 4 * (1 / Real.log t ^ 2) := by
            have ht0 : t ≠ 0 := by linarith
            field_simp
    _ = Real.log 4 * (∫ t in (2 : ℝ)..x, 1 / Real.log t ^ 2) := by
      rw [intervalIntegral.integral_const_mul]
    _ ≤ Real.log 4 * ((5 / 2 : ℝ) * x / Real.log x ^ 2) := by
      gcongr
      exact integral_one_div_log_sq_le_five_halves hx

private theorem log_lower_of_million_le {x : ℝ} (hx : 1000000 ≤ x) :
    (99 / 5 : ℝ) * Real.log 2 < Real.log x := by
  have hxpos : (0 : ℝ) < x := by linarith
  have hpow : (2 : ℝ) ^ 33 < (10 : ℝ) ^ 10 := by norm_num
  have hlogpow := Real.strictMonoOn_log (by norm_num) (by norm_num) hpow
  rw [Real.log_pow, Real.log_pow] at hlogpow
  have hmillion : Real.log (1000000 : ℝ) = 6 * Real.log 10 := by
    convert Real.log_pow (10 : ℝ) 6 using 1 <;> norm_num
  have hmono : Real.log (1000000 : ℝ) ≤ Real.log x :=
    Real.strictMonoOn_log.monotoneOn (by norm_num) hxpos hx
  rw [hmillion] at hmono
  norm_num at hlogpow ⊢
  nlinarith

theorem eight_mul_primeCounting_lt_of_million_le
    {k : ℕ} (hk : 1000000 ≤ k) :
    8 * Nat.primeCounting k < k := by
  have hkR : (1000000 : ℝ) ≤ k := by exact_mod_cast hk
  have hk512 : (512 : ℝ) ≤ k := by linarith
  have hkpos : (0 : ℝ) < k := by positivity
  have hlogLower := log_lower_of_million_le hkR
  have hlog2pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlogpos : (0 : ℝ) < Real.log (k : ℝ) := by
    nlinarith
  have hlog4eq : Real.log 4 = 2 * Real.log 2 := by
    convert Real.log_pow (2 : ℝ) 2 using 1 <;> norm_num
  have hmain :
      Real.log 4 / Real.log (k : ℝ) < (10 / 99 : ℝ) := by
    apply (div_lt_iff₀ hlogpos).2
    rw [hlog4eq]
    nlinarith
  have hscaledpos : (0 : ℝ) < (99 / 5 : ℝ) * Real.log 2 := by positivity
  have hsq :
      ((99 / 5 : ℝ) * Real.log 2) ^ 2 < Real.log (k : ℝ) ^ 2 := by
    nlinarith [mul_self_lt_mul_self (le_of_lt hscaledpos) hlogLower]
  have hlogSquare :
      (250 : ℝ) * Real.log 2 < Real.log (k : ℝ) ^ 2 := by
    nlinarith [Real.log_two_gt_d9]
  have hsecond :
      ((5 / 2 : ℝ) * Real.log 4) / Real.log (k : ℝ) ^ 2 <
        (1 / 50 : ℝ) := by
    apply (div_lt_iff₀ (sq_pos_of_pos hlogpos)).2
    rw [hlog4eq]
    nlinarith
  have hcoeff :
      Real.log 4 / Real.log (k : ℝ) +
          ((5 / 2 : ℝ) * Real.log 4) / Real.log (k : ℝ) ^ 2 <
        (1 / 8 : ℝ) := by
    nlinarith [hmain, hsecond]
  have htheta := integral_theta_div_log_sq_le_five_halves hk512
  have hpiIdentity := Chebyshev.primeCounting_eq_theta_div_log_add_integral
    (x := (k : ℝ)) (by linarith : (2 : ℝ) ≤ k)
  have hpiIdentity' :
      (Nat.primeCounting k : ℝ) =
        Chebyshev.theta (k : ℝ) / Real.log (k : ℝ) +
          ∫ t in (2 : ℝ)..k, Chebyshev.theta t / (t * Real.log t ^ 2) := by
    simpa using hpiIdentity
  have hthetaMain :
      Chebyshev.theta (k : ℝ) / Real.log (k : ℝ) ≤
        Real.log 4 * k / Real.log (k : ℝ) := by
    gcongr
    exact Chebyshev.theta_le_log4_mul_x (by positivity)
  have hpi :
      (Nat.primeCounting k : ℝ) <
        (k : ℝ) / 8 := by
    rw [hpiIdentity']
    calc
      Chebyshev.theta (k : ℝ) / Real.log (k : ℝ) +
          ∫ t in (2 : ℝ)..k, Chebyshev.theta t / (t * Real.log t ^ 2)
          ≤ Real.log 4 * k / Real.log (k : ℝ) +
              Real.log 4 * ((5 / 2 : ℝ) * k / Real.log (k : ℝ) ^ 2) :=
        add_le_add hthetaMain htheta
      _ = (k : ℝ) *
          (Real.log 4 / Real.log (k : ℝ) +
            ((5 / 2 : ℝ) * Real.log 4) / Real.log (k : ℝ) ^ 2) := by ring
      _ < (k : ℝ) * (1 / 8 : ℝ) := mul_lt_mul_of_pos_left hcoeff hkpos
      _ = (k : ℝ) / 8 := by ring
  exact_mod_cast (show (8 : ℝ) * Nat.primeCounting k < k by nlinarith)

#print axioms integral_one_div_log_sq_le_at_512
#print axioms integral_one_div_log_sq_le_five_halves
#print axioms integral_theta_div_log_sq_le_five_halves
#print axioms eight_mul_primeCounting_lt_of_million_le

end Erdos686Variant
end Erdos686
