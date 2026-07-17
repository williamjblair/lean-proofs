/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import PrimeNumberTheoremAnd.Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Erdős 686: an axiom-clean Chebyshev prime-counting tail

This file records the strongest short elementary consequence of the
formalized Chebyshev estimate needed by the matching-tail campaign.  It is
deliberately not advertised as a replacement for the current matching-tail
analytic dependency: its useful rational consequences start only at `10^10`,
so they leave the interval from `10^6` to `10^10` uncovered.
-/

namespace Erdos686
namespace Erdos686Variant

/-- Natural-input form of the axiom-clean Chebyshev prime-counting bound. -/
theorem primeCounting_le_chebyshev_log4
    {k : ℕ} (hk : 2 ≤ k) :
    (Nat.primeCounting k : ℝ) ≤
      Real.log 4 * k / Real.log (Real.sqrt k) + Real.sqrt k := by
  simpa using (Chebyshev.pi_le_log4_mul_div
    (x := (k : ℝ)) (by exact_mod_cast (show 1 < k by omega)))

private theorem log_nat_gt_twenty_four_of_trillion_le
    {k : ℕ} (hk : 1000000000000 ≤ k) :
    24 < Real.log (k : ℝ) := by
  have hkpos : (0 : ℝ) < k := by positivity
  have hlog10 : (2 : ℝ) < Real.log 10 := by
    have hlog8 : Real.log (8 : ℝ) = 3 * Real.log 2 := by
      convert Real.log_pow (2 : ℝ) 3 using 1 <;> norm_num
    have h8lt10 : Real.log (8 : ℝ) < Real.log 10 :=
      Real.strictMonoOn_log (by norm_num) (by norm_num) (by norm_num)
    rw [hlog8] at h8lt10
    nlinarith [Real.log_two_gt_d9]
  have htrillion : Real.log (1000000000000 : ℝ) =
      12 * Real.log 10 := by
    convert Real.log_pow (10 : ℝ) 12 using 1 <;> norm_num
  have hmono : Real.log (1000000000000 : ℝ) ≤ Real.log (k : ℝ) :=
    Real.strictMonoOn_log.monotoneOn (by norm_num) hkpos (by exact_mod_cast hk)
  rw [htrillion] at hmono
  linarith

private theorem sqrt_nat_le_millionth_of_trillion_le
    {k : ℕ} (hk : 1000000000000 ≤ k) :
    Real.sqrt (k : ℝ) ≤ (k : ℝ) / 1000000 := by
  rw [Real.sqrt_le_iff]
  constructor
  · positivity
  · have hkR : (1000000000000 : ℝ) ≤ k := by exact_mod_cast hk
    have hk0 : (0 : ℝ) ≤ k := by positivity
    have hmul : (1000000000000 : ℝ) * k ≤ k * k :=
      mul_le_mul_of_nonneg_right hkR hk0
    rw [div_pow]
    norm_num
    exact (le_div_iff₀ (by norm_num : (0 : ℝ) < 1000000000000)).2
      (by simpa [pow_two, mul_comm] using hmul)

private theorem log_nat_gt_twenty_of_ten_billion_le
    {k : ℕ} (hk : 10000000000 ≤ k) :
    20 < Real.log (k : ℝ) := by
  have hkpos : (0 : ℝ) < k := by positivity
  have hlog10 : (2 : ℝ) < Real.log 10 := by
    have hlog8 : Real.log (8 : ℝ) = 3 * Real.log 2 := by
      convert Real.log_pow (2 : ℝ) 3 using 1 <;> norm_num
    have h8lt10 : Real.log (8 : ℝ) < Real.log 10 :=
      Real.strictMonoOn_log (by norm_num) (by norm_num) (by norm_num)
    rw [hlog8] at h8lt10
    nlinarith [Real.log_two_gt_d9]
  have htenBillion : Real.log (10000000000 : ℝ) =
      10 * Real.log 10 := by
    convert Real.log_pow (10 : ℝ) 10 using 1 <;> norm_num
  have hmono : Real.log (10000000000 : ℝ) ≤ Real.log (k : ℝ) :=
    Real.strictMonoOn_log.monotoneOn (by norm_num) hkpos (by exact_mod_cast hk)
  rw [htenBillion] at hmono
  linarith

private theorem sqrt_nat_le_hundred_thousandth_of_ten_billion_le
    {k : ℕ} (hk : 10000000000 ≤ k) :
    Real.sqrt (k : ℝ) ≤ (k : ℝ) / 100000 := by
  rw [Real.sqrt_le_iff]
  constructor
  · positivity
  · have hkR : (10000000000 : ℝ) ≤ k := by exact_mod_cast hk
    have hk0 : (0 : ℝ) ≤ k := by positivity
    have hmul : (10000000000 : ℝ) * k ≤ k * k :=
      mul_le_mul_of_nonneg_right hkR hk0
    rw [div_pow]
    norm_num
    exact (le_div_iff₀ (by norm_num : (0 : ℝ) < 10000000000)).2
      (by simpa [pow_two, mul_comm] using hmul)

/-- A stronger, earlier rational form useful to exact matching-tail
comparisons: `π(k) < k/7` from `10^10` onward. -/
theorem seven_mul_primeCounting_lt_of_ten_billion_le
    {k : ℕ} (hk : 10000000000 ≤ k) :
    7 * Nat.primeCounting k < k := by
  have hk2 : 2 ≤ k := by omega
  have hkRpos : (0 : ℝ) < k := by positivity
  have hlog := log_nat_gt_twenty_of_ten_billion_le hk
  have hsqrt := sqrt_nat_le_hundred_thousandth_of_ten_billion_le hk
  have hcheb := primeCounting_le_chebyshev_log4 hk2
  have hlog4 : Real.log 4 < (7 / 5 : ℝ) := by
    have hlog4eq : Real.log 4 = 2 * Real.log 2 := by
      convert Real.log_pow (2 : ℝ) 2 using 1 <;> norm_num
    rw [hlog4eq]
    nlinarith [Real.log_two_lt_d9]
  have hcoeff : Real.log 4 <
      (7 / 50 : ℝ) * (Real.log (k : ℝ) / 2) := by
    nlinarith
  have hlogsqrt : Real.log (Real.sqrt (k : ℝ)) =
      Real.log (k : ℝ) / 2 := Real.log_sqrt (by positivity)
  have hlogsqrtPos : 0 < Real.log (Real.sqrt (k : ℝ)) := by
    rw [hlogsqrt]
    linarith
  have hterm :
      Real.log 4 * k / Real.log (Real.sqrt k) <
        (7 / 50 : ℝ) * k := by
    apply (div_lt_iff₀ hlogsqrtPos).2
    rw [hlogsqrt]
    simpa [mul_assoc, mul_comm, mul_left_comm] using
      (mul_lt_mul_of_pos_right hcoeff hkRpos)
  have hpi : (Nat.primeCounting k : ℝ) < (k : ℝ) / 7 := by
    calc
      (Nat.primeCounting k : ℝ) ≤
          Real.log 4 * k / Real.log (Real.sqrt k) + Real.sqrt k := hcheb
      _ < (7 / 50 : ℝ) * k + (k : ℝ) / 100000 :=
        add_lt_add_of_lt_of_le hterm hsqrt
      _ < (k : ℝ) / 7 := by
        nlinarith
  exact_mod_cast (show (7 : ℝ) * Nat.primeCounting k < k by nlinarith)

/-- Power-of-two sharpening at the same threshold.  The exact inequality
`2^33 < 10^10` gives `33 log 2 < log k`; after using
`log 4 = 2 log 2`, the Chebyshev main term is below `4k/33`.
Together with the square-root term this proves `π(k) < k/8`. -/
theorem eight_mul_primeCounting_lt_of_ten_billion_le
    {k : ℕ} (hk : 10000000000 ≤ k) :
    8 * Nat.primeCounting k < k := by
  have hk2 : 2 ≤ k := by omega
  have hkRpos : (0 : ℝ) < k := by positivity
  have hpow : (2 : ℝ) ^ 33 < k := by
    have : (8589934592 : ℕ) < k := by omega
    norm_num at this ⊢
    exact_mod_cast this
  have hlogLower : 33 * Real.log 2 < Real.log (k : ℝ) := by
    have h := Real.strictMonoOn_log (by norm_num) hkRpos hpow
    rw [Real.log_pow] at h
    norm_num at h ⊢
    exact h
  have hsqrt := sqrt_nat_le_hundred_thousandth_of_ten_billion_le hk
  have hcheb := primeCounting_le_chebyshev_log4 hk2
  have hlog4eq : Real.log 4 = 2 * Real.log 2 := by
    convert Real.log_pow (2 : ℝ) 2 using 1 <;> norm_num
  have hcoeff : Real.log 4 <
      (4 / 33 : ℝ) * (Real.log (k : ℝ) / 2) := by
    rw [hlog4eq]
    nlinarith
  have hlogsqrt : Real.log (Real.sqrt (k : ℝ)) =
      Real.log (k : ℝ) / 2 := Real.log_sqrt (by positivity)
  have hlogsqrtPos : 0 < Real.log (Real.sqrt (k : ℝ)) := by
    rw [hlogsqrt]
    have : 0 < Real.log 2 := Real.log_pos (by norm_num)
    nlinarith
  have hterm :
      Real.log 4 * k / Real.log (Real.sqrt k) <
        (4 / 33 : ℝ) * k := by
    apply (div_lt_iff₀ hlogsqrtPos).2
    rw [hlogsqrt]
    simpa [mul_assoc, mul_comm, mul_left_comm] using
      (mul_lt_mul_of_pos_right hcoeff hkRpos)
  have hpi : (Nat.primeCounting k : ℝ) < (k : ℝ) / 8 := by
    calc
      (Nat.primeCounting k : ℝ) ≤
          Real.log 4 * k / Real.log (Real.sqrt k) + Real.sqrt k := hcheb
      _ < (4 / 33 : ℝ) * k + (k : ℝ) / 100000 :=
        add_lt_add_of_lt_of_le hterm hsqrt
      _ < (k : ℝ) / 8 := by
        nlinarith
  exact_mod_cast (show (8 : ℝ) * Nat.primeCounting k < k by nlinarith)

/-- Fully formal explicit consequence of the Chebyshev theorem:
`π(k) < k/8` from `k = 10^12` onward. -/
theorem eight_mul_primeCounting_lt_of_trillion_le
    {k : ℕ} (hk : 1000000000000 ≤ k) :
    8 * Nat.primeCounting k < k := by
  have hk2 : 2 ≤ k := by omega
  have hkRpos : (0 : ℝ) < k := by positivity
  have hlog := log_nat_gt_twenty_four_of_trillion_le hk
  have hsqrt := sqrt_nat_le_millionth_of_trillion_le hk
  have hcheb := primeCounting_le_chebyshev_log4 hk2
  have hlog4 : Real.log 4 < (7 / 5 : ℝ) := by
    have hlog4eq : Real.log 4 = 2 * Real.log 2 := by
      convert Real.log_pow (2 : ℝ) 2 using 1 <;> norm_num
    rw [hlog4eq]
    nlinarith [Real.log_two_lt_d9]
  have hcoeff : Real.log 4 <
      (7 / 60 : ℝ) * (Real.log (k : ℝ) / 2) := by
    nlinarith
  have hlogsqrt : Real.log (Real.sqrt (k : ℝ)) =
      Real.log (k : ℝ) / 2 := Real.log_sqrt (by positivity)
  have hlogsqrtPos : 0 < Real.log (Real.sqrt (k : ℝ)) := by
    rw [hlogsqrt]
    linarith
  have hterm :
      Real.log 4 * k / Real.log (Real.sqrt k) <
        (7 / 60 : ℝ) * k := by
    apply (div_lt_iff₀ hlogsqrtPos).2
    rw [hlogsqrt]
    simpa [mul_assoc, mul_comm, mul_left_comm] using
      (mul_lt_mul_of_pos_right hcoeff hkRpos)
  have hpi : (Nat.primeCounting k : ℝ) < (k : ℝ) / 8 := by
    calc
      (Nat.primeCounting k : ℝ) ≤
          Real.log 4 * k / Real.log (Real.sqrt k) + Real.sqrt k := hcheb
      _ < (7 / 60 : ℝ) * k + (k : ℝ) / 1000000 :=
        add_lt_add_of_lt_of_le hterm hsqrt
      _ < (k : ℝ) / 8 := by
        nlinarith
  exact_mod_cast (show (8 : ℝ) * Nat.primeCounting k < k by nlinarith)

#print axioms primeCounting_le_chebyshev_log4
#print axioms seven_mul_primeCounting_lt_of_ten_billion_le
#print axioms eight_mul_primeCounting_lt_of_ten_billion_le
#print axioms eight_mul_primeCounting_lt_of_trillion_le

end Erdos686Variant
end Erdos686
