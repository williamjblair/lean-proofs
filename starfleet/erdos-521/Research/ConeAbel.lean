import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

open scoped BigOperators

namespace Erdos521

/-- Sum of the first `r + 1` terms of a real sequence. -/
def prefixSum (c : ℕ → ℝ) (r : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (r + 1), c i

/-- Finite Abel summation, in the form needed for the cone criterion. -/
lemma abel_sum_identity (c : ℕ → ℝ) (y : ℝ) : ∀ m : ℕ,
    (∑ i ∈ Finset.range (m + 1), c i * y ^ i) =
      (1 - y) * (∑ r ∈ Finset.range m, prefixSum c r * y ^ r) +
        prefixSum c m * y ^ m := by
  intro m
  induction m with
  | zero => simp [prefixSum]
  | succ m ih =>
      rw [Finset.sum_range_succ, ih, Finset.sum_range_succ]
      simp only [prefixSum, Finset.sum_range_succ]
      ring

/-- Nonnegative prefix sums give a nonnegative power sum on `[0,1]`. -/
lemma sum_mul_pow_nonneg_of_prefixSum_nonneg (c : ℕ → ℝ) {y : ℝ} {m : ℕ}
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1) (hprefix : ∀ r ≤ m, 0 ≤ prefixSum c r) :
    0 ≤ ∑ i ∈ Finset.range (m + 1), c i * y ^ i := by
  rw [abel_sum_identity]
  have hsum : 0 ≤ ∑ r ∈ Finset.range m, prefixSum c r * y ^ r :=
    Finset.sum_nonneg fun r hr ↦
      mul_nonneg (hprefix r (Finset.mem_range.mp hr).le) (pow_nonneg hy0 _)
  exact add_nonneg (mul_nonneg (sub_nonneg.mpr hy1) hsum)
    (mul_nonneg (hprefix m le_rfl) (pow_nonneg hy0 _))

/-- If a prefix sum is positive, Abel summation makes the power sum strictly positive in `(0,1)`. -/
lemma sum_mul_pow_pos_of_prefixSum_nonneg (c : ℕ → ℝ) {y : ℝ} {m : ℕ}
    (hy0 : 0 < y) (hy1 : y < 1) (hprefix : ∀ r ≤ m, 0 ≤ prefixSum c r)
    (hstrict : ∃ r ≤ m, 0 < prefixSum c r) :
    0 < ∑ i ∈ Finset.range (m + 1), c i * y ^ i := by
  rw [abel_sum_identity]
  obtain ⟨r, hrm, hr⟩ := hstrict
  by_cases hreq : r = m
  · subst r
    have hlast : 0 < prefixSum c m * y ^ m := mul_pos hr (pow_pos hy0 _)
    exact add_pos_of_nonneg_of_pos (mul_nonneg (sub_nonneg.mpr hy1.le)
      (Finset.sum_nonneg fun i hi ↦ mul_nonneg (hprefix i (Finset.mem_range.mp hi).le)
        (pow_nonneg hy0.le _))) hlast
  · have hrlt : r < m := lt_of_le_of_ne hrm hreq
    have hterm : 0 < prefixSum c r * y ^ r := mul_pos hr (pow_pos hy0 _)
    have hsum : 0 < ∑ i ∈ Finset.range m, prefixSum c i * y ^ i :=
      Finset.sum_pos' (fun i hi ↦ mul_nonneg (hprefix i (Finset.mem_range.mp hi).le)
        (pow_nonneg hy0.le _)) ⟨r, Finset.mem_range.mpr hrlt, hterm⟩
    exact add_pos_of_pos_of_nonneg (mul_pos (sub_pos.mpr hy1) hsum)
      (mul_nonneg (hprefix m le_rfl) (pow_nonneg hy0.le _))

/-- The zeroth prefix sum is the zeroth coefficient. -/
@[simp] lemma prefixSum_zero (c : ℕ → ℝ) : prefixSum c 0 = c 0 := by
  simp [prefixSum]

/-- Successive prefix sums differ by the new coefficient. -/
lemma prefixSum_succ (c : ℕ → ℝ) (r : ℕ) :
    prefixSum c (r + 1) = prefixSum c r + c (r + 1) := by
  simp [prefixSum, Finset.sum_range_succ]

private lemma exists_strict_prefix_of_pair_ne_zero (e o : ℕ → ℝ) {m : ℕ}
    (hplus : ∀ r ≤ m, 0 ≤ prefixSum (fun i ↦ e i + o i) r)
    (hminus : ∀ r ≤ m, 0 ≤ prefixSum (fun i ↦ e i - o i) r)
    (hne : ∃ i ≤ m, e i ≠ 0 ∨ o i ≠ 0) :
    (∃ r ≤ m, 0 < prefixSum (fun i ↦ e i + o i) r) ∨
      (∃ r ≤ m, 0 < prefixSum (fun i ↦ e i - o i) r) := by
  by_contra hstrict
  push_neg at hstrict
  obtain ⟨i, him, hei | hoi⟩ := hne
  · have hp (r : ℕ) (hr : r ≤ m) : prefixSum (fun j ↦ e j + o j) r = 0 :=
      le_antisymm (hstrict.1 r hr) (hplus r hr)
    have hm (r : ℕ) (hr : r ≤ m) : prefixSum (fun j ↦ e j - o j) r = 0 :=
      le_antisymm (hstrict.2 r hr) (hminus r hr)
    cases i with
    | zero =>
        have hp0 := hp 0 him
        have hm0 := hm 0 him
        simp only [prefixSum_zero] at hp0 hm0
        exact hei (by linarith)
    | succ r =>
        have hrm : r ≤ m := le_trans (Nat.le_succ r) him
        have hpNew := hp (r + 1) him
        have hpOld := hp r hrm
        have hmNew := hm (r + 1) him
        have hmOld := hm r hrm
        rw [prefixSum_succ] at hpNew hmNew
        exact hei (by linarith)
  · have hp (r : ℕ) (hr : r ≤ m) : prefixSum (fun j ↦ e j + o j) r = 0 :=
      le_antisymm (hstrict.1 r hr) (hplus r hr)
    have hm (r : ℕ) (hr : r ≤ m) : prefixSum (fun j ↦ e j - o j) r = 0 :=
      le_antisymm (hstrict.2 r hr) (hminus r hr)
    cases i with
    | zero =>
        have hp0 := hp 0 him
        have hm0 := hm 0 him
        simp only [prefixSum_zero] at hp0 hm0
        exact hoi (by linarith)
    | succ r =>
        have hrm : r ≤ m := le_trans (Nat.le_succ r) him
        have hpNew := hp (r + 1) him
        have hpOld := hp r hrm
        have hmNew := hm (r + 1) him
        have hmOld := hm r hrm
        rw [prefixSum_succ] at hpNew hmNew
        exact hoi (by linarith)

/-- Paired Abel criterion in a form that directly evaluates the polynomial.
If every prefix sum of `e+o` and `e-o` is nonnegative and some coefficient pair is nonzero,
then the paired polynomial is positive at every `x` with `0 < |x| < 1`. -/
lemma abel_pair_pos (e o : ℕ → ℝ) {m : ℕ} {x : ℝ}
    (hx0 : 0 < |x|) (hx1 : |x| < 1)
    (hplus : ∀ r ≤ m, 0 ≤ prefixSum (fun i ↦ e i + o i) r)
    (hminus : ∀ r ≤ m, 0 ≤ prefixSum (fun i ↦ e i - o i) r)
    (hne : ∃ i ≤ m, e i ≠ 0 ∨ o i ≠ 0) :
    0 < ∑ i ∈ Finset.range (m + 1), (e i + x * o i) * (x ^ 2) ^ i := by
  have hy0 : 0 < x ^ 2 := sq_pos_of_ne_zero (abs_pos.mp hx0)
  have hy1 : x ^ 2 < 1 := by
    have := (sq_lt_sq).mpr (show |x| < |(1 : ℝ)| by simpa using hx1)
    norm_num at this ⊢
    exact this
  have hp0 := sum_mul_pow_nonneg_of_prefixSum_nonneg (fun i ↦ e i + o i)
    hy0.le hy1.le hplus
  have hm0 := sum_mul_pow_nonneg_of_prefixSum_nonneg (fun i ↦ e i - o i)
    hy0.le hy1.le hminus
  obtain hp | hm := exists_strict_prefix_of_pair_ne_zero e o hplus hminus hne
  · have hp' := sum_mul_pow_pos_of_prefixSum_nonneg (fun i ↦ e i + o i)
      hy0 hy1 hplus hp
    have hwplus : 0 < (1 + x) / 2 :=
      div_pos (by linarith [neg_lt_of_abs_lt hx1]) (by norm_num)
    have hwminus : 0 ≤ (1 - x) / 2 :=
      (div_pos (by linarith [lt_of_abs_lt hx1]) (by norm_num)).le
    have hcomb : 0 < (1 + x) / 2 *
          (∑ i ∈ Finset.range (m + 1), (e i + o i) * (x ^ 2) ^ i) +
        (1 - x) / 2 *
          (∑ i ∈ Finset.range (m + 1), (e i - o i) * (x ^ 2) ^ i) :=
      add_pos_of_pos_of_nonneg (mul_pos hwplus hp') (mul_nonneg hwminus hm0)
    convert hcomb using 1 <;>
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib] <;>
      apply Finset.sum_congr rfl <;> intro i hi <;> ring
  · have hm' := sum_mul_pow_pos_of_prefixSum_nonneg (fun i ↦ e i - o i)
      hy0 hy1 hminus hm
    have hwplus : 0 ≤ (1 + x) / 2 :=
      (div_pos (by linarith [neg_lt_of_abs_lt hx1]) (by norm_num)).le
    have hwminus : 0 < (1 - x) / 2 :=
      div_pos (by linarith [lt_of_abs_lt hx1]) (by norm_num)
    have hcomb : 0 < (1 + x) / 2 *
          (∑ i ∈ Finset.range (m + 1), (e i + o i) * (x ^ 2) ^ i) +
        (1 - x) / 2 *
          (∑ i ∈ Finset.range (m + 1), (e i - o i) * (x ^ 2) ^ i) :=
      add_pos_of_nonneg_of_pos (mul_nonneg hwplus hp0) (mul_pos hwminus hm')
    convert hcomb using 1 <;>
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib] <;>
      apply Finset.sum_congr rfl <;> intro i hi <;> ring

/-- The cone formulation of the paired Abel criterion (`u ≥ |v|`). -/
lemma abel_cone_criterion (e o : ℕ → ℝ) {m : ℕ} {x : ℝ}
    (hx0 : 0 < |x|) (hx1 : |x| < 1)
    (hcone : ∀ r ≤ m, |prefixSum o r| ≤ prefixSum e r)
    (hne : ∃ i ≤ m, e i ≠ 0 ∨ o i ≠ 0) :
    0 < ∑ i ∈ Finset.range (m + 1), (e i + x * o i) * (x ^ 2) ^ i := by
  apply abel_pair_pos e o hx0 hx1
  · intro r hr
    have h := hcone r hr
    rw [prefixSum]
    simp only [Finset.sum_add_distrib]
    rw [← prefixSum, ← prefixSum]
    linarith [(abs_le.mp h).1]
  · intro r hr
    have h := hcone r hr
    rw [prefixSum]
    simp only [Finset.sum_sub_distrib]
    rw [← prefixSum, ← prefixSum]
    exact sub_nonneg.mpr (le_trans (le_abs_self _) h)
  · exact hne

end Erdos521
