import Research.Definitions
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

open scoped BigOperators

namespace Erdos521

lemma littlewoodPolynomial_eval (ω : ℕ → Bool) (n : ℕ) (x : ℝ) :
    (littlewoodPolynomial ω n).eval x =
      ∑ k ∈ Finset.range (n + 1), sign (ω k) * x ^ k := by
  rw [littlewoodPolynomial, Polynomial.eval_finset_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Polynomial.eval_monomial]

lemma abs_sign (b : Bool) : |sign b| = 1 := by
  cases b <;> norm_num [sign]

lemma abs_sum_tail_lt_one {ω : ℕ → Bool} {n : ℕ} {x : ℝ} (hx : |x| ≤ 1 / 2) :
    |∑ k ∈ Finset.Icc 1 n, sign (ω k) * x ^ k| < 1 := by
  calc
    |∑ k ∈ Finset.Icc 1 n, sign (ω k) * x ^ k| ≤
        ∑ k ∈ Finset.Icc 1 n, |sign (ω k) * x ^ k| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ k ∈ Finset.Icc 1 n, |x| ^ k := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [abs_mul, abs_sign, one_mul, abs_pow]
    _ ≤ ∑ k ∈ Finset.Icc 1 n, (1 / 2 : ℝ) ^ k := by
      apply Finset.sum_le_sum
      intro k hk
      exact pow_le_pow_left₀ (abs_nonneg x) hx k
    _ < 1 := by
      have hs : Finset.Icc 1 n = Finset.Ico 1 (n + 1) := by
        ext k
        simp
      rw [hs, Finset.sum_Ico_eq_sum_range]
      rw [show (∑ k ∈ Finset.range (n + 1 - 1), (1 / 2 : ℝ) ^ (1 + k)) =
          (1 / 2 : ℝ) * ∑ k ∈ Finset.range n, (1 / 2 : ℝ) ^ k by
        rw [show n + 1 - 1 = n by omega, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k hk
        rw [pow_add]
        norm_num]
      rw [geom_sum_eq (by norm_num : (1 / 2 : ℝ) ≠ 1)]
      have hp : 0 < (1 / 2 : ℝ) ^ n := by positivity
      have heq : (1 / 2 : ℝ) * (((1 / 2 : ℝ) ^ n - 1) / ((1 / 2 : ℝ) - 1)) =
          1 - (1 / 2 : ℝ) ^ n := by
        field_simp
        ring
      rw [heq]
      exact sub_lt_self 1 hp

/-- A Littlewood polynomial cannot vanish in the closed central interval `[-1/2,1/2]`, because
its constant coefficient has modulus one while the geometric tail has modulus strictly below
one. -/
lemma littlewoodPolynomial_ne_zero_of_abs_le_half (ω : ℕ → Bool) (n : ℕ) (x : ℝ)
    (hx : |x| ≤ 1 / 2) :
    (littlewoodPolynomial ω n).eval x ≠ 0 := by
  rw [littlewoodPolynomial_eval]
  have hsplit : (∑ k ∈ Finset.range (n + 1), sign (ω k) * x ^ k) =
      sign (ω 0) + ∑ k ∈ Finset.Icc 1 n, sign (ω k) * x ^ k := by
    let f := fun k : ℕ ↦ sign (ω k) * x ^ k
    have ht := Finset.sum_Ico_eq_add_neg f (by omega : 1 ≤ n + 1)
    have hs : Finset.Ico 1 (n + 1) = Finset.Icc 1 n := by
      ext k
      simp
    rw [hs] at ht
    have hzero : ∑ k ∈ Finset.range 1, f k = sign (ω 0) := by simp [f]
    rw [hzero] at ht
    dsimp only [f] at ht
    linarith
  rw [hsplit]
  intro hzero
  have heq : |sign (ω 0)| =
      |∑ k ∈ Finset.Icc 1 n, sign (ω k) * x ^ k| := by
    rw [← neg_eq_iff_add_eq_zero.mpr hzero, abs_neg]
  rw [abs_sign] at heq
  have hlt := abs_sum_tail_lt_one (ω := ω) (n := n) hx
  linarith

lemma central_not_mem_littlewood_rootSet (ω : ℕ → Bool) (n : ℕ) (x : ℝ)
    (hx : |x| ≤ 1 / 2) :
    x ∉ (littlewoodPolynomial ω n).rootSet ℝ := by
  intro hroot
  rw [Polynomial.mem_rootSet] at hroot
  have heval : (littlewoodPolynomial ω n).eval x = 0 := by
    simpa [Polynomial.aeval_def] using hroot.2
  exact littlewoodPolynomial_ne_zero_of_abs_le_half ω n x hx heval

lemma littlewood_rootSet_inter_central (ω : ℕ → Bool) (n : ℕ) :
    (littlewoodPolynomial ω n).rootSet ℝ ∩ {x : ℝ | |x| ≤ 1 / 2} = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  intro x hx
  exact central_not_mem_littlewood_rootSet ω n x hx.2 hx.1

end Erdos521
