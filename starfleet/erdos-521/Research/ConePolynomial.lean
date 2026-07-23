import Research.ConeAbel
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Tactic

open scoped BigOperators Polynomial

namespace Erdos521

/-- Split a sum of even length into its even- and odd-indexed terms. -/
lemma sum_range_even_odd {M : Type*} [AddCommMonoid M] (f : ℕ → M) : ∀ n : ℕ,
    (∑ j ∈ Finset.range (2 * n), f j) =
      ∑ i ∈ Finset.range n, (f (2 * i) + f (2 * i + 1)) := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      rw [show 2 * (n + 1) = 2 * n + 2 by omega]
      rw [Finset.sum_range_succ, Finset.sum_range_succ, ih, Finset.sum_range_succ]
      simp [add_assoc]

/-- Evaluation of an odd-length reflected polynomial, grouped into even/odd coefficient pairs. -/
lemma eval_reflect_odd_eq_pair_sum (p : Polynomial ℝ) (m : ℕ) (x : ℝ)
    (hdeg : p.natDegree ≤ 2 * m + 1) :
    (p.reflect (2 * m + 1)).eval x =
      ∑ i ∈ Finset.range (m + 1),
        (p.coeff (2 * m + 1 - 2 * i) + x * p.coeff (2 * m - 2 * i)) * (x ^ 2) ^ i := by
  have hrefdeg : (p.reflect (2 * m + 1)).natDegree < 2 * (m + 1) := by
    apply lt_of_le_of_lt Polynomial.natDegree_reflect_le
    simp only [max_eq_left hdeg]
    omega
  rw [Polynomial.eval_eq_sum_range' hrefdeg]
  rw [sum_range_even_odd]
  apply Finset.sum_congr rfl
  intro i hi
  have hil : i < m + 1 := Finset.mem_range.mp hi
  have him : i ≤ m := by omega
  have hsub : 2 * m + 1 - (2 * i + 1) = 2 * m - 2 * i := by omega
  have heven : x ^ (2 * i) = (x ^ 2) ^ i := by rw [pow_mul]
  have hodd : x ^ (2 * i + 1) = x * (x ^ 2) ^ i := by
    rw [pow_add, heven, pow_one]
    ring
  rw [Polynomial.coeff_reflect, Polynomial.coeff_reflect]
  rw [Polynomial.revAt_le (by omega : 2 * i ≤ 2 * m + 1)]
  rw [Polynomial.revAt_le (by omega : 2 * i + 1 ≤ 2 * m + 1)]
  rw [hsub, heven, hodd]
  ring

/-- Polynomial form of the Abel cone obstruction: a reflected polynomial whose paired prefix
sums lie in `u ≥ |v|` has no nonzero root in `(-1,1)`. -/
lemma eval_reflect_odd_pos_of_cone (p : Polynomial ℝ) (m : ℕ) {x : ℝ}
    (hdeg : p.natDegree ≤ 2 * m + 1)
    (hx0 : 0 < |x|) (hx1 : |x| < 1)
    (hcone : ∀ r ≤ m,
      |prefixSum (fun i ↦ p.coeff (2 * m - 2 * i)) r| ≤
        prefixSum (fun i ↦ p.coeff (2 * m + 1 - 2 * i)) r)
    (hne : ∃ i ≤ m,
      p.coeff (2 * m + 1 - 2 * i) ≠ 0 ∨ p.coeff (2 * m - 2 * i) ≠ 0) :
    0 < (p.reflect (2 * m + 1)).eval x := by
  rw [eval_reflect_odd_eq_pair_sum p m x hdeg]
  exact abel_cone_criterion
    (fun i ↦ p.coeff (2 * m + 1 - 2 * i))
    (fun i ↦ p.coeff (2 * m - 2 * i)) hx0 hx1 hcone hne

/-- In particular, under the cone hypothesis the reflected polynomial is nonzero throughout
`(-1,0) ∪ (0,1)`. -/
lemma eval_reflect_odd_ne_zero_of_cone (p : Polynomial ℝ) (m : ℕ) {x : ℝ}
    (hdeg : p.natDegree ≤ 2 * m + 1)
    (hx0 : 0 < |x|) (hx1 : |x| < 1)
    (hcone : ∀ r ≤ m,
      |prefixSum (fun i ↦ p.coeff (2 * m - 2 * i)) r| ≤
        prefixSum (fun i ↦ p.coeff (2 * m + 1 - 2 * i)) r)
    (hne : ∃ i ≤ m,
      p.coeff (2 * m + 1 - 2 * i) ≠ 0 ∨ p.coeff (2 * m - 2 * i) ≠ 0) :
    (p.reflect (2 * m + 1)).eval x ≠ 0 :=
  ne_of_gt (eval_reflect_odd_pos_of_cone p m hdeg hx0 hx1 hcone hne)

end Erdos521
