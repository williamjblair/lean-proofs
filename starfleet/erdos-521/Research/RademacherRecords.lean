import Research.ConeRecords
import Research.ConeRecord
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic

open scoped BigOperators

namespace Erdos521

/-- The planar increment formed from one consecutive pair of Rademacher coefficients. -/
def rademacherIncrement (ω : ℕ → Bool) (i : ℕ) : ℝ × ℝ :=
  (sign (ω (2 * i + 1)), sign (ω (2 * i)))

/-- A walk displacement is exactly the corresponding reversed suffix sum. -/
lemma walk_sub_eq_reverse_suffix (z : ℕ → ℝ × ℝ) {m r : ℕ} (hrm : r ≤ m) :
    walk z (m + 1) - walk z (m - r) =
      ∑ i ∈ Finset.range (r + 1), z (m - i) := by
  rw [walk, walk, ← Finset.sum_Ico_eq_sub z (by omega : m - r ≤ m + 1)]
  rw [Finset.sum_Ico_eq_sum_range]
  have hlen : m + 1 - (m - r) = r + 1 := by omega
  rw [hlen]
  rw [← Finset.sum_range_reflect (fun i ↦ z (m - i)) (r + 1)]
  apply Finset.sum_congr rfl
  intro i hi
  have hil : i < r + 1 := Finset.mem_range.mp hi
  have hir : i ≤ r := by omega
  congr 1
  omega

/-- Every planar cone record gives exactly the coefficient suffix-cone condition used in F-002. -/
lemma coneRecord_implies_suffixCone {ω : ℕ → Bool} {m : ℕ}
    (hrec : IsConeRecord (rademacherIncrement ω) (m + 1)) : SuffixCone ω m := by
  intro r hrm
  have hk : m - r < m + 1 := by omega
  have h := hrec (m - r) hk
  rw [walk_sub_eq_reverse_suffix _ hrm] at h
  rw [InCone] at h
  change |(AddMonoidHom.snd ℝ ℝ)
      (∑ i ∈ Finset.range (r + 1), rademacherIncrement ω (m - i))| ≤
    (AddMonoidHom.fst ℝ ℝ)
      (∑ i ∈ Finset.range (r + 1), rademacherIncrement ω (m - i)) at h
  rw [map_sum, map_sum] at h
  change |∑ i ∈ Finset.range (r + 1), sign (ω (2 * (m - i)))| ≤
    ∑ i ∈ Finset.range (r + 1), sign (ω (2 * (m - i) + 1)) at h
  have heven : (∑ i ∈ Finset.range (r + 1), sign (ω (2 * m - 2 * i))) =
      ∑ i ∈ Finset.range (r + 1), sign (ω (2 * (m - i))) := by
    apply Finset.sum_congr rfl
    intro i hi
    have hil : i < r + 1 := Finset.mem_range.mp hi
    have hir : i ≤ r := by omega
    congr 2
    omega
  have hodd : (∑ i ∈ Finset.range (r + 1), sign (ω (2 * m + 1 - 2 * i))) =
      ∑ i ∈ Finset.range (r + 1), sign (ω (2 * (m - i) + 1)) := by
    apply Finset.sum_congr rfl
    intro i hi
    have hil : i < r + 1 := Finset.mem_range.mp hi
    have hir : i ≤ r := by omega
    congr 2
    omega
  rw [prefixSum, prefixSum, heven, hodd]
  exact h

/-- Hence a cone-record time of the paired Rademacher walk produces an odd-degree Littlewood
polynomial with no exterior real root. -/
lemma coneRecord_no_exterior_root {ω : ℕ → Bool} {m : ℕ}
    (hrec : IsConeRecord (rademacherIncrement ω) (m + 1))
    {y : ℝ} (hy : 1 < |y|) :
    (littlewoodPolynomial ω (2 * m + 1)).eval y ≠ 0 :=
  (coneRecord_implies_suffixCone hrec).no_exterior_root hy

end Erdos521
