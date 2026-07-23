import Research.CrossingSparseBC
import Mathlib.Tactic

namespace Erdos521

noncomputable local instance (p : Prop) : Decidable p := Classical.propDecidable p

lemma initialCoefficientList_succ (N : ℕ) (a : ℕ → ℝ) :
    initialCoefficientList (N + 1) a = initialCoefficientList N a ++ [a (N + 1)] := by
  rw [initialCoefficientList_eq_range_map, initialCoefficientList_eq_range_map]
  rw [show N + 1 + 1 = (N + 1).succ by omega, List.range_succ, List.map_append]
  simp

lemma weakCrossingsFrom_append_singleton (p : ℝ) (l : List ℝ) (x : ℝ) :
    weakCrossingsFrom p (l ++ [x]) = weakCrossingsFrom p l +
      if l.getLastD p * x ≤ 0 then 1 else 0 := by
  induction l generalizing p with
  | nil => simp [weakCrossingsFrom]
  | cons y ys ih =>
      rw [List.cons_append]
      simp only [weakCrossingsFrom, List.getLastD_cons]
      rw [ih y]
      omega

lemma weakCrossingCount_append_singleton (l : List ℝ) (x : ℝ) (hl : l ≠ []) :
    weakCrossingCount (l ++ [x]) = weakCrossingCount l +
      if l.getLastD 0 * x ≤ 0 then 1 else 0 := by
  cases l with
  | nil => contradiction
  | cons a l =>
      simp only [List.cons_append, weakCrossingCount, List.getLastD_cons]
      exact weakCrossingsFrom_append_singleton a l x

lemma integratedCrossingCount_succ (ω : ℕ → Bool) (N : ℕ) :
    integratedCrossingCount ω (N + 1) = integratedCrossingCount ω N +
      if integratedRademacherSum ω N * integratedRademacherSum ω (N + 1) ≤ 0 then 1 else 0 := by
  unfold integratedCrossingCount
  rw [initialCoefficientList_succ]
  have hne : initialCoefficientList N (integratedRademacherSum ω) ≠ [] := by
    apply List.ne_nil_of_length_pos
    simp
  rw [weakCrossingCount_append_singleton _ _ hne]
  congr 2
  rw [show (initialCoefficientList N (integratedRademacherSum ω)).getLastD 0 =
      integratedRademacherSum ω N by
    rw [List.getLastD_eq_getLast?, List.getLast?_eq_some_getLast hne]
    simp only [Option.getD_some]
    unfold initialCoefficientList
    rw [List.getLast_ofFn]
    simp]

/-- Indicator of the weak crossing across the edge from time `k` to `k+1`. -/
noncomputable def integratedCrossingIndicator (ω : ℕ → Bool) (k : ℕ) : ℕ :=
  if integratedRademacherSum ω k * integratedRademacherSum ω (k + 1) ≤ 0 then 1 else 0

lemma integratedCrossingCount_eq_sum (ω : ℕ → Bool) (N : ℕ) :
    integratedCrossingCount ω N =
      ∑ k ∈ Finset.range N, integratedCrossingIndicator ω k := by
  induction N with
  | zero => simp [integratedCrossingCount, initialCoefficientList, weakCrossingCount,
      weakCrossingsFrom]
  | succ N ih =>
      rw [show N + 1 = N + 1 by rfl, integratedCrossingCount_succ, ih,
        Finset.sum_range_succ]
      rfl

lemma integratedCrossingCount_sub (ω : ℕ → Bool) {N M : ℕ} (hNM : N ≤ M) :
    integratedCrossingCount ω M - integratedCrossingCount ω N =
      ∑ k ∈ Finset.Ico N M, integratedCrossingIndicator ω k := by
  rw [integratedCrossingCount_eq_sum, integratedCrossingCount_eq_sum]
  have hs := Finset.sum_range_add_sum_Ico (integratedCrossingIndicator ω) hNM
  have hle : (∑ k ∈ Finset.range N, integratedCrossingIndicator ω k) ≤
      ∑ k ∈ Finset.range M, integratedCrossingIndicator ω k := by omega
  apply (Nat.sub_eq_iff_eq_add' hle).2
  exact hs.symm

end Erdos521
