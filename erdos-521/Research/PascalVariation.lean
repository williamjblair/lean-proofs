import Research.SignVariationList
import Mathlib.Tactic

namespace Erdos521

@[simp] lemma adjacentAddAt_length (j : ℕ) (l : List ℝ) :
    (adjacentAddAt j l).length = l.length := by
  induction j generalizing l with
  | zero =>
      cases l with
      | nil => simp [adjacentAddAt]
      | cons a l =>
          cases l with
          | nil => simp [adjacentAddAt]
          | cons b l => simp [adjacentAddAt]
  | succ j ih =>
      cases l with
      | nil => simp [adjacentAddAt]
      | cons a l =>
          cases l with
          | nil => simp [adjacentAddAt]
          | cons b l =>
              cases j with
              | zero => simp [adjacentAddAt]
              | succ j => simp [adjacentAddAt, ih]

lemma adjacentAddAt_getD (j i : ℕ) (l : List ℝ) :
    (adjacentAddAt j l).getD i 0 =
      if i = j ∧ 0 < j ∧ j < l.length then
        l.getD (j - 1) 0 + l.getD j 0 else l.getD i 0 := by
  induction j generalizing i l with
  | zero =>
      cases l with
      | nil => simp [adjacentAddAt]
      | cons a l =>
          cases l with
          | nil => simp [adjacentAddAt]
          | cons b l => simp [adjacentAddAt]
  | succ j ih =>
      cases l with
      | nil => simp [adjacentAddAt]
      | cons a l =>
          cases l with
          | nil =>
              cases i <;> simp [adjacentAddAt]
          | cons b l =>
              cases j with
              | zero =>
                  rcases i with _ | _ | i <;> simp [adjacentAddAt]
              | succ j =>
                  cases i with
                  | zero => simp [adjacentAddAt]
                  | succ i =>
                      simp only [adjacentAddAt, List.getD_cons_succ, List.length_cons]
                      rw [ih]
                      split_ifs with h₁ h₂
                      · rcases h₁ with ⟨rfl, -, -⟩
                        simp [List.getD_cons_succ]
                      · simp only [List.length_cons] at *
                        exfalso; omega
                      · simp only [List.length_cons] at *
                        exfalso; omega
                      · rfl

/-- Apply the adjacent additions at indices `start+count-1, …, start`, in descending order. -/
def descendingSweep (start : ℕ) : ℕ → List ℝ → List ℝ
  | 0, l => l
  | count + 1, l => descendingSweep start count (adjacentAddAt (start + count) l)

@[simp] lemma descendingSweep_length (start count : ℕ) (l : List ℝ) :
    (descendingSweep start count l).length = l.length := by
  induction count generalizing l with
  | zero => rfl
  | succ count ih => simp [descendingSweep, ih]

lemma listSignVariations_descendingSweep_le (start count : ℕ) (l : List ℝ) :
    listSignVariations (descendingSweep start count l) ≤ listSignVariations l := by
  induction count generalizing l with
  | zero => simp [descendingSweep]
  | succ count ih =>
      exact (ih (adjacentAddAt (start + count) l)).trans
        (listSignVariations_adjacentAddAt_le (start + count) l)

lemma descendingSweep_getD (start count i : ℕ) (l : List ℝ)
    (hstart : 0 < start) (hbound : start + count ≤ l.length) :
    (descendingSweep start count l).getD i 0 =
      if start ≤ i ∧ i < start + count then
        l.getD (i - 1) 0 + l.getD i 0 else l.getD i 0 := by
  induction count generalizing l i with
  | zero => simp [descendingSweep]
  | succ count ih =>
      rw [descendingSweep]
      rw [ih i (adjacentAddAt (start + count) l) (by
        rw [adjacentAddAt_length]
        omega)]
      rw [adjacentAddAt_getD]
      split_ifs <;> simp_all <;> try omega
      all_goals
        change (adjacentAddAt (start + count) l).getD i 0 = _
        rw [adjacentAddAt_getD]
        split_ifs <;> simp_all <;> omega

/-- The order-`k` adjacent-binomial convolution, evaluated at index `j`. -/
noncomputable def pascalConvolution (a : ℕ → ℝ) (k j : ℕ) : ℝ :=
  ∑ r ∈ Finset.range (k + 1), (Nat.choose k r : ℝ) * a (j - r)

lemma pascalConvolution_succ (a : ℕ → ℝ) (k j : ℕ) (hkj : k < j) :
    pascalConvolution a (k + 1) j =
      pascalConvolution a k (j - 1) + pascalConvolution a k j := by
  rw [pascalConvolution, Finset.sum_range_succ']
  simp only [Nat.choose_zero_right, Nat.cast_one, one_mul]
  have hsub (r : ℕ) (hr : r ∈ Finset.range (k + 1)) :
      j - (r + 1) = j - 1 - r := by
    have := Finset.mem_range.mp hr
    omega
  calc
    (∑ r ∈ Finset.range (k + 1),
        (Nat.choose (k + 1) (r + 1) : ℝ) * a (j - (r + 1))) + a j =
        (∑ r ∈ Finset.range (k + 1),
          ((Nat.choose k r : ℝ) * a (j - 1 - r) +
            (Nat.choose k (r + 1) : ℝ) * a (j - (r + 1)))) + a j := by
      congr 1
      apply Finset.sum_congr rfl
      intro r hr
      rw [Nat.choose_succ_succ', Nat.cast_add, add_mul, hsub r hr]
    _ = (∑ r ∈ Finset.range (k + 1),
          (Nat.choose k r : ℝ) * a (j - 1 - r)) +
        ((∑ r ∈ Finset.range (k + 1),
          (Nat.choose k (r + 1) : ℝ) * a (j - (r + 1))) + a j) := by
      rw [Finset.sum_add_distrib]
      ring
    _ = pascalConvolution a k (j - 1) + pascalConvolution a k j := by
      rw [pascalConvolution, pascalConvolution]
      congr 1
      have htrim :
          (∑ r ∈ Finset.range (k + 1),
            (Nat.choose k (r + 1) : ℝ) * a (j - (r + 1))) =
            ∑ r ∈ Finset.range k,
              (Nat.choose k (r + 1) : ℝ) * a (j - (r + 1)) := by
        rw [Finset.sum_range_succ]
        simp [Nat.choose_succ_self]
      rw [htrim]
      conv_rhs => rw [Finset.sum_range_succ']
      simp

@[simp] lemma pascalConvolution_zero (a : ℕ → ℝ) (j : ℕ) :
    pascalConvolution a 0 j = a j := by
  simp [pascalConvolution]

/-- Apply the first `stages` descending sweeps of the Pascal factorization in a list of
nominal top index `N`. -/
def pascalStages (N : ℕ) : ℕ → List ℝ → List ℝ
  | 0, l => l
  | k + 1, l => descendingSweep (k + 1) (N - k) (pascalStages N k l)

@[simp] lemma pascalStages_length (N stages : ℕ) (l : List ℝ) :
    (pascalStages N stages l).length = l.length := by
  induction stages with
  | zero => rfl
  | succ stages ih => simp [pascalStages, ih]

lemma listSignVariations_pascalStages_le (N stages : ℕ) (l : List ℝ) :
    listSignVariations (pascalStages N stages l) ≤ listSignVariations l := by
  induction stages with
  | zero => simp [pascalStages]
  | succ stages ih =>
      exact (listSignVariations_descendingSweep_le (stages + 1) (N - stages)
        (pascalStages N stages l)).trans ih

lemma pascalStages_getD (N k j : ℕ) (l : List ℝ)
    (hlen : l.length = N + 1) (hk : k ≤ N) (hj : j ≤ N) :
    (pascalStages N k l).getD j 0 =
      pascalConvolution (fun r ↦ l.getD r 0) (min k j) j := by
  induction k generalizing j with
  | zero => simp [pascalStages]
  | succ k ih =>
      have hkN : k ≤ N := by omega
      rw [pascalStages]
      rw [descendingSweep_getD (k + 1) (N - k) j (pascalStages N k l)
        (by omega) (by rw [pascalStages_length, hlen]; omega)]
      by_cases hjk : j < k + 1
      · rw [if_neg (by omega)]
        rw [ih j hkN hj]
        rw [show min (k + 1) j = j by omega, show min k j = j by omega]
      · rw [if_pos (by constructor <;> omega)]
        rw [ih (j - 1) hkN (by omega : j - 1 ≤ N), ih j hkN hj]
        rw [show min k (j - 1) = k by omega, show min k j = k by omega,
          show min (k + 1) j = k + 1 by omega]
        rw [pascalConvolution_succ (fun r ↦ l.getD r 0) k j (by omega)]

/-- Full lower-Pascal transform of a list of length `N+1`, implemented as adjacent positive
additions. -/
def pascalAlgorithm (N : ℕ) (l : List ℝ) : List ℝ := pascalStages N N l

lemma listSignVariations_pascalAlgorithm_le (N : ℕ) (l : List ℝ) :
    listSignVariations (pascalAlgorithm N l) ≤ listSignVariations l :=
  listSignVariations_pascalStages_le N N l

lemma pascalAlgorithm_getD (N j : ℕ) (l : List ℝ)
    (hlen : l.length = N + 1) (hj : j ≤ N) :
    (pascalAlgorithm N l).getD j 0 =
      ∑ r ∈ Finset.range (j + 1), (Nat.choose j r : ℝ) * l.getD (j - r) 0 := by
  rw [pascalAlgorithm, pascalStages_getD N N j l hlen le_rfl hj,
    min_eq_right hj, pascalConvolution]

lemma pascalConvolution_diagonal (a : ℕ → ℝ) (j : ℕ) :
    pascalConvolution a j j =
      ∑ r ∈ Finset.range (j + 1), (Nat.choose j r : ℝ) * a r := by
  rw [pascalConvolution]
  calc
    (∑ r ∈ Finset.range (j + 1), (Nat.choose j r : ℝ) * a (j - r)) =
        ∑ r ∈ Finset.range (j + 1),
          (Nat.choose j (j - (j + 1 - 1 - r)) : ℝ) * a (j + 1 - 1 - r) := by
      apply Finset.sum_congr rfl
      intro r hr
      have hrj : r ≤ j := by
        have := Finset.mem_range.mp hr
        omega
      rw [show j + 1 - 1 - r = j - r by omega,
        show j - (j - r) = r by omega]
    _ = ∑ r ∈ Finset.range (j + 1), (Nat.choose j (j - r) : ℝ) * a r :=
      Finset.sum_range_reflect (fun r ↦ (Nat.choose j (j - r) : ℝ) * a r) (j + 1)
    _ = ∑ r ∈ Finset.range (j + 1), (Nat.choose j r : ℝ) * a r := by
      apply Finset.sum_congr rfl
      intro r hr
      have hrj : r ≤ j := by
        have := Finset.mem_range.mp hr
        omega
      rw [Nat.choose_symm hrj]

/-- Entries `a 0,…,a N` in increasing-index order. -/
noncomputable def initialCoefficientList (N : ℕ) (a : ℕ → ℝ) : List ℝ :=
  List.ofFn (fun i : Fin (N + 1) ↦ a i)

/-- The ordinary lower-Pascal transform, in increasing-index order. -/
noncomputable def ordinaryPascalTransform (N : ℕ) (a : ℕ → ℝ) : List ℝ :=
  List.ofFn (fun j : Fin (N + 1) ↦
    ∑ r ∈ Finset.range (j + 1), (Nat.choose j r : ℝ) * a r)

@[simp] lemma initialCoefficientList_length (N : ℕ) (a : ℕ → ℝ) :
    (initialCoefficientList N a).length = N + 1 := by
  simp [initialCoefficientList]

@[simp] lemma ordinaryPascalTransform_length (N : ℕ) (a : ℕ → ℝ) :
    (ordinaryPascalTransform N a).length = N + 1 := by
  simp [ordinaryPascalTransform]

lemma initialCoefficientList_getD (N j : ℕ) (a : ℕ → ℝ) (hj : j ≤ N) :
    (initialCoefficientList N a).getD j 0 = a j := by
  rw [List.getD_eq_getElem?_getD, initialCoefficientList, List.getElem?_ofFn,
    dif_pos (by omega)]
  rfl

lemma ordinaryPascalTransform_getD (N j : ℕ) (a : ℕ → ℝ) (hj : j ≤ N) :
    (ordinaryPascalTransform N a).getD j 0 =
      ∑ r ∈ Finset.range (j + 1), (Nat.choose j r : ℝ) * a r := by
  rw [List.getD_eq_getElem?_getD, ordinaryPascalTransform, List.getElem?_ofFn,
    dif_pos (by omega)]
  rfl

lemma pascalAlgorithm_initial_eq_transform (N : ℕ) (a : ℕ → ℝ) :
    pascalAlgorithm N (initialCoefficientList N a) = ordinaryPascalTransform N a := by
  apply List.ext_getElem
  · simp [pascalAlgorithm]
  · intro j hj₁ hj₂
    have hj : j ≤ N := by
      have : j < N + 1 := by simpa using hj₂
      omega
    have hd :
        (pascalAlgorithm N (initialCoefficientList N a)).getD j 0 =
          (ordinaryPascalTransform N a).getD j 0 := by
      rw [pascalAlgorithm_getD N j (initialCoefficientList N a) (by simp) hj]
      rw [ordinaryPascalTransform_getD N j a hj]
      calc
        (∑ r ∈ Finset.range (j + 1),
            (Nat.choose j r : ℝ) * (initialCoefficientList N a).getD (j - r) 0) =
            pascalConvolution a j j := by
          rw [pascalConvolution]
          apply Finset.sum_congr rfl
          intro r hr
          rw [initialCoefficientList_getD N (j - r) a (by omega)]
        _ = _ := pascalConvolution_diagonal a j
    simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj₁,
      List.getElem?_eq_getElem hj₂] using hd

lemma listSignVariations_ordinaryPascalTransform_le (N : ℕ) (a : ℕ → ℝ) :
    listSignVariations (ordinaryPascalTransform N a) ≤
      listSignVariations (initialCoefficientList N a) := by
  rw [← pascalAlgorithm_initial_eq_transform]
  exact listSignVariations_pascalAlgorithm_le N _

end Erdos521
