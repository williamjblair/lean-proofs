import Research.IntegratedWalkCoefficients
import Research.PascalVariation
import Mathlib.Tactic

namespace Erdos521

noncomputable local instance (p : Prop) : Decidable p := Classical.propDecidable p

lemma listSignVariations_initial_eq_of_sign_eq (N : ℕ) (a b : ℕ → ℝ)
    (h : ∀ i ≤ N, SignType.sign (a i) = SignType.sign (b i)) :
    listSignVariations (initialCoefficientList N a) =
      listSignVariations (initialCoefficientList N b) := by
  unfold listSignVariations
  congr 1
  apply List.ext_getElem
  · simp
  · intro i hi₁ hi₂
    simp only [List.length_map, initialCoefficientList_length] at hi₁
    simp only [initialCoefficientList, List.map_ofFn, List.getElem_ofFn]
    exact h i (by omega)

lemma listSignVariations_sublist {l₁ l₂ : List ℝ} (h : l₁.Sublist l₂) :
    listSignVariations l₁ ≤ listSignVariations l₂ := by
  rw [listSignVariations_eq_destutter, listSignVariations_eq_destutter]
  let s₁ := (l₁.map SignType.sign).filter (· ≠ 0)
  let s₂ := (l₂.map SignType.sign).filter (· ≠ 0)
  have hs : s₁.Sublist s₂ := (h.map SignType.sign).filter (· ≠ 0)
  let d := s₁.destutter (· ≠ ·)
  have hdsub : d.Sublist s₂ := (List.destutter_sublist (· ≠ ·) s₁).trans hs
  have hdchain : d.IsChain (· ≠ ·) := List.isChain_destutter (· ≠ ·) s₁
  have hlen := hdchain.length_le_length_destutter_ne hdsub
  exact Nat.sub_le_sub_right hlen 1

lemma listSignVariations_cons_le (x : ℝ) (l : List ℝ) :
    listSignVariations (x :: l) ≤ listSignVariations l + 1 := by
  unfold listSignVariations
  simp only [List.map_cons]
  by_cases hx : SignType.sign x = 0
  · simp [signTransitions, hx]
  · rw [signTransitions, if_neg hx]
    simp only [true_or, if_true, zero_add]
    exact signTransitions_le_succ (SignType.sign x) 0 (l.map SignType.sign)

lemma initialCoefficientList_eq_range_map (N : ℕ) (a : ℕ → ℝ) :
    initialCoefficientList N a = (List.range (N + 1)).map a := by
  apply List.ext_getElem
  · simp
  · intro i hi₁ hi₂
    simp only [initialCoefficientList, List.getElem_ofFn]
    simp only [List.getElem_map, List.getElem_range]

lemma polynomial_coeffList_sublist_padded (P : Polynomial ℝ) (n : ℕ)
    (hdeg : P.natDegree ≤ n) :
    P.coeffList.Sublist (initialCoefficientList n P.coeff).reverse := by
  by_cases hP : P = 0
  · subst P
    simp
  · have hr : (List.range (P.natDegree + 1)).Sublist (List.range (n + 1)) :=
      List.range_sublist.mpr (by omega)
    have hm := hr.reverse.map P.coeff
    simpa [Polynomial.coeffList, Polynomial.withBotSucc_degree_eq_natDegree_add_one hP,
      initialCoefficientList_eq_range_map, List.map_reverse] using hm

lemma choose_ratio_identity (N j r : ℕ) (hrj : r ≤ j) (hjN : j ≤ N) :
    (Nat.choose (N - r) (j - r) : ℝ) =
      (Nat.choose N j : ℝ) * (Nat.choose j r : ℝ) / (Nat.choose N r : ℝ) := by
  have hrN : r ≤ N := hrj.trans hjN
  have hne : (Nat.choose N r : ℝ) ≠ 0 := by
    exact_mod_cast Nat.choose_ne_zero hrN
  apply (eq_div_iff hne).2
  have hnat := Nat.choose_mul (n := N) (k := j) (s := r) hrj
  have hreal : (Nat.choose N r : ℝ) * (Nat.choose (N - r) (j - r) : ℝ) =
      (Nat.choose N j : ℝ) * (Nat.choose j r : ℝ) := by
    exact_mod_cast hnat.symm
  simpa [mul_comm] using hreal

noncomputable def scaledIntegratedSum (ω : ℕ → Bool) (N r : ℕ) : ℝ :=
  integratedRademacherSum ω r / (Nat.choose N r : ℝ)

noncomputable def ordinaryIntegratedPascal (ω : ℕ → Bool) (N j : ℕ) : ℝ :=
  ∑ r ∈ Finset.range (j + 1),
    (Nat.choose j r : ℝ) * scaledIntegratedSum ω N r

lemma ordinaryPascalTransform_scaledIntegrated (ω : ℕ → Bool) (N : ℕ) :
    ordinaryPascalTransform N (scaledIntegratedSum ω N) =
      initialCoefficientList N (ordinaryIntegratedPascal ω N) := by
  rfl

lemma mobius_coeff_eq_choose_mul_ordinaryIntegratedPascal
    (ω : ℕ → Bool) (N j : ℕ) (hjN : j ≤ N) :
    (mobiusPolynomial ω (N + 2)).coeff j =
      (Nat.choose N j : ℝ) * ordinaryIntegratedPascal ω N j := by
  rw [mobiusPolynomial_coeff_eq_integrated]
  · simp only [ordinaryIntegratedPascal, scaledIntegratedSum]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r hr
    have hrj : r ≤ j := by
      have := Finset.mem_range.mp hr
      omega
    rw [show N + 2 - 2 - r = N - r by omega]
    rw [choose_ratio_identity N j r hrj hjN]
    have hne : (Nat.choose N r : ℝ) ≠ 0 := by
      exact_mod_cast Nat.choose_ne_zero (hrj.trans hjN)
    field_simp
  · omega

lemma mobiusPolynomial_natDegree_le (ω : ℕ → Bool) (n : ℕ) :
    (mobiusPolynomial ω n).natDegree ≤ n := by
  rw [Polynomial.natDegree_le_iff_degree_le]
  rw [Polynomial.degree_le_iff_coeff_zero]
  intro m hm
  have hnm : n < m := by exact_mod_cast hm
  rw [mobiusPolynomial_coeff]
  apply Finset.sum_eq_zero
  intro i hi
  have hin : i ≤ n := by
    have := Finset.mem_range.mp hi
    omega
  have him : i ≤ m := hin.trans (Nat.le_of_lt hnm)
  rw [Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, mul_zero]

lemma lowMobius_signVariations_le_integrated (ω : ℕ → Bool) (N : ℕ) :
    listSignVariations
        (initialCoefficientList N (fun j ↦ (mobiusPolynomial ω (N + 2)).coeff j)) ≤
      listSignVariations (initialCoefficientList N (integratedRademacherSum ω)) := by
  calc
    listSignVariations
        (initialCoefficientList N (fun j ↦ (mobiusPolynomial ω (N + 2)).coeff j)) =
        listSignVariations (initialCoefficientList N (ordinaryIntegratedPascal ω N)) := by
      apply listSignVariations_initial_eq_of_sign_eq
      intro j hj
      rw [mobius_coeff_eq_choose_mul_ordinaryIntegratedPascal ω N j hj]
      rw [sign_mul, sign_pos (by exact_mod_cast Nat.choose_pos hj)]
      simp
    _ = listSignVariations (ordinaryPascalTransform N (scaledIntegratedSum ω N)) := by
      rw [ordinaryPascalTransform_scaledIntegrated]
    _ ≤ listSignVariations (initialCoefficientList N (scaledIntegratedSum ω N)) :=
      listSignVariations_ordinaryPascalTransform_le N _
    _ = listSignVariations (initialCoefficientList N (integratedRademacherSum ω)) := by
      apply listSignVariations_initial_eq_of_sign_eq
      intro r hr
      have hc : 0 < (Nat.choose N r : ℝ) := by exact_mod_cast Nat.choose_pos hr
      rw [scaledIntegratedSum, div_eq_mul_inv, sign_mul, sign_pos (inv_pos.mpr hc)]
      simp

lemma initialCoefficientList_add_two (N : ℕ) (a : ℕ → ℝ) :
    initialCoefficientList (N + 2) a =
      initialCoefficientList N a ++ [a (N + 1), a (N + 2)] := by
  rw [initialCoefficientList_eq_range_map, initialCoefficientList_eq_range_map]
  rw [show N + 2 + 1 = (N + 1).succ.succ by omega,
    List.range_succ, List.range_succ, List.map_append, List.map_append]
  simp

lemma mobius_signVariations_le_integrated_add_two (ω : ℕ → Bool) (N : ℕ) :
    (mobiusPolynomial ω (N + 2)).signVariations ≤
      listSignVariations (initialCoefficientList N (integratedRademacherSum ω)) + 2 := by
  let P := mobiusPolynomial ω (N + 2)
  let low := initialCoefficientList N (fun j ↦ P.coeff j)
  have hsub : P.coeffList.Sublist (initialCoefficientList (N + 2) P.coeff).reverse :=
    polynomial_coeffList_sublist_padded P (N + 2) (mobiusPolynomial_natDegree_le ω (N + 2))
  have hpad : (initialCoefficientList (N + 2) P.coeff).reverse =
      P.coeff (N + 2) :: P.coeff (N + 1) :: low.reverse := by
    rw [initialCoefficientList_add_two, List.reverse_append]
    rfl
  rw [polynomial_signVariations_eq_list]
  calc
    listSignVariations P.coeffList ≤
        listSignVariations (initialCoefficientList (N + 2) P.coeff).reverse :=
      listSignVariations_sublist hsub
    _ = listSignVariations (P.coeff (N + 2) :: P.coeff (N + 1) :: low.reverse) := by
      rw [hpad]
    _ ≤ listSignVariations (P.coeff (N + 1) :: low.reverse) + 1 :=
      listSignVariations_cons_le _ _
    _ ≤ listSignVariations low.reverse + 2 := by
      have h := listSignVariations_cons_le (P.coeff (N + 1)) low.reverse
      omega
    _ = listSignVariations low + 2 := by rw [listSignVariations_reverse]
    _ ≤ listSignVariations (initialCoefficientList N (integratedRademacherSum ω)) + 2 := by
      have h := lowMobius_signVariations_le_integrated ω N
      simpa [P, low] using Nat.add_le_add_right h 2

lemma rightRootCount_le_open_count_add_one (ω : ℕ → Bool) (n : ℕ) :
    rightRootCount ω n ≤
      Set.ncard ((littlewoodPolynomial ω n).rootSet ℝ ∩ Set.Ioo (1 / 2 : ℝ) 1) + 1 := by
  rw [rightRootCount]
  let B := (littlewoodPolynomial ω n).rootSet ℝ ∩ Set.Ioo (1 / 2 : ℝ) 1
  have hsub :
      (littlewoodPolynomial ω n).rootSet ℝ ∩ Set.Ioc (1 / 2 : ℝ) 1 ⊆ insert 1 B := by
    rintro x ⟨hxroot, hxhalf, hxone⟩
    rcases lt_or_eq_of_le hxone with hxlt | rfl
    · exact Set.mem_insert_iff.mpr (Or.inr ⟨hxroot, hxhalf, hxlt⟩)
    · exact Set.mem_insert 1 B
  have hfinite : (insert 1 B).Finite :=
    (Polynomial.rootSet_finite (littlewoodPolynomial ω n) ℝ).inter_of_left _ |>.insert 1
  exact (Set.ncard_le_ncard hsub hfinite).trans (Set.ncard_insert_le 1 B)

lemma rightRootCount_le_integrated_variations_add_three (ω : ℕ → Bool) (N : ℕ) :
    rightRootCount ω (N + 2) ≤
      listSignVariations (initialCoefficientList N (integratedRademacherSum ω)) + 3 := by
  calc
    rightRootCount ω (N + 2) ≤
        Set.ncard ((littlewoodPolynomial ω (N + 2)).rootSet ℝ ∩
          Set.Ioo (1 / 2 : ℝ) 1) + 1 :=
      rightRootCount_le_open_count_add_one ω (N + 2)
    _ ≤ (mobiusPolynomial ω (N + 2)).signVariations + 1 := by
      exact Nat.add_le_add_right (ncard_roots_Ioo_half_one_le_signVariations ω (N + 2)) 1
    _ ≤ listSignVariations (initialCoefficientList N (integratedRademacherSum ω)) + 3 := by
      have h := mobius_signVariations_le_integrated_add_two ω N
      omega

end Erdos521
