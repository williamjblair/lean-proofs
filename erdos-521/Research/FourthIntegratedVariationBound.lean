import Research.FourthIntegratedCoefficients
import Research.ThirdIntegratedVariationBound
import Mathlib.Tactic

namespace Erdos521

noncomputable local instance fourthVariationDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

noncomputable def scaledFourthIntegratedSum (ω : ℕ → Bool) (N r : ℕ) : ℝ :=
  fourthIntegratedRademacherSum ω r / (Nat.choose N r : ℝ)

noncomputable def ordinaryFourthIntegratedPascal (ω : ℕ → Bool) (N j : ℕ) : ℝ :=
  ∑ r ∈ Finset.range (j + 1),
    (Nat.choose j r : ℝ) * scaledFourthIntegratedSum ω N r

lemma ordinaryPascalTransform_scaledFourthIntegrated (ω : ℕ → Bool) (N : ℕ) :
    ordinaryPascalTransform N (scaledFourthIntegratedSum ω N) =
      initialCoefficientList N (ordinaryFourthIntegratedPascal ω N) := by
  rfl

lemma mobius_coeff_eq_choose_mul_ordinaryFourthIntegratedPascal
    (ω : ℕ → Bool) (N j : ℕ) (hjN : j ≤ N) :
    (mobiusPolynomial ω (N + 4)).coeff j =
      (Nat.choose N j : ℝ) * ordinaryFourthIntegratedPascal ω N j := by
  rw [mobiusPolynomial_coeff_eq_fourthIntegrated]
  · simp only [ordinaryFourthIntegratedPascal, scaledFourthIntegratedSum]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r hr
    have hrj : r ≤ j := by have := Finset.mem_range.mp hr; omega
    rw [show N + 4 - 4 - r = N - r by omega]
    rw [choose_ratio_identity N j r hrj hjN]
    have hne : (Nat.choose N r : ℝ) ≠ 0 := by
      exact_mod_cast Nat.choose_ne_zero (hrj.trans hjN)
    field_simp
  · omega

lemma lowMobius_signVariations_le_fourthIntegrated (ω : ℕ → Bool) (N : ℕ) :
    listSignVariations
        (initialCoefficientList N (fun j ↦ (mobiusPolynomial ω (N + 4)).coeff j)) ≤
      listSignVariations (initialCoefficientList N (fourthIntegratedRademacherSum ω)) := by
  calc
    listSignVariations
        (initialCoefficientList N (fun j ↦ (mobiusPolynomial ω (N + 4)).coeff j)) =
        listSignVariations (initialCoefficientList N (ordinaryFourthIntegratedPascal ω N)) := by
      apply listSignVariations_initial_eq_of_sign_eq
      intro j hj
      rw [mobius_coeff_eq_choose_mul_ordinaryFourthIntegratedPascal ω N j hj]
      rw [sign_mul, sign_pos (by exact_mod_cast Nat.choose_pos hj)]
      simp
    _ = listSignVariations (ordinaryPascalTransform N (scaledFourthIntegratedSum ω N)) := by
      rw [ordinaryPascalTransform_scaledFourthIntegrated]
    _ ≤ listSignVariations (initialCoefficientList N (scaledFourthIntegratedSum ω N)) :=
      listSignVariations_ordinaryPascalTransform_le N _
    _ = listSignVariations
        (initialCoefficientList N (fourthIntegratedRademacherSum ω)) := by
      apply listSignVariations_initial_eq_of_sign_eq
      intro r hr
      have hc : 0 < (Nat.choose N r : ℝ) := by exact_mod_cast Nat.choose_pos hr
      rw [scaledFourthIntegratedSum, div_eq_mul_inv, sign_mul, sign_pos (inv_pos.mpr hc)]
      simp

lemma initialCoefficientList_add_four (N : ℕ) (a : ℕ → ℝ) :
    initialCoefficientList (N + 4) a =
      initialCoefficientList N a ++ [a (N + 1), a (N + 2), a (N + 3), a (N + 4)] := by
  rw [initialCoefficientList_eq_range_map, initialCoefficientList_eq_range_map]
  rw [show N + 4 + 1 = (N + 1).succ.succ.succ.succ by omega,
    List.range_succ, List.range_succ, List.range_succ, List.range_succ,
    List.map_append, List.map_append, List.map_append, List.map_append]
  simp

lemma mobius_signVariations_le_fourthIntegrated_add_four (ω : ℕ → Bool) (N : ℕ) :
    (mobiusPolynomial ω (N + 4)).signVariations ≤
      listSignVariations (initialCoefficientList N (fourthIntegratedRademacherSum ω)) + 4 := by
  let P := mobiusPolynomial ω (N + 4)
  let low := initialCoefficientList N (fun j ↦ P.coeff j)
  have hsub : P.coeffList.Sublist (initialCoefficientList (N + 4) P.coeff).reverse :=
    polynomial_coeffList_sublist_padded P (N + 4) (mobiusPolynomial_natDegree_le ω (N + 4))
  have hpad : (initialCoefficientList (N + 4) P.coeff).reverse =
      P.coeff (N + 4) :: P.coeff (N + 3) :: P.coeff (N + 2) ::
        P.coeff (N + 1) :: low.reverse := by
    rw [initialCoefficientList_add_four, List.reverse_append]
    rfl
  rw [polynomial_signVariations_eq_list]
  calc
    listSignVariations P.coeffList ≤
        listSignVariations (initialCoefficientList (N + 4) P.coeff).reverse :=
      listSignVariations_sublist hsub
    _ = listSignVariations (P.coeff (N + 4) :: P.coeff (N + 3) ::
        P.coeff (N + 2) :: P.coeff (N + 1) :: low.reverse) := by rw [hpad]
    _ ≤ listSignVariations (P.coeff (N + 3) :: P.coeff (N + 2) ::
        P.coeff (N + 1) :: low.reverse) + 1 := listSignVariations_cons_le _ _
    _ ≤ listSignVariations (P.coeff (N + 2) :: P.coeff (N + 1) :: low.reverse) + 2 := by
      have h := listSignVariations_cons_le (P.coeff (N + 3))
        (P.coeff (N + 2) :: P.coeff (N + 1) :: low.reverse)
      omega
    _ ≤ listSignVariations (P.coeff (N + 1) :: low.reverse) + 3 := by
      have h := listSignVariations_cons_le (P.coeff (N + 2))
        (P.coeff (N + 1) :: low.reverse)
      omega
    _ ≤ listSignVariations low.reverse + 4 := by
      have h := listSignVariations_cons_le (P.coeff (N + 1)) low.reverse
      omega
    _ = listSignVariations low + 4 := by rw [listSignVariations_reverse]
    _ ≤ listSignVariations
        (initialCoefficientList N (fourthIntegratedRademacherSum ω)) + 4 := by
      have h := lowMobius_signVariations_le_fourthIntegrated ω N
      simpa [P, low] using Nat.add_le_add_right h 4

lemma rightRootCount_le_fourthIntegrated_variations_add_five (ω : ℕ → Bool) (N : ℕ) :
    rightRootCount ω (N + 4) ≤
      listSignVariations (initialCoefficientList N (fourthIntegratedRademacherSum ω)) + 5 := by
  calc
    rightRootCount ω (N + 4) ≤
        Set.ncard ((littlewoodPolynomial ω (N + 4)).rootSet ℝ ∩
          Set.Ioo (1 / 2 : ℝ) 1) + 1 := rightRootCount_le_open_count_add_one ω (N + 4)
    _ ≤ (mobiusPolynomial ω (N + 4)).signVariations + 1 := by
      exact Nat.add_le_add_right (ncard_roots_Ioo_half_one_le_signVariations ω (N + 4)) 1
    _ ≤ listSignVariations
        (initialCoefficientList N (fourthIntegratedRademacherSum ω)) + 5 := by
      have h := mobius_signVariations_le_fourthIntegrated_add_four ω N
      omega

end Erdos521
