import Research.FourthIntegratedCrossings
import Research.RademacherBallot
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic

open scoped BigOperators

namespace Erdos521

noncomputable local instance fourthPairDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

lemma sum_Icc_sub_eq_sum_range (f : ℕ → ℕ) (i k : ℕ) (hik : i ≤ k) :
    (∑ x ∈ Finset.Icc i k, f (x - i)) =
      ∑ j ∈ Finset.range (k - i + 1), f j := by
  symm
  apply Finset.sum_bij (fun j hj ↦ i + j)
  · intro j hj
    simp only [Finset.mem_Icc]
    have hj' := Finset.mem_range.mp hj
    omega
  · intro a ha b hb hab
    omega
  · intro x hx
    have hx' := Finset.mem_Icc.mp hx
    refine ⟨x - i, Finset.mem_range.mpr (by omega), ?_⟩
    omega
  · intro j hj
    rw [Nat.add_sub_cancel_left]

lemma thirdIntegratedRademacherSum_eq_weighted_choose (ω : ℕ → Bool) (k : ℕ) :
    thirdIntegratedRademacherSum ω k =
      ∑ i ∈ Finset.range (k + 1),
        (Nat.choose (k - i + 2) 2 : ℝ) * sign (ω i) := by
  unfold thirdIntegratedRademacherSum
  simp_rw [integratedRademacherSum_eq_weighted]
  rw [sum_range_triangle_swap]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← Finset.sum_mul]
  congr 1
  have hik : i ≤ k := by have := Finset.mem_range.mp hi; omega
  have hnat : (∑ x ∈ Finset.Icc i k, (x - i + 1 : ℕ)) =
      Nat.choose (k - i + 2) 2 := by
    rw [sum_Icc_sub_eq_sum_range (fun d ↦ d + 1) i k hik]
    induction k - i with
    | zero => simp
    | succ d ih =>
      rw [Finset.sum_range_succ, ih]
      rw [show Nat.choose (d + 1 + 2) 2 =
          Nat.choose (d + 2) 2 + (d + 2) by
        rw [show d + 1 + 2 = (d + 2) + 1 by omega, Nat.choose_succ_succ']
        simp
        omega]
  exact_mod_cast hnat

lemma fourthIntegratedRademacherSum_eq_weighted_choose (ω : ℕ → Bool) (k : ℕ) :
    fourthIntegratedRademacherSum ω k =
      ∑ i ∈ Finset.range (k + 1),
        (Nat.choose (k - i + 3) 3 : ℝ) * sign (ω i) := by
  unfold fourthIntegratedRademacherSum
  simp_rw [thirdIntegratedRademacherSum_eq_weighted_choose]
  rw [sum_range_triangle_swap]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← Finset.sum_mul]
  congr 1
  have hik : i ≤ k := by have := Finset.mem_range.mp hi; omega
  have hnat : (∑ x ∈ Finset.Icc i k, Nat.choose (x - i + 2) 2) =
      Nat.choose (k - i + 3) 3 := by
    rw [sum_Icc_sub_eq_sum_range (fun d ↦ Nat.choose (d + 2) 2) i k hik]
    simpa [add_comm, add_left_comm, add_assoc] using
      Nat.sum_range_add_choose (k - i) 2
  exact_mod_cast hnat

lemma sum_range_two_mul {α : Type*} [AddCommMonoid α] (f : ℕ → α) (m : ℕ) :
    (∑ i ∈ Finset.range (2 * m), f i) =
      ∑ j ∈ Finset.range m, (f (2 * j) + f (2 * j + 1)) := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [show 2 * (m + 1) = (2 * m + 1) + 1 by omega,
        Finset.sum_range_succ, Finset.sum_range_succ, ih,
        Finset.sum_range_succ]
      abel

lemma sum_range_two_mul_add_one {α : Type*} [AddCommMonoid α] (f : ℕ → α) (m : ℕ) :
    (∑ i ∈ Finset.range (2 * m + 1), f i) =
      (∑ j ∈ Finset.range m, (f (2 * j) + f (2 * j + 1))) + f (2 * m) := by
  rw [Finset.sum_range_succ, sum_range_two_mul]

/-- Pair coordinates: exactly one of these two values is nonzero for Boolean signs. -/
noncomputable def pairHorizontal (ω : ℕ → Bool) (j : ℕ) : ℝ :=
  (sign (ω (2 * j)) + sign (ω (2 * j + 1))) / 2

noncomputable def pairVertical (ω : ℕ → Bool) (j : ℕ) : ℝ :=
  (sign (ω (2 * j + 1)) - sign (ω (2 * j))) / 2

lemma sign_even_eq_pair (ω : ℕ → Bool) (j : ℕ) :
    sign (ω (2 * j)) = pairHorizontal ω j - pairVertical ω j := by
  simp [pairHorizontal, pairVertical]
  ring

lemma sign_odd_eq_pair (ω : ℕ → Bool) (j : ℕ) :
    sign (ω (2 * j + 1)) = pairHorizontal ω j + pairVertical ω j := by
  simp [pairHorizontal, pairVertical]
  ring

lemma choose_three_succ_difference (q : ℕ) :
    (Nat.choose (q + 1) 3 : ℝ) = Nat.choose q 3 + Nat.choose q 2 := by
  rw [show 3 = 2 + 1 by omega, Nat.choose_succ_succ']
  push_cast
  ring

/-- At odd coefficient times the fourth sum is a cubic horizontal form plus a quadratic vertical
perturbation. -/
lemma fourthIntegratedRademacherSum_odd_pair (ω : ℕ → Bool) (m : ℕ) :
    fourthIntegratedRademacherSum ω (2 * m + 1) =
      ∑ j ∈ Finset.range (m + 1),
        (((Nat.choose (2 * (m - j) + 4) 3 +
            Nat.choose (2 * (m - j) + 3) 3 : ℕ) : ℝ) * pairHorizontal ω j -
          (Nat.choose (2 * (m - j) + 3) 2 : ℝ) * pairVertical ω j) := by
  rw [fourthIntegratedRademacherSum_eq_weighted_choose]
  rw [show 2 * m + 1 + 1 = 2 * (m + 1) by omega,
    sum_range_two_mul]
  apply Finset.sum_congr rfl
  intro j hj
  have hjm : j ≤ m := by have := Finset.mem_range.mp hj; omega
  rw [show 2 * m + 1 - 2 * j + 3 = 2 * (m - j) + 4 by omega,
    show 2 * m + 1 - (2 * j + 1) + 3 = 2 * (m - j) + 3 by omega,
    sign_even_eq_pair, sign_odd_eq_pair]
  have hd : (Nat.choose (2 * (m - j) + 4) 3 : ℝ) =
      Nat.choose (2 * (m - j) + 3) 3 + Nat.choose (2 * (m - j) + 3) 2 := by
    simpa only [show 2 * (m - j) + 3 + 1 = 2 * (m - j) + 4 by omega] using
      choose_three_succ_difference (2 * (m - j) + 3)
  push_cast
  rw [hd]
  ring

/-- At even coefficient times the same decomposition holds, with the adjacent Pascal weights. -/
lemma fourthIntegratedRademacherSum_even_pair (ω : ℕ → Bool) (m : ℕ) :
    fourthIntegratedRademacherSum ω (2 * m) =
      ∑ j ∈ Finset.range (m + 1),
        (((Nat.choose (2 * (m - j) + 3) 3 +
            Nat.choose (2 * (m - j) + 2) 3 : ℕ) : ℝ) * pairHorizontal ω j -
          (Nat.choose (2 * (m - j) + 2) 2 : ℝ) * pairVertical ω j) := by
  rw [fourthIntegratedRademacherSum_eq_weighted_choose]
  rw [sum_range_two_mul_add_one]
  rw [Finset.sum_range_succ]
  congr 1
  · apply Finset.sum_congr rfl
    intro j hj
    have hjm : j < m := Finset.mem_range.mp hj
    rw [show 2 * m - 2 * j + 3 = 2 * (m - j) + 3 by omega,
      show 2 * m - (2 * j + 1) + 3 = 2 * (m - j) + 2 by omega,
      sign_even_eq_pair, sign_odd_eq_pair]
    have hd : (Nat.choose (2 * (m - j) + 3) 3 : ℝ) =
        Nat.choose (2 * (m - j) + 2) 3 + Nat.choose (2 * (m - j) + 2) 2 := by
      simpa only [show 2 * (m - j) + 2 + 1 = 2 * (m - j) + 3 by omega] using
        choose_three_succ_difference (2 * (m - j) + 2)
    push_cast
    rw [hd]
    ring
  · norm_num
    exact sign_even_eq_pair ω m

end Erdos521
