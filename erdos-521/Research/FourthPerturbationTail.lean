import Research.FourthCoordinateReduction
import Research.AxisPairCoordinates
import Research.FourthLateCutoff
import Research.FiniteRademacherConcentration
import Mathlib.Tactic

open scoped BigOperators

namespace Erdos521

noncomputable local instance fourthPerturbationDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

def axisWordPairBitsEquiv (r : ℕ) :
    AxisWord r ≃ (Fin r × Fin 2 → Bool) :=
  (axisWordBitsEquiv r).trans
    (Equiv.piCongrLeft (fun _ : Fin (2 * r) ↦ Bool) (pairIndexEquiv r)).symm

@[simp] lemma axisWordPairBitsEquiv_apply {r : ℕ} (w : AxisWord r)
    (ij : Fin r × Fin 2) :
    axisWordPairBitsEquiv r w ij = axisWordBits w (pairIndexEquiv r ij) := rfl

noncomputable def fourthEvenPerturbationWeight (m : ℕ) : Fin (m + 1) × Fin 2 → ℝ :=
  fun ij ↦
    let b : ℝ := Nat.choose (2 * (m - ij.1.val) + 2) 2
    if ij.2 = 0 then -b / 2 else b / 2

noncomputable def fourthOddPerturbationWeight (m : ℕ) : Fin (m + 1) × Fin 2 → ℝ :=
  fun ij ↦
    let b : ℝ := Nat.choose (2 * (m - ij.1.val) + 3) 2
    if ij.2 = 0 then -b / 2 else b / 2

lemma finiteRademacherSum_evenPerturbation (m : ℕ) (w : AxisWord (m + 1)) :
    finiteRademacherRealSum (fourthEvenPerturbationWeight m)
      (axisWordPairBitsEquiv (m + 1) w) =
        fourthVerticalEven (axisWordCoefficients w) m := by
  unfold finiteRademacherRealSum fourthEvenPerturbationWeight fourthVerticalEven
  rw [Fintype.sum_prod_type]
  rw [← Fin.sum_univ_eq_sum_range
    (fun j : ℕ ↦ (Nat.choose (2 * (m - j) + 2) 2 : ℝ) *
      pairVertical (axisWordCoefficients w) j) (m + 1)]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Fin.sum_univ_two]
  norm_num
  have heven : axisWordPairBitsEquiv (m + 1) w (j, 0) =
      axisWordBits w ⟨2 * j.val, by omega⟩ := by
    simp [pairIndexEquiv, finProdFinEquiv]
  have hodd : axisWordPairBitsEquiv (m + 1) w (j, 1) =
      axisWordBits w ⟨2 * j.val + 1, by omega⟩ := by
    simp [pairIndexEquiv, finProdFinEquiv]
    congr 1
    apply Fin.ext
    simp [finProdFinEquiv]
    omega
  have hidx0 : pairIndexEquiv (m + 1) (j, 0) = ⟨2 * j.val, by omega⟩ := by
    apply Fin.ext
    simp [pairIndexEquiv, finProdFinEquiv]
  have hidx1 : pairIndexEquiv (m + 1) (j, 1) = ⟨2 * j.val + 1, by omega⟩ := by
    apply Fin.ext
    simp [pairIndexEquiv, finProdFinEquiv]
    omega
  rw [hidx0, hidx1, pairVertical]
  have hc0 : axisWordCoefficients w (2 * j.val) =
      axisWordBits w ⟨2 * j.val, by omega⟩ := extendBits_of_lt _ (by omega)
  have hc1 : axisWordCoefficients w (2 * j.val + 1) =
      axisWordBits w ⟨2 * j.val + 1, by omega⟩ := extendBits_of_lt _ (by omega)
  rw [hc0, hc1]
  ring

lemma finiteRademacherSum_oddPerturbation (m : ℕ) (w : AxisWord (m + 1)) :
    finiteRademacherRealSum (fourthOddPerturbationWeight m)
      (axisWordPairBitsEquiv (m + 1) w) =
        fourthVerticalOdd (axisWordCoefficients w) m := by
  unfold finiteRademacherRealSum fourthOddPerturbationWeight fourthVerticalOdd
  rw [Fintype.sum_prod_type]
  rw [← Fin.sum_univ_eq_sum_range
    (fun j : ℕ ↦ (Nat.choose (2 * (m - j) + 3) 2 : ℝ) *
      pairVertical (axisWordCoefficients w) j) (m + 1)]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Fin.sum_univ_two]
  norm_num
  have heven : axisWordPairBitsEquiv (m + 1) w (j, 0) =
      axisWordBits w ⟨2 * j.val, by omega⟩ := by
    simp [pairIndexEquiv, finProdFinEquiv]
  have hodd : axisWordPairBitsEquiv (m + 1) w (j, 1) =
      axisWordBits w ⟨2 * j.val + 1, by omega⟩ := by
    simp [pairIndexEquiv, finProdFinEquiv]
    congr 1
    apply Fin.ext
    simp [finProdFinEquiv]
    omega
  have hidx0 : pairIndexEquiv (m + 1) (j, 0) = ⟨2 * j.val, by omega⟩ := by
    apply Fin.ext
    simp [pairIndexEquiv, finProdFinEquiv]
  have hidx1 : pairIndexEquiv (m + 1) (j, 1) = ⟨2 * j.val + 1, by omega⟩ := by
    apply Fin.ext
    simp [pairIndexEquiv, finProdFinEquiv]
    omega
  rw [hidx0, hidx1, pairVertical]
  have hc0 : axisWordCoefficients w (2 * j.val) =
      axisWordBits w ⟨2 * j.val, by omega⟩ := extendBits_of_lt _ (by omega)
  have hc1 : axisWordCoefficients w (2 * j.val + 1) =
      axisWordBits w ⟨2 * j.val + 1, by omega⟩ := extendBits_of_lt _ (by omega)
  rw [hc0, hc1]
  ring

lemma fourthEvenPerturbationVariance_le (m : ℕ) :
    finiteRademacherVariance (fourthEvenPerturbationWeight m) ≤
      128 * (m + 1 : ℝ) ^ 5 := by
  unfold finiteRademacherVariance fourthEvenPerturbationWeight
  rw [Fintype.sum_prod_type]
  calc
    (∑ j : Fin (m + 1), ∑ q : Fin 2,
      (let b : ℝ := Nat.choose (2 * (m - j.val) + 2) 2
       if q = 0 then -b / 2 else b / 2) ^ 2) =
        ∑ j : Fin (m + 1),
          (Nat.choose (2 * (m - j.val) + 2) 2 : ℝ) ^ 2 / 2 := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [Fin.sum_univ_two]
      norm_num
      ring
    _ ≤ ∑ _j : Fin (m + 1), 128 * (m + 1 : ℝ) ^ 4 := by
      apply Finset.sum_le_sum
      intro j hj
      have hchoose := Nat.choose_le_pow (2 * (m - j.val) + 2) 2
      have harg : 2 * (m - j.val) + 2 ≤ 4 * (m + 1) := by omega
      have hpNat := hchoose.trans (Nat.pow_le_pow_left harg 2)
      have hp : (Nat.choose (2 * (m - j.val) + 2) 2 : ℝ) ≤
          (4 * (m + 1 : ℝ)) ^ 2 := by exact_mod_cast hpNat
      have hsquare := (sq_le_sq₀ (by positivity)
        (by positivity : 0 ≤ (4 * (m + 1 : ℝ)) ^ 2)).2 hp
      nlinarith
    _ = 128 * (m + 1 : ℝ) ^ 5 := by
      simp
      ring

lemma fourthOddPerturbationVariance_le (m : ℕ) :
    finiteRademacherVariance (fourthOddPerturbationWeight m) ≤
      128 * (m + 2 : ℝ) ^ 5 := by
  unfold finiteRademacherVariance fourthOddPerturbationWeight
  rw [Fintype.sum_prod_type]
  calc
    (∑ j : Fin (m + 1), ∑ q : Fin 2,
      (let b : ℝ := Nat.choose (2 * (m - j.val) + 3) 2
       if q = 0 then -b / 2 else b / 2) ^ 2) =
        ∑ j : Fin (m + 1),
          (Nat.choose (2 * (m - j.val) + 3) 2 : ℝ) ^ 2 / 2 := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [Fin.sum_univ_two]
      norm_num
      ring
    _ ≤ ∑ _j : Fin (m + 1), 128 * (m + 2 : ℝ) ^ 4 := by
      apply Finset.sum_le_sum
      intro j hj
      have hchoose := Nat.choose_le_pow (2 * (m - j.val) + 3) 2
      have harg : 2 * (m - j.val) + 3 ≤ 4 * (m + 2) := by omega
      have hpNat := hchoose.trans (Nat.pow_le_pow_left harg 2)
      have hp : (Nat.choose (2 * (m - j.val) + 3) 2 : ℝ) ≤
          (4 * (m + 2 : ℝ)) ^ 2 := by exact_mod_cast hpNat
      have hsquare := (sq_le_sq₀ (by positivity)
        (by positivity : 0 ≤ (4 * (m + 2 : ℝ)) ^ 2)).2 hp
      nlinarith
    _ ≤ 128 * (m + 2 : ℝ) ^ 5 := by
      simp
      have hm : (m + 1 : ℝ) ≤ m + 2 := by norm_num
      nlinarith [mul_le_mul_of_nonneg_right hm (by positivity : 0 ≤ 128 * (m + 2 : ℝ) ^ 4)]

noncomputable def fourthEvenPerturbationWords (m : ℕ) (T : ℝ) :
    Finset (AxisWord (m + 1)) :=
  Finset.univ.filter fun w ↦ T ≤ |fourthVerticalEven (axisWordCoefficients w) m|

noncomputable def fourthOddPerturbationWords (m : ℕ) (T : ℝ) :
    Finset (AxisWord (m + 1)) :=
  Finset.univ.filter fun w ↦ T ≤ |fourthVerticalOdd (axisWordCoefficients w) m|

lemma fourthEvenPerturbationWords_density_eq (m : ℕ) (T : ℝ) :
    ((fourthEvenPerturbationWords m T).card : ℝ) / (4 : ℝ) ^ (m + 1) =
      finiteRademacherAbsTailProbability (fourthEvenPerturbationWeight m) T := by
  unfold fourthEvenPerturbationWords finiteRademacherAbsTailProbability
  rw [Finset.card_filter]
  push_cast
  rw [show (∑ w : AxisWord (m + 1),
      if T ≤ |fourthVerticalEven (axisWordCoefficients w) m| then (1 : ℝ) else 0) =
      ∑ e : Fin (m + 1) × Fin 2 → Bool,
        if T ≤ |finiteRademacherRealSum (fourthEvenPerturbationWeight m) e| then 1 else 0 by
    apply Fintype.sum_equiv (axisWordPairBitsEquiv (m + 1))
    intro w
    rw [finiteRademacherSum_evenPerturbation]]
  congr 1
  · apply Finset.sum_congr (by ext e; simp)
    intro e he
    rfl
  · simp only [Fintype.card_prod, Fintype.card_fin]
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul]
    congr 1
    omega

lemma fourthOddPerturbationWords_density_eq (m : ℕ) (T : ℝ) :
    ((fourthOddPerturbationWords m T).card : ℝ) / (4 : ℝ) ^ (m + 1) =
      finiteRademacherAbsTailProbability (fourthOddPerturbationWeight m) T := by
  unfold fourthOddPerturbationWords finiteRademacherAbsTailProbability
  rw [Finset.card_filter]
  push_cast
  rw [show (∑ w : AxisWord (m + 1),
      if T ≤ |fourthVerticalOdd (axisWordCoefficients w) m| then (1 : ℝ) else 0) =
      ∑ e : Fin (m + 1) × Fin 2 → Bool,
        if T ≤ |finiteRademacherRealSum (fourthOddPerturbationWeight m) e| then 1 else 0 by
    apply Fintype.sum_equiv (axisWordPairBitsEquiv (m + 1))
    intro w
    rw [finiteRademacherSum_oddPerturbation]]
  congr 1
  · apply Finset.sum_congr (by ext e; simp)
    intro e he
    rfl
  · simp only [Fintype.card_prod, Fintype.card_fin]
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul]
    congr 1
    omega

end Erdos521
