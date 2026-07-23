import Research.FourthCharacteristicTaylor
import Mathlib.Tactic

open scoped BigOperators

namespace Erdos521

/-- A weighted telescoping inequality for finite products.  Each single-factor error is
multiplied by the majorants for all of the other factors. -/
lemma abs_prod_sub_prod_le_weighted {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (a b w : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i)
    (ha : ∀ i ∈ s, |a i| ≤ w i)
    (hb : ∀ i ∈ s, |b i| ≤ w i) :
    |(∏ i ∈ s, a i) - ∏ i ∈ s, b i| ≤
      ∑ i ∈ s, |a i - b i| * ∏ j ∈ s.erase i, w j := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      have hwi := hw i (Finset.mem_insert_self i s)
      have hai := ha i (Finset.mem_insert_self i s)
      have hbi := hb i (Finset.mem_insert_self i s)
      have hwS : ∀ j ∈ s, 0 ≤ w j := fun j hj ↦ hw j (Finset.mem_insert_of_mem hj)
      have haS : ∀ j ∈ s, |a j| ≤ w j := fun j hj ↦ ha j (Finset.mem_insert_of_mem hj)
      have hbS : ∀ j ∈ s, |b j| ≤ w j := fun j hj ↦ hb j (Finset.mem_insert_of_mem hj)
      have hprodW : 0 ≤ ∏ j ∈ s, w j := Finset.prod_nonneg hwS
      have hprodB : |∏ j ∈ s, b j| ≤ ∏ j ∈ s, w j := by
        rw [Finset.abs_prod]
        exact Finset.prod_le_prod (fun _ _ ↦ abs_nonneg _) hbS
      rw [Finset.prod_insert hi, Finset.prod_insert hi, Finset.sum_insert hi]
      calc
        |a i * (∏ j ∈ s, a j) - b i * ∏ j ∈ s, b j| =
            |a i * ((∏ j ∈ s, a j) - ∏ j ∈ s, b j) +
              (a i - b i) * ∏ j ∈ s, b j| := by congr 1 <;> ring
        _ ≤ |a i| * |(∏ j ∈ s, a j) - ∏ j ∈ s, b j| +
            |a i - b i| * |∏ j ∈ s, b j| := by
          rw [← abs_mul, ← abs_mul]
          exact abs_add_le _ _
        _ ≤ w i * (∑ j ∈ s, |a j - b j| * ∏ l ∈ s.erase j, w l) +
            |a i - b i| * ∏ j ∈ s, w j := by
          apply add_le_add
          · exact mul_le_mul hai (ih hwS haS hbS) (abs_nonneg _) hwi
          · exact mul_le_mul_of_nonneg_left hprodB (abs_nonneg _)
        _ = |a i - b i| * ∏ j ∈ s, w j +
            ∑ j ∈ s, |a j - b j| *
              ∏ l ∈ (insert i s).erase j, w l := by
          rw [Finset.mul_sum]
          conv_lhs => rw [add_comm]
          apply congrArg (fun z : ℝ ↦ |a i - b i| * ∏ j ∈ s, w j + z)
          apply Finset.sum_congr rfl
          intro j hj
          have hji : j ≠ i := by
            intro h
            subst h
            exact hi hj
          rw [Finset.erase_insert_of_ne (Ne.symm hji), Finset.prod_insert]
          · ring
          · simp [hi]
        _ = |a i - b i| * ∏ j ∈ (insert i s).erase i, w j +
            ∑ j ∈ s, |a j - b j| *
              ∏ l ∈ (insert i s).erase j, w l := by simp [hi]

/-- When no phase carries more than half of the total square mass, the fourth-order
cosine/Gaussian product error retains a Gaussian factor from all the other phases. -/
lemma abs_cos_prod_sub_gaussian_prod_damped {ι : Type*} [Fintype ι]
    (x : ι → ℝ) (hx : ∀ i, |x i| ≤ 1)
    (hhalf : ∀ i, x i ^ 2 ≤ (1 / 2 : ℝ) * ∑ j, x j ^ 2) :
    |(∏ i, Real.cos (x i)) - ∏ i, Real.exp (-(x i ^ 2) / 2)| ≤
      ((1 / 4 : ℝ) * ∑ i, x i ^ 4) *
        Real.exp (-(1 / Real.pi ^ 2) * ∑ i, x i ^ 2) := by
  classical
  let c : ℝ := 2 / Real.pi ^ 2
  let w : ι → ℝ := fun i ↦ Real.exp (-c * x i ^ 2)
  have hc0 : 0 ≤ c := by dsimp [c]; positivity
  have hcHalf : c ≤ 1 / 2 := by
    dsimp [c]
    have hp : 0 < Real.pi ^ 2 := sq_pos_of_pos Real.pi_pos
    apply (div_le_iff₀ hp).2
    nlinarith [Real.pi_gt_three, sq_nonneg (Real.pi - 2)]
  have hw (i : ι) : 0 ≤ w i := (Real.exp_pos _).le
  have hcos (i : ι) : |Real.cos (x i)| ≤ w i := by
    dsimp [w, c]
    exact abs_cos_le_exp_neg_sq (hx i)
  have hgauss (i : ι) : |Real.exp (-(x i ^ 2) / 2)| ≤ w i := by
    rw [abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr
    have hsq : 0 ≤ x i ^ 2 := sq_nonneg _
    nlinarith
  have htel := abs_prod_sub_prod_le_weighted Finset.univ
    (fun i ↦ Real.cos (x i)) (fun i ↦ Real.exp (-(x i ^ 2) / 2)) w
    (fun i _ ↦ hw i) (fun i _ ↦ hcos i) (fun i _ ↦ hgauss i)
  calc
    |(∏ i, Real.cos (x i)) - ∏ i, Real.exp (-(x i ^ 2) / 2)| ≤
        ∑ i, |Real.cos (x i) - Real.exp (-(x i ^ 2) / 2)| *
          ∏ j ∈ Finset.univ.erase i, w j := htel
    _ ≤ ∑ i, (x i ^ 4 / 4) *
        Real.exp (-(1 / Real.pi ^ 2) * ∑ j, x j ^ 2) := by
      apply Finset.sum_le_sum
      intro i hi
      have herr := abs_cos_sub_gaussian_le (hx i)
      have hsumErase : (∑ j ∈ Finset.univ.erase i, x j ^ 2) =
          (∑ j, x j ^ 2) - x i ^ 2 := by
        have h := Finset.sum_erase_add (s := Finset.univ)
          (f := fun j ↦ x j ^ 2) (Finset.mem_univ i)
        linarith
      have hremain : (1 / 2 : ℝ) * (∑ j, x j ^ 2) ≤
          ∑ j ∈ Finset.univ.erase i, x j ^ 2 := by
        rw [hsumErase]
        linarith [hhalf i]
      have hprodEq : (∏ j ∈ Finset.univ.erase i, w j) =
          Real.exp (-c * ∑ j ∈ Finset.univ.erase i, x j ^ 2) := by
        dsimp [w]
        rw [← Real.exp_sum]
        congr 1
        rw [Finset.mul_sum]
      have hprod : (∏ j ∈ Finset.univ.erase i, w j) ≤
          Real.exp (-(1 / Real.pi ^ 2) * ∑ j, x j ^ 2) := by
        rw [hprodEq]
        apply Real.exp_le_exp.mpr
        dsimp [c]
        calc
          -(2 / Real.pi ^ 2) * (∑ j ∈ Finset.univ.erase i, x j ^ 2) ≤
              -(2 / Real.pi ^ 2) * ((1 / 2 : ℝ) * ∑ j, x j ^ 2) :=
            mul_le_mul_of_nonpos_left hremain (neg_nonpos.mpr (by positivity))
          _ = -(1 / Real.pi ^ 2) * ∑ j, x j ^ 2 := by ring
      exact mul_le_mul herr hprod (Finset.prod_nonneg fun j hj ↦ hw j)
        (by positivity)
    _ = ((1 / 4 : ℝ) * ∑ i, x i ^ 4) *
        Real.exp (-(1 / Real.pi ^ 2) * ∑ i, x i ^ 2) := by
      rw [← Finset.sum_mul]
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring

/-- The full whitened fourth-array characteristic product has an integrable `O(1/k)`
Taylor remainder throughout the expanding central Fourier ball. -/
lemma fourthCharacteristicProduct_damped_taylor (k : ℕ) (hk : 23 ≤ k) (s t : ℝ)
    (hst : (s ^ 2 + t ^ 2) * (12 / (k + 1 : ℝ)) ≤ 1) :
    |Real.cos (t * fourthWhitenedNewY k) *
        (∏ q : Fin (k + 1),
          Real.cos (s * fourthWhitenedX k q + t * fourthWhitenedY k q)) -
      Real.exp (-(s ^ 2 + t ^ 2) / 2)| ≤
        ((3 / (k + 1 : ℝ)) * (s ^ 2 + t ^ 2) ^ 2) *
          Real.exp (-(1 / Real.pi ^ 2) * (s ^ 2 + t ^ 2)) := by
  have hkR : (24 : ℝ) ≤ (k + 1 : ℝ) := by exact_mod_cast (show 24 ≤ k + 1 by omega)
  have hkpos : (0 : ℝ) < (k + 1 : ℝ) := by positivity
  have hcoef : 12 / (k + 1 : ℝ) ≤ (1 / 2 : ℝ) := by
    apply (div_le_iff₀ hkpos).2
    nlinarith
  have hhalf (i : Option (Fin (k + 1))) :
      fourthPhase k s t i ^ 2 ≤
        (1 / 2 : ℝ) * ∑ j : Option (Fin (k + 1)), fourthPhase k s t j ^ 2 := by
    rw [fourthPhase_fintype_sq_sum]
    calc
      fourthPhase k s t i ^ 2 ≤
          (s ^ 2 + t ^ 2) * (12 / (k + 1 : ℝ)) :=
        fourthPhase_sq_le k s t i
      _ ≤ (s ^ 2 + t ^ 2) * (1 / 2 : ℝ) :=
        mul_le_mul_of_nonneg_left hcoef (by positivity)
      _ = (1 / 2 : ℝ) * (s ^ 2 + t ^ 2) := by ring
  have hgeneric := abs_cos_prod_sub_gaussian_prod_damped
    (fourthPhase k s t) (fourthPhase_abs_le_one k s t hst) hhalf
  have hcos : (∏ i : Option (Fin (k + 1)), Real.cos (fourthPhase k s t i)) =
      Real.cos (t * fourthWhitenedNewY k) *
        ∏ q : Fin (k + 1),
          Real.cos (s * fourthWhitenedX k q + t * fourthWhitenedY k q) := by
    rw [Fintype.prod_option]
    rfl
  have hgauss : (∏ i : Option (Fin (k + 1)),
      Real.exp (-(fourthPhase k s t i ^ 2) / 2)) =
      Real.exp (-(s ^ 2 + t ^ 2) / 2) := by
    rw [← Real.exp_sum]
    congr 1
    calc
      (∑ i : Option (Fin (k + 1)), -(fourthPhase k s t i ^ 2) / 2) =
          (-1 / 2 : ℝ) *
            ∑ i : Option (Fin (k + 1)), fourthPhase k s t i ^ 2 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = -(s ^ 2 + t ^ 2) / 2 := by
        rw [fourthPhase_fintype_sq_sum]
        ring
  rw [hcos, hgauss, fourthPhase_fintype_sq_sum] at hgeneric
  calc
    _ ≤ ((1 / 4 : ℝ) *
        ∑ i : Option (Fin (k + 1)), fourthPhase k s t i ^ 4) *
          Real.exp (-(1 / Real.pi ^ 2) * (s ^ 2 + t ^ 2)) := hgeneric
    _ ≤ ((3 / (k + 1 : ℝ)) * (s ^ 2 + t ^ 2) ^ 2) *
          Real.exp (-(1 / Real.pi ^ 2) * (s ^ 2 + t ^ 2)) := by
      apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
      calc
        (1 / 4 : ℝ) *
            ∑ i : Option (Fin (k + 1)), fourthPhase k s t i ^ 4 ≤
          (1 / 4 : ℝ) *
            ((12 / (k + 1 : ℝ)) * (s ^ 2 + t ^ 2) ^ 2) := by
              gcongr
              exact fourthPhase_fourth_sum_le k s t
        _ = (3 / (k + 1 : ℝ)) * (s ^ 2 + t ^ 2) ^ 2 := by ring

end Erdos521
