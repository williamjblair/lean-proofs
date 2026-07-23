import Research.FourthFourierIntegralBounds
import Research.RademacherCharacteristic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic

open scoped BigOperators Matrix ComplexConjugate Interval
open MeasureTheory

namespace Erdos521

noncomputable def boolSignInt (b : Bool) : ℤ := if b then 1 else -1

@[simp] lemma boolSignInt_true : boolSignInt true = 1 := by simp [boolSignInt]
@[simp] lemma boolSignInt_false : boolSignInt false = -1 := by simp [boolSignInt]

lemma intCast_boolSignInt (b : Bool) : (boolSignInt b : ℝ) = sign b := by
  cases b <;> simp [boolSignInt, sign]

lemma integral_Icc_cexp_even_character (m : ℤ) :
    (∫ t : ℝ in Set.Icc (-Real.pi / 2) (Real.pi / 2),
      Complex.exp (Complex.I * (((2 * m : ℤ) : ℝ) * t))) =
        if m = 0 then Real.pi else 0 := by
  by_cases hm : m = 0
  · subst m
    norm_num
    rw [max_eq_left]
    · ring
    · linarith [Real.pi_pos]
  · have hle : -Real.pi / 2 ≤ Real.pi / 2 := by linarith [Real.pi_pos]
    rw [if_neg hm, integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le hle]
    let c : ℂ := Complex.I * ((2 * m : ℤ) : ℝ)
    have hc : c ≠ 0 := by
      dsimp [c]
      exact mul_ne_zero Complex.I_ne_zero (by exact_mod_cast (mul_ne_zero (by norm_num : (2 : ℤ) ≠ 0) hm))
    have hfun (t : ℝ) :
        Complex.exp (Complex.I * (((2 * m : ℤ) : ℝ) * t)) = Complex.exp (c * t) := by
      dsimp [c]
      push_cast
      congr 1
      ring
    simp_rw [hfun]
    rw [integral_exp_mul_complex hc]
    have hplus : c * (Real.pi / 2 : ℝ) = (((m : ℝ) * Real.pi : ℝ) : ℂ) * Complex.I := by
      dsimp [c]
      push_cast
      ring
    have hminus : c * (-Real.pi / 2 : ℝ) = ((-(m : ℝ) * Real.pi : ℝ) : ℂ) * Complex.I := by
      dsimp [c]
      push_cast
      ring
    have hexpeq : Complex.exp (c * (Real.pi / 2 : ℝ)) =
        Complex.exp (c * (-Real.pi / 2 : ℝ)) := by
      rw [hplus, hminus]
      have hp : (((m : ℝ) * Real.pi : ℝ) : ℂ) * Complex.I =
          (m : ℂ) * ((Real.pi : ℂ) * Complex.I) := by push_cast; ring
      have hn : ((-(m : ℝ) * Real.pi : ℝ) : ℂ) * Complex.I =
          (-m : ℂ) * ((Real.pi : ℂ) * Complex.I) := by push_cast; ring
      rw [hp, hn]
      rw [show (m : ℂ) = (m : ℤ) by rfl,
        show (-m : ℂ) = (-m : ℤ) by norm_cast,
        Complex.exp_int_mul, Complex.exp_int_mul, Complex.exp_pi_mul_I]
      rw [zpow_neg, ← inv_zpow]
      simp
    rw [hexpeq, sub_self, zero_div]
    norm_num

noncomputable def boolNegativeIndicator (b : Bool) : ℤ := if b then 0 else 1

lemma boolSignInt_eq_one_sub_two_indicator (b : Bool) :
    boolSignInt b = 1 - 2 * boolNegativeIndicator b := by
  cases b <;> simp [boolSignInt, boolNegativeIndicator]

noncomputable def signedIntVectorSum {ι : Type*} [Fintype ι]
    (v : ι → Fin 2 → ℤ) (e : ι → Bool) : Fin 2 → ℤ :=
  fun j ↦ ∑ i, boolSignInt (e i) * v i j

noncomputable def signedIntVectorBase {ι : Type*} [Fintype ι]
    (v : ι → Fin 2 → ℤ) : Fin 2 → ℤ :=
  fun j ↦ ∑ i, v i j

noncomputable def signedIntVectorNegativeSum {ι : Type*} [Fintype ι]
    (v : ι → Fin 2 → ℤ) (e : ι → Bool) : Fin 2 → ℤ :=
  fun j ↦ ∑ i, boolNegativeIndicator (e i) * v i j

noncomputable def signedIntLatticeTarget {ι : Type*} [Fintype ι]
    (v : ι → Fin 2 → ℤ) (d : Fin 2 → ℤ) : Fin 2 → ℤ :=
  fun j ↦ signedIntVectorBase v j + 2 * d j

lemma signedIntVectorSum_eq_base_sub_two_negative {ι : Type*} [Fintype ι]
    (v : ι → Fin 2 → ℤ) (e : ι → Bool) (j : Fin 2) :
    signedIntVectorSum v e j =
      signedIntVectorBase v j - 2 * signedIntVectorNegativeSum v e j := by
  classical
  unfold signedIntVectorSum signedIntVectorBase signedIntVectorNegativeSum
  simp_rw [boolSignInt_eq_one_sub_two_indicator, sub_mul, one_mul, mul_assoc]
  rw [Finset.sum_sub_distrib, Finset.mul_sum]

lemma signedIntVectorSum_sub_target {ι : Type*} [Fintype ι]
    (v : ι → Fin 2 → ℤ) (e : ι → Bool) (d : Fin 2 → ℤ) (j : Fin 2) :
    signedIntVectorSum v e j - signedIntLatticeTarget v d j =
      2 * (-(signedIntVectorNegativeSum v e j + d j)) := by
  rw [signedIntVectorSum_eq_base_sub_two_negative]
  unfold signedIntLatticeTarget
  ring

noncomputable def signedIntCharacteristic {ι : Type*} [Fintype ι]
    (v : ι → Fin 2 → ℤ) (x : Fin 2 → ℝ) : ℂ :=
  ∏ i, (Real.cos (∑ j : Fin 2, x j * (v i j : ℝ)) : ℂ)

lemma signedIntCharacteristic_eq_average {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v : ι → Fin 2 → ℤ) (x : Fin 2 → ℝ) :
    signedIntCharacteristic v x =
      (∑ e : ι → Bool, Complex.exp (Complex.I *
        (∑ j : Fin 2, x j * (signedIntVectorSum v e j : ℝ)))) /
          (2 : ℂ) ^ Fintype.card ι := by
  classical
  have hphase (e : ι → Bool) :
      (∑ j : Fin 2, x j * (signedIntVectorSum v e j : ℝ)) =
        ∑ i : ι, sign (e i) * (∑ j : Fin 2, x j * (v i j : ℝ)) := by
    unfold signedIntVectorSum
    push_cast
    calc
      (∑ j : Fin 2, x j * ∑ i : ι,
          (boolSignInt (e i) : ℝ) * (v i j : ℝ)) =
        ∑ j : Fin 2, ∑ i : ι,
          x j * ((boolSignInt (e i) : ℝ) * (v i j : ℝ)) := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [Finset.mul_sum]
      _ = ∑ i : ι, ∑ j : Fin 2,
          x j * ((boolSignInt (e i) : ℝ) * (v i j : ℝ)) := Finset.sum_comm
      _ = ∑ i : ι, sign (e i) * (∑ j : Fin 2, x j * (v i j : ℝ)) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [intCast_boolSignInt, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        ring
  have hpoint (e : ι → Bool) :
      Complex.exp (Complex.I *
        (∑ j : Fin 2, x j * (signedIntVectorSum v e j : ℝ))) =
      ∏ i : ι, Complex.exp (Complex.I *
        ((∑ j : Fin 2, x j * (v i j : ℝ)) * sign (e i))) := by
    rw [hphase]
    rw [show Complex.I * (↑(∑ i : ι,
        sign (e i) * (∑ j : Fin 2, x j * (v i j : ℝ))) : ℂ) =
      ∑ i : ι, Complex.I *
        ((∑ j : Fin 2, x j * (v i j : ℝ)) * sign (e i)) by
      push_cast
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring]
    exact Complex.exp_sum Finset.univ _
  have hsum :
      (∑ e : ι → Bool, Complex.exp (Complex.I *
        (∑ j : Fin 2, x j * (signedIntVectorSum v e j : ℝ)))) =
      (2 : ℂ) ^ Fintype.card ι * signedIntCharacteristic v x := by
    rw [show (∑ e : ι → Bool, Complex.exp (Complex.I *
          (∑ j : Fin 2, x j * (signedIntVectorSum v e j : ℝ)))) =
        ∑ e : ι → Bool, ∏ i : ι, Complex.exp (Complex.I *
          ((∑ j : Fin 2, x j * (v i j : ℝ)) * sign (e i))) by
      apply Finset.sum_congr rfl
      intro e he
      exact hpoint e]
    calc
      (∑ e : ι → Bool, ∏ i : ι, Complex.exp (Complex.I *
          ((∑ j : Fin 2, x j * (v i j : ℝ)) * sign (e i)))) =
        ∏ i : ι, ∑ b : Bool, Complex.exp (Complex.I *
          ((∑ j : Fin 2, x j * (v i j : ℝ)) * sign b)) := by
            exact (Fintype.prod_sum
              (fun i : ι ↦ fun b : Bool ↦ Complex.exp (Complex.I *
                ((∑ j : Fin 2, x j * (v i j : ℝ)) * sign b)))).symm
      _ = ∏ i : ι, (2 *
          (Real.cos (∑ j : Fin 2, x j * (v i j : ℝ)) : ℂ)) := by
        apply Finset.prod_congr rfl
        intro i hi
        exact sum_bool_cexp_sign _
      _ = (2 : ℂ) ^ Fintype.card ι * signedIntCharacteristic v x := by
        rw [signedIntCharacteristic, Finset.prod_mul_distrib]
        simp
  rw [hsum]
  field_simp

lemma integral_fourthDualCell_even_character (m : Fin 2 → ℤ) :
    (∫ x : Fin 2 → ℝ in fourthDualCell,
      Complex.exp (Complex.I *
        ((((2 * m 0 : ℤ) : ℝ) * x 0) + (((2 * m 1 : ℤ) : ℝ) * x 1)))) =
      (if m 0 = 0 then Real.pi else 0) * (if m 1 = 0 then Real.pi else 0) := by
  have hpoint (x : Fin 2 → ℝ) :
      Complex.exp (Complex.I *
        ((((2 * m 0 : ℤ) : ℝ) * x 0) + (((2 * m 1 : ℤ) : ℝ) * x 1))) =
      ∏ i : Fin 2, Complex.exp (Complex.I * (((2 * m i : ℤ) : ℝ) * x i)) := by
    rw [Fin.prod_univ_two, ← Complex.exp_add]
    congr 1
    ring
  rw [show (∫ x : Fin 2 → ℝ in fourthDualCell,
      Complex.exp (Complex.I *
        ((((2 * m 0 : ℤ) : ℝ) * x 0) + (((2 * m 1 : ℤ) : ℝ) * x 1)))) =
      ∫ x : Fin 2 → ℝ in fourthDualCell,
        ∏ i : Fin 2, Complex.exp (Complex.I * (((2 * m i : ℤ) : ℝ) * x i)) by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall hpoint]
  change (∫ x : Fin 2 → ℝ,
      ∏ i : Fin 2, Complex.exp (Complex.I * (((2 * m i : ℤ) : ℝ) * x i))
        ∂volume.restrict fourthDualCell) = _
  rw [fourthDualCell, volume_pi, Measure.restrict_pi_pi]
  rw [show (∫ x : Fin 2 → ℝ,
      ∏ i : Fin 2, Complex.exp (Complex.I * (((2 * m i : ℤ) : ℝ) * x i))
        ∂Measure.pi fun _i : Fin 2 ↦ volume.restrict
          (Set.Icc (-Real.pi / 2) (Real.pi / 2))) =
      ∏ i : Fin 2, ∫ t : ℝ in Set.Icc (-Real.pi / 2) (Real.pi / 2),
        Complex.exp (Complex.I * (((2 * m i : ℤ) : ℝ) * t)) by
      exact integral_fintype_prod_eq_prod
        (fun i : Fin 2 ↦ fun t : ℝ ↦
          Complex.exp (Complex.I * (((2 * m i : ℤ) : ℝ) * t)))]
  rw [Fin.prod_univ_two,
    integral_Icc_cexp_even_character, integral_Icc_cexp_even_character]

lemma isCompact_fourthDualCell : IsCompact fourthDualCell := by
  unfold fourthDualCell
  exact isCompact_univ_pi (fun _ ↦ isCompact_Icc)

lemma integrableOn_cexp_fin_two_linear (a : Fin 2 → ℝ) :
    IntegrableOn (fun x : Fin 2 → ℝ ↦
      Complex.exp (Complex.I * ∑ j : Fin 2, x j * a j)) fourthDualCell volume := by
  apply ContinuousOn.integrableOn_compact isCompact_fourthDualCell
  fun_prop

lemma integral_signedIntVector_character_orthogonality
    {ι : Type*} [Fintype ι] (v : ι → Fin 2 → ℤ)
    (e : ι → Bool) (d : Fin 2 → ℤ) :
    (∫ x : Fin 2 → ℝ in fourthDualCell,
      Complex.exp (Complex.I *
        (∑ j : Fin 2, x j *
          ((signedIntVectorSum v e j - signedIntLatticeTarget v d j : ℤ) : ℝ)))) =
      if signedIntVectorSum v e = signedIntLatticeTarget v d then Real.pi ^ 2 else 0 := by
  let m : Fin 2 → ℤ := fun j ↦ -(signedIntVectorNegativeSum v e j + d j)
  have hdiff (j : Fin 2) :
      signedIntVectorSum v e j - signedIntLatticeTarget v d j = 2 * m j := by
    exact signedIntVectorSum_sub_target v e d j
  have hpoint (x : Fin 2 → ℝ) :
      Complex.exp (Complex.I *
        (∑ j : Fin 2, x j *
          ((signedIntVectorSum v e j - signedIntLatticeTarget v d j : ℤ) : ℝ))) =
      Complex.exp (Complex.I *
        ((((2 * m 0 : ℤ) : ℝ) * x 0) + (((2 * m 1 : ℤ) : ℝ) * x 1))) := by
    rw [Fin.sum_univ_two]
    rw [hdiff, hdiff]
    push_cast
    congr 1
    ring
  rw [show (∫ x : Fin 2 → ℝ in fourthDualCell,
      Complex.exp (Complex.I *
        (∑ j : Fin 2, x j *
          ((signedIntVectorSum v e j - signedIntLatticeTarget v d j : ℤ) : ℝ)))) =
      ∫ x : Fin 2 → ℝ in fourthDualCell,
        Complex.exp (Complex.I *
          ((((2 * m 0 : ℤ) : ℝ) * x 0) + (((2 * m 1 : ℤ) : ℝ) * x 1))) by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall hpoint]
  rw [integral_fourthDualCell_even_character]
  have hm : (m 0 = 0 ∧ m 1 = 0) ↔
      signedIntVectorSum v e = signedIntLatticeTarget v d := by
    constructor
    · rintro ⟨hm0, hm1⟩
      funext j
      have hd := hdiff j
      have hmj : m j = 0 := by
        fin_cases j
        · simpa using hm0
        · simpa using hm1
      rw [hmj] at hd
      omega
    · intro h
      constructor
      · have hd := hdiff 0
        rw [congrFun h 0] at hd
        omega
      · have hd := hdiff 1
        rw [congrFun h 1] at hd
        omega
  by_cases heq : signedIntVectorSum v e = signedIntLatticeTarget v d
  · have hm01 := hm.2 heq
    simp [heq, hm01.1, hm01.2]
    push_cast
    ring
  · have hmnot : ¬(m 0 = 0 ∧ m 1 = 0) := fun h ↦ heq (hm.1 h)
    rcases not_and_or.mp hmnot with hm0 | hm1
    · simp [heq, hm0]
    · simp [heq, hm1]

noncomputable def signedIntAtomProbability {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v : ι → Fin 2 → ℤ) (d : Fin 2 → ℤ) : ℝ :=
  (∑ e : ι → Bool,
    if signedIntVectorSum v e = signedIntLatticeTarget v d then (1 : ℝ) else 0) /
      (2 : ℝ) ^ Fintype.card ι

noncomputable def signedIntAtomProbabilityC {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v : ι → Fin 2 → ℤ) (d : Fin 2 → ℤ) : ℂ :=
  (∑ e : ι → Bool,
    if signedIntVectorSum v e = signedIntLatticeTarget v d then (1 : ℂ) else 0) /
      (2 : ℂ) ^ Fintype.card ι

lemma signedIntAtomProbabilityC_eq_real {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v : ι → Fin 2 → ℤ) (d : Fin 2 → ℤ) :
    signedIntAtomProbabilityC v d = (signedIntAtomProbability v d : ℂ) := by
  unfold signedIntAtomProbabilityC signedIntAtomProbability
  push_cast
  congr 1
  apply Finset.sum_congr rfl
  intro e he
  split_ifs <;> simp

lemma integral_signedIntCharacteristic_target
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v : ι → Fin 2 → ℤ) (d : Fin 2 → ℤ) :
    (∫ x : Fin 2 → ℝ in fourthDualCell,
      signedIntCharacteristic v x *
        Complex.exp (-Complex.I *
          (∑ j : Fin 2, x j * (signedIntLatticeTarget v d j : ℝ)))) =
      (Real.pi ^ 2 : ℂ) * signedIntAtomProbabilityC v d := by
  classical
  let D : ℂ := (2 : ℂ) ^ Fintype.card ι
  let F : (ι → Bool) → (Fin 2 → ℝ) → ℂ := fun e x ↦
    Complex.exp (Complex.I *
      (∑ j : Fin 2, x j *
        ((signedIntVectorSum v e j - signedIntLatticeTarget v d j : ℤ) : ℝ)))
  have hphase (e : ι → Bool) (x : Fin 2 → ℝ) :
      Complex.exp (Complex.I *
          (∑ j : Fin 2, x j * (signedIntVectorSum v e j : ℝ))) *
        Complex.exp (-Complex.I *
          (∑ j : Fin 2, x j * (signedIntLatticeTarget v d j : ℝ))) = F e x := by
    dsimp [F]
    rw [← Complex.exp_add]
    congr 1
    push_cast
    simp only [Fin.sum_univ_two]
    ring
  have hi (e : ι → Bool) : IntegrableOn (F e) fourthDualCell volume := by
    apply integrableOn_cexp_fin_two_linear
  have hpoint (x : Fin 2 → ℝ) :
      signedIntCharacteristic v x *
          Complex.exp (-Complex.I *
            (∑ j : Fin 2, x j * (signedIntLatticeTarget v d j : ℝ))) =
        (∑ e : ι → Bool, F e x) / D := by
    rw [signedIntCharacteristic_eq_average]
    dsimp [D]
    rw [div_mul_eq_mul_div, Finset.sum_mul]
    apply congrArg (fun z : ℂ ↦ z / (2 : ℂ) ^ Fintype.card ι)
    apply Finset.sum_congr rfl
    intro e he
    exact hphase e x
  have hsum :
      (∫ x : Fin 2 → ℝ in fourthDualCell, ∑ e : ι → Bool, F e x) =
        ∑ e : ι → Bool, ∫ x : Fin 2 → ℝ in fourthDualCell, F e x := by
    exact integral_finset_sum Finset.univ (fun e he ↦ hi e)
  calc
    (∫ x : Fin 2 → ℝ in fourthDualCell,
      signedIntCharacteristic v x *
        Complex.exp (-Complex.I *
          (∑ j : Fin 2, x j * (signedIntLatticeTarget v d j : ℝ)))) =
      ∫ x : Fin 2 → ℝ in fourthDualCell, (∑ e : ι → Bool, F e x) / D := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall hpoint
    _ = (∑ e : ι → Bool, ∫ x : Fin 2 → ℝ in fourthDualCell, F e x) / D := by
      simp_rw [div_eq_mul_inv]
      rw [integral_mul_const, hsum]
    _ = (∑ e : ι → Bool,
        if signedIntVectorSum v e = signedIntLatticeTarget v d
          then (Real.pi ^ 2 : ℂ) else 0) / D := by
      congr 1
      apply Finset.sum_congr rfl
      intro e he
      dsimp [F]
      rw [integral_signedIntVector_character_orthogonality]
      split_ifs <;> norm_num
    _ = (Real.pi ^ 2 : ℂ) * signedIntAtomProbabilityC v d := by
      unfold signedIntAtomProbabilityC
      dsimp [D]
      have hsumif :
          (∑ e : ι → Bool,
            if signedIntVectorSum v e = signedIntLatticeTarget v d
              then (Real.pi ^ 2 : ℂ) else 0) =
          (Real.pi ^ 2 : ℂ) * ∑ e : ι → Bool,
            (if signedIntVectorSum v e = signedIntLatticeTarget v d
              then (1 : ℂ) else 0) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro e he
        split_ifs <;> ring
      rw [hsumif]
      ring

lemma signedIntAtomProbability_fourier_inversion
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v : ι → Fin 2 → ℤ) (d : Fin 2 → ℤ) :
    (signedIntAtomProbability v d : ℂ) =
      (1 / Real.pi ^ 2 : ℂ) *
        ∫ x : Fin 2 → ℝ in fourthDualCell,
          signedIntCharacteristic v x *
            Complex.exp (-Complex.I *
              (∑ j : Fin 2, x j * (signedIntLatticeTarget v d j : ℝ))) := by
  rw [integral_signedIntCharacteristic_target]
  have hp : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp
  exact (signedIntAtomProbabilityC_eq_real v d).symm

end Erdos521
