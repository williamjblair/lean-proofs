import Research.FourthCrossingFirstMomentGate
import Mathlib.Tactic

open scoped BigOperators

namespace Erdos521

noncomputable local instance coneFourthTransferDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

/-- Terminal axis words whose reconstructed coefficients have a fourth-integrated weak crossing. -/
noncomputable def fourthCrossingAxisWords (r k : ℕ) : Finset (AxisWord r) :=
  Finset.univ.filter (fun w ↦
    fourthIntegratedRademacherSum (axisWordCoefficients w) k *
      fourthIntegratedRademacherSum (axisWordCoefficients w) (k + 1) ≤ 0)

/-- Good full paths whose reconstructed coefficient word crosses at edge `k`. -/
abbrev FourthCrossingAxisPath (n k : ℕ) := {p : AxisGoodPath n //
  fourthIntegratedRademacherSum (axisPathCoefficients p) k *
    fourthIntegratedRademacherSum (axisPathCoefficients p) (k + 1) ≤ 0}

lemma axisPath_eq_bitsAxis {n : ℕ} (p : AxisGoodPath n) :
    (⟨bitsAxisEquiv n ((bitsAxisEquiv n).symm p.1), by
      simpa using p.property⟩ : AxisGoodPath n) = p := by
  apply Subtype.ext
  exact (bitsAxisEquiv n).apply_symm_apply p.1

lemma axisSuffix_coefficients_eq_of_lt {s r : ℕ} (p : AxisGoodPath (s + r))
    {i : ℕ} (hi : i < 2 * r) :
    axisWordCoefficients (axisSuffix p) i = axisPathCoefficients p i := by
  let x := (bitsAxisEquiv (s + r)).symm p.1
  have hxgood : AxisGood (bitsAxisEquiv (s + r) x).1
      (bitsAxisEquiv (s + r) x).2 := by simpa [x] using p.property
  have hsuffix := axisWordBits_axisSuffix_bitsAxis x hxgood
  have hp : (⟨bitsAxisEquiv (s + r) x, hxgood⟩ : AxisGoodPath (s + r)) = p := by
    exact axisPath_eq_bitsAxis p
  rw [hp] at hsuffix
  unfold axisWordCoefficients
  rw [extendBits_of_lt _ hi, hsuffix]
  rw [axisPathCoefficients_eq]
  rw [extendBits_of_lt]
  rfl

lemma fourthSum_axisSuffix_eq {s r k : ℕ} (p : AxisGoodPath (s + r))
    (hk : k < 2 * r) :
    fourthIntegratedRademacherSum (axisWordCoefficients (axisSuffix p)) k =
      fourthIntegratedRademacherSum (axisPathCoefficients p) k := by
  apply fourthIntegratedRademacherSum_eq_of_prefix (N := k) (k := k)
  · intro i hi
    exact axisSuffix_coefficients_eq_of_lt p (by omega)
  · exact le_rfl

lemma axisSuffix_mem_fourthCrossing_iff {s r k : ℕ} (p : AxisGoodPath (s + r))
    (hk : k + 1 < 2 * r) :
    axisSuffix p ∈ fourthCrossingAxisWords r k ↔
      fourthIntegratedRademacherSum (axisPathCoefficients p) k *
        fourthIntegratedRademacherSum (axisPathCoefficients p) (k + 1) ≤ 0 := by
  simp only [fourthCrossingAxisWords, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [fourthSum_axisSuffix_eq p (by omega), fourthSum_axisSuffix_eq p hk]

/-- Sharp finite transfer of a fourth-integrated crossing from iid words to cone paths. -/
theorem cone_fourthCrossing_density_le (s r k : ℕ) (hk : k + 1 < 2 * r) :
    (Fintype.card (FourthCrossingAxisPath (s + r) k) : ℝ) /
        Fintype.card (AxisGoodPath (s + r)) ≤
      ((s + r + 1 : ℝ) / (s + 1 : ℝ)) *
        ((fourthCrossingAxisWords r k).card : ℝ) / (4 : ℝ) ^ r := by
  have hbase := goodPaths_suffix_density_le s r (fourthCrossingAxisWords r k)
  have hcard : Fintype.card (FourthCrossingAxisPath (s + r) k) =
      Fintype.card {p : AxisGoodPath (s + r) //
        axisSuffix p ∈ fourthCrossingAxisWords r k} := by
    apply Fintype.card_congr
    exact Equiv.subtypeEquiv (Equiv.refl _) fun p ↦
      (axisSuffix_mem_fourthCrossing_iff p hk).symm
  rw [hcard]
  exact hbase

lemma card_fourthCrossingAxisWords_eq_bits (r k : ℕ) :
    (fourthCrossingAxisWords r k).card =
      (Finset.univ.filter (fun x : Fin (2 * r) → Bool ↦
        fourthIntegratedRademacherSum (extendBits r x) k *
          fourthIntegratedRademacherSum (extendBits r x) (k + 1) ≤ 0)).card := by
  let f : AxisWord r → Fin (2 * r) → Bool := axisWordBits
  have hf : Function.Bijective f := axisWordBits_bijective r
  apply Finset.card_bij (fun w hw ↦ f w)
  · intro w hw
    simp only [fourthCrossingAxisWords, Finset.mem_filter, Finset.mem_univ, true_and] at hw
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    simpa [f, axisWordCoefficients] using hw
  · intro w₁ hw₁ w₂ hw₂ h
    exact hf.injective h
  · intro x hx
    obtain ⟨w, hw⟩ := hf.surjective x
    refine ⟨w, ?_, hw⟩
    simp only [fourthCrossingAxisWords, Finset.mem_filter, Finset.mem_univ, true_and]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    change fourthIntegratedRademacherSum (extendBits r (f w)) k *
      fourthIntegratedRademacherSum (extendBits r (f w)) (k + 1) ≤ 0
    rw [hw]
    exact hx

end Erdos521
