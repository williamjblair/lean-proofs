import Research.Definitions
import Mathlib.Probability.Distributions.Uniform

open MeasureTheory ProbabilityTheory
open scoped unitInterval ENNReal BigOperators

namespace Erdos521

local instance fairCoin_isProbabilityMeasure_prefix : IsProbabilityMeasure fairCoin := by
  unfold fairCoin
  infer_instance

/-- Each atom of the fair Boolean law has real mass `1/2`. -/
lemma fairCoin_real_singleton (b : Bool) : fairCoin.real {b} = (1 : ℝ) / 2 := by
  cases b <;> simp [fairCoin, half] <;> norm_num

/-- Each atom of the fair Boolean law has `ENNReal` mass `2⁻¹`. -/
lemma fairCoin_singleton (b : Bool) : fairCoin {b} = (2 : ENNReal)⁻¹ := by
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  simpa [Measure.real] using fairCoin_real_singleton b

/-- A finite product of fair Boolean laws is the uniform law on Boolean functions. -/
lemma pi_fairCoin_eq_uniform {ι : Type*} [Fintype ι] [DecidableEq ι] :
    Measure.pi (fun _ : ι ↦ fairCoin) =
      (PMF.uniformOfFintype (ι → Bool)).toMeasure := by
  classical
  apply Measure.ext_of_singleton
  intro f
  rw [Measure.pi_singleton, PMF.toMeasure_apply_singleton]
  simp only [fairCoin_singleton, PMF.uniformOfFintype_apply, Fintype.card_fun,
    Fintype.card_bool, Finset.prod_const, Finset.card_univ]
  · rw [Nat.cast_pow]
    exact (@ENNReal.inv_pow (2 : ENNReal) (Fintype.card ι)).symm
  · measurability

/-- Exact cardinality formula for every event depending on a finite set of fair coordinates. -/
lemma rademacherMeasure_prefix_preimage (S : Finset ℕ) (E : Set (S → Bool)) :
    rademacherMeasure ((fun (ω : ℕ → Bool) (i : S) ↦ ω i) ⁻¹' E) =
      (E.ncard : ENNReal) / (2 ^ S.card : ℕ) := by
  classical
  letI : Fintype E := Fintype.ofFinite E
  have hE : MeasurableSet E := Set.toFinite E |>.measurableSet
  rw [← Measure.map_apply (by fun_prop) hE]
  unfold rademacherMeasure
  change (Measure.map S.restrict (Measure.infinitePi (fun _ : ℕ ↦ fairCoin))) E = _
  rw [Measure.infinitePi_map_restrict, pi_fairCoin_eq_uniform]
  rw [PMF.toMeasure_uniformOfFintype_apply E hE]
  simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_coe]
  rw [Set.fintypeCard_eq_ncard]

end Erdos521
