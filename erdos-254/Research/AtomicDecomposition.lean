import Mathlib

namespace Erdos254.AtomicDecomposition

open MeasureTheory

noncomputable section

local instance : MeasurableSpace Circle := borel Circle
local instance : BorelSpace Circle := ⟨rfl⟩

/-- The points carrying positive mass for a measure. -/
def atomSet (μ : Measure Circle) : Set Circle := {z | μ {z} ≠ 0}

lemma atomSet_countable (μ : Measure Circle) [SFinite μ] :
    (atomSet μ).Countable := by
  have h := Measure.countable_meas_level_set_pos (μ := μ)
    (g := fun z : Circle => z) measurable_id
  simpa [atomSet, pos_iff_ne_zero] using h

lemma atomSet_measurable (μ : Measure Circle) [SFinite μ] :
    MeasurableSet (atomSet μ) := (atomSet_countable μ).measurableSet

/-- The restriction away from all point masses. -/
def continuousPart (μ : Measure Circle) : Measure Circle :=
  μ.restrict (atomSet μ)ᶜ

instance continuousPart_isFinite (μ : Measure Circle) [IsFiniteMeasure μ] :
    IsFiniteMeasure (continuousPart μ) := by
  unfold continuousPart
  infer_instance

instance continuousPart_noAtoms (μ : Measure Circle) [SFinite μ] :
    NoAtoms (continuousPart μ) := by
  constructor
  intro z
  change (μ.restrict (atomSet μ)ᶜ) {z} = 0
  rw [Measure.restrict_apply (MeasurableSet.singleton z)]
  by_cases hz : μ {z} = 0
  · exact measure_mono_null Set.inter_subset_left hz
  · have hzA : z ∈ atomSet μ := hz
    have hempty : {z} ∩ (atomSet μ)ᶜ = ∅ := by
      ext x
      change (x = z ∧ x ∉ atomSet μ) ↔ False
      constructor
      · rintro ⟨rfl, hnot⟩
        exact hnot hzA
      · exact False.elim
    rw [hempty, measure_empty]

theorem summable_atom_weights (μ : Measure Circle) [IsFiniteMeasure μ] :
    Summable (fun z : atomSet μ => μ.real {(z : Circle)}) := by
  apply summable_of_sum_le (fun _ => measureReal_nonneg)
  intro s
  apply sum_measureReal_le_measureReal_univ
  · intro z hz
    exact MeasurableSet.singleton _
  · intro z hz w hw hzw
    exact Set.disjoint_singleton.mpr (fun h => hzw (Subtype.ext h))

/-- A finite measure is the sum of its restriction to its point-mass set and
an atomless remainder. The atomic integral is explicitly a countable sum. -/
theorem integral_eq_atomic_add_continuous
    (μ : Measure Circle) [IsFiniteMeasure μ]
    (f : Circle → ℂ) (hf : Integrable f μ) :
    (∫ z, f z ∂μ) =
      (∑' z : atomSet μ, μ.real {(z : Circle)} • f z) +
      ∫ z, f z ∂(continuousPart μ) := by
  have hA := atomSet_measurable μ
  have hsplit := Measure.restrict_add_restrict_compl (μ := μ) hA
  calc
    (∫ z, f z ∂μ) =
        ∫ z, f z ∂(μ.restrict (atomSet μ) + μ.restrict (atomSet μ)ᶜ) := by
      rw [hsplit]
    _ = (∫ z, f z ∂(μ.restrict (atomSet μ))) +
        ∫ z, f z ∂(μ.restrict (atomSet μ)ᶜ) :=
      integral_add_measure hf.restrict hf.restrict
    _ = (∑' z : atomSet μ, μ.real {(z : Circle)} • f z) +
        ∫ z, f z ∂(continuousPart μ) := by
      rw [setIntegral_countable f (atomSet_countable μ) hf.restrict]
      rfl

end

end Erdos254.AtomicDecomposition
