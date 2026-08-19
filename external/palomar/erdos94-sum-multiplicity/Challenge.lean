import Mathlib

/-!
Trusted statement snapshot for the bounded Erdős 94 sum-multiplicity result.

The definitions and theorem type are copied from source commit
`423344341fbfdf4f8f684a302c5d05379125e7dc`. The `sorry` below is the
intentional Comparator challenge hole, not an unresolved repository proof.
-/

open scoped BigOperators Finset

local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

noncomputable def distanceSet {X : Type*} [MetricSpace X] (points : Finset X) : Finset ℝ :=
  points.offDiag.image fun pair : X × X => dist pair.1 pair.2

noncomputable def distanceMultiplicity (points : Finset ℝ²) (d : ℝ) : ℕ :=
  #(points.offDiag.filter fun pair : ℝ² × ℝ² => dist pair.1 pair.2 = d) / 2

noncomputable section

/-- Comparator challenge for `Erdos94.variants.sum_multiplicity`. -/
theorem erdos94_sum_multiplicity (P : Finset ℝ²) :
    ∑ u ∈ distanceSet P, distanceMultiplicity P u = P.card.choose 2 := by
  sorry

