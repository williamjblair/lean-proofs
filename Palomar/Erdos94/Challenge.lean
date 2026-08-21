import Mathlib

/-!
# Erdős Problem #94: the distance-multiplicity identity

For a finite set `P` of points in the plane, let `distanceSet P` be the set of distinct
distances it determines and `distanceMultiplicity P d` the number of unordered pairs of
distinct points at distance `d`. The theorem below is the bookkeeping identity behind the
problem: summing the multiplicities over the distinct distances counts every unordered
pair of distinct points exactly once, so the sum is `(|P| choose 2)`.

This is the `sum_multiplicity` variant recorded under Erdős Problem #94 in Google
DeepMind's Formal Conjectures (`FormalConjectures/ErdosProblems/94.lean`). It is an
elementary bounded identity, not the cubic distance-multiplicity theorem or the
regular-polygon conjecture of that problem; it is kept here as a hosted, audited
result rather than as a registry candidate.

`distanceSet` and `distanceMultiplicity` are copied verbatim from the Formal
Conjectures file so that the statement is audited against the same objects.
-/

open scoped BigOperators Finset

local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

/-- The distinct distances determined by a finite point set. -/
noncomputable def distanceSet {X : Type*} [MetricSpace X] (points : Finset X) : Finset ℝ :=
  points.offDiag.image fun pair : X × X => dist pair.1 pair.2

/-- The number of unordered pairs of distinct points of `points` at distance `d`. -/
noncomputable def distanceMultiplicity (points : Finset ℝ²) (d : ℝ) : ℕ :=
  #(points.offDiag.filter fun pair : ℝ² × ℝ² => dist pair.1 pair.2 = d) / 2

namespace Palomar.Erdos94

/-- The multiplicities of the distinct distances of `P` sum to the number of unordered
pairs of distinct points. -/
theorem sum_multiplicity (P : Finset ℝ²) :
    ∑ u ∈ distanceSet P, distanceMultiplicity P u = P.card.choose 2 := by
  sorry

end Palomar.Erdos94
