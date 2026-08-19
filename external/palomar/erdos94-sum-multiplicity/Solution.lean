import ErdosProblems.Erdos94SumMultiplicity

/-!
Proved bridge for the bounded Erdős 94 Comparator challenge.

The proof term delegates to the exact source-owned declaration introduced by
commit `423344341fbfdf4f8f684a302c5d05379125e7dc`.
-/

open scoped BigOperators Finset

local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

noncomputable section

theorem erdos94_sum_multiplicity (P : Finset ℝ²) :
    ∑ u ∈ distanceSet P, distanceMultiplicity P u = P.card.choose 2 := by
  exact Erdos94.variants.sum_multiplicity P

