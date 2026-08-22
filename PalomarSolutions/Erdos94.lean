import ErdosProblems.Erdos94

open scoped BigOperators Finset

local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

namespace Palomar.Erdos94

theorem sum_multiplicity (P : Finset ℝ²) :
    ∑ u ∈ distanceSet P, distanceMultiplicity P u = P.card.choose 2 :=
  _root_.Erdos94.variants.sum_multiplicity P

end Palomar.Erdos94
