import Research.BFWFromSpectral
import Research.GeneralBFWReduction
import Research.ConditionalFinalAssembly

namespace Erdos254.FinalProof

open Erdos254.ConditionalFinalAssembly Erdos254.GeneralBFWReduction
open Erdos254.BFWFromSpectral

/-- Canonical Erdős Problem #254 statement. -/
theorem erdos_254 : Erdos254.Statement :=
  bfw_finite_sum_property_implies_statement
    (general_bfw_implies_finite_sum_property general_bfw_from_spectral)

end Erdos254.FinalProof
