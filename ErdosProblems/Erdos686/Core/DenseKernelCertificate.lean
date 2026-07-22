/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import ErdosProblems.Erdos686.Core.SparseJetCertificate

/-!
# Erdős 686: chunked kernel certificates for dense polynomials

Large generated dense identities are checked one coefficient row at a time.
This module assembles those row checks into the existing semantic
`denseBivariateIsZero` predicate.
-/

namespace Erdos686
namespace Erdos686Variant

def DenseBivariateRowsCertificate
    (polynomial : DenseBivariateIntPolynomial) : Prop :=
  ∀ rowIndex < polynomial.length,
    denseIntIsZero (polynomial.getD rowIndex [])

theorem denseBivariateIsZero_of_rows
    {polynomial : DenseBivariateIntPolynomial}
    (hrows : DenseBivariateRowsCertificate polynomial) :
    denseBivariateIsZero polynomial := by
  unfold denseBivariateIsZero
  apply List.all_eq_true.mpr
  intro row hrow
  obtain ⟨rowIndex, hindex, rfl⟩ :=
    List.mem_iff_getElem.mp hrow
  have hzero := hrows rowIndex hindex
  rw [List.getD_eq_getElem polynomial [] hindex] at hzero
  exact hzero

end Erdos686Variant
end Erdos686
