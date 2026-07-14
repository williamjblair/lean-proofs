/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import ErdosProblems.Erdos730SmallPrimeTail

/-! Independent axiom audit for the uniform small-prime main tail. -/

namespace Erdos730.SmallPrimeTailAudit

open Filter
open scoped Topology
open Erdos730.SmallPrimeTail

theorem exposed_tail_bound (R : ℕ) :
    uniformDepthMainTail R ≤ 3 * (2 / 3 : ℝ) ^ R :=
  uniformDepthMainTail_le R

theorem exposed_tail_limit :
    Tendsto uniformDepthMainTail atTop (𝓝 0) :=
  tendsto_uniformDepthMainTail_zero

theorem exposed_finite_tail_bound (R J : ℕ) :
    (∑ r ∈ Finset.Ico R J, uniformDepthMainTerm r) ≤
      uniformDepthMainTail R :=
  uniformDepthMain_sum_Ico_le_tail R J

theorem exposed_deepest_band_limit :
    Tendsto deepestBandMajorant atTop (𝓝 0) :=
  tendsto_deepestBandMajorant_zero

theorem exposed_uniform_mertens_error_limit :
    Tendsto uniformMertensErrorMajorant atTop (𝓝 0) :=
  tendsto_uniformMertensErrorMajorant_zero

theorem exposed_weighted_band_sum
    (s : Finset ℕ) {X : ℕ} (hX : 1 < X)
    (hlower : ∀ r ∈ s,
      2 ≤ Erdos730.FullDensity.fixedDepthPrimeBandLower r (X : ℝ)) :
    (∑ r ∈ s, (2 / 3 : ℝ) ^ r *
      Erdos730.FullDensity.fixedDepthReciprocalPrimeBand r (X : ℝ)) ≤
      (∑ r ∈ s, uniformDepthMainTerm r) +
        uniformMertensErrorMajorant X :=
  weightedFixedDepthBand_sum_le_main_add_error s hX hlower

#print axioms exposed_tail_bound
#print axioms exposed_tail_limit
#print axioms exposed_finite_tail_bound
#print axioms exposed_deepest_band_limit
#print axioms exposed_uniform_mertens_error_limit
#print axioms exposed_weighted_band_sum

end Erdos730.SmallPrimeTailAudit
