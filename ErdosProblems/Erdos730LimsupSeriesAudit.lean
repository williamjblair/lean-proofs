/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import ErdosProblems.Erdos730LimsupSeries

/-! Independent axiom audit for the finite-depth limsup assembly. -/

open Filter
open scoped Topology

namespace Erdos730.LimsupSeriesAudit

open Erdos730.LimsupSeries

variable {κ : Type*} {f : Filter κ} [f.NeBot]
  {term : ℕ → ℝ} {total : κ → ℝ} {band tail : ℕ → κ → ℝ}

theorem exposed_finite_depth_surface
    (htermNonneg : ∀ r, 0 ≤ term r)
    (htermSum : Summable term)
    (htotalNonneg : ∀ x, 0 ≤ total x)
    (hbandNonneg : ∀ r x, 0 ≤ band r x)
    (hbandBdd : ∀ r, IsBoundedUnder (· ≤ ·) f (band r))
    (hbandLimsup : ∀ r, limsup (band r) f ≤ term r)
    (htailNonneg : ∀ R x, 0 ≤ tail R x)
    (htailBdd : ∀ R, IsBoundedUnder (· ≤ ·) f (tail R))
    (epsilon : ℕ → ℝ)
    (hepsilon : Tendsto epsilon atTop (𝓝 0))
    (htailLimsup : ∀ R, limsup (tail R) f ≤ epsilon R)
    (hdecomp : ∀ R, total ≤ᶠ[f]
      fun x ↦ (∑ r ∈ Finset.range R, band r x) + tail R x) :
    limsup total f ≤ ∑' r, term r :=
  limsup_le_tsum_of_finite_depth_and_tail htermNonneg htermSum
    htotalNonneg hbandNonneg hbandBdd hbandLimsup htailNonneg htailBdd
    epsilon hepsilon htailLimsup hdecomp

#print axioms exposed_finite_depth_surface

end Erdos730.LimsupSeriesAudit
