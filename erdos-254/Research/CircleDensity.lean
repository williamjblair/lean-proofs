import Mathlib
import Research.CompactSemigroup
import Research.CircleEscape

namespace Erdos254.CircleDensity

open scoped Topology
open Erdos254.CompactSemigroup Erdos254.CircleEscape Erdos254.TailSemigroup

noncomputable section

/-- If every positive integer multiple of a scalar phase has divergent L1
mass, then distinct subset sums from every tail are dense in the unit circle. -/
theorem tailLimit_eq_univ_of_all_multiples_diverge (A : Set ℕ) (θ : ℝ)
    (hdiv : ∀ q : ℕ, 0 < q →
      Filter.Tendsto (phasePartialSum A ((q : ℝ) * θ))
        (Filter.atTop : Filter ℕ) Filter.atTop) :
    tailLimit A (fun n => ((θ * (n : ℝ) : ℝ) : UnitAddCircle)) = Set.univ := by
  let x : ℕ → UnitAddCircle := fun n => (θ * (n : ℝ) : UnitAddCircle)
  let S := tailLimit A x
  have hSclosed : IsClosed S := tailLimit_isClosed A x
  have hSzero : (0 : UnitAddCircle) ∈ S := zero_mem_tailLimit A x
  have hSadd : ∀ u ∈ S, ∀ v ∈ S, u + v ∈ S := by
    intro u hu v hv
    exact tailLimit_add_mem A x hu hv
  obtain ⟨H, hH⟩ := compact_add_subsemigroup_is_addSubgroup S
    ⟨0, hSzero⟩ hSclosed hSadd
  have hHdense : Dense (H : Set UnitAddCircle) := by
    rw [AddCircle.dense_addSubgroup_iff_ne_zmultiples]
    intro a ha hHa
    let q := addOrderOf a
    have hq : 0 < q := Nat.pos_of_ne_zero ha
    obtain ⟨g, hgS, hqg⟩ := tailLimit_has_nonzero_qsmul A θ q (hdiv q hq)
    have hgH : g ∈ H := by
      change g ∈ (H : Set UnitAddCircle)
      rw [hH]
      exact hgS
    rw [hHa, AddSubgroup.mem_zmultiples_iff] at hgH
    obtain ⟨k, hkg⟩ := hgH
    apply hqg
    rw [← hkg]
    rw [← show ((q : ℤ) • (k • a)) = q • (k • a) by simp]
    rw [smul_smul, mul_comm, ← smul_smul]
    simp [q]
  have hHclosed : IsClosed (H : Set UnitAddCircle) := by
    rw [hH]
    exact hSclosed
  have hHuniv : (H : Set UnitAddCircle) = Set.univ := by
    rw [← hHclosed.closure_eq]
    exact (dense_iff_closure_eq.mp hHdense)
  change S = Set.univ
  exact hH.symm.trans hHuniv

end

end Erdos254.CircleDensity
