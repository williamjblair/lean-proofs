import Mathlib
import Research.PiecewiseAssembly
import Research.TailSemigroup
import Research.CompactSemigroup
import Research.TorusOrbit

namespace Erdos254.TorusCorrectionGroup

open Filter Topology
open scoped BigOperators
open Erdos254.PiecewiseAssembly Erdos254.TailSemigroup
open Erdos254.CompactSemigroup Erdos254.TorusOrbit

noncomputable section

variable {d : Type*} [Fintype d]

lemma sum_nsmul_coeff {G : Type*} [AddCommMonoid G]
    (s : Finset ℕ) (a : G) :
    (∑ n ∈ s, n • a) = (∑ n ∈ s, n) • a := by
  induction s using Finset.induction with
  | empty => simp
  | @insert n s hn ih => simp [hn, ih, add_nsmul]

/-- Full phase divergence produces one closed compact correction subgroup for
any finite torus rotation, with genuine distinct-support corrections dense at
every point of that subgroup. -/
theorem exists_closed_torus_correction_group
    (C : Set ℕ)
    (hphase : ∀ θ : ℝ, θ ∈ Set.Ioo 0 1 →
      Tendsto (phasePartialSum C θ) atTop atTop)
    (α : d → ℝ) :
    ∃ H : AddSubgroup (UnitAddTorus d),
      IsClosed (H : Set (UnitAddTorus d)) ∧
      (fun i => (α i : UnitAddCircle)) ∈ H ∧
      ∀ x ∈ H, ∀ O : Set (UnitAddTorus d), IsOpen O → x ∈ O →
        ∃ q : ℕ, Representable C q ∧
          q • (fun i => (α i : UnitAddCircle)) ∈ O := by
  classical
  let a : UnitAddTorus d := fun i => (α i : UnitAddCircle)
  let seq : ℕ → UnitAddTorus d := fun n => n • a
  let S := tailLimit C seq
  have hSclosed : IsClosed S := tailLimit_isClosed C seq
  have hSzero : (0 : UnitAddTorus d) ∈ S := zero_mem_tailLimit C seq
  have hSadd : ∀ u ∈ S, ∀ v ∈ S, u + v ∈ S := by
    intro u hu v hv
    exact tailLimit_add_mem C seq hu hv
  obtain ⟨H, hH⟩ := compact_add_subsemigroup_is_addSubgroup S
    ⟨0, hSzero⟩ hSclosed hSadd
  have haS : a ∈ S := by
    change a ∈ tailLimit C seq
    rw [tailLimit, Set.mem_iInter]
    intro N
    rw [Metric.mem_closure_iff]
    intro ε hε
    obtain ⟨s, hs, hdist⟩ := torus_orbit_tail_approximation
      C hphase α 1 N ε hε
    refine ⟨∑ n ∈ s, seq n, ⟨s, hs, rfl⟩, ?_⟩
    simpa [seq, a, dist_comm] using hdist
  refine ⟨H, ?_, ?_, ?_⟩
  · rw [hH]
    exact hSclosed
  · change a ∈ (H : Set (UnitAddTorus d))
    rw [hH]
    exact haS
  · intro x hx O hOopen hxO
    have hxS : x ∈ S := by
      rw [← hH]
      exact hx
    change x ∈ tailLimit C seq at hxS
    rw [tailLimit, Set.mem_iInter] at hxS
    have hx0 := hxS 0
    rw [mem_closure_iff] at hx0
    obtain ⟨g, hgO, hgTail⟩ := hx0 O hOopen hxO
    obtain ⟨s, hs, rfl⟩ := hgTail
    let q : ℕ := ∑ n ∈ s, n
    refine ⟨q, ?_, ?_⟩
    · exact ⟨s, fun n hn => (hs n hn).1, rfl⟩
    · have hsum : (∑ n ∈ s, seq n) = q • a := by
        simpa [seq, q] using sum_nsmul_coeff s a
      rw [hsum] at hgO
      exact hgO

end

end Erdos254.TorusCorrectionGroup
