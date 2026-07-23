import Mathlib
import Research.IrrationalDensity
import Research.TailModularCoverage
import Research.Negative

namespace Erdos254.ScalarOrbit

open scoped BigOperators Topology
open Erdos254.IrrationalDensity Erdos254.TailSemigroup

noncomputable section

private lemma rat_mul_circle_eq_of_zmod_eq (r : ℚ) (a b : ℕ)
    (h : (a : ZMod r.den) = (b : ZMod r.den)) :
    (((r : ℝ) * (a : ℝ) : ℝ) : UnitAddCircle) =
      (((r : ℝ) * (b : ℝ) : ℝ) : UnitAddCircle) := by
  letI : NeZero r.den := ⟨r.den_nz⟩
  have hc := congrArg (fun z : ZMod r.den => ZMod.toAddCircle z) h
  rw [ZMod.toAddCircle_natCast, ZMod.toAddCircle_natCast] at hc
  have hnum := congrArg (fun z : UnitAddCircle => r.num • z) hc
  simpa only [← AddCircle.coe_zsmul, zsmul_eq_mul, Rat.cast_def,
    Int.cast_natCast, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hnum

private lemma sum_circle_eq_sum_nat (θ : ℝ) (s : Finset ℕ) :
    (∑ n ∈ s, ((θ * (n : ℝ) : ℝ) : UnitAddCircle)) =
      ((θ * (∑ n ∈ s, n : ℕ) : ℝ) : UnitAddCircle) := by
  let Q : ℝ →+ UnitAddCircle :=
    QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℝ))
  change (∑ n ∈ s, Q (θ * (n : ℝ))) = Q (θ * (∑ n ∈ s, n : ℕ))
  rw [← map_sum Q]
  congr 1
  push_cast
  rw [Finset.mul_sum]

/-- Under the canonical phase hypothesis, every scalar orbit point can be
approximated by a distinct subset sum from every tail. Irrational phases use
F-028; rational phases use F-020 and are attained exactly. -/
theorem scalar_orbit_tail_approximation (A : Set ℕ)
    (hphase : ∀ θ : ℝ, θ ∈ Set.Ioo 0 1 →
      Filter.Tendsto (phasePartialSum A θ)
        (Filter.atTop : Filter ℕ) Filter.atTop)
    (θ : ℝ) (m N : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ s : Finset ℕ,
      (∀ n ∈ s, n ∈ A ∧ N ≤ n) ∧
      dist (∑ n ∈ s, ((θ * (n : ℝ) : ℝ) : UnitAddCircle))
        (m • (θ : UnitAddCircle)) < ε := by
  by_cases hθ : Irrational θ
  · have hfull := irrational_tailLimit_eq_univ A hphase θ hθ
    let x : ℕ → UnitAddCircle := fun n => (θ * (n : ℝ) : UnitAddCircle)
    let target : UnitAddCircle := m • (θ : UnitAddCircle)
    have ht : target ∈ tailLimit A x := by
      rw [hfull]
      exact Set.mem_univ _
    have htN : target ∈ closure (tailSubsetSums A x N) := by
      rw [tailLimit, Set.mem_iInter] at ht
      exact ht N
    rw [Metric.mem_closure_iff] at htN
    obtain ⟨g, ⟨s, hs, hsg⟩, hdist⟩ := htN ε hε
    refine ⟨s, hs, ?_⟩
    rw [hsg]
    simpa only [dist_comm] using hdist
  · have hrange : θ ∈ Set.range ((↑) : ℚ → ℝ) := by
      exact Classical.not_not.mp hθ
    obtain ⟨r, rfl⟩ := hrange
    by_cases hden : r.den = 1
    · refine ⟨∅, by simp, ?_⟩
      have hrint : ((r : ℝ) : UnitAddCircle) = 0 := by
        rw [Rat.cast_def, hden]
        norm_num
      simp [hrint, hε]
    · have hdenpos : 0 < r.den := r.den_pos
      have hq2 : 2 ≤ r.den := by omega
      have htail : ∀ d : ℕ, 2 ≤ d → ∀ K : ℕ,
          ∃ n : ℕ, K ≤ n ∧ n ∈ A ∧ ¬ d ∣ n := by
        intro d hd K
        exact phase_implies_tail_nonmultiple A hphase d hd K
      obtain ⟨s, hs, hmod⟩ :=
        TailModularCoverage.tail_subset_sums_cover_zmod A htail r.den hq2 N
          (m : ZMod r.den)
      refine ⟨s, hs, ?_⟩
      have hcast : ((∑ n ∈ s, n : ℕ) : ZMod r.den) = (m : ZMod r.den) := by
        rw [Nat.cast_sum]
        exact hmod
      have hrat := rat_mul_circle_eq_of_zmod_eq r (∑ n ∈ s, n) m hcast
      rw [sum_circle_eq_sum_nat, hrat]
      have hm : ((((r : ℝ) * (m : ℝ) : ℝ)) : UnitAddCircle) =
          m • ((r : ℝ) : UnitAddCircle) := by
        rw [← AddCircle.coe_nsmul]
        congr 1
        simp [nsmul_eq_mul, mul_comm]
      rw [hm, dist_self]
      exact hε

end

end Erdos254.ScalarOrbit
