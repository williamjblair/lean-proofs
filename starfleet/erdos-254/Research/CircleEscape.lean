import Mathlib
import Research.PhaseEscape
import Research.TailSemigroup

namespace Erdos254.CircleEscape

open scoped BigOperators Topology
open Erdos254.PhaseEscape Erdos254.TailSemigroup

noncomputable section

private def realEscape : Set ℝ :=
  Set.Icc (1 / 4) (3 / 4) ∪ Set.Icc (-3 / 4) (-1 / 4)

private def circleEscape : Set UnitAddCircle :=
  ((fun z : ℝ => (z : UnitAddCircle)) '' realEscape)

private lemma realEscape_isCompact : IsCompact realEscape := by
  exact isCompact_Icc.union isCompact_Icc

private lemma circleEscape_isClosed : IsClosed circleEscape := by
  exact (realEscape_isCompact.image (AddCircle.continuous_mk' 1)).isClosed

private lemma zero_not_mem_circleEscape : (0 : UnitAddCircle) ∉ circleEscape := by
  rintro ⟨z, hz, hz0⟩
  have hcoe : (z : UnitAddCircle) = 0 := hz0
  obtain ⟨k, hk⟩ := (AddCircle.coe_eq_zero_iff (1 : ℝ)).mp hcoe
  have hkz : (k : ℝ) = z := by simpa using hk
  rcases hz with hz | hz
  · have hkpos : (0 : ℤ) < k := by
      exact_mod_cast (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 4) (hkz.symm ▸ hz.1))
    have hklt : k < (1 : ℤ) := by
      exact_mod_cast (lt_of_le_of_lt (hkz.symm ▸ hz.2) (by norm_num : (3 / 4 : ℝ) < 1))
    omega
  · have hkgt : (-1 : ℤ) < k := by
      exact_mod_cast (lt_of_lt_of_le (by norm_num : (-1 : ℝ) < -3 / 4) (hkz.symm ▸ hz.1))
    have hkneg : k < (0 : ℤ) := by
      exact_mod_cast (lt_of_le_of_lt (hkz.symm ▸ hz.2) (by norm_num : (-1 / 4 : ℝ) < 0))
    omega

private lemma coe_centeredFraction (x : ℝ) :
    (centeredFraction x : UnitAddCircle) = (x : UnitAddCircle) := by
  rw [centeredFraction]
  split_ifs
  · rw [← Int.fract_add_floor x]
    simp
  · rw [← Int.fract_add_floor x]
    simp

/-- If the phase series for `qθ` diverges, the common tail-subset-sum limit of
`θn mod 1` contains a point not killed by multiplication by `q`. -/
theorem tailLimit_has_nonzero_qsmul (A : Set ℕ) (θ : ℝ) (q : ℕ)
    (hdiv : Filter.Tendsto (phasePartialSum A ((q : ℝ) * θ))
      (Filter.atTop : Filter ℕ) Filter.atTop) :
    ∃ g ∈ tailLimit A (fun n => ((θ * (n : ℝ) : ℝ) : UnitAddCircle)),
      q • g ≠ 0 := by
  let x : ℕ → UnitAddCircle := fun n => (θ * (n : ℝ) : UnitAddCircle)
  let E : Set UnitAddCircle := (fun g => q • g) ⁻¹' circleEscape
  have hE : IsClosed E := circleEscape_isClosed.preimage (continuous_nsmul q)
  have hmeet : ∀ N, (tailSubsetSums A x N ∩ E).Nonempty := by
    intro N
    obtain ⟨s, hs, hphase⟩ := tail_phase_escape A ((q : ℝ) * θ) hdiv N
    let z := ∑ n ∈ s, centeredFraction (((q : ℝ) * θ) * (n : ℝ))
    have hz : z ∈ realEscape := by
      rcases hphase with hp | hm
      · exact Or.inl hp
      · exact Or.inr hm
    let g : UnitAddCircle := ∑ n ∈ s, x n
    refine ⟨g, ⟨s, hs, rfl⟩, ?_⟩
    change q • g ∈ circleEscape
    refine ⟨z, hz, ?_⟩
    let Q : ℝ →+ UnitAddCircle :=
      QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℝ))
    have hg : g = Q (∑ n ∈ s, θ * (n : ℝ)) := by
      change (∑ n ∈ s, Q (θ * (n : ℝ))) = Q (∑ n ∈ s, θ * (n : ℝ))
      exact (map_sum Q (fun n : ℕ => θ * (n : ℝ)) s).symm
    have hzcoe : (z : UnitAddCircle) =
        Q (∑ n ∈ s, ((q : ℝ) * θ) * (n : ℝ)) := by
      change Q (∑ n ∈ s, centeredFraction (((q : ℝ) * θ) * (n : ℝ))) = _
      rw [map_sum]
      conv_rhs => rw [map_sum]
      apply Finset.sum_congr rfl
      intro n hn
      exact coe_centeredFraction _
    rw [hg, ← map_nsmul Q]
    change (z : UnitAddCircle) = Q (q • ∑ n ∈ s, θ * (n : ℝ))
    rw [hzcoe]
    congr 1
    simp only [nsmul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    ring
  obtain ⟨g, hg, hgE⟩ := tailLimit_meets_closed A x E hE hmeet
  refine ⟨g, hg, ?_⟩
  intro hqg
  exact zero_not_mem_circleEscape (hqg ▸ hgE)

end

end Erdos254.CircleEscape
