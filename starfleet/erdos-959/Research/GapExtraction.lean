import Research.OrderedUnordered
import Research.Foundations

noncomputable section
namespace Erdos959

lemma frequency_pos_iff_mem_distanceValues
    {n : ℕ} (P : Fin n → Point) (d : ℝ) :
    0 < frequency P d ↔ d ∈ distanceValues P := by
  constructor
  · intro hpos
    have hn : ((indexPairs n).filter fun ij =>
        sqDist (P ij.1) (P ij.2) = d).Nonempty := Finset.card_pos.mp hpos
    rcases hn with ⟨ij, hij⟩
    have hm := Finset.mem_filter.mp hij
    apply Finset.mem_image.mpr
    exact ⟨ij, hm.1, hm.2⟩
  · intro hd
    rcases Finset.mem_image.mp hd with ⟨ij, hij, heq⟩
    apply Finset.card_pos.mpr
    exact ⟨ij, Finset.mem_filter.mpr ⟨hij, heq⟩⟩

lemma multiplicityGap_lower_of_ordered_dominance
    (Y : Finset Point) (S : ℕ)
    (hS : 1 ≤ S)
    (hspectrum : 2 ≤ (pointDistanceSpectrum Y).card)
    (htarget : S ≤ 1152 * (orderedRealDistancePairs Y 1).card)
    (hcompetitor : ∀ d : ℝ, d ≠ 1 →
      2304 * (orderedRealDistancePairs Y d).card ≤ S) :
    S ≤ 4608 * multiplicityGap (enumerateFinset Y) := by
  let P := enumerateFinset Y
  have htarget' : S ≤ 2304 * frequency P 1 := by
    rw [orderedRealDistancePairs_card_eq_twice_frequency] at htarget
    calc
      S ≤ 1152 * (2 * frequency (enumerateFinset Y) 1) := htarget
      _ = 2304 * frequency P 1 := by dsimp [P]; ring
  have htargetPos : 0 < frequency P 1 := by
    by_contra h
    have hz : frequency P 1 = 0 := by omega
    rw [hz] at htarget'
    simp at htarget'
    omega
  have htargetMem : 1 ∈ distanceValues P :=
    (frequency_pos_iff_mem_distanceValues P 1).mp htargetPos
  have hruDiv : runnerUpFrequency P 1 ≤ S / 4608 := by
    apply Finset.sup_le
    intro d hd
    have hdne : d ≠ 1 := (Finset.mem_erase.mp hd).1
    have hc := hcompetitor d hdne
    rw [orderedRealDistancePairs_card_eq_twice_frequency] at hc
    apply (Nat.le_div_iff_mul_le (by norm_num : 0 < 4608)).2
    simpa [P, mul_assoc, mul_comm, mul_left_comm] using hc
  have hruMul : 4608 * runnerUpFrequency P 1 ≤ S := by
    calc
      4608 * runnerUpFrequency P 1 ≤ 4608 * (S / 4608) :=
        Nat.mul_le_mul_left _ hruDiv
      _ = S / 4608 * 4608 := by ring
      _ ≤ S := Nat.div_mul_le_self S 4608
  have hlocal : S ≤ 4608 *
      (frequency P 1 - runnerUpFrequency P 1) := by
    omega
  have hsup : frequency P 1 - runnerUpFrequency P 1 ≤ multiplicityGap P := by
    simpa [multiplicityGap] using
      (Finset.le_sup (f := fun d => frequency P d - runnerUpFrequency P d) htargetMem)
  exact hlocal.trans (Nat.mul_le_mul_left 4608 hsup)

lemma extremalGap_lower_of_ordered_dominance
    (Y : Finset Point) (S : ℕ)
    (hS : 1 ≤ S)
    (hspectrum : 2 ≤ (pointDistanceSpectrum Y).card)
    (htarget : S ≤ 1152 * (orderedRealDistancePairs Y 1).card)
    (hcompetitor : ∀ d : ℝ, d ≠ 1 →
      2304 * (orderedRealDistancePairs Y d).card ≤ S) :
    S ≤ 4608 * extremalGap Y.card := by
  classical
  let P := enumerateFinset Y
  have hAdm : Admissible P := by
    constructor
    · exact enumerateFinset_injective Y
    · rw [distanceValues_enumerateFinset]
      exact hspectrum
  have hatt : AttainableGap Y.card (multiplicityGap P) :=
    ⟨P, hAdm, rfl⟩
  have hbound : multiplicityGap P ≤ Nat.choose Y.card 2 :=
    multiplicityGap_le_choose P
  have hext : multiplicityGap P ≤ extremalGap Y.card := by
    exact Nat.le_findGreatest hbound hatt
  exact (multiplicityGap_lower_of_ordered_dominance Y S hS hspectrum
    htarget hcompetitor).trans (Nat.mul_le_mul_left 4608 hext)

end Erdos959
