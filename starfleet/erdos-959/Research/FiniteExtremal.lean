import Research.FiniteConstruction
import Research.GapExtraction
import Research.Admissibility

noncomputable section
namespace Erdos959

lemma orderedRealDistancePairs_card_le_sq (Y : Finset Point) (d : ℝ) :
    (orderedRealDistancePairs Y d).card ≤ Y.card ^ 2 := by
  calc
    (orderedRealDistancePairs Y d).card ≤ (Y.product Y).card :=
      Finset.card_filter_le _ _
    _ = Y.card ^ 2 := by simp [pow_two]

/-- The finite construction stated directly as a lower bound for the faithful
extremal quantity. -/
theorem finite_parameters_imply_extremal_gap
    (U : Finset ℕ) (h Q P : ℕ)
    (hhU : h ≤ U.card)
    (hp : ∀ p ∈ U, p.Prime)
    (hmod : ∀ p ∈ U, p % 4 = 1)
    (hpP : ∀ p ∈ U, p ≤ P)
    (z : ℕ → GaussianInt)
    (hz : ∀ p ∈ U, (z p).norm.natAbs = p)
    (hsLarge : ∀ K ∈ U.powersetCard h, 2049 ≤ ∏ p ∈ K, p)
    (hQ : ∀ K ∈ U.powersetCard h, (∏ p ∈ K, p) ≤ Q)
    (hbase : (128 * 11520 ^ 2) * P * h ^ 2 ≤ 4 * U.card ^ 2)
    (hcross : 23040 ≤ (U.powersetCard h).card * 2 ^ h) :
    ∃ N : ℕ,
      (U.powersetCard h).card * Q ≤ 1152 * N ∧
      N ≤ 5 * ((U.powersetCard h).card * Q) ∧
      N * 2 ^ h ≤ 23040 * extremalGap N := by
  obtain ⟨Y, hlowerN, hupperN, htarget, hcomp⟩ :=
    exists_finite_scaled_lattice_gap U h Q P hhU hp hmod hpP z hz
      hsLarge hQ hbase hcross
  let S := (U.powersetCard h).card * Q * 2 ^ h
  have hPowNonempty : (U.powersetCard h).Nonempty :=
    Finset.powersetCard_nonempty.mpr hhU
  obtain ⟨K, hK⟩ := hPowNonempty
  have hQpos : 1 ≤ Q := by
    have hs := hsLarge K hK
    have hsq := hQ K hK
    omega
  have hSlarge : 23040 ≤ S := by
    dsimp [S]
    calc
      23040 ≤ (U.powersetCard h).card * 2 ^ h := hcross
      _ ≤ ((U.powersetCard h).card * 2 ^ h) * Q := by
        exact Nat.le_mul_of_pos_right _ hQpos
      _ = (U.powersetCard h).card * Q * 2 ^ h := by ring
  have hYfour : 4 ≤ Y.card := by
    by_contra hnot
    have hYle : Y.card ≤ 3 := by omega
    have hsq : Y.card ^ 2 ≤ 3 ^ 2 := Nat.pow_le_pow_left hYle 2
    have hfreqSq := orderedRealDistancePairs_card_le_sq Y 1
    have : S ≤ 1152 * (Y.card ^ 2) := htarget.trans
      (Nat.mul_le_mul_left 1152 hfreqSq)
    norm_num at hsq
    omega
  have hspectrum : 2 ≤ (pointDistanceSpectrum Y).card := by
    rw [← distanceValues_enumerateFinset]
    exact distanceValues_card_ge_two_of_four_le hYfour _
      (enumerateFinset_injective Y)
  have hSpos : 1 ≤ S := by omega
  have hext : S ≤ 4608 * extremalGap Y.card :=
    extremalGap_lower_of_ordered_dominance Y S hSpos hspectrum htarget hcomp
  refine ⟨Y.card, hlowerN, hupperN, ?_⟩
  calc
    Y.card * 2 ^ h ≤ 5 * ((U.powersetCard h).card * Q) * 2 ^ h :=
      Nat.mul_le_mul_right _ hupperN
    _ = 5 * S := by dsimp [S]; ring
    _ ≤ 5 * (4608 * extremalGap Y.card) := Nat.mul_le_mul_left 5 hext
    _ = 23040 * extremalGap Y.card := by ring

end Erdos959
