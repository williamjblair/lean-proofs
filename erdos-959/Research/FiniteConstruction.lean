import Research.AggregateConstruction
import Research.IndexedPlacement

noncomputable section
namespace Erdos959

/-- Copy indices: one index for each of the `floor(Q/s_K)` copies of block K. -/
def replicatedBlockIndices (U : Finset ℕ) (h Q : ℕ) :
    Finset ((K : Finset ℕ) × ℕ) :=
  (U.powersetCard h).sigma fun K => Finset.range (Q / ∏ p ∈ K, p)

/-- The normalized block attached to a copy index. -/
def replicatedScaledBlock (idx : (K : Finset ℕ) × ℕ) : Finset Point :=
  scaledLatticeBlock (∏ p ∈ idx.1, p) (blockRadius (∏ p ∈ idx.1, p))

lemma sum_replicatedBlock_card
    (U : Finset ℕ) (h Q : ℕ)
    (hsPos : ∀ K ∈ U.powersetCard h, 1 ≤ ∏ p ∈ K, p) :
    (∑ idx ∈ replicatedBlockIndices U h Q, (replicatedScaledBlock idx).card) =
      ∑ K ∈ U.powersetCard h,
        (Q / ∏ p ∈ K, p) * (latticeDisk (blockRadius (∏ p ∈ K, p))).card := by
  rw [replicatedBlockIndices, Finset.sum_sigma]
  apply Finset.sum_congr rfl
  intro K hK
  simp only [replicatedScaledBlock]
  rw [Finset.sum_const]
  simp [card_scaledLatticeBlock (hsPos K hK), nsmul_eq_mul]

lemma sum_replicatedBlock_frequency
    (U : Finset ℕ) (h Q : ℕ) (d : ℝ) :
    (∑ idx ∈ replicatedBlockIndices U h Q,
      (orderedRealDistancePairs (replicatedScaledBlock idx) d).card) =
      aggregateScaledInternalFrequency U h Q d := by
  rw [replicatedBlockIndices, Finset.sum_sigma]
  apply Finset.sum_congr rfl
  intro K hK
  simp only [replicatedScaledBlock]
  rw [Finset.sum_const]
  simp [aggregateScaledInternalFrequency, nsmul_eq_mul]

lemma mem_replicated_indexed_spectrum_iff
    (U : Finset ℕ) (h Q : ℕ) (d : ℝ) :
    d ∈ indexedBlockSpectrum (replicatedBlockIndices U h Q) replicatedScaledBlock ↔
      ∃ K ∈ U.powersetCard h,
        1 ≤ Q / ∏ p ∈ K, p ∧
        d ∈ pointDistanceSpectrum
          (scaledLatticeBlock (∏ p ∈ K, p) (blockRadius (∏ p ∈ K, p))) := by
  constructor
  · intro hd
    rcases Finset.mem_biUnion.mp hd with ⟨idx, hidx, hdidx⟩
    have hm := Finset.mem_sigma.mp hidx
    refine ⟨idx.1, hm.1, ?_, ?_⟩
    · have := Finset.mem_range.mp hm.2
      omega
    · exact hdidx
  · rintro ⟨K, hK, hc, hdK⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨⟨K, 0⟩, ?_, ?_⟩
    · apply Finset.mem_sigma.mpr
      exact ⟨hK, Finset.mem_range.mpr hc⟩
    · exact hdK

/-- Complete finite construction theorem before asymptotic parameter selection.
It produces an actual planar set whose target ordered frequency beats every
competitor by a factor two. -/
theorem exists_finite_scaled_lattice_gap
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
    ∃ Y : Finset Point,
      (U.powersetCard h).card * Q ≤ 1152 * Y.card ∧
      Y.card ≤ 5 * ((U.powersetCard h).card * Q) ∧
      (U.powersetCard h).card * Q * 2 ^ h ≤
        1152 * (orderedRealDistancePairs Y 1).card ∧
      (∀ d : ℝ, d ≠ 1 →
        2304 * (orderedRealDistancePairs Y d).card ≤
          (U.powersetCard h).card * Q * 2 ^ h) := by
  let I := replicatedBlockIndices U h Q
  let blocks : ((K : Finset ℕ) × ℕ) → Finset Point := replicatedScaledBlock
  have hsPos : ∀ K ∈ U.powersetCard h, 1 ≤ ∏ p ∈ K, p := by
    intro K hK
    have hlarge := hsLarge K hK
    omega
  have hsize : ∀ idx ∈ I, (blocks idx).card ≤ 5 * Q := by
    intro idx hidx
    have hm := Finset.mem_sigma.mp hidx
    let s := ∏ p ∈ idx.1, p
    have hsL := hsLarge idx.1 hm.1
    have hsQ := hQ idx.1 hm.1
    have hodd : s % 2 = 1 :=
      prime_one_mod_four_product_odd idx.1 fun q hq =>
        hmod q ((Finset.mem_powersetCard.mp hm.1).1 hq)
    dsimp [blocks, replicatedScaledBlock]
    rw [card_scaledLatticeBlock (hsPos idx.1 hm.1)]
    exact (latticeDisk_size_comparable_to_target s hsL hodd).2.trans
      (Nat.mul_le_mul_left 5 hsQ)
  obtain ⟨Y, hYcard, hYinternal, hYexternal⟩ :=
    exists_isolated_placement_of_indexed_family_bounded I blocks (5 * Q) hsize
  refine ⟨Y, ?_, ?_, ?_, ?_⟩
  · rw [hYcard, show (∑ idx ∈ I, (blocks idx).card) =
        ∑ K ∈ U.powersetCard h,
          (Q / ∏ p ∈ K, p) *
            (latticeDisk (blockRadius (∏ p ∈ K, p))).card by
      exact sum_replicatedBlock_card U h Q hsPos]
    calc
      (U.powersetCard h).card * Q = ∑ _K ∈ U.powersetCard h, Q := by
        rw [Finset.sum_const]
        simp
      _ ≤ ∑ K ∈ U.powersetCard h,
          1152 * ((Q / ∏ p ∈ K, p) *
            (latticeDisk (blockRadius (∏ p ∈ K, p))).card) := by
        apply Finset.sum_le_sum
        intro K hK
        have hodd : (∏ p ∈ K, p) % 2 = 1 :=
          prime_one_mod_four_product_odd K fun q hq =>
            hmod q ((Finset.mem_powersetCard.mp hK).1 hq)
        exact (replicated_block_point_bounds (∏ p ∈ K, p) Q
          (hsLarge K hK) hodd (hQ K hK)).1
      _ = 1152 * ∑ K ∈ U.powersetCard h,
          (Q / ∏ p ∈ K, p) *
            (latticeDisk (blockRadius (∏ p ∈ K, p))).card := by
        rw [Finset.mul_sum]
  · rw [hYcard, show (∑ idx ∈ I, (blocks idx).card) =
        ∑ K ∈ U.powersetCard h,
          (Q / ∏ p ∈ K, p) *
            (latticeDisk (blockRadius (∏ p ∈ K, p))).card by
      exact sum_replicatedBlock_card U h Q hsPos]
    calc
      (∑ K ∈ U.powersetCard h,
        (Q / ∏ p ∈ K, p) *
          (latticeDisk (blockRadius (∏ p ∈ K, p))).card) ≤
          ∑ _K ∈ U.powersetCard h, 5 * Q := by
        apply Finset.sum_le_sum
        intro K hK
        have hodd : (∏ p ∈ K, p) % 2 = 1 :=
          prime_one_mod_four_product_odd K fun q hq =>
            hmod q ((Finset.mem_powersetCard.mp hK).1 hq)
        exact (replicated_block_point_bounds (∏ p ∈ K, p) Q
          (hsLarge K hK) hodd (hQ K hK)).2
      _ = 5 * ((U.powersetCard h).card * Q) := by
        rw [Finset.sum_const]
        simp
        ring
  · have hPowNonempty : (U.powersetCard h).Nonempty := by
      exact Finset.powersetCard_nonempty.mpr hhU
    obtain ⟨K, hK⟩ := hPowNonempty
    have hc : 1 ≤ Q / ∏ p ∈ K, p :=
      (Nat.le_div_iff_mul_le (by have := hsPos K hK; omega)).2 (by simpa using hQ K hK)
    have htargetMemBlock : 1 ∈ pointDistanceSpectrum
        (scaledLatticeBlock (∏ p ∈ K, p) (blockRadius (∏ p ∈ K, p))) := by
      apply (mem_pointDistanceSpectrum_iff_nonempty _ _).mpr
      apply Finset.card_pos.mp
      rw [scaled_target_fiber_card (hsPos K hK)]
      have hpK : ∀ p ∈ K, p.Prime := fun p hpK =>
        hp p ((Finset.mem_powersetCard.mp hK).1 hpK)
      have hmK : ∀ p ∈ K, p % 4 = 1 := fun p hpK =>
        hmod p ((Finset.mem_powersetCard.mp hK).1 hpK)
      have hodd : (∏ p ∈ K, p) % 2 = 1 :=
        prime_one_mod_four_product_odd K hmK
      have hrepTarget := replicated_block_target_frequency K hpK hmK
        (hsLarge K hK) hodd (hQ K hK)
      have hQpos : 0 < Q := lt_of_lt_of_le
        (Finset.prod_pos fun p hpMem => (hpK p hpMem).pos) (hQ K hK)
      have hpositive : 0 < Q * 2 ^ K.card := by positivity
      by_contra hnot
      have hFzero : (orderedDistancePairs
          (latticeDisk (blockRadius (∏ p ∈ K, p))) (∏ p ∈ K, p)).card = 0 := by
        omega
      rw [hFzero] at hrepTarget
      simp at hrepTarget
      exact (Nat.ne_of_gt hQpos) hrepTarget
    have htargetMem : 1 ∈ indexedBlockSpectrum I blocks := by
      change 1 ∈ indexedBlockSpectrum (replicatedBlockIndices U h Q)
        replicatedScaledBlock
      exact (mem_replicated_indexed_spectrum_iff U h Q 1).mpr
        ⟨K, hK, hc, htargetMemBlock⟩
    rw [hYinternal 1 htargetMem]
    have hsumEq : (∑ idx ∈ I,
        (orderedRealDistancePairs (blocks idx) 1).card) =
        aggregateScaledInternalFrequency U h Q 1 :=
      sum_replicatedBlock_frequency U h Q 1
    rw [hsumEq]
    exact aggregate_scaled_target_lower U h Q hp hmod hsLarge hQ
  · intro d hd
    by_cases hdInt : d ∈ indexedBlockSpectrum I blocks
    · rw [hYinternal d hdInt]
      have hsumEq : (∑ idx ∈ I,
          (orderedRealDistancePairs (blocks idx) d).card) =
          aggregateScaledInternalFrequency U h Q d :=
        sum_replicatedBlock_frequency U h Q d
      rw [hsumEq]
      have hdInternal : ∃ K ∈ U.powersetCard h,
          d ∈ pointDistanceSpectrum
            (scaledLatticeBlock (∏ p ∈ K, p) (blockRadius (∏ p ∈ K, p))) := by
        rcases (mem_replicated_indexed_spectrum_iff U h Q d).mp hdInt with
          ⟨K, hK, hc, hdK⟩
        exact ⟨K, hK, hdK⟩
      exact aggregate_scaled_competitor_upper U h Q P d hd hdInternal
        hhU hp hmod hpP z hz hsLarge hQ hbase
    · have hext := hYexternal d hdInt
      calc
        2304 * (orderedRealDistancePairs Y d).card ≤ 2304 * (2 * (5 * Q)) :=
          Nat.mul_le_mul_left _ hext
        _ = 23040 * Q := by ring
        _ ≤ ((U.powersetCard h).card * 2 ^ h) * Q :=
          Nat.mul_le_mul_right Q hcross
        _ = (U.powersetCard h).card * Q * 2 ^ h := by ring

end Erdos959
