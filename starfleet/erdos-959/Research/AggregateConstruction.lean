import Research.ScaledClass
import Research.NumericParameters
import Research.BlockFrequency

noncomputable section
namespace Erdos959

lemma prime_one_mod_four_product_odd
    (K : Finset ℕ) (hmod : ∀ p ∈ K, p % 4 = 1) :
    (∏ p ∈ K, p) % 2 = 1 := by
  have hcong : (∏ p ∈ K, p) ≡ 1 [MOD 2] :=
    Nat.ModEq.prod_one fun p hp => by
      change p % 2 = 1 % 2
      have := hmod p hp
      omega
  exact hcong

lemma reduced_relation_transfer
    {s₀ t₀ s t A D : ℕ}
    (hs₀ : 1 ≤ s₀) (hs : 1 ≤ s)
    (href : D * t₀ = A * s₀)
    (heq : (t₀ : ℝ) / s₀ = (t : ℝ) / s) :
    D * t = A * s := by
  have hcross : s * t₀ = s₀ * t :=
    (normalized_distance_eq_iff_crossmul hs₀ hs).mp heq
  have hcancel : s₀ * (D * t) = s₀ * (A * s) := by
    calc
      s₀ * (D * t) = D * (s₀ * t) := by ring
      _ = D * (s * t₀) := by rw [← hcross]
      _ = s * (D * t₀) := by ring
      _ = s * (A * s₀) := by rw [href]
      _ = s₀ * (A * s) := by ring
  exact Nat.eq_of_mul_eq_mul_left hs₀ hcancel

/-- Weighted sum of a real internal frequency over all normalized lattice
blocks, with replication weight `floor(Q/s_K)`. -/
def aggregateScaledInternalFrequency
    (U : Finset ℕ) (h Q : ℕ) (d : ℝ) : ℕ :=
  ∑ K ∈ U.powersetCard h,
    (Q / ∏ p ∈ K, p) *
      (orderedRealDistancePairs
        (scaledLatticeBlock (∏ p ∈ K, p)
          (blockRadius (∏ p ∈ K, p))) d).card

lemma aggregate_scaled_target_lower
    (U : Finset ℕ) (h Q : ℕ)
    (hp : ∀ p ∈ U, p.Prime)
    (hmod : ∀ p ∈ U, p % 4 = 1)
    (hsLarge : ∀ K ∈ U.powersetCard h, 2049 ≤ ∏ p ∈ K, p)
    (hQ : ∀ K ∈ U.powersetCard h, (∏ p ∈ K, p) ≤ Q) :
    (U.powersetCard h).card * Q * 2 ^ h ≤
      1152 * aggregateScaledInternalFrequency U h Q 1 := by
  have hpoint : ∀ K ∈ U.powersetCard h,
      Q * 2 ^ h ≤ 1152 *
        ((Q / ∏ p ∈ K, p) *
          (orderedRealDistancePairs
            (scaledLatticeBlock (∏ p ∈ K, p)
              (blockRadius (∏ p ∈ K, p))) 1).card) := by
    intro K hK
    have hKcard : K.card = h := Finset.mem_powersetCard.mp hK |>.2
    have hpK : ∀ p ∈ K, p.Prime := fun p hpK =>
      hp p (Finset.mem_powersetCard.mp hK |>.1 hpK)
    have hmK : ∀ p ∈ K, p % 4 = 1 := fun p hpK =>
      hmod p (Finset.mem_powersetCard.mp hK |>.1 hpK)
    have hodd : (∏ p ∈ K, p) % 2 = 1 :=
      prime_one_mod_four_product_odd K hmK
    rw [scaled_target_fiber_card (by
      have hprodPos : 0 < ∏ p ∈ K, p :=
        Finset.prod_pos fun p hpMem => (hpK p hpMem).pos
      omega)]
    simpa [hKcard] using replicated_block_target_frequency
      K hpK hmK (hsLarge K hK) hodd (hQ K hK)
  change (U.powersetCard h).card * Q * 2 ^ h ≤
    1152 * ∑ K ∈ U.powersetCard h,
      (Q / ∏ p ∈ K, p) *
        (orderedRealDistancePairs
          (scaledLatticeBlock (∏ p ∈ K, p)
            (blockRadius (∏ p ∈ K, p))) 1).card
  calc
    (U.powersetCard h).card * Q * 2 ^ h =
        ∑ _K ∈ U.powersetCard h, Q * 2 ^ h := by
      rw [Finset.sum_const]
      simp [nsmul_eq_mul]
      ring
    _ ≤ ∑ K ∈ U.powersetCard h,
        1152 * ((Q / ∏ p ∈ K, p) *
          (orderedRealDistancePairs
            (scaledLatticeBlock (∏ p ∈ K, p)
              (blockRadius (∏ p ∈ K, p))) 1).card) :=
      Finset.sum_le_sum fun K hK => hpoint K hK
    _ = 1152 * ∑ K ∈ U.powersetCard h,
        (Q / ∏ p ∈ K, p) *
          (orderedRealDistancePairs
            (scaledLatticeBlock (∏ p ∈ K, p)
              (blockRadius (∏ p ∈ K, p))) 1).card := by
      rw [Finset.mul_sum]

/-- Under the one numerical base condition, every non-target normalized class
has at most half the target scale, uniformly over its reduced denominator. -/
theorem aggregate_scaled_competitor_upper
    (U : Finset ℕ) (h Q P : ℕ) (d : ℝ)
    (hdTarget : d ≠ 1)
    (hdInternal : ∃ K ∈ U.powersetCard h,
      d ∈ pointDistanceSpectrum
        (scaledLatticeBlock (∏ p ∈ K, p) (blockRadius (∏ p ∈ K, p))))
    (hhU : h ≤ U.card)
    (hp : ∀ p ∈ U, p.Prime)
    (hmod : ∀ p ∈ U, p % 4 = 1)
    (hpP : ∀ p ∈ U, p ≤ P)
    (z : ℕ → GaussianInt)
    (hz : ∀ p ∈ U, (z p).norm.natAbs = p)
    (hsLarge : ∀ K ∈ U.powersetCard h, 2049 ≤ ∏ p ∈ K, p)
    (hQ : ∀ K ∈ U.powersetCard h, (∏ p ∈ K, p) ≤ Q)
    (hbase : (128 * 11520 ^ 2) * P * h ^ 2 ≤ 4 * U.card ^ 2) :
    2304 * aggregateScaledInternalFrequency U h Q d ≤
      (U.powersetCard h).card * Q * 2 ^ h := by
  obtain ⟨K₀, hK₀, hdK₀⟩ := hdInternal
  let s₀ := ∏ p ∈ K₀, p
  have hs₀Pos : 1 ≤ s₀ := by
    have hpp : ∀ p ∈ K₀, p.Prime := fun p hpK =>
      hp p (Finset.mem_powersetCard.mp hK₀ |>.1 hpK)
    have : 0 < s₀ := Finset.prod_pos fun p hpK => (hpp p hpK).pos
    omega
  obtain ⟨t₀, ht₀, hdRatio, hfreq₀⟩ :=
    exists_integer_class_of_mem_scaled_spectrum hs₀Pos (blockRadius s₀) hdK₀
  obtain ⟨A, D, hcop, href, hDpos⟩ := exists_reduced_natural_ratio t₀ s₀ hs₀Pos
  have hpair₀ : (orderedDistancePairs (latticeDisk (blockRadius s₀)) t₀).Nonempty := by
    have hscaled : (orderedRealDistancePairs
        (scaledLatticeBlock s₀ (blockRadius s₀)) d).Nonempty :=
      (mem_pointDistanceSpectrum_iff_nonempty _ _).mp hdK₀
    have hcardPos : 0 < (orderedRealDistancePairs
        (scaledLatticeBlock s₀ (blockRadius s₀)) d).card := Finset.card_pos.mpr hscaled
    rw [hfreq₀] at hcardPos
    exact Finset.card_pos.mp hcardPos
  obtain ⟨xy₀, hxy₀⟩ := hpair₀
  have hm₀ := (mem_orderedDistancePairs_iff xy₀.1 xy₀.2).mp hxy₀
  have htNe : t₀ ≠ s₀ := by
    intro heq
    apply hdTarget
    rw [hdRatio, heq]
    exact div_self (by positivity)
  have hodd₀ : s₀ % 2 = 1 :=
    prime_one_mod_four_product_odd K₀ fun q hq =>
      hmod q (Finset.mem_powersetCard.mp hK₀ |>.1 hq)
  have hbounds := reduced_block_competitor_bounds s₀ (hsLarge K₀ hK₀) hodd₀
    hm₀.1 hm₀.2.1 hm₀.2.2.1 hm₀.2.2.2 hDpos href
  have hAPos : 1 ≤ A := hbounds.1
  have hAlt : A < 2 * D := hbounds.2.1
  have hDgt : 1 < D := hbounds.2.2 htNe
  have hDdiv : D ∣ s₀ := reduced_denominator_dvd_target hcop href
  have hpK₀ : ∀ p ∈ K₀, p.Prime := fun p hpK =>
    hp p (Finset.mem_powersetCard.mp hK₀ |>.1 hpK)
  obtain ⟨J, hJK₀, hD⟩ :=
    divisor_of_prime_finset_product_has_support K₀ hpK₀ (by omega) hDdiv
  have hJU : J ⊆ U := hJK₀.trans (Finset.mem_powersetCard.mp hK₀).1
  have hjPos : 1 ≤ J.card := by
    by_contra hj
    have hJempty : J = ∅ := Finset.card_eq_zero.mp (by omega)
    rw [hJempty] at hD
    simp at hD
    omega
  have hJh : J.card ≤ h := by
    rw [← (Finset.mem_powersetCard.mp hK₀).2]
    exact Finset.card_le_card hJK₀
  have hAltJ : A < 2 * ∏ p ∈ J, p := by rw [← hD]; exact hAlt
  have hnumeric := support_numeric_condition U J (fun p => p) P h A
    hJU hjPos hpP hAltJ hbase
  have hsumRep := competitor_sum_le_target_of_numeric
    J U h A (fun p => p) z hJU hjPos hJh hhU hAPos hp hz hnumeric
  let S := ∑ K ∈ (U.powersetCard h).filter (J ⊆ ·),
    (representationVectors (A * ∏ p ∈ K \ J, p)).card
  have hpoint : ∀ K ∈ U.powersetCard h,
      (Q / ∏ p ∈ K, p) *
        (orderedRealDistancePairs
          (scaledLatticeBlock (∏ p ∈ K, p)
            (blockRadius (∏ p ∈ K, p))) d).card ≤
      if J ⊆ K then 5 * Q *
        (representationVectors (A * ∏ p ∈ K \ J, p)).card else 0 := by
    intro K hK
    let s := ∏ p ∈ K, p
    have hsPos : 1 ≤ s := by
      have hpK : ∀ p ∈ K, p.Prime := fun p hpK =>
        hp p (Finset.mem_powersetCard.mp hK |>.1 hpK)
      have hprodPos : 0 < s :=
        Finset.prod_pos fun p hpMem => (hpK p hpMem).pos
      omega
    by_cases hdK : d ∈ pointDistanceSpectrum
        (scaledLatticeBlock s (blockRadius s))
    · obtain ⟨t, ht, hdKRatio, hfreqK⟩ :=
        exists_integer_class_of_mem_scaled_spectrum hsPos (blockRadius s) hdK
      have hequal : (t₀ : ℝ) / s₀ = (t : ℝ) / s := by rw [← hdRatio, ← hdKRatio]
      have htrans : D * t = A * s :=
        reduced_relation_transfer hs₀Pos hsPos href hequal
      have hKU := (Finset.mem_powersetCard.mp hK).1
      have hclass := equal_scaled_class_forces_support_and_unscaled_value
        U J K (fun p => p) hJU hKU hp (fun _ _ _ _ h => h)
        hcop hD htrans (by omega)
      rw [if_pos hclass.1]
      have hodd : s % 2 = 1 :=
        prime_one_mod_four_product_odd K fun q hq => hmod q (hKU hq)
      rw [hfreqK, hclass.2]
      exact replicated_block_competitor_frequency s Q
        (A * ∏ p ∈ K \ J, p) (hsLarge K hK) hodd (hQ K hK) (by
          have hprodPos : 0 < ∏ p ∈ K \ J, p :=
            Finset.prod_pos fun q hq => (hp q (hKU (Finset.mem_sdiff.mp hq).1)).pos
          exact Nat.mul_pos (by omega) hprodPos)
    · have hzero := orderedRealDistancePairs_card_eq_zero_of_not_mem
        (scaledLatticeBlock s (blockRadius s)) d hdK
      rw [hzero]
      simp
  change 2304 * ∑ K ∈ U.powersetCard h,
      (Q / ∏ p ∈ K, p) *
        (orderedRealDistancePairs
          (scaledLatticeBlock (∏ p ∈ K, p)
            (blockRadius (∏ p ∈ K, p))) d).card ≤ _
  have hagg : (∑ K ∈ U.powersetCard h,
      (Q / ∏ p ∈ K, p) *
        (orderedRealDistancePairs
          (scaledLatticeBlock (∏ p ∈ K, p)
            (blockRadius (∏ p ∈ K, p))) d).card) ≤ 5 * Q * S := by
    calc
      _ ≤ ∑ K ∈ U.powersetCard h,
          if J ⊆ K then 5 * Q *
            (representationVectors (A * ∏ p ∈ K \ J, p)).card else 0 :=
        Finset.sum_le_sum fun K hK => hpoint K hK
      _ = 5 * Q * S := by
        dsimp [S]
        rw [← Finset.sum_filter]
        rw [Finset.mul_sum]
  calc
    2304 * (∑ K ∈ U.powersetCard h,
      (Q / ∏ p ∈ K, p) *
        (orderedRealDistancePairs
          (scaledLatticeBlock (∏ p ∈ K, p)
            (blockRadius (∏ p ∈ K, p))) d).card) ≤
        2304 * (5 * Q * S) := Nat.mul_le_mul_left _ hagg
    _ = Q * (11520 * S) := by ring
    _ ≤ Q * ((U.powersetCard h).card * 2 ^ h) :=
      Nat.mul_le_mul_left Q hsumRep
    _ = (U.powersetCard h).card * Q * 2 ^ h := by ring

end Erdos959
