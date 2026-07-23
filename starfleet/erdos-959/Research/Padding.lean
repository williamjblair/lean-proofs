import Research.ParameterSupply

noncomputable section
namespace Erdos959

/-- A one-point block used to pad a construction. -/
def paddingSingleton : Finset Point := {(0, 0)}

@[simp] lemma paddingSingleton_card : paddingSingleton.card = 1 := by
  simp [paddingSingleton]

@[simp] lemma paddingSingleton_spectrum : pointDistanceSpectrum paddingSingleton = ∅ := by
  ext d
  simp [paddingSingleton, pointDistanceSpectrum]

@[simp] lemma paddingSingleton_frequency (d : ℝ) :
    (orderedRealDistancePairs paddingSingleton d).card = 0 := by
  rw [← orderedRealDistancePairs_card_eq_zero_of_not_mem]
  simp

/-- Add any prescribed number of generic points. All original distance
frequencies are preserved, while every newly created distance has ordered
frequency at most two (one unordered pair). -/
theorem exists_padding_preserving_spectrum (Y : Finset Point) (r : ℕ) :
    ∃ Z : Finset Point,
      Z.card = Y.card + r ∧
      (∀ d ∈ pointDistanceSpectrum Y,
        (orderedRealDistancePairs Z d).card =
          (orderedRealDistancePairs Y d).card) ∧
      (∀ d ∉ pointDistanceSpectrum Y,
        (orderedRealDistancePairs Z d).card ≤ 2) := by
  induction r with
  | zero =>
      refine ⟨Y, by simp, fun d _ => rfl, ?_⟩
      intro d hd
      rw [orderedRealDistancePairs_card_eq_zero_of_not_mem Y d hd]
      omega
  | succ r ih =>
      obtain ⟨Z, hZcard, hZold, hZnew⟩ := ih
      have hsub : pointDistanceSpectrum paddingSingleton ⊆ pointDistanceSpectrum Y := by
        simp
      obtain ⟨t, hdisj, hprotected, hoff⟩ :=
        exists_globally_avoiding_frequency_step paddingSingleton Z
          (pointDistanceSpectrum Y) hsub
      let W := translatedFinset t paddingSingleton ∪ Z
      refine ⟨W, ?_, ?_, ?_⟩
      · dsimp [W]
        rw [Finset.card_union_of_disjoint hdisj, card_translatedFinset,
          paddingSingleton_card, hZcard]
        omega
      · intro d hd
        dsimp [W]
        rw [hprotected d hd, paddingSingleton_frequency, hZold d hd]
        omega
      · intro d hd
        by_cases hdZ : d ∈ pointDistanceSpectrum Z
        · dsimp [W]
          rw [(hoff d hd).1 hdZ]
          exact hZnew d hd
        · dsimp [W]
          simpa using (hoff d hd).2 hdZ

/-- Exact-cardinality version of a dominant-distance construction. -/
theorem pad_dominant_set_to_exact_card
    (Y : Finset Point) (S T : ℕ)
    (hcard : Y.card ≤ T)
    (hS : 4608 ≤ S)
    (htarget : S ≤ 1152 * (orderedRealDistancePairs Y 1).card)
    (hcomp : ∀ d : ℝ, d ≠ 1 →
      2304 * (orderedRealDistancePairs Y d).card ≤ S) :
    ∃ Z : Finset Point,
      Z.card = T ∧
      S ≤ 1152 * (orderedRealDistancePairs Z 1).card ∧
      (∀ d : ℝ, d ≠ 1 →
        2304 * (orderedRealDistancePairs Z d).card ≤ S) := by
  obtain ⟨Z, hZcard, hpreserve, hnew⟩ :=
    exists_padding_preserving_spectrum Y (T - Y.card)
  have hcardEq : Z.card = T := by omega
  have htargetPos : 0 < (orderedRealDistancePairs Y 1).card := by
    by_contra hn
    have hz : (orderedRealDistancePairs Y 1).card = 0 := by omega
    rw [hz] at htarget
    simp at htarget
    omega
  have hone : 1 ∈ pointDistanceSpectrum Y :=
    (mem_pointDistanceSpectrum_iff_nonempty Y 1).mpr (Finset.card_pos.mp htargetPos)
  refine ⟨Z, hcardEq, ?_, ?_⟩
  · rw [hpreserve 1 hone]
    exact htarget
  · intro d hd
    by_cases hdY : d ∈ pointDistanceSpectrum Y
    · rw [hpreserve d hdY]
      exact hcomp d hd
    · calc
        2304 * (orderedRealDistancePairs Z d).card ≤ 2304 * 2 :=
          Nat.mul_le_mul_left 2304 (hnew d hdY)
        _ ≤ S := hS

end Erdos959
