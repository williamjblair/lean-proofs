import Research.ScaledFrequency
import Research.PrimeSupport
import Research.CompetitorRatio

noncomputable section
namespace Erdos959

lemma exists_integer_class_of_mem_scaled_spectrum
    {s : ℕ} (hs : 1 ≤ s) (R : ℕ) {d : ℝ}
    (hd : d ∈ pointDistanceSpectrum (scaledLatticeBlock s R)) :
    ∃ t : ℕ, 1 ≤ t ∧ d = (t : ℝ) / s ∧
      (orderedRealDistancePairs (scaledLatticeBlock s R) d).card =
        (orderedDistancePairs (latticeDisk R) t).card := by
  obtain ⟨uv, huv⟩ := (mem_pointDistanceSpectrum_iff_nonempty _ _).mp hd
  have hm := Finset.mem_filter.mp huv
  have hp := Finset.mem_product.mp hm.1
  rcases Finset.mem_image.mp hp.1 with ⟨x, hx, hxu⟩
  rcases Finset.mem_image.mp hp.2 with ⟨y, hy, hyv⟩
  have hxy : x ≠ y := by
    intro h
    apply hm.2.1
    rw [← hxu, ← hyv, h]
  have hnormPos : 0 < intNormSq (y - x) := positive_intNormSq_of_ne x y hxy
  let t := (intNormSq (y - x)).toNat
  have ht : 1 ≤ t := by
    dsimp [t]
    omega
  have hnorm : (t : ℤ) = intNormSq (y - x) := by
    dsimp [t]
    rw [Int.toNat_of_nonneg (le_of_lt hnormPos)]
  have hdRatio : d = (t : ℝ) / s := by
    rw [← hm.2.2, ← hxu, ← hyv, sqDist_scaledIntPoint_ordered hs]
    congr 1
    exact_mod_cast hnorm.symm
  refine ⟨t, ht, hdRatio, ?_⟩
  rw [hdRatio]
  exact scaled_ordered_fiber_card hs R t

lemma quotient_class_unscaled_distance
    {α : Type*} [DecidableEq α]
    (p : α → ℕ) (J K : Finset α) (hJK : J ⊆ K)
    {A D t : ℕ}
    (hD : D = ∏ i ∈ J, p i)
    (hDt : D * t = A * ∏ i ∈ K, p i)
    (hDpos : 0 < D) :
    t = A * ∏ i ∈ K \ J, p i := by
  have hsplit := Finset.prod_sdiff (f := p) hJK
  have heq : D * t = D * (A * ∏ i ∈ K \ J, p i) := by
    calc
      D * t = A * ∏ i ∈ K, p i := hDt
      _ = A * ((∏ i ∈ K \ J, p i) * ∏ i ∈ J, p i) := by rw [hsplit]
      _ = D * (A * ∏ i ∈ K \ J, p i) := by rw [hD]; ring
  exact Nat.eq_of_mul_eq_mul_left hDpos heq

/-- A fixed reduced denominator support controls every block in which the same
normalized class occurs. -/
lemma equal_scaled_class_forces_support_and_unscaled_value
    {α : Type*} [DecidableEq α]
    (U J K : Finset α) (p : α → ℕ)
    (hJU : J ⊆ U) (hKU : K ⊆ U)
    (hp : ∀ i ∈ U, (p i).Prime)
    (hinj : Set.InjOn p U)
    {A D t : ℕ}
    (hcop : D.Coprime A)
    (hD : D = ∏ i ∈ J, p i)
    (hDt : D * t = A * ∏ i ∈ K, p i)
    (hDpos : 0 < D) :
    J ⊆ K ∧ t = A * ∏ i ∈ K \ J, p i := by
  have hDdiv : D ∣ ∏ i ∈ K, p i :=
    reduced_denominator_dvd_target hcop hDt
  have hJK : J ⊆ K := by
    intro i hiJ
    have hpi : (p i).Prime := hp i (hJU hiJ)
    have hpidD : p i ∣ D := by
      rw [hD]
      exact Finset.dvd_prod_of_mem p hiJ
    have hpidK : p i ∣ ∏ k ∈ K, p k := hpidD.trans hDdiv
    rcases (Prime.dvd_finsetProd_iff hpi.prime p).mp hpidK with ⟨k, hk, hpik⟩
    have heq : p i = p k :=
      (Nat.prime_dvd_prime_iff_eq hpi (hp k (hKU hk))).mp hpik
    have hik : i = k := hinj (hJU hiJ) (hKU hk) heq
    simpa [hik] using hk
  exact ⟨hJK, quotient_class_unscaled_distance p J K hJK hD hDt hDpos⟩

end Erdos959
