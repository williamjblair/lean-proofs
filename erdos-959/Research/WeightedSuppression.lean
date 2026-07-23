import Research.Suppression
import Research.GaussianRepresentation

namespace Erdos959

/-- Root-free aggregate suppression over all `h`-subsets containing a fixed
`j`-subset. -/
lemma weighted_containing_family_sq_bound
    {α : Type*} [DecidableEq α]
    (J U : Finset α) (h A : ℕ)
    (r : Finset α → ℕ)
    (hJU : J ⊆ U) (hJh : J.card ≤ h) (hhU : h ≤ U.card)
    (hr : ∀ K ∈ (U.powersetCard h).filter (J ⊆ ·),
      r K ^ 2 ≤ 64 * A * 4 ^ (h - J.card)) :
    (U.card ^ J.card *
        ∑ K ∈ (U.powersetCard h).filter (J ⊆ ·), r K) ^ 2 ≤
      (h ^ J.card * (U.powersetCard h).card) ^ 2 *
        (64 * A * 4 ^ (h - J.card)) := by
  let F := (U.powersetCard h).filter (J ⊆ ·)
  let L := 64 * A * 4 ^ (h - J.card)
  have hCauchy : (∑ K ∈ F, r K) ^ 2 ≤ F.card * ∑ K ∈ F, r K ^ 2 :=
    sq_sum_le_card_mul_sum_sq
  have hsumSq : ∑ K ∈ F, r K ^ 2 ≤ F.card * L := by
    calc
      ∑ K ∈ F, r K ^ 2 ≤ ∑ _K ∈ F, L := by
        exact Finset.sum_le_sum fun K hK => hr K hK
      _ = F.card * L := by simp
  have hsum : (∑ K ∈ F, r K) ^ 2 ≤ F.card ^ 2 * L := by
    calc
      (∑ K ∈ F, r K) ^ 2 ≤ F.card * ∑ K ∈ F, r K ^ 2 := hCauchy
      _ ≤ F.card * (F.card * L) := Nat.mul_le_mul_left _ hsumSq
      _ = F.card ^ 2 * L := by ring
  have hcontain : U.card ^ J.card * F.card ≤
      h ^ J.card * (U.powersetCard h).card := by
    exact (containing_subsets_exact_and_suppressed J U h hJU hJh hhU).2
  calc
    (U.card ^ J.card * ∑ K ∈ F, r K) ^ 2 =
        (U.card ^ J.card) ^ 2 * (∑ K ∈ F, r K) ^ 2 := by ring
    _ ≤ (U.card ^ J.card) ^ 2 * (F.card ^ 2 * L) :=
      Nat.mul_le_mul_left _ hsum
    _ = (U.card ^ J.card * F.card) ^ 2 * L := by ring
    _ ≤ (h ^ J.card * (U.powersetCard h).card) ^ 2 * L := by
      exact Nat.mul_le_mul_right L (Nat.pow_le_pow_left hcontain 2)

theorem splitCompetitor_aggregate_sq_bound
    {α : Type*} [DecidableEq α]
    (J U : Finset α) (h A : ℕ)
    (p : α → ℕ) (z : α → GaussianInt)
    (hJU : J ⊆ U) (hJh : J.card ≤ h) (hhU : h ≤ U.card)
    (hA : 1 ≤ A)
    (hp : ∀ i ∈ U, (p i).Prime)
    (hz : ∀ i ∈ U, (z i).norm.natAbs = p i) :
    (U.card ^ J.card *
      ∑ K ∈ (U.powersetCard h).filter (J ⊆ ·),
        (representationVectors (A * ∏ i ∈ K \ J, p i)).card) ^ 2 ≤
      (h ^ J.card * (U.powersetCard h).card) ^ 2 *
        (64 * A * 4 ^ (h - J.card)) := by
  apply weighted_containing_family_sq_bound J U h A
    (fun K => (representationVectors (A * ∏ i ∈ K \ J, p i)).card)
    hJU hJh hhU
  intro K hK
  have hKdata := Finset.mem_filter.mp hK
  have hKpow := Finset.mem_powersetCard.mp hKdata.1
  have hKsub : K ⊆ U := hKpow.1
  have hKcard : K.card = h := hKpow.2
  have hJK : J ⊆ K := hKdata.2
  have hrem : (K \ J).card = h - J.card := by
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hJK, hKcard]
  have hupper := representationVectors_mul_splitProduct_upper
    (K \ J) p z
    (by intro i hi; exact hp i (hKsub (Finset.mem_sdiff.mp hi).1))
    (by intro i hi; exact hz i (hKsub (Finset.mem_sdiff.mp hi).1))
    A hA
  have hsquare := Nat.pow_le_pow_left hupper 2
  calc
    (representationVectors (A * ∏ i ∈ K \ J, p i)).card ^ 2 ≤
        ((representationVectors A).card * 2 ^ (K \ J).card) ^ 2 := hsquare
    _ = (representationVectors A).card ^ 2 * 4 ^ (K \ J).card := by
      simp only [mul_pow]
      rw [show (4 : ℕ) = 2 * 2 by norm_num, mul_pow]
      ring
    _ ≤ (64 * A) * 4 ^ (K \ J).card :=
      Nat.mul_le_mul_right _ (representationVectors_card_sq_le A hA)
    _ = 64 * A * 4 ^ (h - J.card) := by rw [hrem]

lemma competitor_sum_le_target_of_numeric
    {α : Type*} [DecidableEq α]
    (J U : Finset α) (h A : ℕ)
    (p : α → ℕ) (z : α → GaussianInt)
    (hJU : J ⊆ U) (hjPos : 1 ≤ J.card)
    (hJh : J.card ≤ h) (hhU : h ≤ U.card) (hA : 1 ≤ A)
    (hp : ∀ i ∈ U, (p i).Prime)
    (hz : ∀ i ∈ U, (z i).norm.natAbs = p i)
    (hnumeric :
      11520 ^ 2 * (64 * A) * h ^ (2 * J.card) ≤
        U.card ^ (2 * J.card) * 4 ^ J.card) :
    11520 *
      (∑ K ∈ (U.powersetCard h).filter (J ⊆ ·),
        (representationVectors (A * ∏ i ∈ K \ J, p i)).card) ≤
      (U.powersetCard h).card * 2 ^ h := by
  let S := ∑ K ∈ (U.powersetCard h).filter (J ⊆ ·),
    (representationVectors (A * ∏ i ∈ K \ J, p i)).card
  let B := (U.powersetCard h).card
  let k := U.card
  let j := J.card
  have hkPos : 0 < k := by omega
  have hmaster := splitCompetitor_aggregate_sq_bound
    J U h A p z hJU hJh hhU hA hp hz
  change (k ^ j * S) ^ 2 ≤ (h ^ j * B) ^ 2 * (64 * A * 4 ^ (h - j)) at hmaster
  change 11520 ^ 2 * (64 * A) * h ^ (2 * j) ≤
    k ^ (2 * j) * 4 ^ j at hnumeric
  have hcross : k ^ (2 * j) * (11520 * S) ^ 2 ≤
      k ^ (2 * j) * (B * 2 ^ h) ^ 2 := by
    calc
      k ^ (2 * j) * (11520 * S) ^ 2 =
          11520 ^ 2 * (k ^ j * S) ^ 2 := by ring
      _ ≤ 11520 ^ 2 *
          ((h ^ j * B) ^ 2 * (64 * A * 4 ^ (h - j))) :=
            Nat.mul_le_mul_left _ hmaster
      _ = B ^ 2 * 4 ^ (h - j) *
          (11520 ^ 2 * (64 * A) * h ^ (2 * j)) := by ring
      _ ≤ B ^ 2 * 4 ^ (h - j) * (k ^ (2 * j) * 4 ^ j) :=
        Nat.mul_le_mul_left _ hnumeric
      _ = k ^ (2 * j) * B ^ 2 * (4 ^ (h - j) * 4 ^ j) := by ring
      _ = k ^ (2 * j) * B ^ 2 * 4 ^ h := by
        rw [show 4 ^ (h - j) * 4 ^ j = 4 ^ h by
          rw [← pow_add, Nat.sub_add_cancel hJh]]
      _ = k ^ (2 * j) * (B * 2 ^ h) ^ 2 := by
        rw [show (4 : ℕ) = 2 * 2 by norm_num, mul_pow]
        ring
  have hsquare : (11520 * S) ^ 2 ≤ (B * 2 ^ h) ^ 2 :=
    Nat.le_of_mul_le_mul_left hcross (pow_pos hkPos _)
  exact (Nat.pow_le_pow_iff_left (by norm_num : (2 : ℕ) ≠ 0)).mp hsquare

end Erdos959
