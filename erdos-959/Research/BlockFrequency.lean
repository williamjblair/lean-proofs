import Research.BlockRadius
import Research.GaussianRepresentation

namespace Erdos959

lemma splitPrimeProduct_representation_lower_finset
    (K : Finset ℕ) (hp : ∀ p ∈ K, p.Prime)
    (hmod : ∀ p ∈ K, p % 4 = 1) :
    2 ^ K.card ≤ (representationVectors (∏ p ∈ K, p)).card := by
  let p : K → ℕ := fun i => i.1
  have h := splitPrimeProduct_representation_lower p
    (fun i => hp i.1 i.2) (fun i => hmod i.1 i.2)
    (fun _ _ hij => Subtype.ext hij)
  have hprod : (∏ i : K, p i) = ∏ q ∈ K, q := by
    change (∏ x ∈ K.attach, (x : ℕ)) = ∏ q ∈ K, q
    exact Finset.prod_attach K (fun q : ℕ => q)
  rw [hprod] at h
  simpa [p] using h

lemma single_block_target_frequency
    (K : Finset ℕ) (hp : ∀ p ∈ K, p.Prime)
    (hmod : ∀ p ∈ K, p % 4 = 1)
    (hs : 2049 ≤ ∏ p ∈ K, p)
    (hodd : (∏ p ∈ K, p) % 2 = 1) :
    (∏ p ∈ K, p) * 2 ^ K.card ≤
      576 * (orderedDistancePairs
        (latticeDisk (blockRadius (∏ p ∈ K, p))) (∏ p ∈ K, p)).card := by
  let s := ∏ p ∈ K, p
  let R := blockRadius s
  let F := (orderedDistancePairs (latticeDisk R) s).card
  have hR : 32 ≤ R := blockRadius_ge_thirtyTwo s hs
  have hshort : (s : ℝ) ≤ (3 * (R : ℝ) / 2) ^ 2 :=
    (blockRadius_real_target_window s hs hodd).2
  have hsPos : 1 ≤ s := by omega
  have hfreq := target_ordered_pairs_lower s R hsPos hR hshort
  have hrep : 2 ^ K.card ≤ (representationVectors s).card := by
    simpa [s] using splitPrimeProduct_representation_lower_finset K hp hmod
  have htarget : 2 ^ K.card * R ^ 2 ≤ 256 * F := by
    exact (Nat.mul_le_mul_right (R ^ 2) hrep).trans hfreq
  have hsR : 4 * s ≤ 9 * R ^ 2 :=
    (blockRadius_sq_bounds s hs hodd).2
  change s * 2 ^ K.card ≤ 576 * F
  apply Nat.le_of_mul_le_mul_left _ (by norm_num : 0 < 4)
  calc
    4 * (s * 2 ^ K.card) = (4 * s) * 2 ^ K.card := by ring
    _ ≤ (9 * R ^ 2) * 2 ^ K.card := Nat.mul_le_mul_right _ hsR
    _ = 9 * (2 ^ K.card * R ^ 2) := by ring
    _ ≤ 9 * (256 * F) := Nat.mul_le_mul_left _ htarget
    _ = 4 * (576 * F) := by ring

lemma replicated_block_target_frequency
    (K : Finset ℕ) (hp : ∀ p ∈ K, p.Prime)
    (hmod : ∀ p ∈ K, p % 4 = 1)
    (hs : 2049 ≤ ∏ p ∈ K, p)
    (hodd : (∏ p ∈ K, p) % 2 = 1)
    {Q : ℕ} (hQ : (∏ p ∈ K, p) ≤ Q) :
    Q * 2 ^ K.card ≤ 1152 *
      ((Q / (∏ p ∈ K, p)) *
        (orderedDistancePairs
          (latticeDisk (blockRadius (∏ p ∈ K, p))) (∏ p ∈ K, p)).card) := by
  let s := ∏ p ∈ K, p
  let F := (orderedDistancePairs (latticeDisk (blockRadius s)) s).card
  have hsPos : 1 ≤ s := by
    have : 0 < s := Finset.prod_pos fun p hpK => (hp p hpK).pos
    omega
  have hbalance := (floor_ratio_balance hsPos hQ).1
  have hsingle := single_block_target_frequency K hp hmod hs hodd
  change Q * 2 ^ K.card ≤ 1152 * (Q / s * F)
  calc
    Q * 2 ^ K.card ≤ (2 * (Q / s * s)) * 2 ^ K.card :=
      Nat.mul_le_mul_right _ hbalance
    _ = 2 * (Q / s) * (s * 2 ^ K.card) := by ring
    _ ≤ 2 * (Q / s) * (576 * F) := Nat.mul_le_mul_left _ hsingle
    _ = 1152 * (Q / s * F) := by ring

lemma replicated_block_point_bounds
    (s Q : ℕ) (hs : 2049 ≤ s) (hodd : s % 2 = 1) (hQ : s ≤ Q) :
    Q ≤ 1152 * (Q / s * (latticeDisk (blockRadius s)).card) ∧
      Q / s * (latticeDisk (blockRadius s)).card ≤ 5 * Q := by
  have hsPos : 1 ≤ s := by omega
  have hsize := latticeDisk_size_comparable_to_target s hs hodd
  have hbalance := floor_ratio_balance hsPos hQ
  constructor
  · calc
      Q ≤ 2 * (Q / s * s) := hbalance.1
      _ ≤ 2 * (Q / s * (576 * (latticeDisk (blockRadius s)).card)) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hsize.1)
      _ = 1152 * (Q / s * (latticeDisk (blockRadius s)).card) := by ring
  · calc
      Q / s * (latticeDisk (blockRadius s)).card ≤ Q / s * (5 * s) :=
        Nat.mul_le_mul_left _ hsize.2
      _ = 5 * (Q / s * s) := by ring
      _ ≤ 5 * Q := Nat.mul_le_mul_left _ hbalance.2

lemma replicated_block_competitor_frequency
    (s Q t : ℕ) (hs : 2049 ≤ s) (hodd : s % 2 = 1)
    (hQ : s ≤ Q) (ht : 1 ≤ t) :
    (Q / s) * (orderedDistancePairs (latticeDisk (blockRadius s)) t).card ≤
      5 * Q * (representationVectors t).card := by
  have hupper := orderedDistancePairs_upper (latticeDisk (blockRadius s)) t ht
  have hpoints := (replicated_block_point_bounds s Q hs hodd hQ).2
  calc
    (Q / s) * (orderedDistancePairs (latticeDisk (blockRadius s)) t).card ≤
        (Q / s) * ((latticeDisk (blockRadius s)).card *
          (representationVectors t).card) := Nat.mul_le_mul_left _ hupper
    _ = (Q / s * (latticeDisk (blockRadius s)).card) *
        (representationVectors t).card := by ring
    _ ≤ (5 * Q) * (representationVectors t).card :=
      Nat.mul_le_mul_right _ hpoints
    _ = 5 * Q * (representationVectors t).card := by ring

end Erdos959
