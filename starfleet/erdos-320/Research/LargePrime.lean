import Research.Partition
import Research.SubsetSums

/-!
# Denominator blocks for the large-prime recurrence

This file connects the zero-based definition of `S(N)` to positive denominator
sets and proves that a block of multiples of a nonzero integer has the same
number of reciprocal subset sums as its scaled-down interval.
-/

namespace Research

open scoped Pointwise

/-- Reciprocal weight on a positive denominator. (Its value at zero is harmless
for the generic definition but zero is never put in our denominator sets.) -/
def reciprocalWeight (n : ℕ) : ℚ := (1 : ℚ) / n

/-- Distinct reciprocal subset sums using the positive denominators `1,...,N`. -/
def denominatorSubsetSums (N : ℕ) : Finset ℚ :=
  subsetSumValues reciprocalWeight (Finset.Icc 1 N)

/-- The positive-denominator presentation agrees exactly with the pinned
zero-based presentation of Erdős Problem 320. -/
theorem denominatorSubsetSums_eq (N : ℕ) :
    denominatorSubsetSums N = reciprocalSubsetSums N := by
  have hIcc : Finset.Icc 1 N = (Finset.range N).image Nat.succ := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_image, Finset.mem_range,
      Nat.succ_eq_add_one]
    constructor
    · rintro ⟨hn1, hnN⟩
      refine ⟨n - 1, by omega, by omega⟩
    · rintro ⟨a, ha, rfl⟩
      omega
  rw [denominatorSubsetSums, subsetSumValues, hIcc, Finset.powerset_image,
    Finset.image_image, reciprocalSubsetSums]
  apply Finset.image_congr
  intro A hA
  change A ∈ (Finset.range N).powerset at hA
  rw [Finset.mem_powerset] at hA
  simp only [Function.comp_apply]
  rw [Finset.sum_image]
  · simp [reciprocalSubsetSum, reciprocalWeight, Nat.succ_eq_add_one]
  · intro a ha b hb hab
    exact Nat.succ.inj hab

/-- In particular, its cardinality is `S(N)`. -/
theorem card_denominatorSubsetSums (N : ℕ) :
    (denominatorSubsetSums N).card = S N := by
  rw [denominatorSubsetSums_eq, S]

/-- The block `p,2p,...,floor(N/p)p`. -/
def multipleBlock (N p : ℕ) : Finset ℕ :=
  (Finset.Icc 1 (N / p)).image (fun k => p * k)

/-- Blocks belonging to distinct primes above `Q` are disjoint as soon as
`N ≤ Q²`: a common denominator would be divisible by their product, which is
both larger than `Q²` and at most `N`. -/
theorem multipleBlock_disjoint {N Q p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpQ : Q < p) (hqQ : Q < q)
    (hpq : p ≠ q) (hNQ : N ≤ Q * Q) :
    Disjoint (multipleBlock N p) (multipleBlock N q) := by
  rw [Finset.disjoint_left]
  intro n hnp hnq
  rw [multipleBlock, Finset.mem_image] at hnp hnq
  obtain ⟨a, ha, han⟩ := hnp
  obtain ⟨b, hb, hbn⟩ := hnq
  have haLe : a ≤ N / p := (Finset.mem_Icc.mp ha).2
  have hbLe : b ≤ N / q := (Finset.mem_Icc.mp hb).2
  have haPos : 0 < a :=
    lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp ha).1
  have hnPos : 0 < n := by
    rw [← han]
    exact Nat.mul_pos hp.pos haPos
  have hnN : n ≤ N := by
    rw [← han]
    have := (Nat.le_div_iff_mul_le hp.pos).mp haLe
    simpa [Nat.mul_comm] using this
  have hpd : p ∣ n := ⟨a, han.symm⟩
  have hqd : q ∣ n := ⟨b, hbn.symm⟩
  have hpqCoprime : p.Coprime q := (Nat.coprime_primes hp hq).mpr hpq
  have hpqd : p * q ∣ n := hpqCoprime.mul_dvd_of_dvd_of_dvd hpd hqd
  have hpqLe : p * q ≤ n := Nat.le_of_dvd hnPos hpqd
  nlinarith

/-- Reciprocal sums on a multiples block are a nonzero scalar image of the
corresponding unscaled reciprocal sums. -/
theorem subsetSumValues_multipleBlock (N p : ℕ) (hp : 0 < p) :
    subsetSumValues reciprocalWeight (multipleBlock N p) =
      (denominatorSubsetSums (N / p)).image
        (fun x : ℚ => x / (p : ℚ)) := by
  rw [multipleBlock, subsetSumValues, Finset.powerset_image, Finset.image_image,
    denominatorSubsetSums, subsetSumValues, Finset.image_image]
  apply Finset.image_congr
  intro A hA
  change A ∈ (Finset.Icc 1 (N / p)).powerset at hA
  rw [Finset.mem_powerset] at hA
  simp only [Function.comp_apply]
  rw [Finset.sum_image]
  · rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro a ha
    have haPos : 0 < a := by
      have := (Finset.mem_Icc.mp (hA ha)).1
      omega
    simp only [reciprocalWeight]
    push_cast
    field_simp
  · intro a ha b hb hab
    exact Nat.eq_of_mul_eq_mul_left (by omega) hab

/-- Hence a multiples block contributes exactly `S(floor(N/p))` distinct
values. -/
theorem card_subsetSumValues_multipleBlock (N p : ℕ) (hp : 0 < p) :
    (subsetSumValues reciprocalWeight (multipleBlock N p)).card = S (N / p) := by
  rw [subsetSumValues_multipleBlock N p hp]
  calc
    ((denominatorSubsetSums (N / p)).image
        (fun x : ℚ => x / (p : ℚ))).card =
        (denominatorSubsetSums (N / p)).card := by
      apply Finset.card_image_of_injective
      intro x y hxy
      have hpq : (p : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hp)
      exact (div_left_inj' hpq).mp hxy
    _ = S (N / p) := card_denominatorSubsetSums _

/-- Primes in the large-prime range `(Q,N]`. -/
def largePrimes (N Q : ℕ) : Finset ℕ :=
  (Finset.Icc (Q + 1) N).filter Nat.Prime

/-- All denominator blocks carrying a prime greater than `Q`. -/
def largePrimePart (N Q : ℕ) : Finset ℕ :=
  (largePrimes N Q).biUnion (multipleBlock N)

/-- Denominators up to `N` carrying no prime greater than `Q`. -/
def smoothRemainder (N Q : ℕ) : Finset ℕ :=
  Finset.Icc 1 N \ largePrimePart N Q

/-- The large-prime blocks are pairwise disjoint when `N ≤ Q²`. -/
theorem largePrimeBlocks_pairwise (N Q : ℕ) (hNQ : N ≤ Q * Q) :
    ∀ p ∈ largePrimes N Q, ∀ q ∈ largePrimes N Q, p ≠ q →
      Disjoint (multipleBlock N p) (multipleBlock N q) := by
  intro p hp q hq hpq
  rw [largePrimes, Finset.mem_filter] at hp hq
  exact multipleBlock_disjoint hp.2 hq.2
    (Nat.lt_of_succ_le (Finset.mem_Icc.mp hp.1).1)
    (Nat.lt_of_succ_le (Finset.mem_Icc.mp hq.1).1) hpq hNQ

/-- Every large-prime block really consists of denominators in `[1,N]`. -/
theorem largePrimePart_subset (N Q : ℕ) :
    largePrimePart N Q ⊆ Finset.Icc 1 N := by
  rw [largePrimePart, Finset.biUnion_subset_iff_forall_subset]
  intro p hp n hn
  rw [largePrimes, Finset.mem_filter] at hp
  rw [multipleBlock, Finset.mem_image] at hn
  obtain ⟨k, hk, hkn⟩ := hn
  have hkBounds := Finset.mem_Icc.mp hk
  have hkPos : 0 < k := lt_of_lt_of_le Nat.zero_lt_one hkBounds.1
  have hpkN : p * k ≤ N := by
    have := (Nat.le_div_iff_mul_le hp.2.pos).mp hkBounds.2
    simpa [Nat.mul_comm] using this
  rw [← hkn]
  exact Finset.mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr
    (Nat.mul_ne_zero hp.2.ne_zero (Nat.ne_of_gt hkPos)), hpkN⟩

/-- **Exact finite-algebra upper recurrence.** Splitting denominators according
to their unique prime factor above `Q > sqrt N` bounds `S(N)` by the support
of the smooth remainder times the product of the smaller values `S(N/p)`. -/
theorem S_le_smooth_mul_prime_product (N Q : ℕ) (hNQ : N ≤ Q * Q) :
    S N ≤
      (subsetSumValues reciprocalWeight (smoothRemainder N Q)).card *
        ∏ p ∈ largePrimes N Q, S (N / p) := by
  let L := largePrimePart N Q
  let R := smoothRemainder N Q
  have hLsub : L ⊆ Finset.Icc 1 N := largePrimePart_subset N Q
  have hRL : Disjoint R L := by
    exact Finset.sdiff_disjoint
  have hpart : R ∪ L = Finset.Icc 1 N :=
    Finset.sdiff_union_of_subset hLsub
  have hpair := largePrimeBlocks_pairwise N Q hNQ
  rw [← card_denominatorSubsetSums N]
  change (subsetSumValues reciprocalWeight (Finset.Icc 1 N)).card ≤ _
  rw [← hpart]
  calc
    (subsetSumValues reciprocalWeight (R ∪ L)).card ≤
        (subsetSumValues reciprocalWeight R).card *
          (subsetSumValues reciprocalWeight L).card :=
      card_subsetSumValues_union_le reciprocalWeight hRL
    _ ≤ (subsetSumValues reciprocalWeight R).card *
          ∏ p ∈ largePrimes N Q,
            (subsetSumValues reciprocalWeight (multipleBlock N p)).card := by
      apply Nat.mul_le_mul_left
      exact card_subsetSumValues_biUnion_le reciprocalWeight
        (largePrimes N Q) (multipleBlock N) hpair
    _ = (subsetSumValues reciprocalWeight R).card *
          ∏ p ∈ largePrimes N Q, S (N / p) := by
      congr 1
      apply Finset.prod_congr rfl
      intro p hp
      rw [largePrimes, Finset.mem_filter] at hp
      exact card_subsetSumValues_multipleBlock N p hp.2.pos

end Research
