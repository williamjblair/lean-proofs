import Research.TuranLocal
import Mathlib.NumberTheory.SumPrimeReciprocals

namespace Erdos450

/-- Non-summability of prime reciprocals means that finite prime sums are
unbounded. -/
theorem exists_prime_finset_reciprocal_sum_gt (C : ℝ) :
    ∃ T : Finset Nat.Primes, C < ∑ p ∈ T, (1 : ℝ) / (p : ℝ) := by
  by_contra h
  have hbound : ∀ T : Finset Nat.Primes,
      (∑ p ∈ T, (1 : ℝ) / (p : ℝ)) ≤ C := by
    intro T
    exact le_of_not_gt (fun hTC => h ⟨T, hTC⟩)
  apply Nat.Primes.not_summable_one_div
  apply summable_of_sum_le
  · intro p
    positivity
  · exact hbound

/-- Deleting the finitely many primes below five still leaves finite prime
sets of arbitrarily large reciprocal mass. -/
theorem exists_large_primeReciprocalMean (C : ℝ) :
    ∃ S : Finset ℕ,
      (∀ p ∈ S, Nat.Prime p) ∧
      (∀ p ∈ S, 5 ≤ p) ∧
      C < primeReciprocalMean S := by
  classical
  obtain ⟨T, hT⟩ := exists_prime_finset_reciprocal_sum_gt (C + 5)
  let H : Finset Nat.Primes := T.filter fun p => 5 ≤ (p : ℕ)
  let L : Finset Nat.Primes := T.filter fun p => ¬ 5 ≤ (p : ℕ)
  let S : Finset ℕ := H.image (fun p : Nat.Primes => (p : ℕ))
  have hSprime : ∀ p ∈ S, Nat.Prime p := by
    intro p hp
    have hp' : p ∈ H.image (fun q : Nat.Primes => (q : ℕ)) := by
      simpa only [S] using hp
    obtain ⟨q, hqH, hqp⟩ := Finset.mem_image.mp hp'
    subst p
    exact q.property
  have hSfive : ∀ p ∈ S, 5 ≤ p := by
    intro p hp
    have hp' : p ∈ H.image (fun q : Nat.Primes => (q : ℕ)) := by
      simpa only [S] using hp
    obtain ⟨q, hqH, hqp⟩ := Finset.mem_image.mp hp'
    subst p
    have hqfilter : q ∈ T.filter (fun q : Nat.Primes => 5 ≤ (q : ℕ)) := by
      simpa only [H] using hqH
    exact (Finset.mem_filter.mp hqfilter).2
  have hmean : primeReciprocalMean S =
      ∑ p ∈ H, (1 : ℝ) / (p : ℝ) := by
    unfold primeReciprocalMean
    change (∑ p ∈ H.image (fun q : Nat.Primes => (q : ℕ)),
      (1 : ℝ) / (p : ℝ)) = _
    exact Finset.sum_image Set.injOn_subtype_val
  have hcardL : L.card ≤ 5 := by
    have hinj : Set.InjOn (fun p : Nat.Primes => (p : ℕ)) L :=
      Set.injOn_subtype_val
    have himage : (L.image fun p : Nat.Primes => (p : ℕ)) ⊆ Finset.range 5 := by
      intro p hp
      obtain ⟨q, hqL, hqp⟩ := Finset.mem_image.mp hp
      subst p
      have hqfilter : q ∈ T.filter (fun q : Nat.Primes => ¬5 ≤ (q : ℕ)) := by
        simpa only [L] using hqL
      have hnot : ¬5 ≤ (q : ℕ) := (Finset.mem_filter.mp hqfilter).2
      exact Finset.mem_range.mpr (by omega)
    calc
      L.card = (L.image fun p : Nat.Primes => (p : ℕ)).card := by
        symm
        exact Finset.card_image_iff.mpr hinj
      _ ≤ (Finset.range 5).card := Finset.card_le_card himage
      _ = 5 := Finset.card_range 5
  have hlow : (∑ p ∈ L, (1 : ℝ) / (p : ℝ)) ≤ 5 := by
    calc
      (∑ p ∈ L, (1 : ℝ) / (p : ℝ)) ≤ L.card • (1 : ℝ) := by
        apply Finset.sum_le_card_nsmul
        intro p hp
        have hpR : (0 : ℝ) < (p : ℝ) := by
          exact_mod_cast p.property.pos
        apply (div_le_one hpR).2
        exact_mod_cast (show 1 ≤ (p : ℕ) from le_trans (by omega) p.property.two_le)
      _ = (L.card : ℝ) := by simp
      _ ≤ 5 := Nat.cast_le.mpr hcardL
  have hpartition :
      (∑ p ∈ H, (1 : ℝ) / (p : ℝ)) +
        (∑ p ∈ L, (1 : ℝ) / (p : ℝ)) =
          ∑ p ∈ T, (1 : ℝ) / (p : ℝ) := by
    simpa only [H, L] using Finset.sum_filter_add_sum_filter_not T
      (fun p : Nat.Primes => 5 ≤ (p : ℕ))
      (fun p : Nat.Primes => (1 : ℝ) / (p : ℝ))
  refine ⟨S, hSprime, hSfive, ?_⟩
  rw [hmean]
  linarith

end Erdos450
