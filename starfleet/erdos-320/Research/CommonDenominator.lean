import Research.LargePrime

/-!
# A common-denominator support bound

A finite set of reciprocal sums whose denominators divide `L` embeds into the
integer subset sums of the weights `L/n`.  Bounding those integers by a finite
interval gives a simple exact cardinality bound.
-/

namespace Research

/-- Integer subset sums after clearing a common denominator `L`. -/
def clearedSubsetSums (L : ℕ) (D : Finset ℕ) : Finset ℕ :=
  subsetSumValues (fun n => L / n) D

private theorem reciprocal_eq_cleared_div {L n : ℕ}
    (hL : 0 < L) (hn : 0 < n) (hdiv : n ∣ L) :
    reciprocalWeight n = ((L / n : ℕ) : ℚ) / (L : ℚ) := by
  rw [reciprocalWeight]
  have hLq : (L : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hL)
  have hnq : (n : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  field_simp
  exact_mod_cast (by
    simpa [Nat.mul_comm] using (Nat.div_mul_cancel hdiv).symm)

/-- Clearing denominators describes the rational support as an image of an
integer subset-sum support. -/
theorem subsetSumValues_eq_cleared_image {L : ℕ} {D : Finset ℕ}
    (hL : 0 < L) (hpos : ∀ n ∈ D, 0 < n) (hdiv : ∀ n ∈ D, n ∣ L) :
    subsetSumValues reciprocalWeight D =
      (clearedSubsetSums L D).image (fun k : ℕ => (k : ℚ) / (L : ℚ)) := by
  rw [subsetSumValues, clearedSubsetSums, subsetSumValues, Finset.image_image]
  apply Finset.image_congr
  intro A hA
  change A ∈ D.powerset at hA
  rw [Finset.mem_powerset] at hA
  simp only [Function.comp_apply]
  calc
    ∑ n ∈ A, reciprocalWeight n =
        ∑ n ∈ A, (((L / n : ℕ) : ℚ) / (L : ℚ)) := by
      apply Finset.sum_congr rfl
      intro n hn
      exact reciprocal_eq_cleared_div hL (hpos n (hA hn)) (hdiv n (hA hn))
    _ = (∑ n ∈ A, ((L / n : ℕ) : ℚ)) / (L : ℚ) := by
      rw [Finset.sum_div]
    _ = ((∑ n ∈ A, L / n : ℕ) : ℚ) / (L : ℚ) := by
      norm_cast

/-- Every cleared subset sum is at most `|D| L`, so there are at most
`|D| L + 1` of them. -/
theorem card_clearedSubsetSums_le (L : ℕ) (D : Finset ℕ) :
    (clearedSubsetSums L D).card ≤ D.card * L + 1 := by
  have hsubset :
      clearedSubsetSums L D ⊆ Finset.range (D.card * L + 1) := by
    intro y hy
    rw [clearedSubsetSums, subsetSumValues, Finset.mem_image] at hy
    obtain ⟨A, hA, rfl⟩ := hy
    change A ∈ D.powerset at hA
    rw [Finset.mem_powerset] at hA
    rw [Finset.mem_range]
    have hterm : ∑ n ∈ A, L / n ≤ ∑ _n ∈ A, L := by
      apply Finset.sum_le_sum
      intro n hn
      exact Nat.div_le_self L n
    have hcard : A.card ≤ D.card := Finset.card_le_card hA
    calc
      ∑ n ∈ A, L / n ≤ ∑ _n ∈ A, L := hterm
      _ = A.card * L := by simp
      _ ≤ D.card * L := Nat.mul_le_mul_right L hcard
      _ < D.card * L + 1 := Nat.lt_succ_self _
  simpa using Finset.card_le_card hsubset

/-- Common-denominator obstruction: if every positive denominator in `D`
divides `L`, then its reciprocal subset-sum support has at most `|D|L+1`
values. -/
theorem card_subsetSumValues_le_commonDenominator {L : ℕ} {D : Finset ℕ}
    (hL : 0 < L) (hpos : ∀ n ∈ D, 0 < n) (hdiv : ∀ n ∈ D, n ∣ L) :
    (subsetSumValues reciprocalWeight D).card ≤ D.card * L + 1 := by
  rw [subsetSumValues_eq_cleared_image hL hpos hdiv]
  exact le_trans Finset.card_image_le (card_clearedSubsetSums_le L D)

end Research
