import Research.SidonCoreBound

namespace Erdos796

/-- Elements whose prime factors all lie at or below `sqrt n`. -/
def smoothPart (A : Finset ℕ) (n : ℕ) : Finset ℕ :=
  A.filter fun a => ∀ q ∈ Nat.primesLE a, q ∣ a → q ≤ n.sqrt

/-- The large-prime-fiber lift extracted from an arbitrary finite set. -/
def extractedLargePart (A : Finset ℕ) (n : ℕ) : Finset ℕ :=
  heterogeneousLift (sqrtPrimeLabels n) n.sqrt
    (fun q => extractedFiber A n.sqrt q)

/-- Every extracted large-prime product belongs to the original set. -/
theorem extractedLargePart_subset (A : Finset ℕ) (n : ℕ) :
    extractedLargePart A n ⊆ A := by
  intro a ha
  rcases Finset.mem_image.mp ha with ⟨⟨q, d⟩, hqd, rfl⟩
  have hqd' := Finset.mem_filter.mp hqd
  have hd := hqd'.2
  exact (Finset.mem_filter.mp hd).2

/-- Every nonsmooth element of `[1,n]` occurs in its unique extracted
large-prime fiber. -/
theorem sdiff_smoothPart_subset_extracted
    {A : Finset ℕ} {n : ℕ} (hA : A ⊆ Finset.Icc 1 n) :
    A \ smoothPart A n ⊆ extractedLargePart A n := by
  intro a ha
  have ha' := Finset.mem_sdiff.mp ha
  have haI := Finset.mem_Icc.mp (hA ha'.1)
  have hnotsmooth : ¬(∀ q ∈ Nat.primesLE a, q ∣ a → q ≤ n.sqrt) := by
    intro h
    exact ha'.2 (Finset.mem_filter.mpr ⟨ha'.1, h⟩)
  push Not at hnotsmooth
  rcases hnotsmooth with ⟨q, hqmem, hqdiv, hqs⟩
  have hqprime := Nat.prime_of_mem_primesLE hqmem
  have hqle : q ≤ n := le_trans (Nat.le_of_dvd haI.1 hqdiv) haI.2
  have hqLabel : q ∈ sqrtPrimeLabels n := by
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_Icc.mpr ⟨by omega, hqle⟩, hqprime⟩
  let d := a / q
  have hdpos : 0 < d := by
    dsimp [d]
    exact Nat.div_pos (Nat.le_of_dvd haI.1 hqdiv) hqprime.pos
  have hdle : d ≤ n.sqrt := by
    dsimp [d]
    calc
      a / q ≤ n / q := Nat.div_le_div_right haI.2
      _ ≤ n.sqrt := div_label_le_sqrt hqLabel
  have hprod : q * d = a := by
    dsimp [d]
    exact Nat.mul_div_cancel' hqdiv
  unfold extractedLargePart heterogeneousLift
  apply Finset.mem_image.mpr
  refine ⟨(q, d), Finset.mem_filter.mpr ⟨?_, ?_⟩, hprod⟩
  · exact Finset.mem_product.mpr
      ⟨hqLabel, Finset.mem_Icc.mpr ⟨hdpos, hdle⟩⟩
  · unfold extractedFiber
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr ⟨hdpos, hdle⟩, hprod ▸ ha'.1⟩

/-- The extracted large part is exactly the nonsmooth part. -/
theorem extractedLargePart_eq_sdiff
    {A : Finset ℕ} {n : ℕ} (hA : A ⊆ Finset.Icc 1 n) :
    extractedLargePart A n = A \ smoothPart A n := by
  apply Finset.Subset.antisymm
  · intro a ha
    apply Finset.mem_sdiff.mpr
    refine ⟨extractedLargePart_subset A n ha, ?_⟩
    intro hsmooth
    have hs := (Finset.mem_filter.mp hsmooth).2
    rcases Finset.mem_image.mp ha with ⟨⟨q, d⟩, hqd, rfl⟩
    have hqd' := Finset.mem_filter.mp hqd
    have hq := (Finset.mem_product.mp hqd'.1).1
    have hq' := Finset.mem_filter.mp hq
    have hqI := Finset.mem_Icc.mp hq'.1
    have hdI := Finset.mem_Icc.mp (Finset.mem_product.mp hqd'.1).2
    have hqdvd : q ∣ q * d := Nat.dvd_mul_right q d
    exact (not_le_of_gt (by omega : n.sqrt < q))
      (hs q (Nat.mem_primesLE.mpr ⟨by
        calc q ≤ q * d := Nat.le_mul_of_pos_right q hdI.1
             _ = q * d := rfl, hq'.2⟩) hqdvd)
  · exact sdiff_smoothPart_subset_extracted hA

/-- Exact cardinal decomposition into the smooth remainder and extracted
large-prime fibers. -/
theorem card_eq_smoothPart_add_fibers
    {A : Finset ℕ} {n : ℕ} (hA : A ⊆ Finset.Icc 1 n) :
    A.card = (smoothPart A n).card +
      ∑ q ∈ sqrtPrimeLabels n, (extractedFiber A n.sqrt q).card := by
  have hsmooth : smoothPart A n ⊆ A := by
    intro a ha
    exact (Finset.mem_filter.mp ha).1
  have hQ : ∀ q ∈ sqrtPrimeLabels n, n.sqrt < q ∧ q.Prime := by
    intro q hq
    have hq' := Finset.mem_filter.mp hq
    have hqI := Finset.mem_Icc.mp hq'.1
    exact ⟨by omega, hq'.2⟩
  have hC : ∀ q ∈ sqrtPrimeLabels n,
      extractedFiber A n.sqrt q ⊆ Finset.Icc 1 n.sqrt := by
    intro q hq d hd
    exact (Finset.mem_filter.mp hd).1
  have hpart := Finset.card_sdiff_add_card_eq_card hsmooth
  have hlift := heterogeneousLift_card_eq_sum
    (sqrtPrimeLabels n) n.sqrt (fun q => extractedFiber A n.sqrt q) hQ hC
  change (extractedLargePart A n).card =
      ∑ q ∈ sqrtPrimeLabels n, (extractedFiber A n.sqrt q).card at hlift
  rw [extractedLargePart_eq_sdiff hA] at hlift
  omega

end Erdos796
