import Mathlib

namespace Erdos254.BalancedReservation

open scoped BigOperators

noncomputable section

/-- Among all `r`-subsets of a finite set, one has weight at most the
corresponding fraction of the total weight. -/
theorem exists_subset_card_sum_le_average
    {α : Type*} [DecidableEq α] (s : Finset α) (f : α → ℝ)
    (r : ℕ) (hr : r ≤ s.card) :
    ∃ t : Finset α, t ⊆ s ∧ t.card = r ∧
      (s.card : ℝ) * (∑ x ∈ t, f x) ≤
        (r : ℝ) * (∑ x ∈ s, f x) := by
  classical
  let P := s.powersetCard r
  have hP : P.Nonempty := by
    exact Finset.powersetCard_nonempty.mpr hr
  let vals : Finset ℝ := P.image (fun t => ∑ x ∈ t, f x)
  have hvals : vals.Nonempty := hP.image _
  let m := vals.min' hvals
  have hm : m ∈ vals := Finset.min'_mem vals hvals
  change m ∈ P.image (fun t => ∑ x ∈ t, f x) at hm
  rw [Finset.mem_image] at hm
  obtain ⟨t, htP, htSum⟩ := hm
  have hts : t ⊆ s := (Finset.mem_powersetCard.mp htP).1
  have htcard : t.card = r := (Finset.mem_powersetCard.mp htP).2
  have hminimal : ∀ u ∈ P, (∑ x ∈ t, f x) ≤ ∑ x ∈ u, f x := by
    intro u hu
    have huval : (∑ x ∈ u, f x) ∈ vals := Finset.mem_image.mpr ⟨u, hu, rfl⟩
    have hmin := Finset.min'_le vals (∑ x ∈ u, f x) huval
    calc
      (∑ x ∈ t, f x) = m := htSum
      _ ≤ ∑ x ∈ u, f x := hmin
  have hpair : ∀ y ∈ t, ∀ x ∈ s \ t, f y ≤ f x := by
    intro y hyt x hxc
    by_contra hnot
    have hxy : f x < f y := lt_of_not_ge hnot
    let u := insert x (t.erase y)
    have hxt : x ∉ t := (Finset.mem_sdiff.mp hxc).2
    have hyx : x ≠ y := by
      intro h
      subst x
      exact hxt hyt
    have huSub : u ⊆ s := by
      apply Finset.insert_subset
      · exact (Finset.mem_sdiff.mp hxc).1
      · exact (t.erase_subset y).trans hts
    have hxErase : x ∉ t.erase y := by
      intro hx
      exact hxt (Finset.mem_of_mem_erase hx)
    have hucard : u.card = r := by
      change (insert x (t.erase y)).card = r
      have htpos : 0 < t.card := Finset.card_pos.mpr ⟨y, hyt⟩
      rw [Finset.card_insert_of_notMem hxErase,
        Finset.card_erase_of_mem hyt, htcard]
      omega
    have huP : u ∈ P := Finset.mem_powersetCard.mpr ⟨huSub, hucard⟩
    have hsumu : (∑ z ∈ u, f z) = (∑ z ∈ t, f z) - f y + f x := by
      change (∑ z ∈ insert x (t.erase y), f z) = _
      rw [Finset.sum_insert hxErase]
      have herase := Finset.sum_erase_add t f hyt
      calc
        f x + ∑ z ∈ t.erase y, f z =
            (∑ z ∈ t.erase y, f z) + f y - f y + f x := by ring
        _ = (∑ z ∈ t, f z) - f y + f x := by rw [herase]
    have hmin := hminimal u huP
    rw [hsumu] at hmin
    linarith
  let c := s \ t
  have hdouble :
      (c.card : ℝ) * (∑ y ∈ t, f y) ≤
        (t.card : ℝ) * (∑ x ∈ c, f x) := by
    calc
      (c.card : ℝ) * (∑ y ∈ t, f y) =
          ∑ x ∈ c, ∑ y ∈ t, f y := by simp [mul_comm]
      _ ≤ ∑ x ∈ c, ∑ y ∈ t, f x := by
        apply Finset.sum_le_sum
        intro x hxc
        apply Finset.sum_le_sum
        intro y hyt
        exact hpair y hyt x hxc
      _ = (t.card : ℝ) * (∑ x ∈ c, f x) := by
        simp only [Finset.sum_const, nsmul_eq_mul]
        rw [Finset.mul_sum]
  have hcCard : c.card + t.card = s.card := by
    change (s \ t).card + t.card = s.card
    rw [Finset.card_sdiff_of_subset hts]
    omega
  have hsumSplit : (∑ x ∈ t, f x) + ∑ x ∈ c, f x = ∑ x ∈ s, f x := by
    change (∑ x ∈ t, f x) + ∑ x ∈ s \ t, f x = ∑ x ∈ s, f x
    have hdis : Disjoint t (s \ t) := Finset.disjoint_sdiff
    have hunion : t ∪ (s \ t) = s := Finset.union_sdiff_of_subset hts
    rw [← Finset.sum_union hdis, hunion]
  have hdoubleR :
      (c.card : ℝ) * (∑ y ∈ t, f y) ≤
        (r : ℝ) * (∑ x ∈ c, f x) := by
    simpa [htcard] using hdouble
  refine ⟨t, hts, htcard, ?_⟩
  rw [← hcCard, Nat.cast_add, htcard, ← hsumSplit]
  calc
    ((c.card : ℝ) + r) * (∑ x ∈ t, f x) =
        (c.card : ℝ) * (∑ x ∈ t, f x) + r * (∑ x ∈ t, f x) := by ring
    _ ≤ r * (∑ x ∈ c, f x) + r * (∑ x ∈ t, f x) := by
      simpa [add_comm] using
        (add_le_add_right hdoubleR (r * (∑ x ∈ t, f x)))
    _ = (r : ℝ) * ((∑ x ∈ t, f x) + ∑ x ∈ c, f x) := by ring

/-- Simultaneous normalized version: reserve `r` elements while taking at most
an `r*d/h` fraction of every one of `d` nonnegative weight coordinates. -/
theorem exists_subset_card_simultaneous_normalized
    {α ι : Type*} [DecidableEq α] [Fintype ι]
    (s : Finset α) (w : ι → α → ℝ)
    (hw : ∀ i x, x ∈ s → 0 ≤ w i x)
    (r : ℕ) (hr : r ≤ s.card) :
    ∃ t : Finset α, t ⊆ s ∧ t.card = r ∧
      ∀ i : ι,
        (s.card : ℝ) * (∑ x ∈ t, w i x) ≤
          (r * Fintype.card ι : ℕ) * (∑ x ∈ s, w i x) := by
  classical
  let W : ι → ℝ := fun i => ∑ x ∈ s, w i x
  let f : α → ℝ := fun x => ∑ i : ι, if W i = 0 then 0 else w i x / W i
  obtain ⟨t, hts, htcard, havg⟩ :=
    exists_subset_card_sum_le_average s f r hr
  refine ⟨t, hts, htcard, ?_⟩
  intro i
  by_cases hWi : W i = 0
  · have hzero : ∀ x ∈ s, w i x = 0 := by
      intro x hx
      have hnonneg := hw i x hx
      have hle : w i x ≤ W i := Finset.single_le_sum
        (fun y hy => hw i y hy) hx
      rw [hWi] at hle
      linarith
    have hzeroT : ∑ x ∈ t, w i x = 0 := by
      apply Finset.sum_eq_zero
      intro x hx
      exact hzero x (hts hx)
    rw [hzeroT, mul_zero]
    exact mul_nonneg (Nat.cast_nonneg _)
      (Finset.sum_nonneg fun x hx => hw i x hx)
  · have hWpos : 0 < W i := lt_of_le_of_ne
      (Finset.sum_nonneg fun x hx => hw i x hx) (Ne.symm hWi)
    have hcoord : ∑ x ∈ t, w i x / W i ≤ ∑ x ∈ t, f x := by
      apply Finset.sum_le_sum
      intro x hx
      dsimp [f]
      have hterms : ∀ j ∈ (Finset.univ : Finset ι),
          0 ≤ if W j = 0 then 0 else w j x / W j := by
        intro j hj
        by_cases hWj : W j = 0
        · simp [hWj]
        · simp only [hWj, ↓reduceIte]
          exact div_nonneg (hw j x (hts hx))
            (Finset.sum_nonneg fun y hy => hw j y hy)
      calc
        w i x / W i = (if W i = 0 then 0 else w i x / W i) := by simp [hWi]
        _ ≤ ∑ j : ι, (if W j = 0 then 0 else w j x / W j) :=
          Finset.single_le_sum hterms (Finset.mem_univ i)
    have hsumf : (∑ x ∈ s, f x) ≤ Fintype.card ι := by
      calc
        (∑ x ∈ s, f x) = ∑ i : ι, ∑ x ∈ s,
            (if W i = 0 then 0 else w i x / W i) := by
              simp only [f]
              rw [Finset.sum_comm]
        _ ≤ ∑ _i : ι, (1 : ℝ) := by
          apply Finset.sum_le_sum
          intro j hj
          by_cases hWj : W j = 0
          · simp [hWj]
          · simp only [hWj, ↓reduceIte]
            rw [← Finset.sum_div]
            simp [W, hWj]
        _ = Fintype.card ι := by simp
    have hraw : (s.card : ℝ) * (∑ x ∈ t, w i x / W i) ≤
        (r : ℝ) * Fintype.card ι := by
      calc
        _ ≤ (s.card : ℝ) * (∑ x ∈ t, f x) :=
          mul_le_mul_of_nonneg_left hcoord (Nat.cast_nonneg _)
        _ ≤ (r : ℝ) * (∑ x ∈ s, f x) := havg
        _ ≤ (r : ℝ) * Fintype.card ι :=
          mul_le_mul_of_nonneg_left hsumf (Nat.cast_nonneg _)
    rw [← Finset.sum_div] at hraw
    have hmul := mul_le_mul_of_nonneg_right hraw hWpos.le
    calc
      (s.card : ℝ) * (∑ x ∈ t, w i x) =
          ((s.card : ℝ) * ((∑ x ∈ t, w i x) / W i)) * W i := by
            field_simp
      _ ≤ ((r : ℝ) * Fintype.card ι) * W i := hmul
      _ = ((r * Fintype.card ι : ℕ) : ℝ) * (∑ x ∈ s, w i x) := by
        simp only [W, Nat.cast_mul]

end

end Erdos254.BalancedReservation
