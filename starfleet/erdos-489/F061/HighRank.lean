import Mathlib

/-- If distinct objects carry distinct nonnegative ranks, at most `t` of them
can have rank below `t`.  Equivalently, all but at most `t` objects have rank
at least `t`. -/
theorem card_le_card_rank_ge_add
    {α : Type*} [DecidableEq α] (s : Finset α) (rank : α → ℕ)
    (hinj : Set.InjOn rank (s : Set α)) (t : ℕ) :
    s.card ≤ (s.filter (fun x => t ≤ rank x)).card + t := by
  classical
  let low : Finset α := s.filter (fun x => rank x < t)
  have hilow : Set.InjOn rank (low : Set α) :=
    hinj.mono (by
      intro x hx
      exact (Finset.mem_filter.mp hx).1)
  have hcardimage : (low.image rank).card = low.card :=
    Finset.card_image_iff.mpr hilow
  have himage : low.image rank ⊆ Finset.range t := by
    intro r hr
    rcases Finset.mem_image.mp hr with ⟨x, hx, rfl⟩
    exact Finset.mem_range.mpr (Finset.mem_filter.mp hx).2
  have hlow : low.card ≤ t := by
    rw [← hcardimage]
    simpa using Finset.card_le_card himage
  have hpart : low.card + (s.filter (fun x => t ≤ rank x)).card = s.card := by
    have h := Finset.filter_card_add_filter_neg_card_eq_card
      (s := s) (fun x => rank x < t)
    simpa [low, Nat.not_lt] using h
  omega

/-- In particular, if there are at least `2t` distinctly ranked objects, at
least `t` of them have rank at least `t`. -/
theorem card_rank_ge_of_twice_le_card
    {α : Type*} [DecidableEq α] (s : Finset α) (rank : α → ℕ)
    (hinj : Set.InjOn rank (s : Set α)) (t : ℕ)
    (hcard : 2 * t ≤ s.card) :
    t ≤ (s.filter (fun x => t ≤ rank x)).card := by
  have h := card_le_card_rank_ge_add s rank hinj t
  omega
