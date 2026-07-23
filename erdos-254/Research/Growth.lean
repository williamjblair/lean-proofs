import Research.Statement

namespace Erdos254

open Filter

noncomputable section

def shellCount (A : Set ℕ) (x : ℕ) : ℕ := by
  classical
  exact ((Finset.Ioc x (2 * x)).filter (fun n => n ∈ A)).card

lemma dyadicIncrement_eq_shellCard (A : Set ℕ) (x : ℕ) :
    dyadicIncrement A x = shellCount A x := by
  classical
  let s := (Finset.Icc 1 x).filter (fun n => n ∈ A)
  let t := (Finset.Icc 1 (2 * x)).filter (fun n => n ∈ A)
  have hst : s ⊆ t := by
    intro n hn
    simp only [s, t, Finset.mem_filter, Finset.mem_Icc] at hn ⊢
    exact ⟨⟨hn.1.1, hn.1.2.trans (by omega)⟩, hn.2⟩
  rw [dyadicIncrement, countingFunction, countingFunction]
  change t.card - s.card = _
  rw [← Finset.card_sdiff_of_subset hst]
  apply congrArg Finset.card
  ext n
  simp only [t, s, Finset.mem_sdiff, Finset.mem_filter,
    Finset.mem_Icc, Finset.mem_Ioc]
  constructor
  · rintro ⟨⟨hlo, hA⟩, hnot⟩
    refine ⟨⟨?_, hlo.2⟩, hA⟩
    by_contra hnx
    exact hnot ⟨⟨hlo.1, Nat.le_of_not_gt hnx⟩, hA⟩
  · rintro ⟨⟨hxn, hn2x⟩, hA⟩
    refine ⟨⟨⟨by omega, hn2x⟩, hA⟩, ?_⟩
    rintro ⟨⟨_, hnx⟩, _⟩
    omega

lemma dyadic_tendsto_eventually_many (A : Set ℕ)
    (hdyadic : Tendsto (dyadicIncrement A) atTop atTop) (K : ℕ) :
    ∀ᶠ x : ℕ in atTop, K ≤ shellCount A x := by
  filter_upwards [tendsto_atTop.1 hdyadic K] with x hx
  simpa only [dyadicIncrement_eq_shellCard] using hx

end

end Erdos254
