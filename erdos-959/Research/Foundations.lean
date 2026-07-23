import Research.Basic

noncomputable section
namespace Erdos959

lemma indexPairs_card (n : ℕ) : (indexPairs n).card = Nat.choose n 2 := by
  classical
  let quotient : Fin n × Fin n → Sym2 (Fin n) := Function.uncurry Sym2.mk
  have hinj : Set.InjOn quotient (indexPairs n : Set (Fin n × Fin n)) := by
    intro a ha b hb hab
    have ha' : a.1 < a.2 := by simpa [indexPairs] using ha
    have hb' : b.1 < b.2 := by simpa [indexPairs] using hb
    rcases (Sym2.eq_iff.mp hab) with h | h
    · exact Prod.ext h.1 h.2
    · exfalso
      rw [h.1, h.2] at ha'
      exact lt_asymm ha' hb'
  have himage : (indexPairs n).image quotient =
      Finset.univ.offDiag.image quotient := by
    ext s
    constructor
    · intro hs
      rw [Finset.mem_image] at hs
      rcases hs with ⟨a, ha, rfl⟩
      rw [Finset.mem_image]
      refine ⟨a, ?_, rfl⟩
      rw [Finset.mem_offDiag]
      simp only [Finset.mem_univ, true_and]
      exact ne_of_lt (Finset.mem_filter.mp ha).2
    · intro hs
      rw [Finset.mem_image] at hs
      rcases hs with ⟨a, ha, rfl⟩
      rw [Finset.mem_offDiag] at ha
      by_cases h : a.1 < a.2
      · rw [Finset.mem_image]
        refine ⟨a, ?_, rfl⟩
        simp [indexPairs, h]
      · have h' : a.2 < a.1 := lt_of_le_of_ne (le_of_not_gt h) ha.2.2.symm
        rw [Finset.mem_image]
        refine ⟨(a.2, a.1), ?_, ?_⟩
        · simp [indexPairs, h']
        · exact (Sym2.eq_iff.mpr (Or.inr ⟨rfl, rfl⟩))
  calc
    (indexPairs n).card = ((indexPairs n).image quotient).card :=
      (Finset.card_image_iff.mpr hinj).symm
    _ = (Finset.univ.offDiag.image quotient).card := by rw [himage]
    _ = Nat.choose n 2 := by simpa using Sym2.card_image_offDiag (Finset.univ : Finset (Fin n))

lemma frequency_le_choose {n : ℕ} (P : Fin n → Point) (d : ℝ) :
    frequency P d ≤ Nat.choose n 2 := by
  calc
    frequency P d ≤ (indexPairs n).card := by
      exact Finset.card_filter_le _ _
    _ = Nat.choose n 2 := indexPairs_card n

lemma runnerUpFrequency_le_choose {n : ℕ} (P : Fin n → Point) (d : ℝ) :
    runnerUpFrequency P d ≤ Nat.choose n 2 := by
  apply Finset.sup_le
  intro e he
  exact frequency_le_choose P e

lemma multiplicityGap_le_choose {n : ℕ} (P : Fin n → Point) :
    multiplicityGap P ≤ Nat.choose n 2 := by
  apply Finset.sup_le
  intro d hd
  exact (Nat.sub_le _ _).trans (frequency_le_choose P d)

lemma attainableGap_le_choose {n g : ℕ} (hg : AttainableGap n g) :
    g ≤ Nat.choose n 2 := by
  rcases hg with ⟨P, hP, rfl⟩
  exact multiplicityGap_le_choose P

lemma extremalGap_le_choose (n : ℕ) :
    extremalGap n ≤ Nat.choose n 2 := by
  classical
  exact Nat.findGreatest_le _

end Erdos959
