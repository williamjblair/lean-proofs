import Mathlib.Algebra.Polynomial.RuleOfSigns
import Mathlib.Tactic

namespace Erdos521

/-- Number of nonzero sign transitions in `l`, given the preceding nonzero sign `previous`.
The value `0` for `previous` means that no nonzero entry has yet occurred. -/
def signTransitions : SignType → List SignType → ℕ
  | _, [] => 0
  | previous, s :: l =>
      if s = 0 then signTransitions previous l
      else (if previous = 0 ∨ previous = s then 0 else 1) + signTransitions s l

lemma signTransitions_le_succ (p q : SignType) (l : List SignType) :
    signTransitions p l ≤ signTransitions q l + 1 := by
  induction l generalizing p q with
  | nil => simp [signTransitions]
  | cons s l ih =>
      by_cases hs : s = 0
      · simp only [signTransitions, if_pos hs]
        exact ih p q
      · simp only [signTransitions, if_neg hs]
        split_ifs <;> omega

/-- Replacing an entry `b` immediately following `a` by the positive adjacent addition `a+b`
cannot create a new sign transition in the remaining list. -/
lemma signTransitions_sign_add_le (a b : ℝ) (l : List SignType) :
    signTransitions (SignType.sign a) (SignType.sign (a + b) :: l) ≤
      signTransitions (SignType.sign a) (SignType.sign b :: l) := by
  have hpn := signTransitions_le_succ (1 : SignType) (-1 : SignType) l
  have hnp := signTransitions_le_succ (-1 : SignType) (1 : SignType) l
  rcases lt_trichotomy a 0 with ha | ha | ha
  · rcases lt_trichotomy b 0 with hb | hb | hb
    · have hab : a + b < 0 := by linarith
      simp [signTransitions, sign_neg ha, sign_neg hb, sign_neg hab]
    · subst b
      simp [signTransitions, sign_neg ha]
    · rcases lt_trichotomy (a + b) 0 with hab | hab | hab
      · simp [signTransitions, sign_neg ha, sign_pos hb, sign_neg hab]
        omega
      · rw [hab]
        simp [signTransitions, sign_neg ha, sign_pos hb]
        omega
      · simp [signTransitions, sign_neg ha, sign_pos hb, sign_pos hab]
  · subst a
    simp [signTransitions]
  · rcases lt_trichotomy b 0 with hb | hb | hb
    · rcases lt_trichotomy (a + b) 0 with hab | hab | hab
      · simp [signTransitions, sign_pos ha, sign_neg hb, sign_neg hab]
      · rw [hab]
        simp [signTransitions, sign_pos ha, sign_neg hb]
        omega
      · simp [signTransitions, sign_pos ha, sign_neg hb, sign_pos hab]
        omega
    · subst b
      simp [signTransitions, sign_pos ha]
    · have hab : 0 < a + b := by linarith
      simp [signTransitions, sign_pos ha, sign_pos hb, sign_pos hab]

lemma signTransitions_cons_le_of_le (p s : SignType) (hs : s ≠ 0)
    {l₁ l₂ : List SignType} (h : signTransitions s l₁ ≤ signTransitions s l₂) :
    signTransitions p (s :: l₁) ≤ signTransitions p (s :: l₂) := by
  rw [signTransitions, signTransitions, if_neg hs, if_neg hs]
  omega

lemma signTransitions_adjacent_add_pair_le (p : SignType) (a b : ℝ)
    (l : List SignType) :
    signTransitions p (SignType.sign a :: SignType.sign (a + b) :: l) ≤
      signTransitions p (SignType.sign a :: SignType.sign b :: l) := by
  by_cases ha : SignType.sign a = 0
  · have haz : a = 0 := sign_eq_zero_iff.mp ha
    subst a
    simp [signTransitions]
  · apply signTransitions_cons_le_of_le p (SignType.sign a) ha
    exact signTransitions_sign_add_le a b l

/-- Add the entry at `j-1` to the entry at `j`, leaving every other list entry fixed. -/
def adjacentAddAt : ℕ → List ℝ → List ℝ
  | _, [] => []
  | _, [a] => [a]
  | 0, a :: b :: l => a :: b :: l
  | 1, a :: b :: l => a :: (a + b) :: l
  | j + 2, a :: b :: l => a :: adjacentAddAt (j + 1) (b :: l)

lemma signTransitions_adjacentAddAt_le (p : SignType) (j : ℕ) (l : List ℝ) :
    signTransitions p ((adjacentAddAt j l).map SignType.sign) ≤
      signTransitions p (l.map SignType.sign) := by
  induction j generalizing p l with
  | zero =>
      cases l with
      | nil => simp [adjacentAddAt, signTransitions]
      | cons a l =>
          cases l with
          | nil => simp [adjacentAddAt, signTransitions]
          | cons b l => simp [adjacentAddAt]
  | succ j ih =>
      cases l with
      | nil => simp [adjacentAddAt, signTransitions]
      | cons a l =>
          cases l with
          | nil => simp [adjacentAddAt, signTransitions]
          | cons b l =>
              cases j with
              | zero =>
                  simpa [adjacentAddAt] using
                    signTransitions_adjacent_add_pair_le p a b (l.map SignType.sign)
              | succ j =>
                  simp only [adjacentAddAt, List.map_cons]
                  by_cases ha : SignType.sign a = 0
                  · rw [signTransitions, signTransitions, if_pos ha, if_pos ha]
                    exact ih p (b :: l)
                  · apply signTransitions_cons_le_of_le p (SignType.sign a) ha
                    exact ih (SignType.sign a) (b :: l)

/-- Sign variations of a finite real coefficient list, read in its given order. -/
noncomputable def listSignVariations (l : List ℝ) : ℕ :=
  signTransitions 0 (l.map SignType.sign)

lemma listSignVariations_adjacentAddAt_le (j : ℕ) (l : List ℝ) :
    listSignVariations (adjacentAddAt j l) ≤ listSignVariations l :=
  signTransitions_adjacentAddAt_le 0 j l

lemma signTransitions_eq_destutter'_length_sub_one (p : SignType) (hp : p ≠ 0)
    (l : List SignType) :
    signTransitions p l =
      ((l.filter (· ≠ 0)).destutter' (· ≠ ·) p).length - 1 := by
  induction l generalizing p with
  | nil => simp [signTransitions]
  | cons s l ih =>
      by_cases hs : s = 0
      · subst s
        simp [signTransitions, ih p hp]
      · rw [signTransitions, if_neg hs]
        simp only [List.filter_cons, decide_eq_true_eq]
        conv_rhs => rw [if_pos hs]
        rw [List.destutter'_cons]
        by_cases hps : p = s
        · subst p
          simp [ih s hs]
        · rw [if_pos hps]
          simp only [hp, hps, or_self, if_false]
          rw [ih s hs]
          have hn : 0 < ((l.filter (· ≠ 0)).destutter' (· ≠ ·) s).length :=
            List.length_pos_of_ne_nil (List.destutter'_ne_nil (l.filter (· ≠ 0)) (· ≠ ·))
          simp only [List.length_cons]
          omega

lemma signTransitions_filter_nonzero (p : SignType) (l : List SignType) :
    signTransitions p l = signTransitions p (l.filter (· ≠ 0)) := by
  induction l generalizing p with
  | nil => simp [signTransitions]
  | cons s l ih =>
      by_cases hs : s = 0
      · subst s
        simp [signTransitions, ih]
      · rw [signTransitions, if_neg hs]
        simp only [List.filter_cons, decide_eq_true_eq]
        conv_rhs => rw [if_pos hs]
        conv_rhs => rw [signTransitions, if_neg hs]
        rw [ih s]

lemma signTransitions_zero_eq_destutter_length_sub_one (l : List SignType) :
    signTransitions 0 l =
      ((l.filter (· ≠ 0)).destutter (· ≠ ·)).length - 1 := by
  rw [signTransitions_filter_nonzero]
  generalize hfilter : l.filter (· ≠ 0) = nz
  cases nz with
  | nil => simp [signTransitions]
  | cons s t =>
      have hs : s ≠ 0 := by
        have hm : s ∈ l.filter (· ≠ 0) := by rw [hfilter]; simp
        exact of_decide_eq_true (List.mem_filter.mp hm).2
      have ht : t.filter (· ≠ 0) = t := by
        apply List.filter_eq_self.mpr
        intro x hx
        have hm : x ∈ l.filter (· ≠ 0) := by rw [hfilter]; simp [hx]
        exact (List.mem_filter.mp hm).2
      rw [signTransitions, if_neg hs]
      simp only [true_or, if_true, zero_add]
      rw [signTransitions_eq_destutter'_length_sub_one s hs t, ht]
      rw [List.destutter_cons']

lemma listSignVariations_eq_destutter (l : List ℝ) :
    listSignVariations l =
      ((((l.map SignType.sign).filter (· ≠ 0)).destutter (· ≠ ·)).length - 1) := by
  exact signTransitions_zero_eq_destutter_length_sub_one (l.map SignType.sign)

lemma destutter_ne_length_reverse (l : List SignType) :
    (l.reverse.destutter (· ≠ ·)).length = (l.destutter (· ≠ ·)).length := by
  apply le_antisymm
  · let d := l.reverse.destutter (· ≠ ·)
    have hdsub : d.reverse.Sublist l := by
      have h := (List.destutter_sublist (· ≠ ·) l.reverse).reverse
      simpa [d] using h
    have hdchain : d.reverse.IsChain (· ≠ ·) := by
      rw [List.isChain_reverse]
      simpa [ne_comm, d] using List.isChain_destutter (· ≠ ·) l.reverse
    have hle := hdchain.length_le_length_destutter_ne hdsub
    simpa [d] using hle
  · let d := l.destutter (· ≠ ·)
    have hdsub : d.reverse.Sublist l.reverse := (List.destutter_sublist (· ≠ ·) l).reverse
    have hdchain : d.reverse.IsChain (· ≠ ·) := by
      rw [List.isChain_reverse]
      simpa [ne_comm, d] using List.isChain_destutter (· ≠ ·) l
    have hle := hdchain.length_le_length_destutter_ne hdsub
    simpa [d] using hle

lemma listSignVariations_reverse (l : List ℝ) :
    listSignVariations l.reverse = listSignVariations l := by
  rw [listSignVariations_eq_destutter, listSignVariations_eq_destutter]
  rw [List.map_reverse, List.filter_reverse, destutter_ne_length_reverse]

lemma polynomial_signVariations_eq_list (P : Polynomial ℝ) :
    P.signVariations = listSignVariations P.coeffList := by
  rw [listSignVariations_eq_destutter]
  rfl

end Erdos521
