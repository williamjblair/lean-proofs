import Research.AxisHorizontalEventTransfer
import Mathlib.Tactic

namespace Erdos521

noncomputable local instance axisVerticalEventDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

lemma scheduleDownEquiv_compl_fst {n : ℕ} (H : Finset (Fin n)) (S : Fin n → Bool) :
    (scheduleDownEquiv Hᶜ S).1 = (scheduleDownEquiv H S).2 := by
  ext i
  simp

lemma scheduleDownEquiv_compl_snd {n : ℕ} (H : Finset (Fin n)) (S : Fin n → Bool) :
    IsMeander (scheduleDownEquiv Hᶜ S).2 ↔ IsMeander (scheduleDownEquiv H S).1 := by
  rw [scheduleDownEquiv_snd_eq, scheduleDownEquiv_fst_eq, compl_compl]

lemma axisGood_compl_iff {n : ℕ} (H : Finset (Fin n)) (S : Fin n → Bool) :
    AxisGood Hᶜ S ↔ AxisGood H S := by
  rw [AxisGood, AxisGood, scheduleDownEquiv_compl_fst,
    scheduleDownEquiv_compl_snd]
  tauto

noncomputable def rotateAxisGoodPath {n : ℕ} (p : AxisGoodPath n) : AxisGoodPath n :=
  ⟨(p.1.1ᶜ, p.1.2), (axisGood_compl_iff p.1.1 p.1.2).mpr p.property⟩

lemma rotateAxisGoodPath_involutive {n : ℕ} : Function.Involutive
    (rotateAxisGoodPath : AxisGoodPath n → AxisGoodPath n) := by
  intro p
  apply Subtype.ext
  apply Prod.ext
  · simp [rotateAxisGoodPath]
  · rfl

noncomputable def rotateAxisGoodEquiv (n : ℕ) : AxisGoodPath n ≃ AxisGoodPath n where
  toFun := rotateAxisGoodPath
  invFun := rotateAxisGoodPath
  left_inv := rotateAxisGoodPath_involutive
  right_inv := rotateAxisGoodPath_involutive

noncomputable def swapAxisWord {r : ℕ} (w : AxisWord r) : AxisWord r :=
  (fun i ↦ !(w.1 i), w.2)

lemma axisSuffix_rotate {s r : ℕ} (p : AxisGoodPath (s + r)) :
    axisSuffix (rotateAxisGoodPath p) = swapAxisWord (axisSuffix p) := by
  apply Prod.ext
  · funext i
    simp [axisSuffix, rotateAxisGoodPath, swapAxisWord]
  · rfl

lemma pairHorizontal_swapAxisWord {r : ℕ} (w : AxisWord r) (j : Fin r) :
    pairHorizontal (axisWordCoefficients (swapAxisWord w)) j.val =
      pairVertical (axisWordCoefficients w) j.val := by
  rw [pairHorizontal_axisWord, pairVertical_axisWord]
  cases h : w.1 j.rev <;> simp [swapAxisWord, h]

lemma pairVertical_swapAxisWord {r : ℕ} (w : AxisWord r) (j : Fin r) :
    pairVertical (axisWordCoefficients (swapAxisWord w)) j.val =
      pairHorizontal (axisWordCoefficients w) j.val := by
  rw [pairVertical_axisWord, pairHorizontal_axisWord]
  cases h : w.1 j.rev <;> simp [swapAxisWord, h]

lemma swapAxisWord_involutive {r : ℕ} : Function.Involutive (swapAxisWord : AxisWord r → AxisWord r) := by
  intro w
  apply Prod.ext
  · funext i
    simp [swapAxisWord]
  · rfl

noncomputable def swapAxisWordEquiv (r : ℕ) : AxisWord r ≃ AxisWord r where
  toFun := swapAxisWord
  invFun := swapAxisWord
  left_inv := swapAxisWord_involutive
  right_inv := swapAxisWord_involutive

noncomputable def swappedAxisWords {r : ℕ} (E : Finset (AxisWord r)) :
    Finset (AxisWord r) := Finset.univ.filter fun w ↦ swapAxisWord w ∈ E

@[simp] lemma mem_swappedAxisWords {r : ℕ} (E : Finset (AxisWord r)) (w : AxisWord r) :
    w ∈ swappedAxisWords E ↔ swapAxisWord w ∈ E := by
  simp [swappedAxisWords]

lemma swappedAxisWords_card {r : ℕ} (E : Finset (AxisWord r)) :
    (swappedAxisWords E).card = E.card := by
  apply Finset.card_equiv (swapAxisWordEquiv r)
  intro w
  simpa [swapAxisWordEquiv] using (mem_swappedAxisWords E w)

lemma pairVertical_swap_horizontalSuffix_eq_core {s r : ℕ}
    (p : HorizontalGoodPath (s + r)) (j : Fin r) :
    pairVertical (axisWordCoefficients (swapAxisWord (horizontalAxisSuffix p))) j.val =
      pairVertical (axisWordCoefficients
        (swapAxisWord (horizontalCoreCanonicalSuffix (oneCoordinateHorizontalCore p)))) j.val := by
  calc
    _ = pairHorizontal (axisWordCoefficients (horizontalAxisSuffix p)) j.val :=
      pairVertical_swapAxisWord _ j
    _ = pairHorizontal (axisWordCoefficients
        (horizontalCoreCanonicalSuffix (oneCoordinateHorizontalCore p))) j.val :=
      pairHorizontal_horizontalSuffix_eq_core p j
    _ = _ := (pairVertical_swapAxisWord _ j).symm

lemma pairVertical_swap_axisSuffix_eq_core {s r : ℕ}
    (p : AxisGoodPath (s + r)) (j : Fin r) :
    pairVertical (axisWordCoefficients (swapAxisWord (axisSuffix p))) j.val =
      pairVertical (axisWordCoefficients
        (swapAxisWord (horizontalCoreCanonicalSuffix (axisHorizontalCore p)))) j.val := by
  calc
    _ = pairHorizontal (axisWordCoefficients (axisSuffix p)) j.val :=
      pairVertical_swapAxisWord _ j
    _ = pairHorizontal (axisWordCoefficients
        (horizontalCoreCanonicalSuffix (axisHorizontalCore p))) j.val :=
      pairHorizontal_axisSuffix_eq_core p j
    _ = _ := (pairVertical_swapAxisWord _ j).symm

lemma fourthVerticalEven_swap_horizontalSuffix_eq_core {s r m : ℕ} (hm : m < r)
    (p : HorizontalGoodPath (s + r)) :
    fourthVerticalEven (axisWordCoefficients (swapAxisWord (horizontalAxisSuffix p))) m =
      fourthVerticalEven (axisWordCoefficients
        (swapAxisWord (horizontalCoreCanonicalSuffix (oneCoordinateHorizontalCore p)))) m := by
  unfold fourthVerticalEven
  apply Finset.sum_congr rfl
  intro j hj
  have hjr : j < r := (Finset.mem_range.mp hj).trans_le (by omega)
  rw [pairVertical_swap_horizontalSuffix_eq_core p ⟨j, hjr⟩]

lemma fourthVerticalOdd_swap_horizontalSuffix_eq_core {s r m : ℕ} (hm : m < r)
    (p : HorizontalGoodPath (s + r)) :
    fourthVerticalOdd (axisWordCoefficients (swapAxisWord (horizontalAxisSuffix p))) m =
      fourthVerticalOdd (axisWordCoefficients
        (swapAxisWord (horizontalCoreCanonicalSuffix (oneCoordinateHorizontalCore p)))) m := by
  unfold fourthVerticalOdd
  apply Finset.sum_congr rfl
  intro j hj
  have hjr : j < r := (Finset.mem_range.mp hj).trans_le (by omega)
  rw [pairVertical_swap_horizontalSuffix_eq_core p ⟨j, hjr⟩]

lemma fourthVerticalEven_swap_axisSuffix_eq_core {s r m : ℕ} (hm : m < r)
    (p : AxisGoodPath (s + r)) :
    fourthVerticalEven (axisWordCoefficients (swapAxisWord (axisSuffix p))) m =
      fourthVerticalEven (axisWordCoefficients
        (swapAxisWord (horizontalCoreCanonicalSuffix (axisHorizontalCore p)))) m := by
  unfold fourthVerticalEven
  apply Finset.sum_congr rfl
  intro j hj
  have hjr : j < r := (Finset.mem_range.mp hj).trans_le (by omega)
  rw [pairVertical_swap_axisSuffix_eq_core p ⟨j, hjr⟩]

lemma fourthVerticalOdd_swap_axisSuffix_eq_core {s r m : ℕ} (hm : m < r)
    (p : AxisGoodPath (s + r)) :
    fourthVerticalOdd (axisWordCoefficients (swapAxisWord (axisSuffix p))) m =
      fourthVerticalOdd (axisWordCoefficients
        (swapAxisWord (horizontalCoreCanonicalSuffix (axisHorizontalCore p)))) m := by
  unfold fourthVerticalOdd
  apply Finset.sum_congr rfl
  intro j hj
  have hjr : j < r := (Finset.mem_range.mp hj).trans_le (by omega)
  rw [pairVertical_swap_axisSuffix_eq_core p ⟨j, hjr⟩]

noncomputable def rotateAxisGoodSubtypeEquiv {n r : ℕ}
    (EV EH : Finset (AxisWord r))
    (hmem : ∀ w, w ∈ EV ↔ swapAxisWord w ∈ EH)
    (suffix : AxisGoodPath n → AxisWord r)
    (hrotate : ∀ p, suffix (rotateAxisGoodPath p) = swapAxisWord (suffix p)) :
    {p : AxisGoodPath n // suffix p ∈ EV} ≃ {p : AxisGoodPath n // suffix p ∈ EH} where
  toFun p := ⟨rotateAxisGoodPath p.1, by rw [hrotate]; exact (hmem _).mp p.property⟩
  invFun p := ⟨rotateAxisGoodPath p.1, by
    rw [hrotate]
    apply (hmem _).mpr
    rw [swapAxisWord_involutive]
    exact p.property⟩
  left_inv p := by
    apply Subtype.ext
    exact rotateAxisGoodPath_involutive p.1
  right_inv p := by
    apply Subtype.ext
    exact rotateAxisGoodPath_involutive p.1

/-- Transfer a terminal event which becomes horizontal-core measurable after swapping axes. -/
theorem axisGood_vertical_terminal_event_natCard_density_le
    (s r : ℕ) (hsr : 1 ≤ s + r)
    (E : Finset (AxisWord r))
    (Q : HorizontalCore (s + r) → Prop)
    (haxis : ∀ p : AxisGoodPath (s + r),
      swapAxisWord (axisSuffix p) ∈ E ↔ Q (axisHorizontalCore p))
    (hhorizontal : ∀ p : HorizontalGoodPath (s + r),
      swapAxisWord (horizontalAxisSuffix p) ∈ E ↔ Q (oneCoordinateHorizontalCore p)) :
    (Nat.card {p : AxisGoodPath (s + r) // axisSuffix p ∈ E} : ℝ) /
        Nat.card (AxisGoodPath (s + r)) ≤
      128 * Real.sqrt (((s : ℝ) + r + 1) / (s + 1)) *
          ((E.card : ℝ) / (4 : ℝ) ^ r) +
        16 * ((s : ℝ) + r + 1) * Real.exp (-((s : ℝ) + r) / 8) := by
  let ES := swappedAxisWords E
  have haxis' : ∀ p : AxisGoodPath (s + r),
      axisSuffix p ∈ ES ↔ Q (axisHorizontalCore p) := by
    intro p
    simpa [ES] using haxis p
  have hhorizontal' : ∀ p : HorizontalGoodPath (s + r),
      horizontalAxisSuffix p ∈ ES ↔ Q (oneCoordinateHorizontalCore p) := by
    intro p
    simpa [ES] using hhorizontal p
  have h := axisGood_horizontal_terminal_event_natCard_density_le s r hsr ES Q
    (fun p ↦ axisSuffix p ∈ ES) haxis' hhorizontal'
  rw [show ES.card = E.card from swappedAxisWords_card E] at h
  have hmem : ∀ w, w ∈ E ↔ swapAxisWord w ∈ ES := by
    intro w
    dsimp [ES]
    rw [mem_swappedAxisWords, swapAxisWord_involutive w]
  have he := rotateAxisGoodSubtypeEquiv E ES hmem
    (axisSuffix : AxisGoodPath (s + r) → AxisWord r) axisSuffix_rotate
  rw [Nat.card_congr he]
  exact h

lemma fourthVerticalEven_axisGood_density_le (s r m : ℕ) (hm : m < r) (T : ℝ) :
    (Nat.card {p : AxisGoodPath (s + r) //
        axisSuffix p ∈ (Finset.univ.filter fun w : AxisWord r ↦
          T ≤ |fourthVerticalEven (axisWordCoefficients w) m|)} : ℝ) /
        Nat.card (AxisGoodPath (s + r)) ≤
      128 * Real.sqrt (((s : ℝ) + r + 1) / (s + 1)) *
          (((Finset.univ.filter fun w : AxisWord r ↦
            T ≤ |fourthVerticalEven (axisWordCoefficients w) m|).card : ℝ) /
              (4 : ℝ) ^ r) +
        16 * ((s : ℝ) + r + 1) * Real.exp (-((s : ℝ) + r) / 8) := by
  let E : Finset (AxisWord r) := Finset.univ.filter fun w ↦
    T ≤ |fourthVerticalEven (axisWordCoefficients w) m|
  let Q : HorizontalCore (s + r) → Prop := fun c ↦
    T ≤ |fourthVerticalEven (axisWordCoefficients
      (swapAxisWord (horizontalCoreCanonicalSuffix c))) m|
  apply axisGood_vertical_terminal_event_natCard_density_le s r (by omega) E Q
  · intro p
    simp only [E, Q, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [fourthVerticalEven_swap_axisSuffix_eq_core hm p]
  · intro p
    simp only [E, Q, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [fourthVerticalEven_swap_horizontalSuffix_eq_core hm p]

lemma fourthVerticalOdd_axisGood_density_le (s r m : ℕ) (hm : m < r) (T : ℝ) :
    (Nat.card {p : AxisGoodPath (s + r) //
        axisSuffix p ∈ (Finset.univ.filter fun w : AxisWord r ↦
          T ≤ |fourthVerticalOdd (axisWordCoefficients w) m|)} : ℝ) /
        Nat.card (AxisGoodPath (s + r)) ≤
      128 * Real.sqrt (((s : ℝ) + r + 1) / (s + 1)) *
          (((Finset.univ.filter fun w : AxisWord r ↦
            T ≤ |fourthVerticalOdd (axisWordCoefficients w) m|).card : ℝ) /
              (4 : ℝ) ^ r) +
        16 * ((s : ℝ) + r + 1) * Real.exp (-((s : ℝ) + r) / 8) := by
  let E : Finset (AxisWord r) := Finset.univ.filter fun w ↦
    T ≤ |fourthVerticalOdd (axisWordCoefficients w) m|
  let Q : HorizontalCore (s + r) → Prop := fun c ↦
    T ≤ |fourthVerticalOdd (axisWordCoefficients
      (swapAxisWord (horizontalCoreCanonicalSuffix c))) m|
  apply axisGood_vertical_terminal_event_natCard_density_le s r (by omega) E Q
  · intro p
    simp only [E, Q, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [fourthVerticalOdd_swap_axisSuffix_eq_core hm p]
  · intro p
    simp only [E, Q, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [fourthVerticalOdd_swap_horizontalSuffix_eq_core hm p]

end Erdos521
