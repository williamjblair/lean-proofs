import Research.AxisTerminalCoordinateTransfer
import Research.FourthOddCoordinateEvents
import Research.AxisPairCoordinates
import Mathlib.Tactic

namespace Erdos521

noncomputable local instance horizontalCoreFormsDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

noncomputable def horizontalCoreCanonicalSign {n : ℕ} (c : HorizontalCore n) : Fin n → Bool :=
  (scheduleDownEquiv c.1).symm (c.2.1, ∅)

noncomputable def horizontalCoreCanonicalPath {n : ℕ} (c : HorizontalCore n) :
    Finset (Fin n) × (Fin n → Bool) :=
  (c.1, horizontalCoreCanonicalSign c)

noncomputable def rawAxisSuffix {s r : ℕ}
    (w : Finset (Fin (s + r)) × (Fin (s + r) → Bool)) : AxisWord r :=
  (fun i ↦ decide (Fin.natAdd s i ∈ w.1),
    fun i ↦ w.2 (Fin.natAdd s i))

noncomputable def horizontalCoreCanonicalSuffix {s r : ℕ} (c : HorizontalCore (s + r)) :
    AxisWord r := rawAxisSuffix (horizontalCoreCanonicalPath c)

lemma oneCoordinateHorizontalCore_fst {n : ℕ} (p : HorizontalGoodPath n) :
    (oneCoordinateHorizontalCore p).1 = p.1.1 := rfl

lemma oneCoordinateHorizontalCore_snd_val {n : ℕ} (p : HorizontalGoodPath n) :
    (oneCoordinateHorizontalCore p).2.1 = (scheduleDownEquiv p.1.1 p.1.2).1 := rfl

lemma axisHorizontalCore_fst {n : ℕ} (p : AxisGoodPath n) :
    (axisHorizontalCore p).1 = p.1.1 := rfl

lemma axisHorizontalCore_snd_val {n : ℕ} (p : AxisGoodPath n) :
    (axisHorizontalCore p).2.1 = (scheduleDownEquiv p.1.1 p.1.2).1 := rfl

lemma horizontalCoreCanonical_compressed_fst {n : ℕ} (c : HorizontalCore n) :
    (scheduleDownEquiv c.1 (horizontalCoreCanonicalSign c)).1 = c.2.1 := by
  unfold horizontalCoreCanonicalSign
  exact congrArg Prod.fst ((scheduleDownEquiv c.1).apply_symm_apply (c.2.1, ∅))

lemma sign_eq_of_compressed_fst_eq {n : ℕ} (H : Finset (Fin n))
    (S U : Fin n → Bool)
    (h : (scheduleDownEquiv H S).1 = (scheduleDownEquiv H U).1)
    (i : Fin n) (hi : i ∈ H) : S i = U i := by
  let j : Fin H.card := (H.orderIsoOfFin rfl).symm ⟨i, hi⟩
  have hj := congrArg (fun D : Finset (Fin H.card) ↦ j ∈ D) h
  have happ := (H.orderIsoOfFin rfl).apply_symm_apply ⟨i, hi⟩
  have he : H.orderEmbOfFin rfl j = i := congrArg Subtype.val happ
  simp only [mem_scheduleDownEquiv_fst] at hj
  rw [he] at hj
  cases hS : S i <;> cases hU : U i <;> simp_all

lemma horizontalGood_sign_eq_canonical {n : ℕ} (p : HorizontalGoodPath n)
    (i : Fin n) (hi : i ∈ p.1.1) :
    p.1.2 i = horizontalCoreCanonicalSign (oneCoordinateHorizontalCore p) i := by
  apply sign_eq_of_compressed_fst_eq p.1.1
  · rw [← oneCoordinateHorizontalCore_snd_val p]
    have hc := horizontalCoreCanonical_compressed_fst (oneCoordinateHorizontalCore p)
    convert hc.symm
    all_goals first | exact (oneCoordinateHorizontalCore_fst p).symm | rfl
  · exact hi

lemma axisGood_sign_eq_canonical {n : ℕ} (p : AxisGoodPath n)
    (i : Fin n) (hi : i ∈ p.1.1) :
    p.1.2 i = horizontalCoreCanonicalSign (axisHorizontalCore p) i := by
  apply sign_eq_of_compressed_fst_eq p.1.1
  · rw [← axisHorizontalCore_snd_val p]
    have hc := horizontalCoreCanonical_compressed_fst (axisHorizontalCore p)
    convert hc.symm
    all_goals first | exact (axisHorizontalCore_fst p).symm | rfl
  · exact hi

lemma horizontalAxisSuffix_eq_raw {s r : ℕ} (p : HorizontalGoodPath (s + r)) :
    horizontalAxisSuffix p = rawAxisSuffix p.1 := by
  apply Prod.ext
  · ext i
    simp [horizontalAxisSuffix, rawAxisSuffix]
  · rfl

lemma axisSuffix_eq_raw {s r : ℕ} (p : AxisGoodPath (s + r)) :
    axisSuffix p = rawAxisSuffix p.1 := by
  apply Prod.ext
  · ext i
    simp [axisSuffix, rawAxisSuffix]
  · rfl

lemma pairHorizontal_horizontalSuffix_eq_core {s r : ℕ}
    (p : HorizontalGoodPath (s + r)) (j : Fin r) :
    pairHorizontal (axisWordCoefficients (horizontalAxisSuffix p)) j.val =
      pairHorizontal (axisWordCoefficients
        (horizontalCoreCanonicalSuffix (oneCoordinateHorizontalCore p))) j.val := by
  rw [pairHorizontal_axisWord, pairHorizontal_axisWord]
  let i : Fin (s + r) := Fin.natAdd s j.rev
  by_cases hi : i ∈ p.1.1
  · have hs : p.1.2 i =
        horizontalCoreCanonicalSign (oneCoordinateHorizontalCore p) i :=
      horizontalGood_sign_eq_canonical p i hi
    simp only [horizontalAxisSuffix, horizontalCoreCanonicalSuffix, rawAxisSuffix,
      horizontalCoreCanonicalPath]
    rw [if_pos (by simpa [i] using hi),
      if_pos (by simpa [i, oneCoordinateHorizontalCore_fst] using hi)]
    exact congrArg sign hs
  · simp only [horizontalAxisSuffix, horizontalCoreCanonicalSuffix, rawAxisSuffix,
      horizontalCoreCanonicalPath]
    rw [if_neg (by simpa [i] using hi),
      if_neg (by simpa [i, oneCoordinateHorizontalCore_fst] using hi)]

lemma pairHorizontal_axisSuffix_eq_core {s r : ℕ}
    (p : AxisGoodPath (s + r)) (j : Fin r) :
    pairHorizontal (axisWordCoefficients (axisSuffix p)) j.val =
      pairHorizontal (axisWordCoefficients
        (horizontalCoreCanonicalSuffix (axisHorizontalCore p))) j.val := by
  rw [pairHorizontal_axisWord, pairHorizontal_axisWord]
  let i : Fin (s + r) := Fin.natAdd s j.rev
  by_cases hi : i ∈ p.1.1
  · have hs : p.1.2 i =
        horizontalCoreCanonicalSign (axisHorizontalCore p) i :=
      axisGood_sign_eq_canonical p i hi
    simp only [axisSuffix, horizontalCoreCanonicalSuffix, rawAxisSuffix,
      horizontalCoreCanonicalPath]
    rw [if_pos (by simpa [i] using hi),
      if_pos (by simpa [i, axisHorizontalCore_fst] using hi)]
    exact congrArg sign hs
  · simp only [axisSuffix, horizontalCoreCanonicalSuffix, rawAxisSuffix,
      horizontalCoreCanonicalPath]
    rw [if_neg (by simpa [i] using hi),
      if_neg (by simpa [i, axisHorizontalCore_fst] using hi)]

lemma fourthHorizontalEven_horizontalSuffix_eq_core {s r m : ℕ} (hm : m < r)
    (p : HorizontalGoodPath (s + r)) :
    fourthHorizontalEven (axisWordCoefficients (horizontalAxisSuffix p)) m =
      fourthHorizontalEven (axisWordCoefficients
        (horizontalCoreCanonicalSuffix (oneCoordinateHorizontalCore p))) m := by
  unfold fourthHorizontalEven
  apply Finset.sum_congr rfl
  intro j hj
  have hjr : j < r := (Finset.mem_range.mp hj).trans_le (by omega)
  rw [pairHorizontal_horizontalSuffix_eq_core p ⟨j, hjr⟩]

lemma fourthHorizontalOdd_horizontalSuffix_eq_core {s r m : ℕ} (hm : m < r)
    (p : HorizontalGoodPath (s + r)) :
    fourthHorizontalOdd (axisWordCoefficients (horizontalAxisSuffix p)) m =
      fourthHorizontalOdd (axisWordCoefficients
        (horizontalCoreCanonicalSuffix (oneCoordinateHorizontalCore p))) m := by
  unfold fourthHorizontalOdd
  apply Finset.sum_congr rfl
  intro j hj
  have hjr : j < r := (Finset.mem_range.mp hj).trans_le (by omega)
  rw [pairHorizontal_horizontalSuffix_eq_core p ⟨j, hjr⟩]

lemma fourthHorizontalEven_axisSuffix_eq_core {s r m : ℕ} (hm : m < r)
    (p : AxisGoodPath (s + r)) :
    fourthHorizontalEven (axisWordCoefficients (axisSuffix p)) m =
      fourthHorizontalEven (axisWordCoefficients
        (horizontalCoreCanonicalSuffix (axisHorizontalCore p))) m := by
  unfold fourthHorizontalEven
  apply Finset.sum_congr rfl
  intro j hj
  have hjr : j < r := (Finset.mem_range.mp hj).trans_le (by omega)
  rw [pairHorizontal_axisSuffix_eq_core p ⟨j, hjr⟩]

lemma fourthHorizontalOdd_axisSuffix_eq_core {s r m : ℕ} (hm : m < r)
    (p : AxisGoodPath (s + r)) :
    fourthHorizontalOdd (axisWordCoefficients (axisSuffix p)) m =
      fourthHorizontalOdd (axisWordCoefficients
        (horizontalCoreCanonicalSuffix (axisHorizontalCore p))) m := by
  unfold fourthHorizontalOdd
  apply Finset.sum_congr rfl
  intro j hj
  have hjr : j < r := (Finset.mem_range.mp hj).trans_le (by omega)
  rw [pairHorizontal_axisSuffix_eq_core p ⟨j, hjr⟩]

end Erdos521
