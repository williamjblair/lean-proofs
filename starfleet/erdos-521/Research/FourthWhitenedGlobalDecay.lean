import Research.FourthGlobalCharacteristicDecay
import Mathlib.Tactic

open scoped BigOperators

namespace Erdos521

noncomputable def fourthWhitenedToOriginalS (k : ℕ) (u v : ℝ) : ℝ :=
  u / Real.sqrt (fourthVarianceA k) -
    v * fourthIncrementCovarianceC k /
      Real.sqrt (fourthVarianceA k * fourthDet k)

noncomputable def fourthWhitenedToOriginalT (k : ℕ) (_u v : ℝ) : ℝ :=
  v * fourthVarianceA k / Real.sqrt (fourthVarianceA k * fourthDet k)

noncomputable def fourthWhitenedCharacteristicProduct (k : ℕ) (u v : ℝ) : ℝ :=
  Real.cos (v * fourthWhitenedNewY k) *
    ∏ q : Fin (k + 1),
      Real.cos (u * fourthWhitenedX k q + v * fourthWhitenedY k q)

lemma fourthPhase_eq_original_transformed (k : ℕ) (u v : ℝ)
    (i : Option (Fin (k + 1))) :
    fourthPhase k u v i = fourthOriginalPhase k
      (fourthWhitenedToOriginalS k u v) (fourthWhitenedToOriginalT k u v) i := by
  cases i with
  | none =>
      unfold fourthPhase fourthOriginalPhase fourthWhitenedToOriginalT
        fourthWhitenedNewY
      ring
  | some q =>
      unfold fourthPhase fourthOriginalPhase fourthWhitenedToOriginalS
        fourthWhitenedToOriginalT fourthWhitenedX fourthWhitenedY
      ring

lemma fourthWhitenedCharacteristicProduct_eq_original (k : ℕ) (u v : ℝ) :
    fourthWhitenedCharacteristicProduct k u v =
      fourthOriginalCharacteristicProduct k
        (fourthWhitenedToOriginalS k u v) (fourthWhitenedToOriginalT k u v) := by
  unfold fourthWhitenedCharacteristicProduct fourthOriginalCharacteristicProduct
  rw [Fintype.prod_option]
  apply congrArg₂ (· * ·)
  · rw [← fourthPhase_eq_original_transformed k u v none]
    rfl
  · apply Finset.prod_congr rfl
    intro q hq
    rw [← fourthPhase_eq_original_transformed k u v (some q)]
    rfl

lemma fourthOriginalPhase_transformed_sq_sum (k : ℕ) (u v : ℝ) :
    (∑ i : Option (Fin (k + 1)),
      fourthOriginalPhase k (fourthWhitenedToOriginalS k u v)
        (fourthWhitenedToOriginalT k u v) i ^ 2) = u ^ 2 + v ^ 2 := by
  have h := fourthPhase_fintype_sq_sum k u v
  simpa only [fourthPhase_eq_original_transformed] using h

/-- F-083 expressed in covariance-whitened coordinates. On the transformed fundamental cell it
is a radial Gaussian/macroscopic minimum bound. -/
lemma fourthWhitenedCharacteristicProduct_global_decay
    (N : ℕ) (hN : 20 ≤ N) (u v : ℝ)
    (hs : |fourthWhitenedToOriginalS (N + 2) u v| ≤ Real.pi / 2)
    (ht : |fourthWhitenedToOriginalT (N + 2) u v| ≤ Real.pi / 2) :
    |fourthWhitenedCharacteristicProduct (N + 2) u v| ≤
      Real.exp (-(2 / Real.pi ^ 2) *
        min ((N : ℝ) / 100000000000000000000)
          ((u ^ 2 + v ^ 2) / 3000000000)) := by
  rw [fourthWhitenedCharacteristicProduct_eq_original]
  have h := fourthOriginalCharacteristicProduct_global_decay N hN
    (fourthWhitenedToOriginalS (N + 2) u v)
    (fourthWhitenedToOriginalT (N + 2) u v) hs ht
  rw [fourthOriginalPhase_transformed_sq_sum] at h
  exact h

end Erdos521
