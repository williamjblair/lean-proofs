import Research.FourthPairDecomposition
import Research.ConeCrossingTransfer
import Mathlib.Tactic

namespace Erdos521

noncomputable local instance axisPairCoordinatesDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

lemma axisWord_pair_bits_equal_iff {r : ℕ} (w : AxisWord r) (j : Fin r) :
    axisWordBits w ⟨2 * j.val, by omega⟩ =
        axisWordBits w ⟨2 * j.val + 1, by omega⟩ ↔
      w.1 j.rev = true := by
  let x := axisWordBits w
  have hs := bitsAxisEquiv_schedule x j.rev
  have hdata : bitsAxisEquiv r x = axisWordDataEquiv r w := by
    dsimp [x, axisWordBits, axisWordBitsEquiv]
    rw [(bitsAxisEquiv r).apply_symm_apply]
  rw [hdata, mem_axisWordDataEquiv_fst] at hs
  have hrev : j.rev.rev = j := Fin.rev_rev j
  simpa [x, hrev] using hs.symm

lemma axisWord_odd_pair_bit {r : ℕ} (w : AxisWord r) (j : Fin r) :
    axisWordBits w ⟨2 * j.val + 1, by omega⟩ = w.2 j.rev := by
  let x := axisWordBits w
  have hs := bitsAxisEquiv_sign x j.rev
  have hdata : bitsAxisEquiv r x = axisWordDataEquiv r w := by
    dsimp [x, axisWordBits, axisWordBitsEquiv]
    rw [(bitsAxisEquiv r).apply_symm_apply]
  rw [hdata, axisWordDataEquiv_snd] at hs
  have hrev : j.rev.rev = j := Fin.rev_rev j
  simpa [x, hrev] using hs.symm

/-- In path coordinates, the pair-horizontal value is the scheduled sign, or zero on vertical
steps.  Coefficient pair `j` corresponds to reversed path step `j.rev`. -/
lemma pairHorizontal_axisWord {r : ℕ} (w : AxisWord r) (j : Fin r) :
    pairHorizontal (axisWordCoefficients w) j.val =
      if w.1 j.rev = true then sign (w.2 j.rev) else 0 := by
  unfold pairHorizontal
  have heven : axisWordCoefficients w (2 * j.val) =
      axisWordBits w ⟨2 * j.val, by omega⟩ := by
    exact extendBits_of_lt _ (by omega)
  have hoddCoeff : axisWordCoefficients w (2 * j.val + 1) =
      axisWordBits w ⟨2 * j.val + 1, by omega⟩ := by
    exact extendBits_of_lt _ (by omega)
  rw [heven, hoddCoeff]
  have heq := axisWord_pair_bits_equal_iff w j
  have hodd := axisWord_odd_pair_bit w j
  by_cases hH : w.1 j.rev = true
  · rw [if_pos hH]
    have hb := heq.mpr hH
    rw [hb, hodd]
    ring
  · rw [if_neg hH]
    have hb : axisWordBits w ⟨2 * j.val, by omega⟩ ≠
        axisWordBits w ⟨2 * j.val + 1, by omega⟩ := by
      intro h
      exact hH (heq.mp h)
    have hz := sign_add_eq_zero_of_ne
      (axisWordBits w ⟨2 * j.val, by omega⟩)
      (axisWordBits w ⟨2 * j.val + 1, by omega⟩) hb
    rw [add_comm] at hz
    rw [hz]
    norm_num

/-- The pair-vertical value is zero on horizontal steps and the scheduled sign on vertical steps. -/
lemma pairVertical_axisWord {r : ℕ} (w : AxisWord r) (j : Fin r) :
    pairVertical (axisWordCoefficients w) j.val =
      if w.1 j.rev = true then 0 else sign (w.2 j.rev) := by
  unfold pairVertical
  have heven : axisWordCoefficients w (2 * j.val) =
      axisWordBits w ⟨2 * j.val, by omega⟩ := by
    exact extendBits_of_lt _ (by omega)
  have hoddCoeff : axisWordCoefficients w (2 * j.val + 1) =
      axisWordBits w ⟨2 * j.val + 1, by omega⟩ := by
    exact extendBits_of_lt _ (by omega)
  rw [heven, hoddCoeff]
  have heq := axisWord_pair_bits_equal_iff w j
  have hodd := axisWord_odd_pair_bit w j
  by_cases hH : w.1 j.rev = true
  · rw [if_pos hH]
    have hb := heq.mpr hH
    rw [hb]
    ring
  · rw [if_neg hH]
    have hb : axisWordBits w ⟨2 * j.val, by omega⟩ ≠
        axisWordBits w ⟨2 * j.val + 1, by omega⟩ := by
      intro h
      exact hH (heq.mp h)
    have hz := sign_sub_eq_two_mul_of_ne
      (axisWordBits w ⟨2 * j.val, by omega⟩)
      (axisWordBits w ⟨2 * j.val + 1, by omega⟩) hb
    rw [hodd] at hz ⊢
    rw [hz]
    ring

end Erdos521
