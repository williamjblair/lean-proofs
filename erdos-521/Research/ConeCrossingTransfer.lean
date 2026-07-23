import Research.ConeSuffixDensity
import Mathlib.Tactic

open scoped BigOperators

namespace Erdos521

noncomputable local instance coneCrossingTransferDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

/-- Turn the Boolean schedule coordinate of an axis word into its set of `true` locations. -/
def axisWordDataEquiv (r : ℕ) :
    AxisWord r ≃ (Finset (Fin r) × (Fin r → Bool)) where
  toFun w := (Finset.univ.filter (fun i ↦ w.1 i = true), w.2)
  invFun d := (fun i ↦ decide (i ∈ d.1), d.2)
  left_inv w := by
    apply Prod.ext
    · funext i
      cases h : w.1 i <;> simp [h]
    · rfl
  right_inv d := by
    apply Prod.ext
    · ext i
      simp
    · rfl

/-- Exact equivalence reconstructing the low-to-high coefficient bits encoded by an
unconstrained axis word. -/
@[simp] lemma mem_axisWordDataEquiv_fst {r : ℕ} (w : AxisWord r) (i : Fin r) :
    i ∈ (axisWordDataEquiv r w).1 ↔ w.1 i = true := by
  simp [axisWordDataEquiv]

@[simp] lemma axisWordDataEquiv_snd {r : ℕ} (w : AxisWord r) :
    (axisWordDataEquiv r w).2 = w.2 := rfl

def axisWordBitsEquiv (r : ℕ) : AxisWord r ≃ (Fin (2 * r) → Bool) :=
  (axisWordDataEquiv r).trans (bitsAxisEquiv r).symm

def axisWordBits {r : ℕ} (w : AxisWord r) : Fin (2 * r) → Bool :=
  axisWordBitsEquiv r w

/-- Extend an axis word to an infinite coefficient sequence, padding by `false`. -/
def axisWordCoefficients {r : ℕ} (w : AxisWord r) : ℕ → Bool :=
  extendBits r (axisWordBits w)

/-- Restrict a longer finite coefficient word to its lowest `2r` coefficients. -/
def lowCoefficientBits {s r : ℕ} (x : Fin (2 * (s + r)) → Bool) : Fin (2 * r) → Bool :=
  fun i ↦ x ⟨i.val, by omega⟩

/-- The terminal axis word is exactly the axis encoding of the low coefficient block. -/
lemma axisWordBits_axisSuffix_bitsAxis {s r : ℕ} (x : Fin (2 * (s + r)) → Bool)
    (hgood : AxisGood (bitsAxisEquiv (s + r) x).1 (bitsAxisEquiv (s + r) x).2) :
    axisWordBits (axisSuffix
      (⟨bitsAxisEquiv (s + r) x, hgood⟩ : AxisGoodPath (s + r))) =
      lowCoefficientBits x := by
  apply (bitsAxisEquiv r).injective
  simp only [axisWordBits, axisWordBitsEquiv, Equiv.trans_apply,
    Equiv.apply_symm_apply]
  apply Prod.ext
  · ext i
    rw [mem_axisWordDataEquiv_fst, bitsAxisEquiv_schedule]
    simp only [axisSuffix, decide_eq_true_eq]
    rw [bitsAxisEquiv_schedule]
    simp only [lowCoefficientBits]
    have hrev : (Fin.natAdd s i).rev.val = i.rev.val := by
      simp [Fin.rev]
      omega
    simpa only [hrev]
  · funext i
    rw [axisWordDataEquiv_snd, bitsAxisEquiv_sign]
    simp only [axisSuffix]
    rw [bitsAxisEquiv_sign]
    simp only [lowCoefficientBits]
    apply congrArg x
    apply Fin.ext
    simp [Fin.rev]
    omega

/-- Three successive partial summations, defined locally to keep the finite transfer theorem
independent of the analytic root-count branch. -/
def terminalPartialSum (ω : ℕ → Bool) (k : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (k + 1), sign (ω i)

def terminalSecondSum (ω : ℕ → Bool) (k : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (k + 1), terminalPartialSum ω i

def terminalThirdSum (ω : ℕ → Bool) (k : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (k + 1), terminalSecondSum ω i

/-- Terminal axis words whose reconstructed low coefficients have a third-integrated weak
crossing at edge `k`. -/
noncomputable def thirdCrossingAxisWords (r k : ℕ) : Finset (AxisWord r) :=
  Finset.univ.filter (fun w ↦
    terminalThirdSum (axisWordCoefficients w) k *
      terminalThirdSum (axisWordCoefficients w) (k + 1) ≤ 0)

/-- The sharp cone-conditioning transfer bound specialized to a third-integrated crossing. -/
theorem cone_thirdCrossing_density_le (s r k : ℕ) :
    (Fintype.card {p : AxisGoodPath (s + r) //
        axisSuffix p ∈ thirdCrossingAxisWords r k} : ℝ) /
        Fintype.card (AxisGoodPath (s + r)) ≤
      ((s + r + 1 : ℝ) / (s + 1 : ℝ)) *
        ((thirdCrossingAxisWords r k).card : ℝ) / (4 : ℝ) ^ r := by
  exact goodPaths_suffix_density_le s r (thirdCrossingAxisWords r k)

/-- `axisWordBits` is a bijection, so the right side above is exactly an unconditional finite-word
crossing probability rather than an artifact of the axis encoding. -/
lemma axisWordBits_bijective (r : ℕ) : Function.Bijective (@axisWordBits r) :=
  (axisWordBitsEquiv r).bijective

lemma card_thirdCrossingAxisWords_eq_bits (r k : ℕ) :
    (thirdCrossingAxisWords r k).card =
      (Finset.univ.filter (fun x : Fin (2 * r) → Bool ↦
        terminalThirdSum (extendBits r x) k *
          terminalThirdSum (extendBits r x) (k + 1) ≤ 0)).card := by
  let f : AxisWord r → Fin (2 * r) → Bool := axisWordBits
  have hf : Function.Bijective f := axisWordBits_bijective r
  apply Finset.card_bij (fun w hw ↦ f w)
  · intro w hw
    simp only [thirdCrossingAxisWords, Finset.mem_filter, Finset.mem_univ, true_and] at hw
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    simpa [f, axisWordCoefficients] using hw
  · intro w₁ hw₁ w₂ hw₂ h
    exact hf.injective h
  · intro x hx
    obtain ⟨w, hw⟩ := hf.surjective x
    refine ⟨w, ?_, hw⟩
    simp only [thirdCrossingAxisWords, Finset.mem_filter, Finset.mem_univ, true_and]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    change terminalThirdSum (extendBits r (f w)) k *
      terminalThirdSum (extendBits r (f w)) (k + 1) ≤ 0
    rw [hw]
    exact hx

end Erdos521
