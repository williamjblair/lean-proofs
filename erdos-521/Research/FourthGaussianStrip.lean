import Research.FourthCrossingLocalLimitBound
import Research.ShiftedGaussianLatticeSum
import Mathlib.Tactic

open scoped BigOperators

namespace Erdos521

noncomputable local instance fourthGaussianStripDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

lemma fourthGaussianFullAtom_complete_square (k : ℕ) (y : Fin 2 → ℝ) :
    fourthGaussianFullAtom k y =
      (2 / (Real.pi * Real.sqrt (fourthDet k))) *
        Real.exp (-(y 0) ^ 2 / (2 * fourthVarianceA k)) *
        Real.exp (-(fourthVarianceA k / (2 * fourthDet k)) *
          (y 1 - fourthIncrementCovarianceC k * y 0 / fourthVarianceA k) ^ 2) := by
  have hA : 0 < fourthVarianceA k := fourthVarianceA_pos' k
  have hD : 0 < fourthDet k := fourthDet_pos k
  unfold fourthGaussianFullAtom
  rw [Fin.sum_univ_two]
  simp only [fourthPrimalWhitening]
  rw [div_pow (y 0) (Real.sqrt (fourthVarianceA k)) 2,
    div_pow (fourthVarianceA k * y 1 - fourthIncrementCovarianceC k * y 0)
      (Real.sqrt (fourthVarianceA k * fourthDet k)) 2,
    show Real.sqrt (fourthVarianceA k) ^ 2 = fourthVarianceA k from
      Real.sq_sqrt hA.le,
    show Real.sqrt (fourthVarianceA k * fourthDet k) ^ 2 =
      fourthVarianceA k * fourthDet k from Real.sq_sqrt (mul_nonneg hA.le hD.le)]
  rw [mul_assoc, ← Real.exp_add]
  congr 1
  field_simp
  ring

noncomputable def fourthGaussianStripParameters (k T : ℕ) : Finset (Fin 2 → ℤ) :=
  (fourthAttainableLatticeParameters k).filter fun d ↦
    |signedIntLatticeTarget (fourthSignedIntegerVector k) d 0| ≤ (T : ℤ)

noncomputable def fourthGaussianStripMass (k T : ℕ) : ℝ :=
  ∑ d ∈ fourthGaussianStripParameters k T,
    fourthGaussianFullAtom k (fun j ↦
      (signedIntLatticeTarget (fourthSignedIntegerVector k) d j : ℝ))

lemma fourthGaussianStrip_firstCoordinates_card (k T : ℕ) :
    ((fourthGaussianStripParameters k T).image fun d ↦
      signedIntLatticeTarget (fourthSignedIntegerVector k) d 0).card ≤ 2 * T + 1 := by
  let X := (fourthGaussianStripParameters k T).image fun d ↦
    signedIntLatticeTarget (fourthSignedIntegerVector k) d 0
  have hsub : X ⊆ Finset.Icc (-(T : ℤ)) (T : ℤ) := by
    intro x hx
    simp only [X, Finset.mem_image] at hx
    obtain ⟨d, hd, rfl⟩ := hx
    rw [fourthGaussianStripParameters, Finset.mem_filter] at hd
    exact Finset.mem_Icc.mpr (abs_le.mp hd.2)
  calc
    X.card ≤ (Finset.Icc (-(T : ℤ)) (T : ℤ)).card := Finset.card_le_card hsub
    _ = 2 * T + 1 := by
      rw [Int.card_Icc]
      congr 1
      omega

/-- Summing the full bivariate Gaussian over any attainable strip uses a one-dimensional shifted
Gaussian bound in the transverse coordinate. -/
lemma fourthGaussianStripMass_le (k T : ℕ) :
    fourthGaussianStripMass k T ≤
      ((2 * T + 1 : ℕ) : ℝ) *
        (2 / (Real.pi * Real.sqrt (fourthDet k))) *
        (Real.exp 1 * 2 *
          (1 + 1 / (2 * (fourthVarianceA k / (2 * fourthDet k)) *
            Real.sqrt (2 * fourthDet k / fourthVarianceA k)))) := by
  let target := signedIntLatticeTarget (fourthSignedIntegerVector k)
  let S := fourthGaussianStripParameters k T
  let X := S.image fun d ↦ target d 0
  let pref : ℝ := 2 / (Real.pi * Real.sqrt (fourthDet k))
  let a : ℝ := fourthVarianceA k / (2 * fourthDet k)
  let L : ℝ := Real.sqrt (2 * fourthDet k / fourthVarianceA k)
  have hA : 0 < fourthVarianceA k := fourthVarianceA_pos' k
  have hD : 0 < fourthDet k := fourthDet_pos k
  have ha : 0 < a := by dsimp [a]; positivity
  have hLarg : 0 < 2 * fourthDet k / fourthVarianceA k := by positivity
  have hL : 0 < L := by exact Real.sqrt_pos.2 hLarg
  have haL : a * L ^ 2 = 1 := by
    dsimp [a, L]
    rw [Real.sq_sqrt hLarg.le]
    field_simp
  have hpref : 0 ≤ pref := by dsimp [pref]; positivity
  have hfiber (x : ℤ) (hx : x ∈ X) :
      (∑ d ∈ S with target d 0 = x,
        fourthGaussianFullAtom k (fun j ↦ (target d j : ℝ))) ≤
        pref * (Real.exp 1 * 2 * (1 + 1 / (2 * a * L))) := by
    let F := S.filter fun d ↦ target d 0 = x
    let Y := F.image fun d ↦ target d 1
    have hinj : Set.InjOn (fun d ↦ target d 1) F := by
      intro d hd e he h1
      apply signedIntLatticeTarget_injective (fourthSignedIntegerVector k)
      apply funext
      rw [Fin.forall_fin_two]
      have hd0 : target d 0 = x := (Finset.mem_filter.mp hd).2
      have he0 : target e 0 = x := (Finset.mem_filter.mp he).2
      exact ⟨hd0.trans he0.symm, h1⟩
    have hrewrite :
        (∑ d ∈ S with target d 0 = x,
          fourthGaussianFullAtom k (fun j ↦ (target d j : ℝ))) =
          ∑ y ∈ Y, fourthGaussianFullAtom k (fun j ↦
            if j = 0 then (x : ℝ) else (y : ℝ)) := by
      rw [show (∑ d ∈ S with target d 0 = x,
          fourthGaussianFullAtom k (fun j ↦ (target d j : ℝ))) =
          ∑ d ∈ F, fourthGaussianFullAtom k (fun j ↦ (target d j : ℝ)) by
        rfl]
      rw [Finset.sum_image]
      · apply Finset.sum_congr rfl
        intro d hd
        have hd0 : target d 0 = x := (Finset.mem_filter.mp hd).2
        congr 2
        funext j
        fin_cases j
        · simp [hd0]
        · simp
      · exact hinj
    rw [hrewrite]
    calc
      _ = ∑ y ∈ Y, pref * Real.exp (-(x : ℝ) ^ 2 /
            (2 * fourthVarianceA k)) *
          Real.exp (-a * ((y : ℝ) -
            fourthIncrementCovarianceC k * x / fourthVarianceA k) ^ 2) := by
        apply Finset.sum_congr rfl
        intro y hy
        rw [fourthGaussianFullAtom_complete_square]
        simp only [Fin.isValue, ↓reduceIte]
        rfl
      _ ≤ ∑ y ∈ Y, pref *
          Real.exp (-a * ((y : ℝ) -
            fourthIncrementCovarianceC k * x / fourthVarianceA k) ^ 2) := by
        apply Finset.sum_le_sum
        intro y hy
        have hexp : Real.exp (-(x : ℝ) ^ 2 / (2 * fourthVarianceA k)) ≤ 1 := by
          rw [Real.exp_le_one_iff]
          exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg _)) (by positivity)
        calc
          pref * Real.exp (-(x : ℝ) ^ 2 / (2 * fourthVarianceA k)) *
              Real.exp (-a * ((y : ℝ) -
                fourthIncrementCovarianceC k * x / fourthVarianceA k) ^ 2) ≤
            pref * 1 * Real.exp (-a * ((y : ℝ) -
                fourthIncrementCovarianceC k * x / fourthVarianceA k) ^ 2) :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hexp hpref)
                (Real.exp_nonneg _)
          _ = _ := by ring
      _ = pref * (∑ y ∈ Y, Real.exp (-a * ((y : ℝ) -
            fourthIncrementCovarianceC k * x / fourthVarianceA k) ^ 2)) := by
        rw [Finset.mul_sum]
      _ ≤ pref * (Real.exp (a * L ^ 2) * 2 * (1 + 1 / (2 * a * L))) := by
        gcongr
        exact finset_sum_shifted_gaussian_le Y ha hL
      _ = pref * (Real.exp 1 * 2 * (1 + 1 / (2 * a * L))) := by rw [haL]
  unfold fourthGaussianStripMass
  change (∑ d ∈ S, fourthGaussianFullAtom k (fun j ↦ (target d j : ℝ))) ≤ _
  have hmaps : Set.MapsTo (fun d ↦ target d 0) S X := by
    intro d hd
    exact Finset.mem_image.mpr ⟨d, hd, rfl⟩
  rw [← Finset.sum_fiberwise_of_maps_to (s := S) (t := X)
    (g := fun d ↦ target d 0) hmaps
    (fun d ↦ fourthGaussianFullAtom k (fun j ↦ (target d j : ℝ)))]
  calc
    _ ≤ ∑ x ∈ X, pref * (Real.exp 1 * 2 * (1 + 1 / (2 * a * L))) := by
      exact Finset.sum_le_sum fun x hx ↦ hfiber x hx
    _ = (X.card : ℝ) * pref * (Real.exp 1 * 2 * (1 + 1 / (2 * a * L))) := by
      simp
      ring
    _ ≤ ((2 * T + 1 : ℕ) : ℝ) * pref *
        (Real.exp 1 * 2 * (1 + 1 / (2 * a * L))) := by
      have hcard : (X.card : ℝ) ≤ ((2 * T + 1 : ℕ) : ℝ) := by
        exact_mod_cast fourthGaussianStrip_firstCoordinates_card k T
      gcongr
    _ = _ := by rfl

end Erdos521
