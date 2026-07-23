import Research.FourthCrossingTruncation
import Mathlib.Tactic

open scoped BigOperators

namespace Erdos521

noncomputable local instance fourthGaussianCrossingMassDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

noncomputable def fourthGaussianCrossingMass (k : ℕ) : ℝ :=
  ∑ d ∈ fourthCrossingLatticeParameters k,
    fourthGaussianFullAtom k (fun j ↦
      (signedIntLatticeTarget (fourthSignedIntegerVector k) d j : ℝ))

lemma fourthGaussianFullAtom_nonneg (k : ℕ) (y : Fin 2 → ℝ) :
    0 ≤ fourthGaussianFullAtom k y := by
  unfold fourthGaussianFullAtom
  positivity

lemma fourthGaussianCrossingFiber_sum_le (k n : ℕ)
    (hn : n < fourthIncrementL1 k + 1) :
    (∑ d ∈ fourthCrossingLatticeFiber k n,
      fourthGaussianFullAtom k (fun j ↦
        (signedIntLatticeTarget (fourthSignedIntegerVector k) d j : ℝ))) ≤
      (|(fourthIncrementMeshValue k n : ℝ)| / 2 + 4) *
        ((2 / (Real.pi * Real.sqrt (fourthDet k))) *
          Real.exp (-fourthIncrementGaussianRate k *
            (fourthIncrementMeshValue k n : ℝ) ^ 2)) := by
  let target := signedIntLatticeTarget (fourthSignedIntegerVector k)
  let C := (2 / (Real.pi * Real.sqrt (fourthDet k))) *
    Real.exp (-fourthIncrementGaussianRate k *
      (fourthIncrementMeshValue k n : ℝ) ^ 2)
  have hpoint (d : Fin 2 → ℤ) (hd : d ∈ fourthCrossingLatticeFiber k n) :
      fourthGaussianFullAtom k (fun j ↦ (target d j : ℝ)) ≤ C := by
    have hdFin := hd
    rw [fourthCrossingLatticeFiber, Finset.mem_filter] at hdFin
    have hdouter := hdFin.1
    rw [fourthCrossingLatticeParameters, Finset.mem_filter] at hdouter
    have hdatt := hdouter.1
    have hcross := hdouter.2
    have hgauss := fourthGaussianFullAtom_crossing_le k (target d) hcross
    have hi := fourthLatticeTarget_one_eq_mesh_int k d hdatt
    have hi' : target d 1 = fourthIncrementMeshValue k n := by
      change signedIntLatticeTarget (fourthSignedIntegerVector k) d 1 = _
      rw [hi, hdFin.2]
    dsimp [C]
    rw [hi'] at hgauss
    exact hgauss
  calc
    (∑ d ∈ fourthCrossingLatticeFiber k n,
      fourthGaussianFullAtom k (fun j ↦ (target d j : ℝ))) ≤
        ∑ _d ∈ fourthCrossingLatticeFiber k n, C := by
      exact Finset.sum_le_sum fun d hd ↦ hpoint d hd
    _ = ((fourthCrossingLatticeFiber k n).card : ℝ) * C := by
      simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (|(fourthIncrementMeshValue k n : ℝ)| / 2 + 4) * C := by
      exact mul_le_mul_of_nonneg_right (fourthCrossingLatticeFiber_card_real k n hn)
        (by dsimp [C]; positivity)
    _ = _ := rfl

/-- The complete lattice Gaussian mass of the crossing wedge is the sharp leading
`sqrt(D)/(πA)` term, up to `exp(A/(2D))`, plus a negligible endpoint-count term. -/
lemma fourthGaussianCrossingMass_le (k : ℕ) :
    fourthGaussianCrossingMass k ≤
      Real.exp (fourthIncrementGaussianRate k) *
          (Real.sqrt (fourthDet k) / (Real.pi * fourthVarianceA k)) +
        8 * (fourthIncrementL1 k + 1 : ℝ) /
          (Real.pi * Real.sqrt (fourthDet k)) := by
  let S := fourthCrossingLatticeParameters k
  let L := fourthIncrementL1 k
  let g : (Fin 2 → ℤ) → ℕ := fourthIncrementMeshIndex k
  let G : (Fin 2 → ℤ) → ℝ := fun d ↦
    fourthGaussianFullAtom k (fun j ↦
      (signedIntLatticeTarget (fourthSignedIntegerVector k) d j : ℝ))
  have hmap (d : Fin 2 → ℤ) (hd : d ∈ S) : g d ∈ Finset.range (L + 1) := by
    apply Finset.mem_range.mpr
    dsimp [g, L]
    have hdFin : d ∈ fourthCrossingLatticeParameters k := by
      simpa [S] using hd
    rw [fourthCrossingLatticeParameters, Finset.mem_filter] at hdFin
    exact fourthIncrementMeshIndex_lt k d hdFin.1
  have hpart := Finset.sum_fiberwise_of_maps_to
    (s := S) (t := Finset.range (L + 1)) (g := g) hmap G
  have hfiber (n : ℕ) :
      (S.filter fun d ↦ g d = n) = fourthCrossingLatticeFiber k n := by
    ext d
    simp [S, g, fourthCrossingLatticeFiber]
  have hfiberbound (n : ℕ) (hn : n ∈ Finset.range (L + 1)) :
      (∑ d ∈ S with g d = n, G d) ≤
        (|(fourthIncrementMeshValue k n : ℝ)| / 2 + 4) *
          ((2 / (Real.pi * Real.sqrt (fourthDet k))) *
            Real.exp (-fourthIncrementGaussianRate k *
              (fourthIncrementMeshValue k n : ℝ) ^ 2)) := by
    rw [hfiber]
    exact fourthGaussianCrossingFiber_sum_le k n (by simpa [L] using Finset.mem_range.mp hn)
  have hsumexp :
      (∑ _n ∈ Finset.range (L + 1),
        Real.exp (-fourthIncrementGaussianRate k *
          (fourthIncrementMeshValue k _n : ℝ) ^ 2)) ≤ (L + 1 : ℝ) := by
    calc
      _ ≤ ∑ _n ∈ Finset.range (L + 1), (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro n hn
        rw [← Real.exp_zero]
        apply Real.exp_le_exp.mpr
        have ha := fourthIncrementGaussianRate_pos k
        nlinarith [sq_nonneg (fourthIncrementMeshValue k n : ℝ)]
      _ = (L + 1 : ℝ) := by simp
  have hmesh :
      (∑ n ∈ Finset.range (L + 1),
        |(fourthIncrementMeshValue k n : ℝ)| *
          Real.exp (-fourthIncrementGaussianRate k *
            (fourthIncrementMeshValue k n : ℝ) ^ 2)) ≤
        Real.exp (fourthIncrementGaussianRate k) /
          (2 * fourthIncrementGaussianRate k) := by
    have heq : (∑ n ∈ Finset.range (L + 1),
        |(fourthIncrementMeshValue k n : ℝ)| *
          Real.exp (-fourthIncrementGaussianRate k *
            (fourthIncrementMeshValue k n : ℝ) ^ 2)) =
        gaussianParityMeshFirstMoment (fourthIncrementGaussianRate k) L := by
      unfold gaussianParityMeshFirstMoment gaussianParityMeshTerm
      apply Finset.sum_congr rfl
      intro n hn
      unfold fourthIncrementMeshValue
      push_cast
      rfl
    rw [heq]
    exact gaussianParityMeshFirstMoment_le _ (fourthIncrementGaussianRate_pos k) L
  unfold fourthGaussianCrossingMass
  change (∑ d ∈ S, G d) ≤ _
  rw [← hpart]
  calc
    (∑ n ∈ Finset.range (L + 1), ∑ d ∈ S with g d = n, G d) ≤
        ∑ n ∈ Finset.range (L + 1),
          (|(fourthIncrementMeshValue k n : ℝ)| / 2 + 4) *
            ((2 / (Real.pi * Real.sqrt (fourthDet k))) *
              Real.exp (-fourthIncrementGaussianRate k *
                (fourthIncrementMeshValue k n : ℝ) ^ 2)) :=
      Finset.sum_le_sum fun n hn ↦ hfiberbound n hn
    _ = (2 / (Real.pi * Real.sqrt (fourthDet k))) *
        ((1 / 2) * (∑ n ∈ Finset.range (L + 1),
          |(fourthIncrementMeshValue k n : ℝ)| *
            Real.exp (-fourthIncrementGaussianRate k *
              (fourthIncrementMeshValue k n : ℝ) ^ 2)) +
          4 * (∑ n ∈ Finset.range (L + 1),
            Real.exp (-fourthIncrementGaussianRate k *
              (fourthIncrementMeshValue k n : ℝ) ^ 2))) := by
      let C : ℝ := 2 / (Real.pi * Real.sqrt (fourthDet k))
      change (∑ n ∈ Finset.range (L + 1),
        (|(fourthIncrementMeshValue k n : ℝ)| / 2 + 4) *
          (C * Real.exp (-fourthIncrementGaussianRate k *
            (fourthIncrementMeshValue k n : ℝ) ^ 2))) =
        C * ((1 / 2) * (∑ n ∈ Finset.range (L + 1),
          |(fourthIncrementMeshValue k n : ℝ)| *
            Real.exp (-fourthIncrementGaussianRate k *
              (fourthIncrementMeshValue k n : ℝ) ^ 2)) +
          4 * (∑ n ∈ Finset.range (L + 1),
            Real.exp (-fourthIncrementGaussianRate k *
              (fourthIncrementMeshValue k n : ℝ) ^ 2)))
      rw [mul_add]
      rw [show C * ((1 / 2) * (∑ n ∈ Finset.range (L + 1),
          |(fourthIncrementMeshValue k n : ℝ)| *
            Real.exp (-fourthIncrementGaussianRate k *
              (fourthIncrementMeshValue k n : ℝ) ^ 2))) =
          (C / 2) * (∑ n ∈ Finset.range (L + 1),
            |(fourthIncrementMeshValue k n : ℝ)| *
              Real.exp (-fourthIncrementGaussianRate k *
                (fourthIncrementMeshValue k n : ℝ) ^ 2)) by ring,
        Finset.mul_sum]
      rw [show C * (4 * (∑ n ∈ Finset.range (L + 1),
          Real.exp (-fourthIncrementGaussianRate k *
            (fourthIncrementMeshValue k n : ℝ) ^ 2))) =
          (4 * C) * (∑ n ∈ Finset.range (L + 1),
            Real.exp (-fourthIncrementGaussianRate k *
              (fourthIncrementMeshValue k n : ℝ) ^ 2)) by ring,
        Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro n hn
      ring
    _ ≤ (2 / (Real.pi * Real.sqrt (fourthDet k))) *
        ((1 / 2) * (Real.exp (fourthIncrementGaussianRate k) /
            (2 * fourthIncrementGaussianRate k)) + 4 * (L + 1 : ℝ)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      gcongr
    _ = Real.exp (fourthIncrementGaussianRate k) *
          (Real.sqrt (fourthDet k) / (Real.pi * fourthVarianceA k)) +
        8 * (L + 1 : ℝ) / (Real.pi * Real.sqrt (fourthDet k)) := by
      unfold fourthIncrementGaussianRate
      have hA : fourthVarianceA k ≠ 0 := (fourthVarianceA_pos' k).ne'
      have hD : fourthDet k ≠ 0 := (fourthDet_pos k).ne'
      have hsD : Real.sqrt (fourthDet k) ≠ 0 :=
        (Real.sqrt_pos.2 (fourthDet_pos k)).ne'
      field_simp
      rw [Real.sq_sqrt (fourthDet_pos k).le]
      ring
    _ = _ := by rfl

end Erdos521
