import Research.FourthGaussianCrossingSum
import Research.FiniteRademacherConcentration
import Mathlib.Tactic

open scoped BigOperators

namespace Erdos521

noncomputable local instance fourthCrossingTruncationDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

noncomputable def fourthIncrementWeight (k : ℕ) : Option (Fin (k + 1)) → ℝ :=
  fun i ↦ (fourthSignedIntegerVector k i 1 : ℝ)

lemma finiteRademacherRealSum_fourthIncrementWeight (k : ℕ)
    (e : Option (Fin (k + 1)) → Bool) :
    finiteRademacherRealSum (fourthIncrementWeight k) e =
      (fourthSignedPair k e 1 : ℝ) := by
  unfold finiteRademacherRealSum fourthIncrementWeight fourthSignedPair signedIntVectorSum
  push_cast
  apply Finset.sum_congr rfl
  intro i hi
  rw [intCast_boolSignInt]

lemma finiteRademacherVariance_fourthIncrementWeight (k : ℕ) :
    finiteRademacherVariance (fourthIncrementWeight k) =
      fourthIncrementVarianceB k := by
  unfold finiteRademacherVariance fourthIncrementWeight fourthIncrementVarianceB
  rw [Fintype.sum_option]
  simp only [fourthSignedIntegerVector]
  norm_num
  calc
    (∑ q : Fin (k + 1), ((fourthIntegerB q : ℤ) : ℝ) ^ 2) =
        ∑ q ∈ Finset.range (k + 1), ((fourthIntegerB q : ℤ) : ℝ) ^ 2 :=
      Fin.sum_univ_eq_sum_range
        (fun q : ℕ ↦ ((fourthIntegerB q : ℤ) : ℝ) ^ 2) (k + 1)
    _ = ∑ q ∈ Finset.range (k + 1),
        (Nat.choose (q + 3) 2 : ℝ) ^ 2 := by
      apply Finset.sum_congr rfl
      intro q hq
      simp [fourthIntegerB]

lemma fourthSignedIncrement_abs_tail (k L : ℕ) :
    finiteRademacherAbsTailProbability (fourthIncrementWeight k) (L : ℝ) ≤
      2 * Real.exp (-((L : ℝ) ^ 2) / (2 * fourthIncrementVarianceB k)) := by
  have hV : 0 < finiteRademacherVariance (fourthIncrementWeight k) := by
    rw [finiteRademacherVariance_fourthIncrementWeight]
    unfold fourthIncrementVarianceB
    positivity
  have h := finiteRademacherAbsTailProbability_le
    (fourthIncrementWeight k) (T := (L : ℝ)) (by positivity) hV
  rw [finiteRademacherVariance_fourthIncrementWeight] at h
  exact h

noncomputable def fourthIncrementL1 (k : ℕ) : ℕ :=
  1 + ∑ q ∈ Finset.range (k + 1), Nat.choose (q + 3) 2

noncomputable def boolNegativeNat (b : Bool) : ℕ := if b then 0 else 1

noncomputable def fourthIncrementNegativeNat (k : ℕ)
    (e : Option (Fin (k + 1)) → Bool) : ℕ :=
  boolNegativeNat (e none) +
    ∑ q : Fin (k + 1), Nat.choose (q + 3) 2 * boolNegativeNat (e (some q))

lemma boolNegativeNat_le_one (b : Bool) : boolNegativeNat b ≤ 1 := by
  cases b <;> simp [boolNegativeNat]

lemma fourthIncrementNegativeNat_le (k : ℕ)
    (e : Option (Fin (k + 1)) → Bool) :
    fourthIncrementNegativeNat k e ≤ fourthIncrementL1 k := by
  unfold fourthIncrementNegativeNat fourthIncrementL1
  have hconst :
      (∑ q : Fin (k + 1), Nat.choose (q + 3) 2) =
        ∑ q ∈ Finset.range (k + 1), Nat.choose (q + 3) 2 :=
    Fin.sum_univ_eq_sum_range (fun q : ℕ ↦ Nat.choose (q + 3) 2) (k + 1)
  rw [← hconst]
  apply Nat.add_le_add (boolNegativeNat_le_one _)
  apply Finset.sum_le_sum
  intro q hq
  simpa only [Nat.mul_one] using
    Nat.mul_le_mul_left (Nat.choose (q + 3) 2) (boolNegativeNat_le_one (e (some q)))

lemma fourthSignedVectorBase_one (k : ℕ) :
    signedIntVectorBase (fourthSignedIntegerVector k) 1 = (fourthIncrementL1 k : ℤ) := by
  unfold signedIntVectorBase fourthIncrementL1
  rw [Fintype.sum_option]
  simp only [fourthSignedIntegerVector]
  norm_num
  rw [Fin.sum_univ_eq_sum_range]
  push_cast
  rfl

lemma boolNegativeIndicator_eq_nat (b : Bool) :
    boolNegativeIndicator b = (boolNegativeNat b : ℤ) := by
  cases b <;> simp [boolNegativeIndicator, boolNegativeNat]

lemma fourthSignedVectorNegativeSum_one (k : ℕ)
    (e : Option (Fin (k + 1)) → Bool) :
    signedIntVectorNegativeSum (fourthSignedIntegerVector k) e 1 =
      (fourthIncrementNegativeNat k e : ℤ) := by
  unfold signedIntVectorNegativeSum fourthIncrementNegativeNat
  rw [Fintype.sum_option]
  simp only [fourthSignedIntegerVector]
  norm_num
  push_cast
  rw [boolNegativeIndicator_eq_nat]
  apply congrArg (fun z : ℤ ↦ (boolNegativeNat (e none) : ℤ) + z)
  apply Finset.sum_congr rfl
  intro q hq
  rw [boolNegativeIndicator_eq_nat]
  push_cast
  simp only [fourthIntegerB]
  ring

lemma fourthSignedPair_one_eq_mesh (k : ℕ)
    (e : Option (Fin (k + 1)) → Bool) :
    fourthSignedPair k e 1 =
      (fourthIncrementL1 k : ℤ) - 2 * (fourthIncrementNegativeNat k e : ℤ) := by
  unfold fourthSignedPair
  rw [signedIntVectorSum_eq_base_sub_two_negative,
    fourthSignedVectorBase_one, fourthSignedVectorNegativeSum_one]

lemma fourthSignedPair_one_eq_gaussianParityMesh (k : ℕ)
    (e : Option (Fin (k + 1)) → Bool) :
    (fourthSignedPair k e 1 : ℝ) =
      -(fourthIncrementL1 k : ℝ) +
        2 * (fourthIncrementL1 k - fourthIncrementNegativeNat k e : ℕ) := by
  rw [fourthSignedPair_one_eq_mesh]
  have hle := fourthIncrementNegativeNat_le k e
  push_cast
  rw [Nat.cast_sub hle]
  ring

noncomputable def fourthIncrementMeshIndex (k : ℕ) (d : Fin 2 → ℤ) : ℕ :=
  ((fourthIncrementL1 k : ℤ) + d 1).toNat

lemma fourthIncrementMeshIndex_parameter (k : ℕ)
    (e : Option (Fin (k + 1)) → Bool) :
    fourthIncrementMeshIndex k (fourthSignedLatticeParameter k e) =
      fourthIncrementL1 k - fourthIncrementNegativeNat k e := by
  unfold fourthIncrementMeshIndex fourthSignedLatticeParameter
  rw [fourthSignedVectorNegativeSum_one]
  have hle := fourthIncrementNegativeNat_le k e
  have hnonneg : 0 ≤ (fourthIncrementL1 k : ℤ) -
      (fourthIncrementNegativeNat k e : ℤ) := by
    apply sub_nonneg.mpr
    exact_mod_cast hle
  rw [show (fourthIncrementL1 k : ℤ) +
      -(fourthIncrementNegativeNat k e : ℤ) =
      (fourthIncrementL1 k : ℤ) - (fourthIncrementNegativeNat k e : ℤ) by ring]
  apply Int.ofNat_injective
  change Int.ofNat ((fourthIncrementL1 k : ℤ) -
      (fourthIncrementNegativeNat k e : ℤ)).toNat =
    Int.ofNat (fourthIncrementL1 k - fourthIncrementNegativeNat k e)
  calc
    Int.ofNat ((fourthIncrementL1 k : ℤ) -
        (fourthIncrementNegativeNat k e : ℤ)).toNat =
      (fourthIncrementL1 k : ℤ) -
        (fourthIncrementNegativeNat k e : ℤ) := Int.toNat_of_nonneg hnonneg
    _ = Int.ofNat (fourthIncrementL1 k - fourthIncrementNegativeNat k e) := by
      exact (Nat.cast_sub hle :
        ((fourthIncrementL1 k - fourthIncrementNegativeNat k e : ℕ) : ℤ) =
          (fourthIncrementL1 k : ℤ) -
            (fourthIncrementNegativeNat k e : ℤ)).symm

lemma fourthIncrementMeshIndex_lt (k : ℕ) (d : Fin 2 → ℤ)
    (hd : d ∈ fourthAttainableLatticeParameters k) :
    fourthIncrementMeshIndex k d < fourthIncrementL1 k + 1 := by
  rw [fourthAttainableLatticeParameters, Finset.mem_image] at hd
  obtain ⟨e, he, rfl⟩ := hd
  rw [fourthIncrementMeshIndex_parameter]
  omega

lemma fourthLatticeTarget_one_eq_mesh (k : ℕ) (d : Fin 2 → ℤ)
    (hd : d ∈ fourthAttainableLatticeParameters k) :
    (signedIntLatticeTarget (fourthSignedIntegerVector k) d 1 : ℝ) =
      -(fourthIncrementL1 k : ℝ) + 2 * (fourthIncrementMeshIndex k d : ℝ) := by
  rw [fourthAttainableLatticeParameters, Finset.mem_image] at hd
  obtain ⟨e, he, rfl⟩ := hd
  rw [← congrFun (fourthSignedPair_eq_latticeTarget k e) 1,
    fourthSignedPair_one_eq_gaussianParityMesh,
    fourthIncrementMeshIndex_parameter]

noncomputable def fourthIncrementMeshValue (k n : ℕ) : ℤ :=
  -(fourthIncrementL1 k : ℤ) + 2 * (n : ℤ)

lemma fourthLatticeTarget_one_eq_mesh_int (k : ℕ) (d : Fin 2 → ℤ)
    (hd : d ∈ fourthAttainableLatticeParameters k) :
    signedIntLatticeTarget (fourthSignedIntegerVector k) d 1 =
      fourthIncrementMeshValue k (fourthIncrementMeshIndex k d) := by
  rw [fourthAttainableLatticeParameters, Finset.mem_image] at hd
  obtain ⟨e, he, rfl⟩ := hd
  rw [← congrFun (fourthSignedPair_eq_latticeTarget k e) 1,
    fourthSignedPair_one_eq_mesh, fourthIncrementMeshIndex_parameter]
  unfold fourthIncrementMeshValue
  have hle := fourthIncrementNegativeNat_le k e
  push_cast
  rw [Nat.cast_sub hle]
  ring

noncomputable def fourthCrossingLatticeParameters (k : ℕ) : Finset (Fin 2 → ℤ) :=
  (fourthAttainableLatticeParameters k).filter fun d ↦
    fourthPairCrossing (signedIntLatticeTarget (fourthSignedIntegerVector k) d)

noncomputable def fourthCrossingLatticeFiber (k n : ℕ) : Finset (Fin 2 → ℤ) :=
  (fourthCrossingLatticeParameters k).filter fun d ↦ fourthIncrementMeshIndex k d = n

noncomputable def crossingFirstCoordinateBox (b i : ℤ) : Finset ℤ :=
  if 0 ≤ i then Finset.Icc ((-i - b) / 2 - 1) ((-b) / 2 + 1)
  else Finset.Icc ((-b) / 2 - 1) ((-i - b) / 2 + 1)

lemma crossing_first_coordinate_linear_bounds {x i : ℤ}
    (hcross : x * (x + i) ≤ 0) :
    (0 ≤ i → -i ≤ x ∧ x ≤ 0) ∧
      (i < 0 → 0 ≤ x ∧ x ≤ -i) := by
  constructor
  · intro hi
    constructor <;> by_contra h <;> push_neg at h <;> nlinarith
  · intro hi
    constructor <;> by_contra h <;> push_neg at h <;> nlinarith

lemma mem_crossingFirstCoordinateBox {b i d x : ℤ}
    (hx : x = b + 2 * d) (hcross : x * (x + i) ≤ 0) :
    d ∈ crossingFirstCoordinateBox b i := by
  have hbounds := crossing_first_coordinate_linear_bounds hcross
  unfold crossingFirstCoordinateBox
  by_cases hi : 0 ≤ i
  · rw [if_pos hi]
    have hxi := hbounds.1 hi
    simp only [Finset.mem_Icc]
    constructor <;> omega
  · rw [if_neg hi]
    have hin : i < 0 := lt_of_not_ge hi
    have hxi := hbounds.2 hin
    simp only [Finset.mem_Icc]
    constructor <;> omega

lemma card_crossingFirstCoordinateBox (b i : ℤ) :
    ((crossingFirstCoordinateBox b i).card : ℝ) ≤ |(i : ℝ)| / 2 + 4 := by
  unfold crossingFirstCoordinateBox
  by_cases hi : 0 ≤ i
  · rw [if_pos hi]
    have hcard :
        (Finset.Icc ((-i - b) / 2 - 1) ((-b) / 2 + 1)).card ≤
          (i / 2 + 4).toNat := by
      rw [Int.card_Icc]
      omega
    have hn : 0 ≤ i / 2 + 4 := by omega
    have hto : (((i / 2 + 4).toNat : ℕ) : ℤ) = i / 2 + 4 :=
      Int.toNat_of_nonneg hn
    have htoR : (((i / 2 + 4).toNat : ℕ) : ℝ) = ((i / 2 + 4 : ℤ) : ℝ) := by
      exact_mod_cast hto
    have hfloorZ : 2 * (i / 2) ≤ i := by omega
    have hfloorCast : ((2 * (i / 2) : ℤ) : ℝ) ≤ (i : ℝ) := by
      exact_mod_cast hfloorZ
    have hfloor : ((i / 2 : ℤ) : ℝ) ≤ (i : ℝ) / 2 := by
      push_cast at hfloorCast
      linarith
    have hiR : 0 ≤ (i : ℝ) := by exact_mod_cast hi
    rw [abs_of_nonneg hiR]
    calc
      (((Finset.Icc ((-i - b) / 2 - 1) ((-b) / 2 + 1)).card : ℕ) : ℝ) ≤
          (((i / 2 + 4).toNat : ℕ) : ℝ) := by exact_mod_cast hcard
      _ = ((i / 2 + 4 : ℤ) : ℝ) := htoR
      _ ≤ (i : ℝ) / 2 + 4 := by push_cast; linarith
  · rw [if_neg hi]
    have hin : i < 0 := lt_of_not_ge hi
    have hcard :
        (Finset.Icc ((-b) / 2 - 1) ((-i - b) / 2 + 1)).card ≤
          ((-i) / 2 + 4).toNat := by
      rw [Int.card_Icc]
      omega
    have hn : 0 ≤ (-i) / 2 + 4 := by omega
    have hto : ((((-i) / 2 + 4).toNat : ℕ) : ℤ) = (-i) / 2 + 4 :=
      Int.toNat_of_nonneg hn
    have htoR : ((((-i) / 2 + 4).toNat : ℕ) : ℝ) = (((-i) / 2 + 4 : ℤ) : ℝ) := by
      exact_mod_cast hto
    have hfloorZ : 2 * ((-i) / 2) ≤ -i := by omega
    have hfloorCast : ((2 * ((-i) / 2) : ℤ) : ℝ) ≤ (-i : ℝ) := by
      exact_mod_cast hfloorZ
    have hfloor : (((-i) / 2 : ℤ) : ℝ) ≤ (-i : ℝ) / 2 := by
      push_cast at hfloorCast
      linarith
    have hiR : (i : ℝ) < 0 := by exact_mod_cast hin
    rw [abs_of_neg hiR]
    calc
      (((Finset.Icc ((-b) / 2 - 1) ((-i - b) / 2 + 1)).card : ℕ) : ℝ) ≤
          ((((-i) / 2 + 4).toNat : ℕ) : ℝ) := by exact_mod_cast hcard
      _ = (((-i) / 2 + 4 : ℤ) : ℝ) := htoR
      _ ≤ -(i : ℝ) / 2 + 4 := by push_cast; linarith

lemma fourthCrossingLatticeFiber_card_le_box (k n : ℕ)
    (hn : n < fourthIncrementL1 k + 1) :
    (fourthCrossingLatticeFiber k n).card ≤
      (crossingFirstCoordinateBox
        (signedIntVectorBase (fourthSignedIntegerVector k) 0)
        (fourthIncrementMeshValue k n)).card := by
  let b := signedIntVectorBase (fourthSignedIntegerVector k) 0
  let i := fourthIncrementMeshValue k n
  let target := signedIntLatticeTarget (fourthSignedIntegerVector k)
  apply Finset.card_le_card_of_injOn (fun d : Fin 2 → ℤ ↦ d 0)
  · intro d hd
    have hdFin : d ∈ fourthCrossingLatticeFiber k n := hd
    rw [fourthCrossingLatticeFiber, Finset.mem_filter] at hdFin
    have hdouter := hdFin.1
    rw [fourthCrossingLatticeParameters, Finset.mem_filter] at hdouter
    have hdatt : d ∈ fourthAttainableLatticeParameters k := hdouter.1
    have hcross : fourthPairCrossing (target d) := hdouter.2
    have hidx : fourthIncrementMeshIndex k d = n := hdFin.2
    have hx : target d 0 = b + 2 * d 0 := by
      dsimp [target, b]
      unfold signedIntLatticeTarget
      ring
    have hi : target d 1 = i := by
      dsimp [i]
      rw [← hidx]
      exact fourthLatticeTarget_one_eq_mesh_int k d hdatt
    dsimp only
    apply mem_crossingFirstCoordinateBox hx
    have hi' : target d 1 = fourthIncrementMeshValue k n := by
      simpa [i] using hi
    rw [← hi']
    exact hcross
  · intro d₁ hd₁ d₂ hd₂ heq
    have hdFin₁ : d₁ ∈ fourthCrossingLatticeFiber k n := hd₁
    have hdFin₂ : d₂ ∈ fourthCrossingLatticeFiber k n := hd₂
    rw [fourthCrossingLatticeFiber, Finset.mem_filter] at hdFin₁ hdFin₂
    have hdouter₁ := hdFin₁.1
    have hdouter₂ := hdFin₂.1
    rw [fourthCrossingLatticeParameters, Finset.mem_filter] at hdouter₁ hdouter₂
    have hdatt₁ : d₁ ∈ fourthAttainableLatticeParameters k := hdouter₁.1
    have hdatt₂ : d₂ ∈ fourthAttainableLatticeParameters k := hdouter₂.1
    have hidx : fourthIncrementMeshIndex k d₁ = fourthIncrementMeshIndex k d₂ := by
      rw [hdFin₁.2, hdFin₂.2]
    apply signedIntLatticeTarget_injective (fourthSignedIntegerVector k)
    apply funext
    rw [Fin.forall_fin_two]
    constructor
    · unfold signedIntLatticeTarget
      rw [show d₁ 0 = d₂ 0 by exact heq]
    · rw [fourthLatticeTarget_one_eq_mesh_int k d₁ hdatt₁,
        fourthLatticeTarget_one_eq_mesh_int k d₂ hdatt₂, hidx]

lemma fourthCrossingLatticeFiber_card_real (k n : ℕ)
    (hn : n < fourthIncrementL1 k + 1) :
    ((fourthCrossingLatticeFiber k n).card : ℝ) ≤
      |(fourthIncrementMeshValue k n : ℝ)| / 2 + 4 := by
  calc
    ((fourthCrossingLatticeFiber k n).card : ℝ) ≤
        ((crossingFirstCoordinateBox
          (signedIntVectorBase (fourthSignedIntegerVector k) 0)
          (fourthIncrementMeshValue k n)).card : ℝ) := by
      exact_mod_cast fourthCrossingLatticeFiber_card_le_box k n hn
    _ ≤ |(fourthIncrementMeshValue k n : ℝ)| / 2 + 4 :=
      card_crossingFirstCoordinateBox _ _

end Erdos521
