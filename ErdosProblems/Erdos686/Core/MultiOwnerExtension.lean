/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import ErdosProblems.Erdos686.Core.ThreeBucketRestriction

/-!
# Erdős 686: finite-family cleaned-owner obstructions

This module extends the audited three-bucket second/third elimination to an
arbitrary finite set of distinct owner indices.  Crucially, it retains the
original loss `g`: no unselected cleaned component is absorbed into a new,
unbounded loss.

For owner set `S`, components `P_s`, cofactors `a_s`, and

`a_i P_i^2 - a_j P_j^2 = 3(i-j)`,

put

`Delta_i = product_{j in S\{i}} (i-j)`.

The exact composed obstructions are

`O_i = 3 C_i product(a_s) - 4 D_i g^2 (-3)^(|S|-1) Delta_i`,

`F_i = -3 O_i + 20 E_i g^2 d (-3)^(|S|-1) Delta_i`.

The module also isolates the useful archimedean fact for four or more
owners: the equation-level lower residual bound excludes `O_i=0` uniformly
at `d >= 10^120`.  It does not close the nonzero-obstruction branch; the
obstruction size grows as `d^(|S|-2)` there.
-/

namespace Erdos686
namespace Erdos686Variant

open scoped BigOperators

/-- Product of the signed owner offsets from `i` to every other owner. -/
def multiOwnerDelta (owners : Finset ℤ) (i : ℤ) : ℤ :=
  ∏ j ∈ owners.erase i, (i - j)

/-- Product of all finite-family cofactors. -/
def multiOwnerCofactorProduct (owners : Finset ℤ) (a : ℤ → ℤ) : ℤ :=
  ∏ j ∈ owners, a j

/-- Cofactors away from one distinguished owner. -/
def multiOwnerOppositeCofactorProduct
    (owners : Finset ℤ) (i : ℤ) (a : ℤ → ℤ) : ℤ :=
  ∏ j ∈ owners.erase i, a j

/-- Cleaned components away from one distinguished owner. -/
def multiOwnerOppositeComponentProduct
    (owners : Finset ℤ) (i : ℤ) (P : ℤ → ℤ) : ℤ :=
  ∏ j ∈ owners.erase i, P j

/-- Second local obstruction after eliminating every opposite square
residual. -/
def multiOwnerSecondObstruction
    (owners : Finset ℤ) (i C D g : ℤ) (a : ℤ → ℤ) : ℤ :=
  3 * C * multiOwnerCofactorProduct owners a -
    4 * D * g ^ 2 * (-3) ^ (owners.erase i).card *
      multiOwnerDelta owners i

/-- Third local obstruction after the same finite-family elimination. -/
def multiOwnerThirdObstruction
    (owners : Finset ℤ) (i C D E g d : ℤ) (a : ℤ → ℤ) : ℤ :=
  -3 * multiOwnerSecondObstruction owners i C D g a +
    20 * E * g ^ 2 * d * (-3) ^ (owners.erase i).card *
      multiOwnerDelta owners i

/-- All opposite square residuals reduce simultaneously to the product of
their fixed step-three differences, modulo the square of the distinguished
component. -/
theorem multi_owner_opposite_product_modeq_sq
    {owners : Finset ℤ} {i : ℤ} {P a : ℤ → ℤ}
    (hdiff : ∀ j ∈ owners.erase i,
      a i * (P i) ^ 2 - a j * (P j) ^ 2 = 3 * (i - j)) :
    (∏ j ∈ owners.erase i, a j * (P j) ^ 2) ≡
      (-3) ^ (owners.erase i).card * multiOwnerDelta owners i
        [ZMOD (P i) ^ 2] := by
  have hpoint : ∀ j ∈ owners.erase i,
      a j * (P j) ^ 2 ≡ (-3) * (i - j) [ZMOD (P i) ^ 2] := by
    intro j hj
    apply Int.modEq_of_dvd
    refine ⟨-a i, ?_⟩
    have h := hdiff j hj
    calc
      (-3) * (i - j) - a j * (P j) ^ 2 =
          -(a i * (P i) ^ 2) := by linarith
      _ = (P i) ^ 2 * (-a i) := by ring
  have hprod := Int.ModEq.prod hpoint
  have hright :
      (∏ j ∈ owners.erase i, (-3 : ℤ) * (i - j)) =
        (-3) ^ (owners.erase i).card * multiOwnerDelta owners i := by
    rw [Finset.prod_mul_distrib]
    simp [multiOwnerDelta, Finset.prod_const]
  rw [hright] at hprod
  simpa [Finset.prod_mul_distrib] using hprod

/-- Divisibility form of `multi_owner_opposite_product_modeq_sq`. -/
theorem multi_owner_opposite_product_sub_dvd_sq
    {owners : Finset ℤ} {i : ℤ} {P a : ℤ → ℤ}
    (hdiff : ∀ j ∈ owners.erase i,
      a i * (P i) ^ 2 - a j * (P j) ^ 2 = 3 * (i - j)) :
    (P i) ^ 2 ∣
      (∏ j ∈ owners.erase i, a j * (P j) ^ 2) -
        (-3) ^ (owners.erase i).card * multiOwnerDelta owners i := by
  have hmod := multi_owner_opposite_product_modeq_sq hdiff
  have hdvd := hmod.dvd
  simpa [sub_eq_add_neg, add_comm] using (dvd_neg.mpr hdvd)

/-- The second local lift composes over an arbitrary finite owner family.
The loss `g` is unchanged. -/
theorem multi_owner_second_obstruction_dvd
    {owners : Finset ℤ} {i C D g : ℤ} {P a : ℤ → ℤ}
    (hi : i ∈ owners)
    (hlocal : P i ∣
      3 * C * a i -
        4 * D * (g * multiOwnerOppositeComponentProduct owners i P) ^ 2)
    (hdiff : ∀ j ∈ owners.erase i,
      a i * (P i) ^ 2 - a j * (P j) ^ 2 = 3 * (i - j)) :
    P i ∣ multiOwnerSecondObstruction owners i C D g a := by
  let A₀ : ℤ := multiOwnerOppositeCofactorProduct owners i a
  let B : ℤ := ∏ j ∈ owners.erase i, a j * (P j) ^ 2
  let B₀ : ℤ :=
    (-3) ^ (owners.erase i).card * multiOwnerDelta owners i
  have hprodSq : (P i) ^ 2 ∣ B - B₀ := by
    simpa [B, B₀] using multi_owner_opposite_product_sub_dvd_sq hdiff
  have hpow : P i ∣ (P i) ^ 2 := dvd_pow_self (P i) (by norm_num)
  have hprod : P i ∣ B - B₀ := dvd_trans hpow hprodSq
  have hlocalMul : P i ∣ A₀ *
      (3 * C * a i -
        4 * D * (g * multiOwnerOppositeComponentProduct owners i P) ^ 2) :=
    dvd_mul_of_dvd_right hlocal A₀
  have hcorrection : P i ∣ 4 * D * g ^ 2 * (B - B₀) :=
    dvd_mul_of_dvd_right hprod (4 * D * g ^ 2)
  have hfactor :
      A₀ * (g * multiOwnerOppositeComponentProduct owners i P) ^ 2 =
        g ^ 2 * B := by
    dsimp [A₀, B, multiOwnerOppositeCofactorProduct,
      multiOwnerOppositeComponentProduct]
    rw [mul_pow, ← Finset.prod_pow, Finset.prod_mul_distrib]
    ring
  have hlocalEq :
      A₀ * (3 * C * a i -
        4 * D * (g * multiOwnerOppositeComponentProduct owners i P) ^ 2) =
      3 * C * (a i * A₀) - 4 * D * g ^ 2 * B := by
    calc
      A₀ * (3 * C * a i -
          4 * D * (g * multiOwnerOppositeComponentProduct owners i P) ^ 2) =
          A₀ * (3 * C * a i) - 4 * D *
            (A₀ * (g * multiOwnerOppositeComponentProduct owners i P) ^ 2) := by
              ring
      _ = 3 * C * (a i * A₀) - 4 * D * g ^ 2 * B := by
        rw [hfactor]
        ring
  have hfull : a i * A₀ = multiOwnerCofactorProduct owners a := by
    simpa [A₀, multiOwnerOppositeCofactorProduct,
      multiOwnerCofactorProduct] using Finset.mul_prod_erase owners a hi
  have hsum := dvd_add hlocalMul hcorrection
  convert hsum using 1
  dsimp [multiOwnerSecondObstruction, B₀]
  rw [hlocalEq, ← hfull]
  ring

/-- The third local lift composes over the same arbitrary owner family.  The
only new term is linear in the original gap `d`. -/
theorem multi_owner_third_obstruction_dvd_sq
    {owners : Finset ℤ} {i C D E g d : ℤ} {P a : ℤ → ℤ}
    (hi : i ∈ owners)
    (hd : d = g * P i * multiOwnerOppositeComponentProduct owners i P)
    (hthird : (P i) ^ 2 ∣
      -3 * (3 * C * a i -
        4 * D * (g * multiOwnerOppositeComponentProduct owners i P) ^ 2) +
      20 * E * P i *
        (g * multiOwnerOppositeComponentProduct owners i P) ^ 3)
    (hdiff : ∀ j ∈ owners.erase i,
      a i * (P i) ^ 2 - a j * (P j) ^ 2 = 3 * (i - j)) :
    (P i) ^ 2 ∣ multiOwnerThirdObstruction owners i C D E g d a := by
  let A₀ : ℤ := multiOwnerOppositeCofactorProduct owners i a
  let B : ℤ := ∏ j ∈ owners.erase i, a j * (P j) ^ 2
  let B₀ : ℤ :=
    (-3) ^ (owners.erase i).card * multiOwnerDelta owners i
  have hprodSq : (P i) ^ 2 ∣ B - B₀ := by
    simpa [B, B₀] using multi_owner_opposite_product_sub_dvd_sq hdiff
  have hbase : (P i) ^ 2 ∣ A₀ *
      (-3 * (3 * C * a i -
        4 * D * (g * multiOwnerOppositeComponentProduct owners i P) ^ 2) +
      20 * E * P i *
        (g * multiOwnerOppositeComponentProduct owners i P) ^ 3) :=
    dvd_mul_of_dvd_right hthird A₀
  have hcorrection : (P i) ^ 2 ∣
      -(12 * D * g ^ 2 + 20 * E * g ^ 2 * d) * (B - B₀) :=
    dvd_mul_of_dvd_right hprodSq
      (-(12 * D * g ^ 2 + 20 * E * g ^ 2 * d))
  have hfactorSq :
      A₀ * (g * multiOwnerOppositeComponentProduct owners i P) ^ 2 =
        g ^ 2 * B := by
    dsimp [A₀, B, multiOwnerOppositeCofactorProduct,
      multiOwnerOppositeComponentProduct]
    rw [mul_pow, ← Finset.prod_pow, Finset.prod_mul_distrib]
    ring
  have hfactorCube :
      A₀ * P i *
          (g * multiOwnerOppositeComponentProduct owners i P) ^ 3 =
        g ^ 2 * d * B := by
    calc
      A₀ * P i *
          (g * multiOwnerOppositeComponentProduct owners i P) ^ 3 =
          P i * (g * multiOwnerOppositeComponentProduct owners i P) *
            (A₀ *
              (g * multiOwnerOppositeComponentProduct owners i P) ^ 2) := by
                ring
      _ = P i * (g * multiOwnerOppositeComponentProduct owners i P) *
            (g ^ 2 * B) := by rw [hfactorSq]
      _ = g ^ 2 * d * B := by rw [hd]; ring
  have hfull : a i * A₀ = multiOwnerCofactorProduct owners a := by
    simpa [A₀, multiOwnerOppositeCofactorProduct,
      multiOwnerCofactorProduct] using Finset.mul_prod_erase owners a hi
  have hbaseEq :
      A₀ *
          (-3 * (3 * C * a i -
            4 * D * (g * multiOwnerOppositeComponentProduct owners i P) ^ 2) +
          20 * E * P i *
            (g * multiOwnerOppositeComponentProduct owners i P) ^ 3) =
        -3 * (3 * C * multiOwnerCofactorProduct owners a -
          4 * D * g ^ 2 * B) +
        20 * E * g ^ 2 * d * B := by
    calc
      A₀ *
          (-3 * (3 * C * a i -
            4 * D * (g * multiOwnerOppositeComponentProduct owners i P) ^ 2) +
          20 * E * P i *
            (g * multiOwnerOppositeComponentProduct owners i P) ^ 3) =
          -3 * (3 * C * (a i * A₀) -
            4 * D *
              (A₀ *
                (g * multiOwnerOppositeComponentProduct owners i P) ^ 2)) +
          20 * E *
            (A₀ * P i *
              (g * multiOwnerOppositeComponentProduct owners i P) ^ 3) := by
                ring
      _ = -3 * (3 * C * multiOwnerCofactorProduct owners a -
          4 * D * g ^ 2 * B) +
          20 * E * g ^ 2 * d * B := by
        rw [hfull, hfactorSq, hfactorCube]
        ring
  have hsum := dvd_add hbase hcorrection
  convert hsum using 1
  dsimp [multiOwnerThirdObstruction, multiOwnerSecondObstruction, B₀]
  rw [hbaseEq]
  ring

/-- If every selected positive residual exceeds `5d`, exact decomposition of
the original gap gives a lower bound for the product of all selected
cofactors.  This keeps the original loss `g`; it does not absorb any
unselected component. -/
theorem multi_owner_cofactor_product_scaled_lower
    {α : Type*}
    {owners : Finset α} {a P : α → ℕ} {d g : ℕ}
    (howners : owners.Nonempty)
    (hdpos : 0 < d)
    (hgpos : 0 < g)
    (hdecomp : d = g * ∏ j ∈ owners, P j)
    (hresidual : ∀ j ∈ owners, 5 * d < a j * (P j) ^ 2) :
    g ^ 2 * (5 * d) ^ owners.card <
      (∏ j ∈ owners, a j) * d ^ 2 := by
  have hproduct :
      (∏ _j ∈ owners, 5 * d) <
        ∏ j ∈ owners, a j * (P j) ^ 2 := by
    apply Finset.prod_lt_prod_of_nonempty
    · intro j hj
      exact Nat.mul_pos (by norm_num) hdpos
    · exact hresidual
    · exact howners
  have hscaled := Nat.mul_lt_mul_of_pos_left hproduct (pow_pos hgpos 2)
  calc
    g ^ 2 * (5 * d) ^ owners.card =
        g ^ 2 * ∏ _j ∈ owners, 5 * d := by
          simp [Finset.prod_const]
    _ < g ^ 2 * ∏ j ∈ owners, a j * (P j) ^ 2 := hscaled
    _ = (∏ j ∈ owners, a j) * d ^ 2 := by
      rw [Finset.prod_mul_distrib, Finset.prod_pow, hdecomp, mul_pow]
      ring

/-- A uniform ceiling for the coefficient multiplying `g^2` in a zero
multi-owner second obstruction.  It uses only `|D_i| < 10^12`, at most
fourteen opposite owners, and offsets of absolute value at most fifteen. -/
def multiOwnerZeroCoefficientBound : ℕ :=
  4 * 10 ^ 12 * 3 ^ 14 * 15 ^ 14 + 1

/-- Four or more residuals above `5d` force the cofactor product past the
uniform zero-obstruction coefficient at the target scale. -/
theorem multi_owner_target_cofactor_product_gt_zero_bound
    {α : Type*}
    {owners : Finset α} {a P : α → ℕ} {d g : ℕ}
    (hcard : 4 ≤ owners.card)
    (hd : 10 ^ 120 ≤ d)
    (hgpos : 0 < g)
    (hdecomp : d = g * ∏ j ∈ owners, P j)
    (hresidual : ∀ j ∈ owners, 5 * d < a j * (P j) ^ 2) :
    multiOwnerZeroCoefficientBound * g ^ 2 < ∏ j ∈ owners, a j := by
  have hdpos : 0 < d := lt_of_lt_of_le (by norm_num) hd
  have howners : owners.Nonempty := Finset.card_pos.mp (by omega)
  have hscaled := multi_owner_cofactor_product_scaled_lower
    howners hdpos hgpos hdecomp hresidual
  have hnumeric :
      multiOwnerZeroCoefficientBound < 625 * (10 ^ 120) ^ 2 := by
    norm_num [multiOwnerZeroCoefficientBound]
  have hdSq : (10 ^ 120) ^ 2 ≤ d ^ 2 := Nat.pow_le_pow_left hd 2
  have hKdSq : multiOwnerZeroCoefficientBound < 625 * d ^ 2 :=
    lt_of_lt_of_le hnumeric (Nat.mul_le_mul_left 625 hdSq)
  have hfour :
      multiOwnerZeroCoefficientBound * d ^ 2 < (5 * d) ^ 4 := by
    calc
      multiOwnerZeroCoefficientBound * d ^ 2 <
          (625 * d ^ 2) * d ^ 2 :=
        Nat.mul_lt_mul_of_pos_right hKdSq (pow_pos hdpos 2)
      _ = (5 * d) ^ 4 := by ring
  have hpow : (5 * d) ^ 4 ≤ (5 * d) ^ owners.card :=
    pow_le_pow_right' (by omega : 1 ≤ 5 * d) hcard
  have hKd :
      multiOwnerZeroCoefficientBound * d ^ 2 <
        (5 * d) ^ owners.card := lt_of_lt_of_le hfour hpow
  have hgKd := Nat.mul_lt_mul_of_pos_left hKd (pow_pos hgpos 2)
  have hcancel :
      (multiOwnerZeroCoefficientBound * g ^ 2) * d ^ 2 <
        (∏ j ∈ owners, a j) * d ^ 2 := by
    calc
      (multiOwnerZeroCoefficientBound * g ^ 2) * d ^ 2 =
          g ^ 2 * (multiOwnerZeroCoefficientBound * d ^ 2) := by ring
      _ < g ^ 2 * (5 * d) ^ owners.card := hgKd
      _ < (∏ j ∈ owners, a j) * d ^ 2 := hscaled
  exact (Nat.mul_lt_mul_right (pow_pos hdpos 2)).mp hcancel

/-- Crude but uniform coefficient audit for every target-row owner family of
size at most fifteen. -/
theorem multi_owner_zero_coefficient_natAbs_lt
    {D delta : ℤ} {r : ℕ}
    (hD : Int.natAbs D < 10 ^ 12)
    (hr : r ≤ 14)
    (hdelta : Int.natAbs delta ≤ 15 ^ 14) :
    Int.natAbs (4 * D * (-3) ^ r * delta) <
      multiOwnerZeroCoefficientBound := by
  have hDle : Int.natAbs D ≤ 10 ^ 12 := Nat.le_of_lt hD
  have hpow : 3 ^ r ≤ 3 ^ 14 :=
    pow_le_pow_right' (by norm_num : 1 ≤ (3 : ℕ)) hr
  have hle :
      4 * Int.natAbs D * 3 ^ r * Int.natAbs delta ≤
        4 * 10 ^ 12 * 3 ^ 14 * 15 ^ 14 := by
    exact Nat.mul_le_mul
      (Nat.mul_le_mul
        (Nat.mul_le_mul (le_rfl : 4 ≤ 4) hDle) hpow)
      hdelta
  calc
    Int.natAbs (4 * D * (-3) ^ r * delta) =
        4 * Int.natAbs D * 3 ^ r * Int.natAbs delta := by
      simp [Int.natAbs_mul, Int.natAbs_pow]
    _ ≤ 4 * 10 ^ 12 * 3 ^ 14 * 15 ^ 14 := hle
    _ < multiOwnerZeroCoefficientBound := by
      simp [multiOwnerZeroCoefficientBound]

/-- Once the cofactor product exceeds the uniform coefficient, a bounded
multi-owner second obstruction cannot vanish. -/
theorem bounded_multi_owner_second_obstruction_ne_zero
    {A g r : ℕ} {C D delta : ℤ}
    (hgpos : 0 < g)
    (hC : C ≠ 0)
    (hD : Int.natAbs D < 10 ^ 12)
    (hr : r ≤ 14)
    (hdelta : Int.natAbs delta ≤ 15 ^ 14)
    (hA : multiOwnerZeroCoefficientBound * g ^ 2 < A) :
    3 * C * (A : ℤ) -
      4 * D * (g : ℤ) ^ 2 * (-3) ^ r * delta ≠ 0 := by
  intro hzero
  let coeff : ℤ := 4 * D * (-3) ^ r * delta
  have heq : 3 * C * (A : ℤ) = coeff * (g : ℤ) ^ 2 := by
    dsimp [coeff]
    linarith
  have habs := congrArg Int.natAbs heq
  have habsEq :
      3 * Int.natAbs C * A = Int.natAbs coeff * g ^ 2 := by
    simpa [Int.natAbs_mul, Int.natAbs_pow] using habs
  have hcoeff : Int.natAbs coeff < multiOwnerZeroCoefficientBound := by
    dsimp [coeff]
    exact multi_owner_zero_coefficient_natAbs_lt hD hr hdelta
  have hcoeffScaled :
      Int.natAbs coeff * g ^ 2 < multiOwnerZeroCoefficientBound * g ^ 2 :=
    Nat.mul_lt_mul_of_pos_right hcoeff (pow_pos hgpos 2)
  have hCpos : 0 < Int.natAbs C := Int.natAbs_pos.mpr hC
  have hAle : A ≤ 3 * Int.natAbs C * A := by
    nlinarith
  have hAlt : A < multiOwnerZeroCoefficientBound * g ^ 2 := by
    calc
      A ≤ 3 * Int.natAbs C * A := hAle
      _ = Int.natAbs coeff * g ^ 2 := habsEq
      _ < multiOwnerZeroCoefficientBound * g ^ 2 := hcoeffScaled
  omega

/-- Owner offsets in `[1,15]` have uniformly bounded finite delta product. -/
theorem multi_owner_delta_natAbs_le_pow
    {owners : Finset ℤ} {i : ℤ}
    (hi : i ∈ owners)
    (hrange : ∀ j ∈ owners, 1 ≤ j ∧ j ≤ 15) :
    Int.natAbs (multiOwnerDelta owners i) ≤
      15 ^ (owners.erase i).card := by
  have hpoint : ∀ j ∈ owners.erase i, Int.natAbs (i - j) ≤ 15 := by
    intro j hj
    have hiRange := hrange i hi
    have hjRange := hrange j (Finset.mem_of_mem_erase hj)
    rcases le_total j i with hji | hij
    · have hcast : ((Int.natAbs (i - j) : ℕ) : ℤ) = i - j :=
        Int.natAbs_of_nonneg (sub_nonneg.mpr hji)
      have hbound : ((Int.natAbs (i - j) : ℕ) : ℤ) ≤ (15 : ℤ) := by
        rw [hcast]
        omega
      exact_mod_cast hbound
    · have heq : Int.natAbs (i - j) = Int.natAbs (j - i) := by
        rw [show i - j = -(j - i) by ring, Int.natAbs_neg]
      have hcast : ((Int.natAbs (j - i) : ℕ) : ℤ) = j - i :=
        Int.natAbs_of_nonneg (sub_nonneg.mpr hij)
      have hbound : ((Int.natAbs (j - i) : ℕ) : ℤ) ≤ (15 : ℤ) := by
        rw [hcast]
        omega
      rw [heq]
      exact_mod_cast hbound
  calc
    Int.natAbs (multiOwnerDelta owners i) =
        ∏ j ∈ owners.erase i, Int.natAbs (i - j) := by
      unfold multiOwnerDelta
      exact map_prod Int.natAbsHom (fun j => i - j) (owners.erase i)
    _ ≤ ∏ _j ∈ owners.erase i, 15 := by
      exact Finset.prod_le_prod (fun _j _hj => Nat.zero_le _) hpoint
    _ = 15 ^ (owners.erase i).card := by
      simp [Finset.prod_const]

/-- Uniform target-size zero exclusion for every owner family of cardinality
`4..15`, with the original bounded loss decomposition. -/
theorem target_multi_owner_second_obstruction_ne_zero
    {owners : Finset ℤ} {i C D : ℤ}
    {a P : ℤ → ℕ} {d g : ℕ}
    (hi : i ∈ owners)
    (hcard4 : 4 ≤ owners.card)
    (hcard15 : owners.card ≤ 15)
    (hrange : ∀ j ∈ owners, 1 ≤ j ∧ j ≤ 15)
    (hd : 10 ^ 120 ≤ d)
    (hgpos : 0 < g)
    (hdecomp : d = g * ∏ j ∈ owners, P j)
    (hresidual : ∀ j ∈ owners, 5 * d < a j * (P j) ^ 2)
    (hC : C ≠ 0)
    (hD : Int.natAbs D < 10 ^ 12) :
    multiOwnerSecondObstruction owners i C D (g : ℤ)
      (fun j => (a j : ℤ)) ≠ 0 := by
  have hA := multi_owner_target_cofactor_product_gt_zero_bound
    hcard4 hd hgpos hdecomp hresidual
  have hcardErase : (owners.erase i).card ≤ 14 := by
    rw [Finset.card_erase_of_mem hi]
    omega
  have hdeltaBase := multi_owner_delta_natAbs_le_pow hi hrange
  have hpow : 15 ^ (owners.erase i).card ≤ 15 ^ 14 :=
    pow_le_pow_right' (by norm_num : 1 ≤ (15 : ℕ)) hcardErase
  have hdelta : Int.natAbs (multiOwnerDelta owners i) ≤ 15 ^ 14 :=
    le_trans hdeltaBase hpow
  have hne := bounded_multi_owner_second_obstruction_ne_zero
    hgpos hC hD hcardErase hdelta hA
  simpa [multiOwnerSecondObstruction, multiOwnerCofactorProduct,
    Int.cast_prod, mul_assoc, mul_comm, mul_left_comm] using hne

#print axioms multi_owner_opposite_product_modeq_sq
#print axioms multi_owner_opposite_product_sub_dvd_sq
#print axioms multi_owner_second_obstruction_dvd
#print axioms multi_owner_third_obstruction_dvd_sq
#print axioms multi_owner_cofactor_product_scaled_lower
#print axioms multi_owner_target_cofactor_product_gt_zero_bound
#print axioms multi_owner_zero_coefficient_natAbs_lt
#print axioms bounded_multi_owner_second_obstruction_ne_zero
#print axioms multi_owner_delta_natAbs_le_pow
#print axioms target_multi_owner_second_obstruction_ne_zero

end Erdos686Variant
end Erdos686
