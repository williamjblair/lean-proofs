/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import ErdosProblems.Erdos686.Core.ControlledPairing
import Mathlib.Analysis.MeanInequalities

open scoped BigOperators

namespace Erdos686
namespace Erdos686Variant

theorem list_nary_amgm (xs : List ℕ) (q : ℕ) (hq : 0 < q)
    (hlen : xs.length = q) :
    q ^ q * xs.prod ≤ xs.sum ^ q := by
  let z : Fin xs.length → ℝ := fun i ↦ (xs[i.1] : ℝ)
  have hcard : (Finset.univ : Finset (Fin xs.length)).card = q := by
    simpa [hlen]
  have hweight_pos :
      0 < ∑ _i ∈ (Finset.univ : Finset (Fin xs.length)), (1 : ℝ) := by
    simp [hlen, hq]
  have hz : ∀ i ∈ (Finset.univ : Finset (Fin xs.length)), 0 ≤ z i := by
    intro i hi
    dsimp [z]
    positivity
  have hamgm := Real.geom_mean_le_arith_mean
    (Finset.univ : Finset (Fin xs.length)) (fun _ ↦ (1 : ℝ)) z
    (by intro i hi; positivity) hweight_pos hz
  have hamgm' :
      (∏ i : Fin xs.length, z i) ^ ((q : ℝ)⁻¹) ≤
        (∑ i : Fin xs.length, z i) / (q : ℝ) := by
    simpa [hlen] using hamgm
  have hprod_nonneg : 0 ≤ (∏ i : Fin xs.length, z i) := by
    positivity
  have hsum_nonneg : 0 ≤ (∑ i : Fin xs.length, z i) := by
    exact Finset.sum_nonneg fun i hi ↦ hz i (Finset.mem_univ i)
  have hqR_pos : (0 : ℝ) < q := by exact_mod_cast hq
  have hpow := Real.rpow_le_rpow (by positivity) hamgm' (Nat.cast_nonneg q)
  rw [← Real.rpow_mul hprod_nonneg] at hpow
  have hq_inv : (q : ℝ)⁻¹ * q = 1 := inv_mul_cancel₀ (ne_of_gt hqR_pos)
  rw [hq_inv, Real.rpow_one, Real.rpow_natCast] at hpow
  have hreal : (q : ℝ) ^ q * (∏ i : Fin xs.length, z i) ≤
      (∑ i : Fin xs.length, z i) ^ q := by
    rw [div_pow] at hpow
    exact (le_div_iff₀' (pow_pos hqR_pos q)).mp (by
      simpa [mul_assoc] using hpow)
  have hprod_cast : (∏ i : Fin xs.length, z i) = (xs.prod : ℝ) := by
    simp [z]
  have hsum_cast : (∑ i : Fin xs.length, z i) = (xs.sum : ℝ) := by
    simp [z]
  rw [hprod_cast, hsum_cast] at hreal
  exact_mod_cast hreal

private theorem list_prod_const_mul
    {α : Type*} (xs : List α) (d : ℕ) (f : α → ℕ) :
    (xs.map (fun x => d * f x)).prod =
      d ^ xs.length * (xs.map f).prod := by
  induction xs with
  | nil => simp
  | cons x tail ih =>
      simp only [List.map_cons, List.prod_cons, List.length_cons, pow_succ]
      rw [ih]
      ring

private theorem list_sum_affine
    {α : Type*} (xs : List α) (A B : ℕ) (f : α → ℕ) :
    (xs.map (fun x => A * f x + B)).sum =
      A * (xs.map f).sum + xs.length * B := by
  induction xs with
  | nil => simp
  | cons x tail ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      rw [ih]
      ring

/-- Division-free product estimate used after controlled secant pairing.
The individual factors are bounded by affine functions of nonnegative gap
weights, while only the total gap weight is needed globally. -/
theorem paired_product_upper_of_weight_sum
    {α : Type*} (pairs : List α)
    (value weight : α → ℕ) (k d q : ℕ)
    (hq : 0 < q)
    (hlen : pairs.length = q)
    (hvalue : ∀ p ∈ pairs,
      value p ≤ d * ((k + 1) * weight p + 2 * (k - 1)))
    (hweight : (pairs.map weight).sum ≤ 4 * (k - 1)) :
    q ^ q * (pairs.map value).prod ≤
      (2 * (k - 1) * (q + 2 * (k + 1)) * d) ^ q := by
  let affine : α → ℕ :=
    fun p => (k + 1) * weight p + 2 * (k - 1)
  have hprod :
      (pairs.map value).prod ≤
        (pairs.map (fun p => d * affine p)).prod := by
    apply List.prod_le_prod'
    intro p hp
    exact hvalue p hp
  have hprodSplit :
      (pairs.map (fun p => d * affine p)).prod =
        d ^ q * (pairs.map affine).prod := by
    rw [← hlen]
    exact list_prod_const_mul pairs d affine
  have hamgm :
      q ^ q * (pairs.map affine).prod ≤
        (pairs.map affine).sum ^ q := by
    apply list_nary_amgm (pairs.map affine) q hq
    simpa using hlen
  have hsumAffine :
      (pairs.map affine).sum ≤
        2 * (k - 1) * (q + 2 * (k + 1)) := by
    have hsumEq :
        (pairs.map affine).sum =
          (k + 1) * (pairs.map weight).sum + q * (2 * (k - 1)) := by
      rw [← hlen]
      exact list_sum_affine pairs (k + 1) (2 * (k - 1)) weight
    rw [hsumEq]
    calc
      (k + 1) * (pairs.map weight).sum + q * (2 * (k - 1)) ≤
          (k + 1) * (4 * (k - 1)) + q * (2 * (k - 1)) :=
        Nat.add_le_add_right (Nat.mul_le_mul_left (k + 1) hweight) _
      _ = 2 * (k - 1) * (q + 2 * (k + 1)) := by ring
  have hprod' :
      (pairs.map value).prod ≤
        d ^ q * (pairs.map affine).prod :=
    hprod.trans_eq hprodSplit
  calc
    q ^ q * (pairs.map value).prod ≤
        q ^ q * (d ^ q * (pairs.map affine).prod) :=
      Nat.mul_le_mul_left _ hprod'
    _ = d ^ q * (q ^ q * (pairs.map affine).prod) := by ring
    _ ≤ d ^ q * (pairs.map affine).sum ^ q :=
      Nat.mul_le_mul_left _ hamgm
    _ ≤ d ^ q *
        (2 * (k - 1) * (q + 2 * (k + 1))) ^ q := by
      exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hsumAffine q)
    _ = (d * (2 * (k - 1) * (q + 2 * (k + 1)))) ^ q :=
      (mul_pow d _ q).symm
    _ = (2 * (k - 1) * (q + 2 * (k + 1)) * d) ^ q := by
      rw [mul_comm d]

private theorem natAbs_gap_sum_eq_pairingCost
    {α : Type*} (rho : α → ℤ) (pairs : List (α × α))
    (hnonneg : ∀ p ∈ pairs, 0 ≤ rho p.2 - rho p.1) :
    (((pairs.map (fun p => Int.natAbs (rho p.2 - rho p.1))).sum : ℕ) : ℤ) =
      (pairs.map (fun p => rho p.2 - rho p.1)).sum := by
  induction pairs with
  | nil => simp
  | cons p tail ih =>
      have hp : 0 ≤ rho p.2 - rho p.1 := hnonneg p (by simp)
      have htail : ∀ z ∈ tail, 0 ≤ rho z.2 - rho z.1 := by
        intro z hz
        exact hnonneg z (by simp [hz])
      simp only [List.map_cons, List.sum_cons, Int.natCast_add,
        Int.natCast_natAbs, abs_of_nonneg hp]
      rw [ih htail]

/-- The explicit controlled pairing supplies the exact natural total-weight
bound required by the division-free AM-GM estimate. -/
theorem controlledPairing_natAbs_gap_sum_le
    {k : ℕ} {xs : List (ℕ × ℕ)}
    (hcells : ∀ z ∈ xs,
      ownerCellRow z ∈ Finset.Icc 1 k ∧
        ownerCellColumn z ∈ Finset.Icc 1 k)
    (hsorted : xs.Pairwise (fun a b =>
      ownerCellOffset a < ownerCellOffset b))
    (hlen : 7 ≤ xs.length) :
    ((controlledPairing xs).1.map (fun p =>
      Int.natAbs (ownerCellOffset p.2 - ownerCellOffset p.1))).sum ≤
        4 * (k - 1) := by
  have hfour : 4 ≤ xs.length := by omega
  have hnonneg :
      ∀ p ∈ (controlledPairing xs).1,
        0 ≤ ownerCellOffset p.2 - ownerCellOffset p.1 := by
    intro p hp
    have hpair :=
      every_pair_gap_at_least_two ownerCellOffset xs hsorted hfour p hp
    omega
  have hcast := natAbs_gap_sum_eq_pairingCost ownerCellOffset
    (controlledPairing xs).1 hnonneg
  have hcost :=
    controlled_pairing_total_gap_le_four_k_sub_one hcells hsorted hlen
  rw [pairingCost] at hcost
  exact_mod_cast (hcast.symm ▸ hcost)

/-- Exact controlled-pair product upper bound after clearing the `q^q`
denominator.  The individual pair bounds are the nonzero-secant estimates;
the total weight premise is discharged by the explicit pairing theorem. -/
theorem controlled_pairing_product_upper
    {k d : ℕ} {xs : List (ℕ × ℕ)}
    (P : (ℕ × ℕ) → ℕ)
    (hcells : ∀ z ∈ xs,
      ownerCellRow z ∈ Finset.Icc 1 k ∧
        ownerCellColumn z ∈ Finset.Icc 1 k)
    (hsorted : xs.Pairwise (fun a b =>
      ownerCellOffset a < ownerCellOffset b))
    (hlen : 7 ≤ xs.length)
    (hpairBound : ∀ p ∈ (controlledPairing xs).1,
      P p.1 * P p.2 ≤
        d * ((k + 1) *
          Int.natAbs (ownerCellOffset p.2 - ownerCellOffset p.1) +
          2 * (k - 1))) :
    let q := xs.length / 2
    q ^ q *
        ((controlledPairing xs).1.map (fun p => P p.1 * P p.2)).prod ≤
      (2 * (k - 1) * (q + 2 * (k + 1)) * d) ^ q := by
  dsimp
  let q := xs.length / 2
  have hq : 0 < q := by
    dsimp [q]
    omega
  have hpairLength : (controlledPairing xs).1.length = q := by
    dsimp [q]
    exact pair_count_eq_div_two ownerCellOffset xs hsorted (by omega)
  apply paired_product_upper_of_weight_sum
    (controlledPairing xs).1
    (fun p => P p.1 * P p.2)
    (fun p => Int.natAbs
      (ownerCellOffset p.2 - ownerCellOffset p.1))
    k d q hq hpairLength hpairBound
  exact controlledPairing_natAbs_gap_sum_le hcells hsorted hlen

/-- Exact multiplicative decomposition supplied by permutation coverage of
the controlled pairing. -/
theorem controlledPairing_product_decomposition
    {α : Type*} (P : α → ℕ) (xs : List α) :
    (xs.map P).prod =
      ((controlledPairing xs).1.map (fun p => P p.1 * P p.2)).prod *
        ((controlledPairing xs).2.map P).prod := by
  have hperm := (pairedEntries_perm xs).map P
  have hprod := hperm.prod_eq
  rw [pairedEntries, List.map_append, List.prod_append] at hprod
  have hflat :
      ((List.flatMap (fun p : α × α => [p.1, p.2])
          (controlledPairing xs).1).map P).prod =
        ((controlledPairing xs).1.map
          (fun p => P p.1 * P p.2)).prod := by
    induction (controlledPairing xs).1 with
    | nil => simp
    | cons p tail ih =>
        simp only [List.flatMap_cons, List.map_append, List.prod_append,
          List.map_cons, List.prod_cons]
        simp [ih]
  rw [hflat] at hprod
  exact hprod.symm

private theorem unmatched_product_upper
    {α : Type*} (P : α → ℕ) (d delta : ℕ) (us : List α)
    (hlen : us.length = delta)
    (hdelta : delta ≤ 1)
    (hbound : ∀ u ∈ us, 2 * P u ≤ 3 * d) :
    2 ^ delta * (us.map P).prod ≤ (3 * d) ^ delta := by
  match us with
  | [] =>
      have hzero : delta = 0 := by simpa using hlen.symm
      subst delta
      simp
  | [u] =>
      have hone : delta = 1 := by simpa using hlen.symm
      subst delta
      have hu := hbound u (by simp)
      simpa using hu
  | u :: v :: tail =>
      simp only [List.length_cons] at hlen
      omega

/-- Full controlled matching product upper bound, including the possible
unpaired owner and with every rational denominator cleared. -/
theorem controlled_matching_full_product_upper
    {k d : ℕ} {xs : List (ℕ × ℕ)}
    (P : (ℕ × ℕ) → ℕ)
    (hcells : ∀ z ∈ xs,
      ownerCellRow z ∈ Finset.Icc 1 k ∧
        ownerCellColumn z ∈ Finset.Icc 1 k)
    (hsorted : xs.Pairwise (fun a b =>
      ownerCellOffset a < ownerCellOffset b))
    (hlen : 7 ≤ xs.length)
    (hpairBound : ∀ p ∈ (controlledPairing xs).1,
      P p.1 * P p.2 ≤
        d * ((k + 1) *
          Int.natAbs (ownerCellOffset p.2 - ownerCellOffset p.1) +
          2 * (k - 1)))
    (hunpaired : ∀ u ∈ (controlledPairing xs).2,
      2 * P u ≤ 3 * d) :
    let q := xs.length / 2
    let delta := xs.length % 2
    2 ^ delta * q ^ q * (xs.map P).prod ≤
      (3 * d) ^ delta *
        (2 * (k - 1) * (q + 2 * (k + 1)) * d) ^ q := by
  dsimp
  let q := xs.length / 2
  let delta := xs.length % 2
  have hpair := controlled_pairing_product_upper P hcells hsorted hlen
    hpairBound
  have hunmatchedLength :
      (controlledPairing xs).2.length = delta := by
    dsimp [delta]
    exact unmatched_length_eq_mod_two ownerCellOffset xs hsorted (by omega)
  have hdelta : delta ≤ 1 := by
    dsimp [delta]
    omega
  have hunmatched := unmatched_product_upper P d delta
    (controlledPairing xs).2 hunmatchedLength hdelta hunpaired
  have hdecomp := controlledPairing_product_decomposition P xs
  calc
    2 ^ delta * q ^ q * (xs.map P).prod =
        (2 ^ delta * ((controlledPairing xs).2.map P).prod) *
          (q ^ q * ((controlledPairing xs).1.map
            (fun p => P p.1 * P p.2)).prod) := by
      rw [hdecomp]
      ring
    _ ≤ (3 * d) ^ delta *
        (2 * (k - 1) * (q + 2 * (k + 1)) * d) ^ q :=
      Nat.mul_le_mul hunmatched hpair

#print axioms list_nary_amgm
#print axioms paired_product_upper_of_weight_sum
#print axioms controlledPairing_natAbs_gap_sum_le
#print axioms controlled_pairing_product_upper
#print axioms controlledPairing_product_decomposition
#print axioms controlled_matching_full_product_upper

end Erdos686Variant
end Erdos686
