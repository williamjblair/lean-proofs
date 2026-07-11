/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import ErdosProblems.Erdos686AllOwnerAssembly

/-!
# Independent hostile audit of the all-owner assembly

Every producer theorem is restated under a fresh `hostile_` name and proved
from definitions, upstream assignment/lift theorems, and earlier hostile
lemmas.  No hostile proof invokes the corresponding producer theorem.
-/

namespace Erdos686
namespace Erdos686Variant

open scoped BigOperators

theorem hostile_allOwnerBucket_pos
    (k d i : ℕ) (owner : ℕ → ℕ) :
    0 < allOwnerBucket k d owner i := by
  unfold allOwnerBucket globalResidualGroupedLeft
  apply Finset.prod_pos
  intro p hp
  unfold globalResidualGroupedLeftFactor
  split
  · exact pow_pos (Nat.prime_of_mem_primeFactors hp).pos _
  · norm_num

theorem hostile_allOwnerLoss_pos (k d : ℕ) :
    0 < globalResidualGroupedLoss k d := by
  unfold globalResidualGroupedLoss globalResidualGroupedLossFactor
  apply Finset.prod_pos
  intro p hp
  exact pow_pos (Nat.prime_of_mem_primeFactors hp).pos _

theorem hostile_allOwnerBucket_dvd_factor
    {k n d i : ℕ} {owner : ℕ → ℕ}
    (hassign : GlobalResidualOwnerAssignment k n d owner) :
    allOwnerBucket k d owner i ∣ n + i := by
  exact globalResidualGroupedLeft_dvd_factor hassign

theorem hostile_allOwnerBucket_square_dvd_residual
    {k n d i : ℕ} {owner : ℕ → ℕ}
    (hassign : GlobalResidualOwnerAssignment k n d owner) :
    (allOwnerBucket k d owner i) ^ 2 ∣ localResidual n d i := by
  exact globalResidualGroupedLeft_square_dvd_residual hassign

theorem hostile_allOwner_residual_decomposition
    {k n d i : ℕ} {owner : ℕ → ℕ}
    (hassign : GlobalResidualOwnerAssignment k n d owner) :
    localResidual n d i =
      allOwnerCofactor k n d owner i *
        (allOwnerBucket k d owner i) ^ 2 := by
  unfold allOwnerCofactor
  exact (Nat.div_mul_cancel
    (hostile_allOwnerBucket_square_dvd_residual hassign)).symm

theorem hostile_allOwner_one_prime_placement
    {k n d p : ℕ} {owner : ℕ → ℕ}
    (hassign : GlobalResidualOwnerAssignment k n d owner)
    (hp : p ∈ d.primeFactors) :
    (∏ i ∈ allOwnerGrid k,
        globalResidualGroupedLeftFactor k d owner i p) =
      p ^ globalResidualCleanExponent p (d.factorization p) k := by
  classical
  have howner : owner p ∈ allOwnerGrid k := (hassign p hp).1
  rw [Finset.prod_eq_single (owner p)]
  · simp [globalResidualGroupedLeftFactor]
  · intro i hi hne
    simp [globalResidualGroupedLeftFactor, Ne.symm hne]
  · exact fun hnot => (hnot howner).elim

theorem hostile_allOwner_bucket_product_eq_clean_product
    {k n d : ℕ} {owner : ℕ → ℕ}
    (hassign : GlobalResidualOwnerAssignment k n d owner) :
    (∏ i ∈ allOwnerGrid k, allOwnerBucket k d owner i) =
      ∏ p ∈ d.primeFactors,
        p ^ globalResidualCleanExponent p (d.factorization p) k := by
  classical
  unfold allOwnerBucket globalResidualGroupedLeft
  rw [Finset.prod_comm]
  apply Finset.prod_congr rfl
  intro p hp
  exact hostile_allOwner_one_prime_placement hassign hp

theorem hostile_allOwner_gap_decomposition
    {k n d : ℕ} {owner : ℕ → ℕ}
    (hd : 0 < d)
    (hassign : GlobalResidualOwnerAssignment k n d owner) :
    d = globalResidualGroupedLoss k d *
      ∏ i ∈ allOwnerGrid k, allOwnerBucket k d owner i := by
  have hfactorization :
      (∏ p ∈ d.primeFactors, p ^ d.factorization p) = d := by
    rw [← Nat.prod_factorization_eq_prod_primeFactors]
    exact Nat.prod_factorization_pow_eq_self (Nat.ne_of_gt hd)
  calc
    d = ∏ p ∈ d.primeFactors, p ^ d.factorization p := hfactorization.symm
    _ = ∏ p ∈ d.primeFactors,
        globalResidualGroupedLossFactor k d p *
          p ^ globalResidualCleanExponent p (d.factorization p) k := by
      apply Finset.prod_congr rfl
      intro p hp
      exact (globalResidualGroupedLossFactor_mul_clean k d p).symm
    _ = globalResidualGroupedLoss k d *
        ∏ p ∈ d.primeFactors,
          p ^ globalResidualCleanExponent p (d.factorization p) k := by
      rw [Finset.prod_mul_distrib]
      rfl
    _ = globalResidualGroupedLoss k d *
        ∏ i ∈ allOwnerGrid k, allOwnerBucket k d owner i := by
      rw [hostile_allOwner_bucket_product_eq_clean_product hassign]

theorem hostile_allOwner_gap_decomposition_at
    {k n d i : ℕ} {owner : ℕ → ℕ}
    (hi : i ∈ allOwnerGrid k)
    (hd : 0 < d)
    (hassign : GlobalResidualOwnerAssignment k n d owner) :
    d = allOwnerBucket k d owner i *
      (globalResidualGroupedLoss k d *
        ∏ j ∈ (allOwnerGrid k).erase i,
          allOwnerBucket k d owner j) := by
  calc
    d = globalResidualGroupedLoss k d *
        ∏ j ∈ allOwnerGrid k, allOwnerBucket k d owner j :=
      hostile_allOwner_gap_decomposition hd hassign
    _ = allOwnerBucket k d owner i *
        (globalResidualGroupedLoss k d *
          ∏ j ∈ (allOwnerGrid k).erase i,
            allOwnerBucket k d owner j) := by
      rw [← Finset.mul_prod_erase (allOwnerGrid k)
        (allOwnerBucket k d owner) hi]
      ring

theorem hostile_allOwner_residual_cast
    {k n d i : ℕ} {owner : ℕ → ℕ}
    (hassign : GlobalResidualOwnerAssignment k n d owner)
    (hpos : 0 < localResidual n d i) :
    3 * ((n + i : ℕ) : ℤ) - (d : ℤ) =
      (allOwnerCofactor k n d owner i : ℤ) *
        (allOwnerBucket k d owner i : ℤ) ^ 2 := by
  have hdle : d ≤ 3 * (n + i) := by
    unfold localResidual at hpos
    omega
  have hcast : ((localResidual n d i : ℕ) : ℤ) =
      3 * ((n + i : ℕ) : ℤ) - (d : ℤ) := by
    unfold localResidual
    rw [Int.ofNat_sub hdle]
    push_cast
    ring
  have hdecomp := hostile_allOwner_residual_decomposition (i := i) hassign
  calc
    3 * ((n + i : ℕ) : ℤ) - (d : ℤ) =
        ((localResidual n d i : ℕ) : ℤ) := hcast.symm
    _ = ((allOwnerCofactor k n d owner i *
          (allOwnerBucket k d owner i) ^ 2 : ℕ) : ℤ) := by
      exact_mod_cast hdecomp
    _ = (allOwnerCofactor k n d owner i : ℤ) *
        (allOwnerBucket k d owner i : ℤ) ^ 2 := by
      push_cast
      rfl

theorem hostile_allOwnerCofactor_pos
    {k n d i : ℕ} {owner : ℕ → ℕ}
    (hassign : GlobalResidualOwnerAssignment k n d owner)
    (hpos : 0 < localResidual n d i) :
    0 < allOwnerCofactor k n d owner i := by
  by_contra hnot
  have ha0 : allOwnerCofactor k n d owner i = 0 :=
    Nat.eq_zero_of_not_pos hnot
  have hdecomp := hostile_allOwner_residual_decomposition (i := i) hassign
  rw [hdecomp, ha0] at hpos
  simp at hpos

theorem hostile_allOwner_residual_difference
    {k n d i j : ℕ} {owner : ℕ → ℕ}
    (hassign : GlobalResidualOwnerAssignment k n d owner)
    (hipos : 0 < localResidual n d i)
    (hjpos : 0 < localResidual n d j) :
    (allOwnerCofactor k n d owner i : ℤ) *
          (allOwnerBucket k d owner i : ℤ) ^ 2 -
        (allOwnerCofactor k n d owner j : ℤ) *
          (allOwnerBucket k d owner j : ℤ) ^ 2 =
      3 * ((i : ℤ) - (j : ℤ)) := by
  have hi := hostile_allOwner_residual_cast hassign hipos
  have hj := hostile_allOwner_residual_cast hassign hjpos
  calc
    (allOwnerCofactor k n d owner i : ℤ) *
          (allOwnerBucket k d owner i : ℤ) ^ 2 -
        (allOwnerCofactor k n d owner j : ℤ) *
          (allOwnerBucket k d owner j : ℤ) ^ 2 =
        (3 * ((n + i : ℕ) : ℤ) - (d : ℤ)) -
          (3 * ((n + j : ℕ) : ℤ) - (d : ℤ)) := by
      rw [hi, hj]
    _ = 3 * ((i : ℤ) - (j : ℤ)) := by
      push_cast
      ring

theorem hostile_allOwner_residual_pos
    {k n d i : ℕ}
    (hk5 : 5 ≤ k)
    (hkd : k ≤ d)
    (hi : i ∈ allOwnerGrid k)
    (heq : blockProduct k (n + d) = 4 * blockProduct k n) :
    0 < localResidual n d i := by
  have hgap := twice_gap_lt_n_of_four_solution hk5 hkd heq
  have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
  unfold localResidual
  omega

theorem hostile_allOwner_second_local_lift
    {k n d i : ℕ} {owner : ℕ → ℕ}
    (hk5 : 5 ≤ k)
    (hkd : k ≤ d)
    (hi : i ∈ allOwnerGrid k)
    (hassign : GlobalResidualOwnerAssignment k n d owner)
    (heq : blockProduct k (n + d) = 4 * blockProduct k n) :
    (allOwnerBucket k d owner i : ℤ) ∣
      3 * localSecondConstant k i *
          (allOwnerCofactor k n d owner i : ℤ) -
        4 * localSecondLinear k i *
          ((globalResidualGroupedLoss k d *
            ∏ j ∈ (allOwnerGrid k).erase i,
              allOwnerBucket k d owner j : ℕ) : ℤ) ^ 2 := by
  have hd : 0 < d := lt_of_lt_of_le (by omega) hkd
  have hrespos := hostile_allOwner_residual_pos hk5 hkd hi heq
  exact second_order_local_lift hi
    (hostile_allOwnerBucket_pos k d i owner)
    (hostile_allOwner_gap_decomposition_at hi hd hassign)
    (hostile_allOwnerBucket_dvd_factor hassign)
    (hostile_allOwner_residual_cast hassign hrespos) heq

theorem hostile_allOwner_third_local_lift
    {k n d i : ℕ} {owner : ℕ → ℕ}
    (hk5 : 5 ≤ k)
    (hkd : k ≤ d)
    (hi : i ∈ allOwnerGrid k)
    (hassign : GlobalResidualOwnerAssignment k n d owner)
    (heq : blockProduct k (n + d) = 4 * blockProduct k n) :
    (allOwnerBucket k d owner i : ℤ) ^ 2 ∣
      -3 * (3 * localSecondConstant k i *
          (allOwnerCofactor k n d owner i : ℤ) -
        4 * localSecondLinear k i *
          ((globalResidualGroupedLoss k d *
            ∏ j ∈ (allOwnerGrid k).erase i,
              allOwnerBucket k d owner j : ℕ) : ℤ) ^ 2) +
        20 * localThirdQuadratic k i *
          (allOwnerBucket k d owner i : ℤ) *
          ((globalResidualGroupedLoss k d *
            ∏ j ∈ (allOwnerGrid k).erase i,
              allOwnerBucket k d owner j : ℕ) : ℤ) ^ 3 := by
  have hd : 0 < d := lt_of_lt_of_le (by omega) hkd
  have hrespos := hostile_allOwner_residual_pos hk5 hkd hi heq
  exact third_order_local_lift hi
    (hostile_allOwnerBucket_pos k d i owner)
    (hostile_allOwner_gap_decomposition_at hi hd hassign)
    (hostile_allOwnerBucket_dvd_factor hassign)
    (hostile_allOwner_residual_cast hassign hrespos) heq

theorem hostile_allOwner_natCast_mem_intGrid
    {k i : ℕ} (hi : i ∈ allOwnerGrid k) :
    (i : ℤ) ∈ allOwnerIntGrid k := by
  simp [allOwnerIntGrid, hi]

theorem hostile_allOwnerIntGrid_card (k : ℕ) :
    (allOwnerIntGrid k).card = k := by
  calc
    (allOwnerIntGrid k).card = (allOwnerGrid k).card := by
      exact Finset.card_image_of_injective _ Int.ofNat_injective
    _ = k := by simp [allOwnerGrid, Nat.card_Icc]

theorem hostile_allOwnerIntGrid_exists_nat
    {k : ℕ} {z : ℤ} (hz : z ∈ allOwnerIntGrid k) :
    ∃ i ∈ allOwnerGrid k, z = (i : ℤ) := by
  rw [allOwnerIntGrid, Finset.mem_image] at hz
  obtain ⟨i, hi, hiz⟩ := hz
  exact ⟨i, hi, hiz.symm⟩

theorem hostile_allOwnerIntGrid_prod_bucket
    (k d : ℕ) (owner : ℕ → ℕ) :
    (∏ z ∈ allOwnerIntGrid k, allOwnerBucketInt k d owner z) =
      ∏ i ∈ allOwnerGrid k, allOwnerBucket k d owner i := by
  classical
  unfold allOwnerIntGrid
  rw [Finset.prod_image Int.ofNat_injective.injOn]
  apply Finset.prod_congr rfl
  intro i hi
  simp [allOwnerBucketInt]

theorem hostile_allOwnerIntGrid_erase_prod_bucket
    {k d i : ℕ} (owner : ℕ → ℕ) :
    (∏ z ∈ (allOwnerIntGrid k).erase (i : ℤ),
        allOwnerBucketInt k d owner z) =
      ∏ j ∈ (allOwnerGrid k).erase i,
        allOwnerBucket k d owner j := by
  classical
  have herase :
      (allOwnerIntGrid k).erase (i : ℤ) =
        ((allOwnerGrid k).erase i).image Int.ofNat := by
    unfold allOwnerIntGrid
    exact (Finset.image_erase Int.ofNat_injective (allOwnerGrid k) i).symm
  rw [herase]
  rw [Finset.prod_image Int.ofNat_injective.injOn]
  apply Finset.prod_congr rfl
  intro j hj
  simp [allOwnerBucketInt]

theorem hostile_allOwnerIntGrid_opposite_component
    {k d i : ℕ} (owner : ℕ → ℕ) :
    multiOwnerOppositeComponentProduct (allOwnerIntGrid k) (i : ℤ)
        (fun z => (allOwnerBucketInt k d owner z : ℤ)) =
      ((∏ j ∈ (allOwnerGrid k).erase i,
          allOwnerBucket k d owner j : ℕ) : ℤ) := by
  unfold multiOwnerOppositeComponentProduct
  have h := hostile_allOwnerIntGrid_erase_prod_bucket
    (k := k) (d := d) (i := i) owner
  have hcast := congrArg (fun q : ℕ => (q : ℤ)) h
  push_cast at hcast
  push_cast
  exact hcast

theorem hostile_allOwnerIntGrid_gap_decomposition
    {k n d : ℕ} {owner : ℕ → ℕ}
    (hd : 0 < d)
    (hassign : GlobalResidualOwnerAssignment k n d owner) :
    d = globalResidualGroupedLoss k d *
      ∏ z ∈ allOwnerIntGrid k, allOwnerBucketInt k d owner z := by
  rw [hostile_allOwnerIntGrid_prod_bucket]
  exact hostile_allOwner_gap_decomposition hd hassign

theorem hostile_allOwnerIntGrid_residual_difference
    {k n d : ℕ} {owner : ℕ → ℕ}
    (hk5 : 5 ≤ k)
    (hkd : k ≤ d)
    (hassign : GlobalResidualOwnerAssignment k n d owner)
    (heq : blockProduct k (n + d) = 4 * blockProduct k n)
    {x y : ℤ}
    (hx : x ∈ allOwnerIntGrid k)
    (hy : y ∈ allOwnerIntGrid k) :
    (allOwnerCofactorInt k n d owner x : ℤ) *
          (allOwnerBucketInt k d owner x : ℤ) ^ 2 -
        (allOwnerCofactorInt k n d owner y : ℤ) *
          (allOwnerBucketInt k d owner y : ℤ) ^ 2 =
      3 * (x - y) := by
  obtain ⟨i, hi, rfl⟩ := hostile_allOwnerIntGrid_exists_nat hx
  obtain ⟨j, hj, rfl⟩ := hostile_allOwnerIntGrid_exists_nat hy
  simpa [allOwnerCofactorInt, allOwnerBucketInt] using
    hostile_allOwner_residual_difference hassign
      (hostile_allOwner_residual_pos hk5 hkd hi heq)
      (hostile_allOwner_residual_pos hk5 hkd hj heq)

theorem hostile_allOwner_second_obstruction_dvd
    {k n d i : ℕ} {owner : ℕ → ℕ}
    (hk5 : 5 ≤ k)
    (hkd : k ≤ d)
    (hi : i ∈ allOwnerGrid k)
    (hassign : GlobalResidualOwnerAssignment k n d owner)
    (heq : blockProduct k (n + d) = 4 * blockProduct k n) :
    (allOwnerBucket k d owner i : ℤ) ∣
      multiOwnerSecondObstruction (allOwnerIntGrid k) (i : ℤ)
        (localSecondConstant k i) (localSecondLinear k i)
        (globalResidualGroupedLoss k d : ℤ)
        (fun z => (allOwnerCofactorInt k n d owner z : ℤ)) := by
  apply multi_owner_second_obstruction_dvd
      (P := fun z => (allOwnerBucketInt k d owner z : ℤ))
  · exact hostile_allOwner_natCast_mem_intGrid hi
  · rw [hostile_allOwnerIntGrid_opposite_component
      (k := k) (d := d) (i := i) owner]
    have hlocal := hostile_allOwner_second_local_lift
      hk5 hkd hi hassign heq
    push_cast at hlocal ⊢
    simpa [allOwnerBucketInt, allOwnerCofactorInt] using hlocal
  · intro z hz
    have hzGrid : z ∈ allOwnerIntGrid k :=
      Finset.mem_of_mem_erase hz
    have hdiff := hostile_allOwnerIntGrid_residual_difference
      hk5 hkd hassign heq (hostile_allOwner_natCast_mem_intGrid hi) hzGrid
    simpa [allOwnerBucketInt, allOwnerCofactorInt] using hdiff

theorem hostile_allOwner_third_obstruction_dvd_sq
    {k n d i : ℕ} {owner : ℕ → ℕ}
    (hk5 : 5 ≤ k)
    (hkd : k ≤ d)
    (hi : i ∈ allOwnerGrid k)
    (hassign : GlobalResidualOwnerAssignment k n d owner)
    (heq : blockProduct k (n + d) = 4 * blockProduct k n) :
    (allOwnerBucket k d owner i : ℤ) ^ 2 ∣
      multiOwnerThirdObstruction (allOwnerIntGrid k) (i : ℤ)
        (localSecondConstant k i) (localSecondLinear k i)
        (localThirdQuadratic k i)
        (globalResidualGroupedLoss k d : ℤ) (d : ℤ)
        (fun z => (allOwnerCofactorInt k n d owner z : ℤ)) := by
  apply multi_owner_third_obstruction_dvd_sq
      (P := fun z => (allOwnerBucketInt k d owner z : ℤ))
  · exact hostile_allOwner_natCast_mem_intGrid hi
  · have hd : 0 < d := lt_of_lt_of_le (by omega) hkd
    have hgap := hostile_allOwner_gap_decomposition_at hi hd hassign
    have hgapCast : (d : ℤ) =
        (allOwnerBucket k d owner i : ℤ) *
          ((globalResidualGroupedLoss k d : ℤ) *
            ((∏ j ∈ (allOwnerGrid k).erase i,
              allOwnerBucket k d owner j : ℕ) : ℤ)) := by
      exact_mod_cast hgap
    push_cast at hgapCast
    rw [hostile_allOwnerIntGrid_opposite_component
      (k := k) (d := d) (i := i) owner]
    simp [allOwnerBucketInt]
    calc
      (d : ℤ) = (allOwnerBucket k d owner i : ℤ) *
          ((globalResidualGroupedLoss k d : ℤ) *
            (∏ j ∈ (allOwnerGrid k).erase i,
              (allOwnerBucket k d owner j : ℤ))) := hgapCast
      _ = (globalResidualGroupedLoss k d : ℤ) *
          (allOwnerBucket k d owner i : ℤ) *
            (∏ j ∈ (allOwnerGrid k).erase i,
              (allOwnerBucket k d owner j : ℤ)) := by ring
  · rw [hostile_allOwnerIntGrid_opposite_component
      (k := k) (d := d) (i := i) owner]
    have hlocal := hostile_allOwner_third_local_lift
      hk5 hkd hi hassign heq
    push_cast at hlocal ⊢
    simpa [allOwnerBucketInt, allOwnerCofactorInt] using hlocal
  · intro z hz
    have hzGrid : z ∈ allOwnerIntGrid k :=
      Finset.mem_of_mem_erase hz
    have hdiff := hostile_allOwnerIntGrid_residual_difference
      hk5 hkd hassign heq (hostile_allOwner_natCast_mem_intGrid hi) hzGrid
    simpa [allOwnerBucketInt, allOwnerCofactorInt] using hdiff

theorem hostile_allOwnerIntGrid_target_range
    {k : ℕ} (hk15 : k ≤ 15) :
    ∀ z ∈ allOwnerIntGrid k, 1 ≤ z ∧ z ≤ 15 := by
  intro z hz
  obtain ⟨i, hi, rfl⟩ := hostile_allOwnerIntGrid_exists_nat hz
  have hi' := Finset.mem_Icc.mp hi
  constructor
  · exact_mod_cast hi'.1
  · exact_mod_cast (le_trans hi'.2 hk15)

theorem hostile_allOwner_localSecondConstant_ne_zero
    {k i : ℕ} (hi : i ∈ allOwnerGrid k) :
    localSecondConstant k i ≠ 0 := by
  rw [localSecondConstant_eq_localBlockCoefficient,
    localBlockCoefficient_eq_sign_mul_nat hi]
  apply mul_ne_zero
  · exact pow_ne_zero _ (by norm_num)
  · exact_mod_cast (by
      unfold localBlockCoefficientNat
      exact mul_ne_zero (Nat.factorial_ne_zero _) (Nat.factorial_ne_zero _))

theorem hostile_allOwnerIntGrid_residual_gt_five_gap
    {k n d : ℕ} {owner : ℕ → ℕ}
    (hk5 : 5 ≤ k)
    (hkd : k ≤ d)
    (hassign : GlobalResidualOwnerAssignment k n d owner)
    (heq : blockProduct k (n + d) = 4 * blockProduct k n) :
    ∀ z ∈ allOwnerIntGrid k,
      5 * d < allOwnerCofactorInt k n d owner z *
        (allOwnerBucketInt k d owner z) ^ 2 := by
  intro z hz
  obtain ⟨i, hi, rfl⟩ := hostile_allOwnerIntGrid_exists_nat hz
  simp only [allOwnerCofactorInt, allOwnerBucketInt]
  simp
  rw [← hostile_allOwner_residual_decomposition (i := i) hassign]
  have hgap := twice_gap_lt_n_of_four_solution hk5 hkd heq
  have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
  unfold localResidual
  omega

theorem hostile_allOwner_second_obstruction_ne_zero
    {k n d i : ℕ} {owner : ℕ → ℕ}
    (hk : k = 5 ∨ k = 7 ∨ k = 9 ∨ k = 11 ∨ k = 13 ∨ k = 15)
    (hdTarget : 10 ^ 120 ≤ d)
    (hi : i ∈ allOwnerGrid k)
    (hassign : GlobalResidualOwnerAssignment k n d owner)
    (heq : blockProduct k (n + d) = 4 * blockProduct k n) :
    multiOwnerSecondObstruction (allOwnerIntGrid k) (i : ℤ)
      (localSecondConstant k i) (localSecondLinear k i)
      (globalResidualGroupedLoss k d : ℤ)
      (fun z => (allOwnerCofactorInt k n d owner z : ℤ)) ≠ 0 := by
  have hk5 : 5 ≤ k := by
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> omega
  have hk15 : k ≤ 15 := by
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> omega
  have hkd : k ≤ d := le_trans hk15 (le_trans (by norm_num) hdTarget)
  have hd : 0 < d := lt_of_lt_of_le (by norm_num) hdTarget
  apply target_multi_owner_second_obstruction_ne_zero
      (a := allOwnerCofactorInt k n d owner)
      (P := allOwnerBucketInt k d owner)
  · exact hostile_allOwner_natCast_mem_intGrid hi
  · rw [hostile_allOwnerIntGrid_card]
    omega
  · rw [hostile_allOwnerIntGrid_card]
    exact hk15
  · exact hostile_allOwnerIntGrid_target_range hk15
  · exact hdTarget
  · exact hostile_allOwnerLoss_pos k d
  · exact hostile_allOwnerIntGrid_gap_decomposition hd hassign
  · exact hostile_allOwnerIntGrid_residual_gt_five_gap hk5 hkd hassign heq
  · exact hostile_allOwner_localSecondConstant_ne_zero hi
  · exact (target_local_taylor_bounds hk hi).2.1

/-- Independently rebuilt certificate constructor. -/
def hostile_allOwnerAssemblyCertificate_of_assignment
    {k n d : ℕ} {owner : ℕ → ℕ}
    (hk : k = 5 ∨ k = 7 ∨ k = 9 ∨ k = 11 ∨ k = 13 ∨ k = 15)
    (hdTarget : 10 ^ 120 ≤ d)
    (hassign : GlobalResidualOwnerAssignment k n d owner)
    (heq : blockProduct k (n + d) = 4 * blockProduct k n) :
    AllOwnerAssemblyCertificate k n d := by
  have hk5 : 5 ≤ k := by
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> omega
  have hk15 : k ≤ 15 := by
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> omega
  have hkd : k ≤ d := le_trans hk15 (le_trans (by norm_num) hdTarget)
  have hd : 0 < d := lt_of_lt_of_le (by norm_num) hdTarget
  refine {
    owner := owner
    assignment := hassign
    exactGap := hostile_allOwner_gap_decomposition hd hassign
    positiveLoss := hostile_allOwnerLoss_pos k d
    boundedLoss := globalResidualGroupedLoss_le_targetAggregateLoss hk
    positiveCofactors := ?_
    exactResiduals := ?_
    residualDifferences := ?_
    secondObstructions := ?_
    thirdObstructions := ?_
    nonzeroSecondObstructions := ?_ }
  · intro i hi
    exact hostile_allOwnerCofactor_pos hassign
      (hostile_allOwner_residual_pos hk5 hkd hi heq)
  · intro i hi
    exact hostile_allOwner_residual_decomposition hassign
  · intro i hi j hj
    exact hostile_allOwner_residual_difference hassign
      (hostile_allOwner_residual_pos hk5 hkd hi heq)
      (hostile_allOwner_residual_pos hk5 hkd hj heq)
  · intro i hi
    exact hostile_allOwner_second_obstruction_dvd hk5 hkd hi hassign heq
  · intro i hi
    exact hostile_allOwner_third_obstruction_dvd_sq hk5 hkd hi hassign heq
  · intro i hi
    exact hostile_allOwner_second_obstruction_ne_zero hk hdTarget hi hassign heq

theorem hostile_exists_allOwnerAssemblyCertificate
    {k n d : ℕ}
    (hk : k = 5 ∨ k = 7 ∨ k = 9 ∨ k = 11 ∨ k = 13 ∨ k = 15)
    (hdTarget : 10 ^ 120 ≤ d)
    (heq : blockProduct k (n + d) = 4 * blockProduct k n) :
    Nonempty (AllOwnerAssemblyCertificate k n d) := by
  have hk5 : 5 ≤ k := by
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> omega
  have hk15 : k ≤ 15 := by
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> omega
  have hkd : k ≤ d := le_trans hk15 (le_trans (by norm_num) hdTarget)
  obtain ⟨owner, hassign⟩ :=
    exists_globalResidualOwnerAssignment hk5 hkd heq
  exact ⟨hostile_allOwnerAssemblyCertificate_of_assignment
    hk hdTarget hassign heq⟩

-- Concrete endpoint, center, empty-grid, and target-bound checks.
example : allOwnerGrid 5 = {1, 2, 3, 4, 5} := by
  decide

example (owner : ℕ → ℕ) : allOwnerBucket 5 1 owner 3 = 1 := by
  simp [allOwnerBucket, globalResidualGroupedLeft,
    globalResidualGroupedLeftFactor]

example : localSecondLinear 5 3 = 0 := by decide
example : localSecondConstant 5 1 ≠ 0 := by decide
example : multiOwnerZeroCoefficientBound < 625 * (10 ^ 120) ^ 2 := by
  norm_num [multiOwnerZeroCoefficientBound]

#check allOwnerBucket_pos
#check allOwnerLoss_pos
#check allOwnerBucket_dvd_factor
#check allOwnerBucket_square_dvd_residual
#check allOwner_residual_decomposition
#check allOwner_one_prime_placement
#check allOwner_bucket_product_eq_clean_product
#check allOwner_gap_decomposition
#check allOwner_gap_decomposition_at
#check allOwner_residual_cast
#check allOwnerCofactor_pos
#check allOwner_residual_difference
#check allOwner_residual_pos
#check allOwner_second_local_lift
#check allOwner_third_local_lift
#check allOwner_natCast_mem_intGrid
#check allOwnerIntGrid_card
#check allOwnerIntGrid_exists_nat
#check allOwnerIntGrid_prod_bucket
#check allOwnerIntGrid_erase_prod_bucket
#check allOwnerIntGrid_opposite_component
#check allOwnerIntGrid_gap_decomposition
#check allOwnerIntGrid_residual_difference
#check allOwner_second_obstruction_dvd
#check allOwner_third_obstruction_dvd_sq
#check allOwnerIntGrid_target_range
#check allOwner_localSecondConstant_ne_zero
#check allOwnerIntGrid_residual_gt_five_gap
#check allOwner_second_obstruction_ne_zero
#check exists_allOwnerAssemblyCertificate

#print axioms hostile_allOwnerBucket_pos
#print axioms hostile_allOwnerLoss_pos
#print axioms hostile_allOwnerBucket_dvd_factor
#print axioms hostile_allOwnerBucket_square_dvd_residual
#print axioms hostile_allOwner_residual_decomposition
#print axioms hostile_allOwner_one_prime_placement
#print axioms hostile_allOwner_bucket_product_eq_clean_product
#print axioms hostile_allOwner_gap_decomposition
#print axioms hostile_allOwner_gap_decomposition_at
#print axioms hostile_allOwner_residual_cast
#print axioms hostile_allOwnerCofactor_pos
#print axioms hostile_allOwner_residual_difference
#print axioms hostile_allOwner_residual_pos
#print axioms hostile_allOwner_second_local_lift
#print axioms hostile_allOwner_third_local_lift
#print axioms hostile_allOwner_natCast_mem_intGrid
#print axioms hostile_allOwnerIntGrid_card
#print axioms hostile_allOwnerIntGrid_exists_nat
#print axioms hostile_allOwnerIntGrid_prod_bucket
#print axioms hostile_allOwnerIntGrid_erase_prod_bucket
#print axioms hostile_allOwnerIntGrid_opposite_component
#print axioms hostile_allOwnerIntGrid_gap_decomposition
#print axioms hostile_allOwnerIntGrid_residual_difference
#print axioms hostile_allOwner_second_obstruction_dvd
#print axioms hostile_allOwner_third_obstruction_dvd_sq
#print axioms hostile_allOwnerIntGrid_target_range
#print axioms hostile_allOwner_localSecondConstant_ne_zero
#print axioms hostile_allOwnerIntGrid_residual_gt_five_gap
#print axioms hostile_allOwner_second_obstruction_ne_zero
#print axioms hostile_allOwnerAssemblyCertificate_of_assignment
#print axioms hostile_exists_allOwnerAssemblyCertificate

end Erdos686Variant
end Erdos686
