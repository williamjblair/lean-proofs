/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import ErdosProblems.Erdos686.Core.MultiOwnerExtension
import ErdosProblems.Erdos686.Core.TwoOwnerGrouping

/-!
# Erdős 686: exact assembly of every cleaned residual owner

For a certified global residual owner assignment, this module retains the
original bounded cleaning loss and creates one cleaned bucket at every index
of the full grid `Icc 1 k`.  Empty buckets are literal units.  The prime and
owner products commute exactly, giving

`d = globalResidualGroupedLoss k d * ∏ i ∈ Icc 1 k, P_i`.

Each square-dividing bucket then has an exact natural residual cofactor.  The
resulting step-three residual progression is fed into the arbitrary finite
owner algebra of `Erdos686MultiOwnerExtension`.  The module exposes the
nonzero composed obstructions but does not claim that their remaining
nonzero branch closes the Erdős equation.
-/

namespace Erdos686
namespace Erdos686Variant

open scoped BigOperators

/-- The full natural owner grid. -/
def allOwnerGrid (k : ℕ) : Finset ℕ := Finset.Icc 1 k

/-- The complete cleaned bucket at one grid index. -/
def allOwnerBucket
    (k d : ℕ) (owner : ℕ → ℕ) (i : ℕ) : ℕ :=
  globalResidualGroupedLeft k d owner i

/-- Exact quotient left after removing a cleaned square bucket from its
positive local residual. -/
def allOwnerCofactor
    (k n d : ℕ) (owner : ℕ → ℕ) (i : ℕ) : ℕ :=
  localResidual n d i / (allOwnerBucket k d owner i) ^ 2

/-- Integer copy of the full owner grid used by the finite-family obstruction
interface. -/
def allOwnerIntGrid (k : ℕ) : Finset ℤ :=
  (allOwnerGrid k).image (Int.ofNat : ℕ → ℤ)

/-- Natural bucket family viewed on integer indices.  Only values on
`allOwnerIntGrid` are used. -/
def allOwnerBucketInt
    (k d : ℕ) (owner : ℕ → ℕ) (i : ℤ) : ℕ :=
  allOwnerBucket k d owner i.natAbs

/-- Natural residual cofactor family viewed on integer indices. -/
def allOwnerCofactorInt
    (k n d : ℕ) (owner : ℕ → ℕ) (i : ℤ) : ℕ :=
  allOwnerCofactor k n d owner i.natAbs

/-- Every full-grid bucket is positive, including empty buckets. -/
theorem allOwnerBucket_pos
    (k d i : ℕ) (owner : ℕ → ℕ) :
    0 < allOwnerBucket k d owner i := by
  unfold allOwnerBucket globalResidualGroupedLeft
  apply Finset.prod_pos
  intro p hp
  unfold globalResidualGroupedLeftFactor
  split
  · exact pow_pos (Nat.prime_of_mem_primeFactors hp).pos _
  · norm_num

/-- The unchanged grouped cleaning loss is positive. -/
theorem allOwnerLoss_pos (k d : ℕ) :
    0 < globalResidualGroupedLoss k d := by
  unfold globalResidualGroupedLoss globalResidualGroupedLossFactor
  apply Finset.prod_pos
  intro p hp
  exact pow_pos (Nat.prime_of_mem_primeFactors hp).pos _

/-- Every bucket divides its owner factor. -/
theorem allOwnerBucket_dvd_factor
    {k n d i : ℕ} {owner : ℕ → ℕ}
    (hassign : GlobalResidualOwnerAssignment k n d owner) :
    allOwnerBucket k d owner i ∣ n + i := by
  exact globalResidualGroupedLeft_dvd_factor hassign

/-- Every bucket square divides its local residual. -/
theorem allOwnerBucket_square_dvd_residual
    {k n d i : ℕ} {owner : ℕ → ℕ}
    (hassign : GlobalResidualOwnerAssignment k n d owner) :
    (allOwnerBucket k d owner i) ^ 2 ∣ localResidual n d i := by
  exact globalResidualGroupedLeft_square_dvd_residual hassign

/-- Exact quotient reconstruction at every grid index. -/
theorem allOwner_residual_decomposition
    {k n d i : ℕ} {owner : ℕ → ℕ}
    (hassign : GlobalResidualOwnerAssignment k n d owner) :
    localResidual n d i =
      allOwnerCofactor k n d owner i *
        (allOwnerBucket k d owner i) ^ 2 := by
  unfold allOwnerCofactor
  exact (Nat.div_mul_cancel
    (allOwnerBucket_square_dvd_residual hassign)).symm

/-- A prime's retained clean power appears exactly once in the full grid,
at its certified owner. -/
theorem allOwner_one_prime_placement
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

/-- Commuting the prime and owner products collects precisely every retained
clean prime power. -/
theorem allOwner_bucket_product_eq_clean_product
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
  exact allOwner_one_prime_placement hassign hp

/-- Exact full-grid reconstruction of the original gap with the unchanged
bounded cleaning loss. -/
theorem allOwner_gap_decomposition
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
      rw [allOwner_bucket_product_eq_clean_product hassign]

/-- Exact gap quotient at one bucket, with every other full-grid bucket and
the original loss left visible. -/
theorem allOwner_gap_decomposition_at
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
      allOwner_gap_decomposition hd hassign
    _ = allOwnerBucket k d owner i *
        (globalResidualGroupedLoss k d *
          ∏ j ∈ (allOwnerGrid k).erase i,
            allOwnerBucket k d owner j) := by
      rw [← Finset.mul_prod_erase (allOwnerGrid k)
        (allOwnerBucket k d owner) hi]
      ring

/-- Cast the exact natural residual quotient into its untruncated signed
step-three identity. -/
theorem allOwner_residual_cast
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
  have hdecomp := allOwner_residual_decomposition (i := i) hassign
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

/-- A positive local residual has a positive exact cofactor because every
cleaned bucket is positive. -/
theorem allOwnerCofactor_pos
    {k n d i : ℕ} {owner : ℕ → ℕ}
    (hassign : GlobalResidualOwnerAssignment k n d owner)
    (hpos : 0 < localResidual n d i) :
    0 < allOwnerCofactor k n d owner i := by
  by_contra hnot
  have ha0 : allOwnerCofactor k n d owner i = 0 :=
    Nat.eq_zero_of_not_pos hnot
  have hdecomp := allOwner_residual_decomposition (i := i) hassign
  rw [hdecomp, ha0] at hpos
  simp at hpos

/-- Exact signed difference between any two reconstructed local residuals. -/
theorem allOwner_residual_difference
    {k n d i j : ℕ} {owner : ℕ → ℕ}
    (hassign : GlobalResidualOwnerAssignment k n d owner)
    (hipos : 0 < localResidual n d i)
    (hjpos : 0 < localResidual n d j) :
    (allOwnerCofactor k n d owner i : ℤ) *
          (allOwnerBucket k d owner i : ℤ) ^ 2 -
        (allOwnerCofactor k n d owner j : ℤ) *
          (allOwnerBucket k d owner j : ℤ) ^ 2 =
      3 * ((i : ℤ) - (j : ℤ)) := by
  have hi := allOwner_residual_cast hassign hipos
  have hj := allOwner_residual_cast hassign hjpos
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

/-- The equation-level window makes every full-grid residual positive. -/
theorem allOwner_residual_pos
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

/-- Second local Taylor lift at every full-grid bucket, with the unchanged
loss multiplied by exactly the opposite buckets. -/
theorem allOwner_second_local_lift
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
  have hrespos := allOwner_residual_pos hk5 hkd hi heq
  exact second_order_local_lift hi
    (allOwnerBucket_pos k d i owner)
    (allOwner_gap_decomposition_at hi hd hassign)
    (allOwnerBucket_dvd_factor hassign)
    (allOwner_residual_cast hassign hrespos) heq

/-- Third local Taylor lift at every full-grid bucket, again retaining the
same original loss and every opposite bucket. -/
theorem allOwner_third_local_lift
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
  have hrespos := allOwner_residual_pos hk5 hkd hi heq
  exact third_order_local_lift hi
    (allOwnerBucket_pos k d i owner)
    (allOwner_gap_decomposition_at hi hd hassign)
    (allOwnerBucket_dvd_factor hassign)
    (allOwner_residual_cast hassign hrespos) heq

/-- Natural grid membership embeds into the integer owner grid. -/
theorem allOwner_natCast_mem_intGrid
    {k i : ℕ} (hi : i ∈ allOwnerGrid k) :
    (i : ℤ) ∈ allOwnerIntGrid k := by
  simp [allOwnerIntGrid, hi]

/-- The integer image has exactly the same cardinality as the natural grid. -/
theorem allOwnerIntGrid_card (k : ℕ) :
    (allOwnerIntGrid k).card = k := by
  calc
    (allOwnerIntGrid k).card = (allOwnerGrid k).card := by
      exact Finset.card_image_of_injective _ Int.ofNat_injective
    _ = k := by simp [allOwnerGrid, Nat.card_Icc]

/-- Every integer grid member is the cast of a unique natural row index. -/
theorem allOwnerIntGrid_exists_nat
    {k : ℕ} {z : ℤ} (hz : z ∈ allOwnerIntGrid k) :
    ∃ i ∈ allOwnerGrid k, z = (i : ℤ) := by
  rw [allOwnerIntGrid, Finset.mem_image] at hz
  obtain ⟨i, hi, hiz⟩ := hz
  exact ⟨i, hi, hiz.symm⟩

/-- Products over the integer grid are exactly the corresponding products
over the natural grid. -/
theorem allOwnerIntGrid_prod_bucket
    (k d : ℕ) (owner : ℕ → ℕ) :
    (∏ z ∈ allOwnerIntGrid k, allOwnerBucketInt k d owner z) =
      ∏ i ∈ allOwnerGrid k, allOwnerBucket k d owner i := by
  classical
  unfold allOwnerIntGrid
  rw [Finset.prod_image Int.ofNat_injective.injOn]
  apply Finset.prod_congr rfl
  intro i hi
  simp [allOwnerBucketInt]

/-- Erasing one cast index also commutes with the integer-grid product. -/
theorem allOwnerIntGrid_erase_prod_bucket
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

/-- The generic integer opposite-component product is the cast of the exact
natural erased product. -/
theorem allOwnerIntGrid_opposite_component
    {k d i : ℕ} (owner : ℕ → ℕ) :
    multiOwnerOppositeComponentProduct (allOwnerIntGrid k) (i : ℤ)
        (fun z => (allOwnerBucketInt k d owner z : ℤ)) =
      ((∏ j ∈ (allOwnerGrid k).erase i,
          allOwnerBucket k d owner j : ℕ) : ℤ) := by
  unfold multiOwnerOppositeComponentProduct
  have h := allOwnerIntGrid_erase_prod_bucket
    (k := k) (d := d) (i := i) owner
  have hcast := congrArg (fun q : ℕ => (q : ℤ)) h
  push_cast at hcast
  push_cast
  exact hcast

/-- Exact full gap decomposition on the integer finite-family interface. -/
theorem allOwnerIntGrid_gap_decomposition
    {k n d : ℕ} {owner : ℕ → ℕ}
    (hd : 0 < d)
    (hassign : GlobalResidualOwnerAssignment k n d owner) :
    d = globalResidualGroupedLoss k d *
      ∏ z ∈ allOwnerIntGrid k, allOwnerBucketInt k d owner z := by
  rw [allOwnerIntGrid_prod_bucket]
  exact allOwner_gap_decomposition hd hassign

/-- Exact signed residual difference after mapping the whole grid into the
integer finite-family interface. -/
theorem allOwnerIntGrid_residual_difference
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
  obtain ⟨i, hi, rfl⟩ := allOwnerIntGrid_exists_nat hx
  obtain ⟨j, hj, rfl⟩ := allOwnerIntGrid_exists_nat hy
  simpa [allOwnerCofactorInt, allOwnerBucketInt] using
    allOwner_residual_difference hassign
      (allOwner_residual_pos hk5 hkd hi heq)
      (allOwner_residual_pos hk5 hkd hj heq)

/-- The arbitrary finite-family second obstruction is divisible by every
full-grid bucket.  Empty buckets contribute the tautological divisor one;
the loss remains exactly `globalResidualGroupedLoss`. -/
theorem allOwner_second_obstruction_dvd
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
  · exact allOwner_natCast_mem_intGrid hi
  · rw [allOwnerIntGrid_opposite_component
      (k := k) (d := d) (i := i) owner]
    have hlocal := allOwner_second_local_lift
      hk5 hkd hi hassign heq
    push_cast at hlocal ⊢
    simpa [allOwnerBucketInt, allOwnerCofactorInt] using hlocal
  · intro z hz
    have hzGrid : z ∈ allOwnerIntGrid k :=
      Finset.mem_of_mem_erase hz
    have hdiff := allOwnerIntGrid_residual_difference
      hk5 hkd hassign heq (allOwner_natCast_mem_intGrid hi) hzGrid
    simpa [allOwnerBucketInt, allOwnerCofactorInt] using hdiff

/-- The composed arbitrary-family third obstruction is square-divisible by
every full-grid bucket, still with the unchanged cleaning loss. -/
theorem allOwner_third_obstruction_dvd_sq
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
  · exact allOwner_natCast_mem_intGrid hi
  · have hd : 0 < d := lt_of_lt_of_le (by omega) hkd
    have hgap := allOwner_gap_decomposition_at hi hd hassign
    have hgapCast : (d : ℤ) =
        (allOwnerBucket k d owner i : ℤ) *
          ((globalResidualGroupedLoss k d : ℤ) *
            ((∏ j ∈ (allOwnerGrid k).erase i,
              allOwnerBucket k d owner j : ℕ) : ℤ)) := by
      exact_mod_cast hgap
    push_cast at hgapCast
    rw [allOwnerIntGrid_opposite_component
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
  · rw [allOwnerIntGrid_opposite_component
      (k := k) (d := d) (i := i) owner]
    have hlocal := allOwner_third_local_lift
      hk5 hkd hi hassign heq
    push_cast at hlocal ⊢
    simpa [allOwnerBucketInt, allOwnerCofactorInt] using hlocal
  · intro z hz
    have hzGrid : z ∈ allOwnerIntGrid k :=
      Finset.mem_of_mem_erase hz
    have hdiff := allOwnerIntGrid_residual_difference
      hk5 hkd hassign heq (allOwner_natCast_mem_intGrid hi) hzGrid
    simpa [allOwnerBucketInt, allOwnerCofactorInt] using hdiff

/-- Every integer full-grid index lies in the uniform target interval. -/
theorem allOwnerIntGrid_target_range
    {k : ℕ} (hk15 : k ≤ 15) :
    ∀ z ∈ allOwnerIntGrid k, 1 ≤ z ∧ z ≤ 15 := by
  intro z hz
  obtain ⟨i, hi, rfl⟩ := allOwnerIntGrid_exists_nat hz
  have hi' := Finset.mem_Icc.mp hi
  constructor
  · exact_mod_cast hi'.1
  · exact_mod_cast (le_trans hi'.2 hk15)

/-- The signed constant Taylor coefficient is nonzero at every true grid
index; this is structural and does not depend on the finite target table. -/
theorem allOwner_localSecondConstant_ne_zero
    {k i : ℕ} (hi : i ∈ allOwnerGrid k) :
    localSecondConstant k i ≠ 0 := by
  rw [localSecondConstant_eq_localBlockCoefficient,
    localBlockCoefficient_eq_sign_mul_nat hi]
  apply mul_ne_zero
  · exact pow_ne_zero _ (by norm_num)
  · exact_mod_cast (by
      unfold localBlockCoefficientNat
      exact mul_ne_zero (Nat.factorial_ne_zero _) (Nat.factorial_ne_zero _))

/-- The multiplier-four equation places every reconstructed residual strictly
above `5d`, the lower bound used by the finite-family zero exclusion. -/
theorem allOwnerIntGrid_residual_gt_five_gap
    {k n d : ℕ} {owner : ℕ → ℕ}
    (hk5 : 5 ≤ k)
    (hkd : k ≤ d)
    (hassign : GlobalResidualOwnerAssignment k n d owner)
    (heq : blockProduct k (n + d) = 4 * blockProduct k n) :
    ∀ z ∈ allOwnerIntGrid k,
      5 * d < allOwnerCofactorInt k n d owner z *
        (allOwnerBucketInt k d owner z) ^ 2 := by
  intro z hz
  obtain ⟨i, hi, rfl⟩ := allOwnerIntGrid_exists_nat hz
  simp only [allOwnerCofactorInt, allOwnerBucketInt]
  simp
  rw [← allOwner_residual_decomposition (i := i) hassign]
  have hgap := twice_gap_lt_n_of_four_solution hk5 hkd heq
  have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
  unfold localResidual
  omega

/-- At target scale every composed full-grid second obstruction is nonzero.
This rules out only the zero-obstruction degeneracy; it does not bound the
remaining nonzero obstruction. -/
theorem allOwner_second_obstruction_ne_zero
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
  · exact allOwner_natCast_mem_intGrid hi
  · rw [allOwnerIntGrid_card]
    omega
  · rw [allOwnerIntGrid_card]
    exact hk15
  · exact allOwnerIntGrid_target_range hk15
  · exact hdTarget
  · exact allOwnerLoss_pos k d
  · exact allOwnerIntGrid_gap_decomposition hd hassign
  · exact allOwnerIntGrid_residual_gt_five_gap hk5 hkd hassign heq
  · exact allOwner_localSecondConstant_ne_zero hi
  · exact (target_local_taylor_bounds hk hi).2.1

/-- Auditable target-scale all-owner package.  It records the certified owner
assignment, exact unchanged-loss factorization, exact residual progression,
and every nonzero composed second/third divisibility.  No field asserts a
contradiction or bounds the nonzero obstruction branch. -/
structure AllOwnerAssemblyCertificate (k n d : ℕ) where
  owner : ℕ → ℕ
  assignment : GlobalResidualOwnerAssignment k n d owner
  exactGap : d = globalResidualGroupedLoss k d *
    ∏ i ∈ allOwnerGrid k, allOwnerBucket k d owner i
  positiveLoss : 0 < globalResidualGroupedLoss k d
  boundedLoss : globalResidualGroupedLoss k d ≤ targetAggregateLoss k
  positiveCofactors : ∀ i ∈ allOwnerGrid k,
    0 < allOwnerCofactor k n d owner i
  exactResiduals : ∀ i ∈ allOwnerGrid k,
    localResidual n d i = allOwnerCofactor k n d owner i *
      (allOwnerBucket k d owner i) ^ 2
  residualDifferences : ∀ i ∈ allOwnerGrid k, ∀ j ∈ allOwnerGrid k,
    (allOwnerCofactor k n d owner i : ℤ) *
          (allOwnerBucket k d owner i : ℤ) ^ 2 -
        (allOwnerCofactor k n d owner j : ℤ) *
          (allOwnerBucket k d owner j : ℤ) ^ 2 =
      3 * ((i : ℤ) - (j : ℤ))
  secondObstructions : ∀ i ∈ allOwnerGrid k,
    (allOwnerBucket k d owner i : ℤ) ∣
      multiOwnerSecondObstruction (allOwnerIntGrid k) (i : ℤ)
        (localSecondConstant k i) (localSecondLinear k i)
        (globalResidualGroupedLoss k d : ℤ)
        (fun z => (allOwnerCofactorInt k n d owner z : ℤ))
  thirdObstructions : ∀ i ∈ allOwnerGrid k,
    (allOwnerBucket k d owner i : ℤ) ^ 2 ∣
      multiOwnerThirdObstruction (allOwnerIntGrid k) (i : ℤ)
        (localSecondConstant k i) (localSecondLinear k i)
        (localThirdQuadratic k i)
        (globalResidualGroupedLoss k d : ℤ) (d : ℤ)
        (fun z => (allOwnerCofactorInt k n d owner z : ℤ))
  nonzeroSecondObstructions : ∀ i ∈ allOwnerGrid k,
    multiOwnerSecondObstruction (allOwnerIntGrid k) (i : ℤ)
      (localSecondConstant k i) (localSecondLinear k i)
      (globalResidualGroupedLoss k d : ℤ)
      (fun z => (allOwnerCofactorInt k n d owner z : ℤ)) ≠ 0

/-- Package a supplied certified owner assignment into the complete
target-scale all-owner interface. -/
def allOwnerAssemblyCertificate_of_assignment
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
    exactGap := allOwner_gap_decomposition hd hassign
    positiveLoss := allOwnerLoss_pos k d
    boundedLoss := globalResidualGroupedLoss_le_targetAggregateLoss hk
    positiveCofactors := ?_
    exactResiduals := ?_
    residualDifferences := ?_
    secondObstructions := ?_
    thirdObstructions := ?_
    nonzeroSecondObstructions := ?_ }
  · intro i hi
    exact allOwnerCofactor_pos hassign
      (allOwner_residual_pos hk5 hkd hi heq)
  · intro i hi
    exact allOwner_residual_decomposition hassign
  · intro i hi j hj
    exact allOwner_residual_difference hassign
      (allOwner_residual_pos hk5 hkd hi heq)
      (allOwner_residual_pos hk5 hkd hj heq)
  · intro i hi
    exact allOwner_second_obstruction_dvd hk5 hkd hi hassign heq
  · intro i hi
    exact allOwner_third_obstruction_dvd_sq hk5 hkd hi hassign heq
  · intro i hi
    exact allOwner_second_obstruction_ne_zero hk hdTarget hi hassign heq

/-- Every target-scale solution has a complete all-owner certificate.  This
is a compositional bridge, not a resolution of the remaining nonzero
short-window obstruction. -/
theorem exists_allOwnerAssemblyCertificate
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
  exact ⟨allOwnerAssemblyCertificate_of_assignment
    hk hdTarget hassign heq⟩

#print axioms allOwnerBucket_pos
#print axioms allOwnerLoss_pos
#print axioms allOwnerBucket_dvd_factor
#print axioms allOwnerBucket_square_dvd_residual
#print axioms allOwner_residual_decomposition
#print axioms allOwner_one_prime_placement
#print axioms allOwner_bucket_product_eq_clean_product
#print axioms allOwner_gap_decomposition
#print axioms allOwner_gap_decomposition_at
#print axioms allOwner_residual_cast
#print axioms allOwnerCofactor_pos
#print axioms allOwner_residual_difference
#print axioms allOwner_residual_pos
#print axioms allOwner_second_local_lift
#print axioms allOwner_third_local_lift
#print axioms allOwner_natCast_mem_intGrid
#print axioms allOwnerIntGrid_card
#print axioms allOwnerIntGrid_exists_nat
#print axioms allOwnerIntGrid_prod_bucket
#print axioms allOwnerIntGrid_erase_prod_bucket
#print axioms allOwnerIntGrid_opposite_component
#print axioms allOwnerIntGrid_gap_decomposition
#print axioms allOwnerIntGrid_residual_difference
#print axioms allOwner_second_obstruction_dvd
#print axioms allOwner_third_obstruction_dvd_sq
#print axioms allOwnerIntGrid_target_range
#print axioms allOwner_localSecondConstant_ne_zero
#print axioms allOwnerIntGrid_residual_gt_five_gap
#print axioms allOwner_second_obstruction_ne_zero
#print axioms exists_allOwnerAssemblyCertificate

end Erdos686Variant
end Erdos686
