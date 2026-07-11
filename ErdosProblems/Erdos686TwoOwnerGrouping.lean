/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import ErdosProblems.Erdos686TwoOwnerAggregate

/-!
# Erdős 686: finite grouping of cleaned prime-power owners

This module supplies the finite bookkeeping interface left open by
`Erdos686TwoOwnerAggregate`.  It chooses one global-residual concentration
owner for every prime divisor of the gap and groups retained prime powers
whose nontrivial owners lie in a set of size at most two.

It does not assert that the chosen owner assignment has at most two owners.
That condition remains an explicit hypothesis of the grouping theorem.
-/

namespace Erdos686
namespace Erdos686Variant

open scoped BigOperators

/-- Per-prime owner data supplied by global residual concentration. -/
def GlobalResidualOwnerAssignment
    (k n d : ℕ) (owner : ℕ → ℕ) : Prop :=
  ∀ p ∈ d.primeFactors,
    owner p ∈ Finset.Icc 1 k ∧
      p ^ globalResidualCleanExponent p (d.factorization p) k ∣ n + owner p ∧
      (p ^ globalResidualCleanExponent p (d.factorization p) k) ^ 2 ∣
        localResidual n d (owner p)

/-- The nontrivial cleaned powers in an assignment use at most two owners. -/
def GlobalResidualOwnerRangeAtMostTwo
    (k d : ℕ) (owner : ℕ → ℕ) (i j : ℕ) : Prop :=
  i ∈ Finset.Icc 1 k ∧ j ∈ Finset.Icc 1 k ∧
    ∀ p ∈ d.primeFactors,
      globalResidualCleanExponent p (d.factorization p) k = 0 ∨
        owner p = i ∨ owner p = j

/-- Complementary loss factor for one prime component. -/
def globalResidualGroupedLossFactor (k d p : ℕ) : ℕ :=
  p ^ (d.factorization p -
    globalResidualCleanExponent p (d.factorization p) k)

/-- Retained factor assigned to the first owner. -/
def globalResidualGroupedLeftFactor
    (k d : ℕ) (owner : ℕ → ℕ) (i p : ℕ) : ℕ :=
  if owner p = i then
    p ^ globalResidualCleanExponent p (d.factorization p) k
  else 1

/-- Retained factor assigned to the second owner, with first-owner precedence.
This makes the two grouped products disjoint even when `i=j`. -/
def globalResidualGroupedRightFactor
    (k d : ℕ) (owner : ℕ → ℕ) (i j p : ℕ) : ℕ :=
  if owner p = i then 1
  else if owner p = j then
    p ^ globalResidualCleanExponent p (d.factorization p) k
  else 1

def globalResidualGroupedLoss (k d : ℕ) : ℕ :=
  ∏ p ∈ d.primeFactors, globalResidualGroupedLossFactor k d p

def globalResidualGroupedLeft
    (k d : ℕ) (owner : ℕ → ℕ) (i : ℕ) : ℕ :=
  ∏ p ∈ d.primeFactors, globalResidualGroupedLeftFactor k d owner i p

def globalResidualGroupedRight
    (k d : ℕ) (owner : ℕ → ℕ) (i j : ℕ) : ℕ :=
  ∏ p ∈ d.primeFactors, globalResidualGroupedRightFactor k d owner i j p

private lemma cleanExponent_le_factorization (p k d : ℕ) :
    globalResidualCleanExponent p (d.factorization p) k ≤ d.factorization p := by
  unfold globalResidualCleanExponent
  omega

private lemma exponent_sub_clean_le_loss (p k d : ℕ) :
    d.factorization p - globalResidualCleanExponent p (d.factorization p) k ≤
      globalResidualLossExponent p k := by
  unfold globalResidualCleanExponent
  omega

/-- One prime component is exactly its complementary loss times its retained
power. -/
theorem globalResidualGroupedLossFactor_mul_clean
    (k d p : ℕ) :
    globalResidualGroupedLossFactor k d p *
        p ^ globalResidualCleanExponent p (d.factorization p) k =
      p ^ d.factorization p := by
  unfold globalResidualGroupedLossFactor
  rw [← pow_add]
  congr 1
  exact Nat.sub_add_cancel (cleanExponent_le_factorization p k d)

/-- The exact per-prime cleaning loss divides the six-row aggregate budget. -/
theorem globalResidualGroupedLossFactor_dvd_targetAggregateLoss
    {k d p : ℕ}
    (hk : k = 5 ∨ k = 7 ∨ k = 9 ∨ k = 11 ∨ k = 13 ∨ k = 15)
    (hp : p.Prime) :
    globalResidualGroupedLossFactor k d p ∣ targetAggregateLoss k := by
  have hexp := exponent_sub_clean_le_loss p k d
  have hpow : globalResidualGroupedLossFactor k d p ∣
      p ^ globalResidualLossExponent p k := by
    exact pow_dvd_pow p hexp
  apply dvd_trans hpow
  by_cases hpk : p < k
  · by_cases hp3 : p = 3
    · subst p
      obtain ⟨h5, h7, h9, h11, h13, h15⟩ := globalResidual_three_loss_table
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
        norm_num [targetAggregateLoss, h5, h7, h9, h11, h13, h15]
    · have hk15 : k ≤ 15 := by
        rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      have hlog : Nat.log p (k - 1) < 15 :=
        lt_of_le_of_lt (Nat.log_le_self p (k - 1)) (by omega)
      have hfac := Nat.factorization_factorial hp hlog
      simp only [globalResidualLossExponent, hp3, if_false]
      rw [hfac]
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl
      all_goals interval_cases p <;> norm_num at hp
      all_goals norm_num [targetAggregateLoss, Finset.sum_Ico_succ_top]
  · have hkp : k ≤ p := Nat.le_of_not_gt hpk
    have hp3 : p ≠ 3 := by
      intro hp3
      subst p
      omega
    have hnot : ¬p ∣ (k - 1).factorial := by
      rw [hp.dvd_factorial]
      omega
    have hzero : (k - 1).factorial.factorization p = 0 :=
      Nat.factorization_eq_zero_of_not_dvd hnot
    simp [globalResidualLossExponent, hp3, hzero]

private lemma groupedLossFactor_pairwise_coprime
    {k d p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    (globalResidualGroupedLossFactor k d p).Coprime
      (globalResidualGroupedLossFactor k d q) := by
  unfold globalResidualGroupedLossFactor
  exact Nat.coprime_pow_primes _ _ hp hq hpq

private theorem finset_prod_dvd_of_pairwise_coprime_nat
    {I : Type*} {s : Finset I} {f : I → ℕ} {z : ℕ}
    (hpair : (s : Set I).Pairwise (Function.onFun Nat.Coprime f))
    (hdvd : ∀ x ∈ s, f x ∣ z) :
    ∏ x ∈ s, f x ∣ z := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.prod_insert ha]
      apply Nat.Coprime.mul_dvd_of_dvd_of_dvd
      · apply Nat.Coprime.prod_right
        intro b hb
        exact hpair (by simp) (by simp [hb])
          (Ne.symm (ne_of_mem_of_not_mem hb ha))
      · exact hdvd a (by simp)
      · apply ih
        · intro x hx y hy hxy
          exact hpair (by simp [hx]) (by simp [hy]) hxy
        · intro x hx
          exact hdvd x (by simp [hx])

/-- The product of all exact complementary losses still fits in the row's
aggregate loss budget.  Pairwise coprimality is essential here: multiplying
the individual divisibilities without it would only give a power of the
budget. -/
theorem globalResidualGroupedLoss_le_targetAggregateLoss
    {k d : ℕ}
    (hk : k = 5 ∨ k = 7 ∨ k = 9 ∨ k = 11 ∨ k = 13 ∨ k = 15) :
    globalResidualGroupedLoss k d ≤ targetAggregateLoss k := by
  have hpair : (d.primeFactors : Set ℕ).Pairwise
      (Function.onFun Nat.Coprime (globalResidualGroupedLossFactor k d)) := by
    intro p hp q hq hpq
    exact groupedLossFactor_pairwise_coprime
      (Nat.prime_of_mem_primeFactors hp)
      (Nat.prime_of_mem_primeFactors hq) hpq
  have hdiv : globalResidualGroupedLoss k d ∣ targetAggregateLoss k := by
    unfold globalResidualGroupedLoss
    apply finset_prod_dvd_of_pairwise_coprime_nat hpair
    intro p hp
    exact globalResidualGroupedLossFactor_dvd_targetAggregateLoss hk
      (Nat.prime_of_mem_primeFactors hp)
  apply Nat.le_of_dvd
  · rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
      norm_num [targetAggregateLoss]
  · exact hdiv

private lemma grouped_component_decomposition
    {k d p i j : ℕ} {owner : ℕ → ℕ}
    (hrange : globalResidualCleanExponent p (d.factorization p) k = 0 ∨
      owner p = i ∨ owner p = j) :
    globalResidualGroupedLossFactor k d p *
        globalResidualGroupedLeftFactor k d owner i p *
        globalResidualGroupedRightFactor k d owner i j p =
      p ^ d.factorization p := by
  rcases hrange with ht0 | hpi | hpj
  · simpa [globalResidualGroupedLeftFactor,
      globalResidualGroupedRightFactor, ht0] using
      globalResidualGroupedLossFactor_mul_clean k d p
  · simpa [globalResidualGroupedLeftFactor,
      globalResidualGroupedRightFactor, hpi] using
      globalResidualGroupedLossFactor_mul_clean k d p
  · by_cases hpi : owner p = i
    · simpa [globalResidualGroupedLeftFactor,
        globalResidualGroupedRightFactor, hpi] using
        globalResidualGroupedLossFactor_mul_clean k d p
    · rw [globalResidualGroupedLeftFactor, if_neg hpi,
        globalResidualGroupedRightFactor, if_neg hpi, if_pos hpj]
      simpa using globalResidualGroupedLossFactor_mul_clean k d p

/-- Exact reconstruction of the gap from the loss and the two retained
buckets. -/
theorem globalResidualGrouped_decomposition
    {k d i j : ℕ} {owner : ℕ → ℕ}
    (hd : 0 < d)
    (hrange : GlobalResidualOwnerRangeAtMostTwo k d owner i j) :
    d = globalResidualGroupedLoss k d *
      globalResidualGroupedLeft k d owner i *
      globalResidualGroupedRight k d owner i j := by
  have hfactorization :
      (∏ p ∈ d.primeFactors, p ^ d.factorization p) = d := by
    rw [← Nat.prod_factorization_eq_prod_primeFactors]
    exact Nat.prod_factorization_pow_eq_self (Nat.ne_of_gt hd)
  calc
    d = ∏ p ∈ d.primeFactors, p ^ d.factorization p := hfactorization.symm
    _ = ∏ p ∈ d.primeFactors,
        globalResidualGroupedLossFactor k d p *
          globalResidualGroupedLeftFactor k d owner i p *
          globalResidualGroupedRightFactor k d owner i j p := by
      apply Finset.prod_congr rfl
      intro p hp
      exact (grouped_component_decomposition (hrange.2.2 p hp)).symm
    _ = globalResidualGroupedLoss k d *
        globalResidualGroupedLeft k d owner i *
        globalResidualGroupedRight k d owner i j := by
      rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
      rfl

private lemma groupedLeftFactor_pairwise_coprime
    {k d i p q : ℕ} {owner : ℕ → ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    (globalResidualGroupedLeftFactor k d owner i p).Coprime
      (globalResidualGroupedLeftFactor k d owner i q) := by
  unfold globalResidualGroupedLeftFactor
  by_cases hpi : owner p = i
  · rw [if_pos hpi]
    by_cases hqi : owner q = i
    · rw [if_pos hqi]
      exact Nat.coprime_pow_primes _ _ hp hq hpq
    · simp [hqi]
  · simp [hpi]

private lemma groupedRightFactor_pairwise_coprime
    {k d i j p q : ℕ} {owner : ℕ → ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    (globalResidualGroupedRightFactor k d owner i j p).Coprime
      (globalResidualGroupedRightFactor k d owner i j q) := by
  unfold globalResidualGroupedRightFactor
  by_cases hpi : owner p = i
  · simp [hpi]
  · by_cases hpj : owner p = j
    · rw [if_neg hpi, if_pos hpj]
      by_cases hqi : owner q = i
      · simp [hqi]
      · by_cases hqj : owner q = j
        · rw [if_neg hqi, if_pos hqj]
          exact Nat.coprime_pow_primes _ _ hp hq hpq
        · simp [hqi, hqj]
    · simp [hpi, hpj]

/-- The two retained buckets are coprime, including in the degenerate
`i=j` case because the left bucket has precedence. -/
theorem globalResidualGroupedLeft_coprime_right
    {k d i j : ℕ} {owner : ℕ → ℕ} :
    (globalResidualGroupedLeft k d owner i).Coprime
      (globalResidualGroupedRight k d owner i j) := by
  unfold globalResidualGroupedLeft globalResidualGroupedRight
  apply Nat.Coprime.prod_left
  intro p hp
  apply Nat.Coprime.prod_right
  intro q hq
  unfold globalResidualGroupedLeftFactor globalResidualGroupedRightFactor
  by_cases hpi : owner p = i
  · simp only [if_pos hpi]
    by_cases hqi : owner q = i
    · simp [hqi]
    · simp only [if_neg hqi]
      by_cases hqj : owner q = j
      · simp only [if_pos hqj]
        have hpq : p ≠ q := by
          intro hpq
          subst q
          exact hqi hpi
        exact Nat.coprime_pow_primes _ _
          (Nat.prime_of_mem_primeFactors hp)
          (Nat.prime_of_mem_primeFactors hq) hpq
      · simp [hqj]
  · simp [hpi]

private lemma groupedLeft_factor_dvd
    {k n d i p : ℕ} {owner : ℕ → ℕ}
    (hassign : GlobalResidualOwnerAssignment k n d owner)
    (hp : p ∈ d.primeFactors) :
    globalResidualGroupedLeftFactor k d owner i p ∣ n + i := by
  by_cases hpi : owner p = i
  · simpa [globalResidualGroupedLeftFactor, hpi] using (hassign p hp).2.1
  · simp [globalResidualGroupedLeftFactor, hpi]

private lemma groupedRight_factor_dvd
    {k n d i j p : ℕ} {owner : ℕ → ℕ}
    (hassign : GlobalResidualOwnerAssignment k n d owner)
    (hp : p ∈ d.primeFactors) :
    globalResidualGroupedRightFactor k d owner i j p ∣ n + j := by
  by_cases hpi : owner p = i
  · simp [globalResidualGroupedRightFactor, hpi]
  · by_cases hpj : owner p = j
    · rw [globalResidualGroupedRightFactor, if_neg hpi, if_pos hpj]
      simpa [hpj] using (hassign p hp).2.1
    · simp [globalResidualGroupedRightFactor, hpi, hpj]

private lemma groupedLeft_square_dvd
    {k n d i p : ℕ} {owner : ℕ → ℕ}
    (hassign : GlobalResidualOwnerAssignment k n d owner)
    (hp : p ∈ d.primeFactors) :
    (globalResidualGroupedLeftFactor k d owner i p) ^ 2 ∣
      localResidual n d i := by
  by_cases hpi : owner p = i
  · simpa [globalResidualGroupedLeftFactor, hpi] using (hassign p hp).2.2
  · simp [globalResidualGroupedLeftFactor, hpi]

private lemma groupedRight_square_dvd
    {k n d i j p : ℕ} {owner : ℕ → ℕ}
    (hassign : GlobalResidualOwnerAssignment k n d owner)
    (hp : p ∈ d.primeFactors) :
    (globalResidualGroupedRightFactor k d owner i j p) ^ 2 ∣
      localResidual n d j := by
  by_cases hpi : owner p = i
  · simp [globalResidualGroupedRightFactor, hpi]
  · by_cases hpj : owner p = j
    · rw [globalResidualGroupedRightFactor, if_neg hpi, if_pos hpj]
      simpa [hpj] using (hassign p hp).2.2
    · simp [globalResidualGroupedRightFactor, hpi, hpj]

/-- The first grouped product divides its owner factor. -/
theorem globalResidualGroupedLeft_dvd_factor
    {k n d i : ℕ} {owner : ℕ → ℕ}
    (hassign : GlobalResidualOwnerAssignment k n d owner) :
    globalResidualGroupedLeft k d owner i ∣ n + i := by
  unfold globalResidualGroupedLeft
  apply finset_prod_dvd_of_pairwise_coprime_nat
  · intro p hp q hq hpq
    exact groupedLeftFactor_pairwise_coprime (k := k) (d := d) (i := i)
      (owner := owner)
      (Nat.prime_of_mem_primeFactors hp)
      (Nat.prime_of_mem_primeFactors hq) hpq
  · intro p hp
    exact groupedLeft_factor_dvd (i := i) hassign hp

/-- The second grouped product divides its owner factor. -/
theorem globalResidualGroupedRight_dvd_factor
    {k n d i j : ℕ} {owner : ℕ → ℕ}
    (hassign : GlobalResidualOwnerAssignment k n d owner) :
    globalResidualGroupedRight k d owner i j ∣ n + j := by
  unfold globalResidualGroupedRight
  apply finset_prod_dvd_of_pairwise_coprime_nat
  · intro p hp q hq hpq
    exact groupedRightFactor_pairwise_coprime (k := k) (d := d) (i := i)
      (j := j) (owner := owner)
      (Nat.prime_of_mem_primeFactors hp)
      (Nat.prime_of_mem_primeFactors hq) hpq
  · intro p hp
    exact groupedRight_factor_dvd (i := i) (j := j) hassign hp

/-- The square of the first grouped product divides its local residual. -/
theorem globalResidualGroupedLeft_square_dvd_residual
    {k n d i : ℕ} {owner : ℕ → ℕ}
    (hassign : GlobalResidualOwnerAssignment k n d owner) :
    (globalResidualGroupedLeft k d owner i) ^ 2 ∣ localResidual n d i := by
  unfold globalResidualGroupedLeft
  rw [← Finset.prod_pow]
  apply finset_prod_dvd_of_pairwise_coprime_nat
  · intro p hp q hq hpq
    exact (groupedLeftFactor_pairwise_coprime (k := k) (d := d) (i := i)
      (owner := owner)
      (Nat.prime_of_mem_primeFactors hp)
      (Nat.prime_of_mem_primeFactors hq) hpq).pow 2 2
  · intro p hp
    exact groupedLeft_square_dvd (i := i) hassign hp

/-- The square of the second grouped product divides its local residual. -/
theorem globalResidualGroupedRight_square_dvd_residual
    {k n d i j : ℕ} {owner : ℕ → ℕ}
    (hassign : GlobalResidualOwnerAssignment k n d owner) :
    (globalResidualGroupedRight k d owner i j) ^ 2 ∣ localResidual n d j := by
  unfold globalResidualGroupedRight
  rw [← Finset.prod_pow]
  apply finset_prod_dvd_of_pairwise_coprime_nat
  · intro p hp q hq hpq
    exact (groupedRightFactor_pairwise_coprime (k := k) (d := d) (i := i)
      (j := j) (owner := owner)
      (Nat.prime_of_mem_primeFactors hp)
      (Nat.prime_of_mem_primeFactors hq) hpq).pow 2 2
  · intro p hp
    exact groupedRight_square_dvd (i := i) (j := j) hassign hp

private lemma globalResidualGroupedLoss_pos (k d : ℕ) :
    0 < globalResidualGroupedLoss k d := by
  unfold globalResidualGroupedLoss globalResidualGroupedLossFactor
  apply Finset.prod_pos
  intro p hp
  exact pow_pos (Nat.prime_of_mem_primeFactors hp).pos _

private lemma globalResidualGroupedLeft_pos
    (k d i : ℕ) (owner : ℕ → ℕ) :
    0 < globalResidualGroupedLeft k d owner i := by
  unfold globalResidualGroupedLeft globalResidualGroupedLeftFactor
  apply Finset.prod_pos
  intro p hp
  split
  · exact pow_pos (Nat.prime_of_mem_primeFactors hp).pos _
  · norm_num

private lemma globalResidualGroupedRight_pos
    (k d i j : ℕ) (owner : ℕ → ℕ) :
    0 < globalResidualGroupedRight k d owner i j := by
  unfold globalResidualGroupedRight globalResidualGroupedRightFactor
  apply Finset.prod_pos
  intro p hp
  split
  · norm_num
  · split
    · exact pow_pos (Nat.prime_of_mem_primeFactors hp).pos _
    · norm_num

/-- Finite grouping theorem: an owner assignment whose nontrivial cleaned
components use at most two owner values gives the exact aggregate interface. -/
theorem hasAtMostTwoGlobalResidualOwners_of_assignment
    {k n d i j : ℕ} {owner : ℕ → ℕ}
    (hk : k = 5 ∨ k = 7 ∨ k = 9 ∨ k = 11 ∨ k = 13 ∨ k = 15)
    (hd : 0 < d)
    (hassign : GlobalResidualOwnerAssignment k n d owner)
    (hrange : GlobalResidualOwnerRangeAtMostTwo k d owner i j) :
    HasAtMostTwoGlobalResidualOwners k n d := by
  refine ⟨globalResidualGroupedLoss k d,
    globalResidualGroupedLeft k d owner i,
    globalResidualGroupedRight k d owner i j, i, j, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact globalResidualGrouped_decomposition hd hrange
  · exact globalResidualGroupedLoss_pos k d
  · exact globalResidualGroupedLeft_pos k d i owner
  · exact globalResidualGroupedRight_pos k d i j owner
  · exact globalResidualGroupedLeft_coprime_right
  · exact globalResidualGroupedLoss_le_targetAggregateLoss hk
  · exact hrange.1
  · exact hrange.2.1
  · exact globalResidualGroupedLeft_dvd_factor hassign
  · exact globalResidualGroupedRight_dvd_factor hassign
  · exact globalResidualGroupedLeft_square_dvd_residual hassign
  · exact globalResidualGroupedRight_square_dvd_residual hassign

/-- Global concentration chooses one certified owner for every prime divisor
of a nonzero solution gap. -/
theorem exists_globalResidualOwnerAssignment
    {k n d : ℕ}
    (hk5 : 5 ≤ k)
    (hkd : k ≤ d)
    (heq : blockProduct k (n + d) = 4 * blockProduct k n) :
    ∃ owner : ℕ → ℕ, GlobalResidualOwnerAssignment k n d owner := by
  have hd0 : d ≠ 0 := by omega
  have hlocal : ∀ p : ℕ, ∃ i : ℕ, p ∈ d.primeFactors →
      i ∈ Finset.Icc 1 k ∧
        p ^ globalResidualCleanExponent p (d.factorization p) k ∣ n + i ∧
        (p ^ globalResidualCleanExponent p (d.factorization p) k) ^ 2 ∣
          localResidual n d i := by
    intro p
    by_cases hpmem : p ∈ d.primeFactors
    · have hp : p.Prime := Nat.prime_of_mem_primeFactors hpmem
      have hpd : p ∣ d := (Nat.mem_primeFactors_of_ne_zero hd0).mp hpmem |>.2
      have hepos : 0 < d.factorization p :=
        hp.factorization_pos_of_dvd hd0 hpd
      have hpow : p ^ d.factorization p ∣ d :=
        (hp.pow_dvd_iff_le_factorization hd0).2 le_rfl
      obtain ⟨i, hi, _hdclean, hfactor, hsquare, _hloss⟩ :=
        primePower_component_exists_globalResidual_clean hp hepos hk5 hkd hpow heq
      exact ⟨i, fun _ => ⟨hi, hfactor, by
        simpa [localResidual, globalLocalResidualNat] using hsquare⟩⟩
    · exact ⟨1, fun hp => (hpmem hp).elim⟩
  choose owner howner using hlocal
  exact ⟨owner, fun p hp => howner p hp⟩

/-- Complete cutoff wrapper with the finite range statement left explicit.
This is the exact remaining interface: concentration supplies `owner`, while
proving that its nontrivial range has size at most two is separate. -/
theorem two_owner_range_equation_below_cutoff
    {k n d C A i j : ℕ} {owner : ℕ → ℕ}
    (hk : k = 5 ∨ k = 7 ∨ k = 9 ∨ k = 11 ∨ k = 13 ∨ k = 15)
    (heq : blockProduct k (n + d) = 4 * blockProduct k n)
    (hbase : n + 1 < C * d)
    (hA : A = 3 * C + 2)
    (hA35 : A ≤ 35)
    (hassign : GlobalResidualOwnerAssignment k n d owner)
    (hrange : GlobalResidualOwnerRangeAtMostTwo k d owner i j) :
    d < 10 ^ 120 := by
  have hd : 0 < d := by
    by_contra hnot
    have hd0 : d = 0 := Nat.eq_zero_of_not_pos hnot
    subst d
    norm_num at hbase
  apply atMostTwoGlobalResidualOwners_below_cutoff hk heq hbase hA hA35
  exact hasAtMostTwoGlobalResidualOwners_of_assignment hk hd hassign hrange

/-- A target-size exact solution has a certified concentration assignment
whose nontrivial cleaned owner range cannot be covered by two indices.  This
does not assert that `d` has three distinct prime divisors: components with
zero cleaned exponent are deliberately ignored by the range predicate. -/
theorem exists_globalResidualOwnerAssignment_not_two_cover
    {k n d C A : ℕ}
    (hk : k = 5 ∨ k = 7 ∨ k = 9 ∨ k = 11 ∨ k = 13 ∨ k = 15)
    (heq : blockProduct k (n + d) = 4 * blockProduct k n)
    (hbase : n + 1 < C * d)
    (hA : A = 3 * C + 2)
    (hA35 : A ≤ 35)
    (hlarge : 10 ^ 120 ≤ d) :
    ∃ owner : ℕ → ℕ,
      GlobalResidualOwnerAssignment k n d owner ∧
        ∀ i j : ℕ, ¬GlobalResidualOwnerRangeAtMostTwo k d owner i j := by
  have hk5 : 5 ≤ k := by
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> omega
  have hkd : k ≤ d := by
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
      norm_num at hlarge ⊢ <;> omega
  obtain ⟨owner, hassign⟩ :=
    exists_globalResidualOwnerAssignment hk5 hkd heq
  refine ⟨owner, hassign, ?_⟩
  intro i j hrange
  exact (Nat.not_lt_of_ge hlarge)
    (two_owner_range_equation_below_cutoff hk heq hbase hA hA35
      hassign hrange)

end Erdos686Variant
end Erdos686
