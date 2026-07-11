/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import ErdosProblems.Erdos686TwoOwnerGrouping

/-!
# Hostile audit: finite two-owner grouping

This audit module does not strengthen the frozen producer theorem.  It checks
the exact boundary behavior of the public grouping definitions and expands
the quantifiers of the final no-two-cover theorem so its scope is explicit.
-/

namespace Erdos686
namespace Erdos686Variant

private theorem hostile_factorization_24_two :
    (24 : ℕ).factorization 2 = 3 := by
  rw [show (24 : ℕ) = (4 : ℕ).factorial by norm_num,
    Nat.factorization_factorial (by norm_num : Nat.Prime 2)
      (show Nat.log 2 4 < 3 by norm_num)]
  norm_num [Finset.sum_Ico_succ_top]

private theorem hostile_factorization_24_three :
    (24 : ℕ).factorization 3 = 1 := by
  rw [show (24 : ℕ) = (4 : ℕ).factorial by norm_num,
    Nat.factorization_factorial (by norm_num : Nat.Prime 3)
      (show Nat.log 3 4 < 2 by norm_num)]
  norm_num [Finset.sum_Ico_succ_top]

private theorem hostile_loss_two_k5 :
    globalResidualLossExponent 2 5 = 2 := by
  norm_num [globalResidualLossExponent, hostile_factorization_24_two]

private theorem hostile_loss_three_k5 :
    globalResidualLossExponent 3 5 = 3 := by
  norm_num [globalResidualLossExponent, hostile_factorization_24_three]

private theorem hostile_loss_seven_k5 :
    globalResidualLossExponent 7 5 = 0 := by
  have hzero : (24 : ℕ).factorization 7 = 0 :=
    Nat.factorization_eq_zero_of_not_dvd (by norm_num)
  norm_num [globalResidualLossExponent, hzero]

private theorem hostile_primeFactors_32 :
    (32 : ℕ).primeFactors = {2} := by
  rw [show (32 : ℕ) = 2 ^ 5 by norm_num]
  exact Nat.primeFactors_prime_pow (by norm_num) (by norm_num)

private theorem hostile_factorization_32_two :
    (32 : ℕ).factorization 2 = 5 := by
  rw [show (32 : ℕ) = 2 ^ 5 by norm_num]
  exact Nat.factorization_pow_self (by norm_num)

private theorem hostile_primeFactors_81 :
    (81 : ℕ).primeFactors = {3} := by
  rw [show (81 : ℕ) = 3 ^ 4 by norm_num]
  exact Nat.primeFactors_prime_pow (by norm_num) (by norm_num)

private theorem hostile_factorization_81_three :
    (81 : ℕ).factorization 3 = 4 := by
  rw [show (81 : ℕ) = 3 ^ 4 by norm_num]
  exact Nat.factorization_pow_self (by norm_num)

/-- Empty prime support contributes three unit products. -/
theorem hostile_grouping_empty_support_boundary :
    globalResidualGroupedLoss 5 1 = 1 ∧
      globalResidualGroupedLeft 5 1 (fun _ => 1) 1 = 1 ∧
      globalResidualGroupedRight 5 1 (fun _ => 1) 1 1 = 1 := by
  norm_num [globalResidualGroupedLoss, globalResidualGroupedLeft,
    globalResidualGroupedRight]

/-- At `k=5`, the cleaned part of `2^5` is `2^3`; first-owner precedence
puts it entirely in the left bucket when the two owner indices coincide. -/
theorem hostile_grouping_two_same_owner_boundary :
    globalResidualGroupedLoss 5 32 = 4 ∧
      globalResidualGroupedLeft 5 32 (fun _ => 3) 3 = 8 ∧
      globalResidualGroupedRight 5 32 (fun _ => 3) 3 3 = 1 := by
  simp [globalResidualGroupedLoss, globalResidualGroupedLeft,
    globalResidualGroupedRight, globalResidualGroupedLossFactor,
    globalResidualGroupedLeftFactor, globalResidualGroupedRightFactor,
    globalResidualCleanExponent, hostile_loss_two_k5,
    hostile_primeFactors_32, hostile_factorization_32_two]

/-- The special `p=3` cleaning rule loses `3^3` at `k=5` and retains one
power of three from `3^4`. -/
theorem hostile_grouping_three_boundary :
    globalResidualGroupedLoss 5 81 = 27 ∧
      globalResidualGroupedLeft 5 81 (fun _ => 2) 2 = 3 ∧
      globalResidualGroupedRight 5 81 (fun _ => 2) 2 4 = 1 := by
  simp [globalResidualGroupedLoss, globalResidualGroupedLeft,
    globalResidualGroupedRight, globalResidualGroupedLossFactor,
    globalResidualGroupedLeftFactor, globalResidualGroupedRightFactor,
    globalResidualCleanExponent, hostile_loss_three_k5,
    hostile_primeFactors_81, hostile_factorization_81_three]

/-- A completely cleaned component may have an owner outside the proposed
two-value cover because it contributes the unit retained power. -/
theorem hostile_grouping_zero_clean_outside_owner_boundary :
    GlobalResidualOwnerRangeAtMostTwo 5 3 (fun _ => 3) 1 2 := by
  have hp : Nat.Prime 3 := by norm_num
  simp [GlobalResidualOwnerRangeAtMostTwo,
    globalResidualCleanExponent, hostile_loss_three_k5,
    Nat.Prime.primeFactors hp, Nat.Prime.factorization_self hp]

/-- A prime at least `k` has zero loss, so its nontrivial owner cannot be
ignored by the two-value range predicate. -/
theorem hostile_grouping_large_prime_outside_owner_rejected :
    ¬ GlobalResidualOwnerRangeAtMostTwo 5 7 (fun _ => 3) 1 2 := by
  have hp : Nat.Prime 7 := by norm_num
  simp [GlobalResidualOwnerRangeAtMostTwo,
    globalResidualCleanExponent, hostile_loss_seven_k5,
    Nat.Prime.primeFactors hp, Nat.Prime.factorization_self hp]

/-- Quantifier-expanded form of the final producer theorem.  The existential
chooses one assignment; the following universal no-cover statement refers to
that same assignment and not to every possible assignment. -/
theorem hostile_exists_certified_assignment_not_two_cover_expanded
    {k n d C A : ℕ}
    (hk : k = 5 ∨ k = 7 ∨ k = 9 ∨ k = 11 ∨ k = 13 ∨ k = 15)
    (heq : blockProduct k (n + d) = 4 * blockProduct k n)
    (hbase : n + 1 < C * d)
    (hA : A = 3 * C + 2)
    (hA35 : A ≤ 35)
    (hlarge : 10 ^ 120 ≤ d) :
    ∃ owner : ℕ → ℕ,
      (∀ p ∈ d.primeFactors,
        owner p ∈ Finset.Icc 1 k ∧
          p ^ globalResidualCleanExponent p (d.factorization p) k ∣ n + owner p ∧
          (p ^ globalResidualCleanExponent p (d.factorization p) k) ^ 2 ∣
            localResidual n d (owner p)) ∧
      ∀ i j : ℕ,
        ¬(i ∈ Finset.Icc 1 k ∧ j ∈ Finset.Icc 1 k ∧
          ∀ p ∈ d.primeFactors,
            globalResidualCleanExponent p (d.factorization p) k = 0 ∨
              owner p = i ∨ owner p = j) := by
  simpa [GlobalResidualOwnerAssignment,
    GlobalResidualOwnerRangeAtMostTwo] using
    (exists_globalResidualOwnerAssignment_not_two_cover hk heq hbase hA hA35 hlarge)
/-! Fresh public-surface and kernel-axiom audit commands. -/
#check globalResidualGroupedLossFactor_mul_clean
#check globalResidualGroupedLossFactor_dvd_targetAggregateLoss
#check globalResidualGroupedLoss_le_targetAggregateLoss
#check globalResidualGrouped_decomposition
#check globalResidualGroupedLeft_coprime_right
#check globalResidualGroupedLeft_dvd_factor
#check globalResidualGroupedRight_dvd_factor
#check globalResidualGroupedLeft_square_dvd_residual
#check globalResidualGroupedRight_square_dvd_residual
#check hasAtMostTwoGlobalResidualOwners_of_assignment
#check exists_globalResidualOwnerAssignment
#check two_owner_range_equation_below_cutoff
#check exists_globalResidualOwnerAssignment_not_two_cover

#print globalResidualGroupedLossFactor_mul_clean
#print globalResidualGroupedLossFactor_dvd_targetAggregateLoss
#print globalResidualGroupedLoss_le_targetAggregateLoss
#print globalResidualGrouped_decomposition
#print globalResidualGroupedLeft_coprime_right
#print globalResidualGroupedLeft_dvd_factor
#print globalResidualGroupedRight_dvd_factor
#print globalResidualGroupedLeft_square_dvd_residual
#print globalResidualGroupedRight_square_dvd_residual
#print hasAtMostTwoGlobalResidualOwners_of_assignment
#print exists_globalResidualOwnerAssignment
#print two_owner_range_equation_below_cutoff
#print exists_globalResidualOwnerAssignment_not_two_cover

#print axioms globalResidualGroupedLossFactor_mul_clean
#print axioms globalResidualGroupedLossFactor_dvd_targetAggregateLoss
#print axioms globalResidualGroupedLoss_le_targetAggregateLoss
#print axioms globalResidualGrouped_decomposition
#print axioms globalResidualGroupedLeft_coprime_right
#print axioms globalResidualGroupedLeft_dvd_factor
#print axioms globalResidualGroupedRight_dvd_factor
#print axioms globalResidualGroupedLeft_square_dvd_residual
#print axioms globalResidualGroupedRight_square_dvd_residual
#print axioms hasAtMostTwoGlobalResidualOwners_of_assignment
#print axioms exists_globalResidualOwnerAssignment
#print axioms two_owner_range_equation_below_cutoff
#print axioms exists_globalResidualOwnerAssignment_not_two_cover


end Erdos686Variant
end Erdos686
