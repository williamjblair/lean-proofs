/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import ErdosProblems.Erdos686TwoOwnerGrouping

/-!
# Erdős 686: extract three explicit cleaned owners

The finite grouping theorem returns one certified assignment whose nonzero
cleaned owner range has no two-index cover.  This module converts that
negative cover statement into three explicit prime-power witnesses with
pairwise-distinct owners.  It is a bookkeeping bridge only; it does not
assert that these are the only nonzero owner buckets.
-/

namespace Erdos686
namespace Erdos686Variant

/-- Three explicit nontrivial cleaned prime powers at pairwise-distinct
owners, together with the factor, square-residual, and coprimality data needed
by later Diophantine arguments. -/
structure ThreeGlobalResidualOwnerWitness
    (k n d : ℕ) (owner : ℕ → ℕ) where
  p : ℕ
  q : ℕ
  r : ℕ
  hpMem : p ∈ d.primeFactors
  hqMem : q ∈ d.primeFactors
  hrMem : r ∈ d.primeFactors
  hpClean : globalResidualCleanExponent p (d.factorization p) k ≠ 0
  hqClean : globalResidualCleanExponent q (d.factorization q) k ≠ 0
  hrClean : globalResidualCleanExponent r (d.factorization r) k ≠ 0
  hpOwner : owner p ∈ Finset.Icc 1 k
  hqOwner : owner q ∈ Finset.Icc 1 k
  hrOwner : owner r ∈ Finset.Icc 1 k
  hpqOwner : owner p ≠ owner q
  hprOwner : owner p ≠ owner r
  hqrOwner : owner q ≠ owner r
  hpFactor : p ^ globalResidualCleanExponent p (d.factorization p) k ∣
    n + owner p
  hqFactor : q ^ globalResidualCleanExponent q (d.factorization q) k ∣
    n + owner q
  hrFactor : r ^ globalResidualCleanExponent r (d.factorization r) k ∣
    n + owner r
  hpSquare : (p ^ globalResidualCleanExponent p (d.factorization p) k) ^ 2 ∣
    localResidual n d (owner p)
  hqSquare : (q ^ globalResidualCleanExponent q (d.factorization q) k) ^ 2 ∣
    localResidual n d (owner q)
  hrSquare : (r ^ globalResidualCleanExponent r (d.factorization r) k) ^ 2 ∣
    localResidual n d (owner r)
  hpqCoprime :
    (p ^ globalResidualCleanExponent p (d.factorization p) k).Coprime
      (q ^ globalResidualCleanExponent q (d.factorization q) k)
  hprCoprime :
    (p ^ globalResidualCleanExponent p (d.factorization p) k).Coprime
      (r ^ globalResidualCleanExponent r (d.factorization r) k)
  hqrCoprime :
    (q ^ globalResidualCleanExponent q (d.factorization q) k).Coprime
      (r ^ globalResidualCleanExponent r (d.factorization r) k)

/-- A certified assignment with no two-index cover contains three explicit
nonzero cleaned components at distinct owners. -/
theorem threeGlobalResidualOwnerWitness_of_not_two_cover
    {k n d : ℕ} {owner : ℕ → ℕ}
    (hk : 1 ≤ k)
    (hassign : GlobalResidualOwnerAssignment k n d owner)
    (hnocover : ∀ i j : ℕ,
      ¬GlobalResidualOwnerRangeAtMostTwo k d owner i j) :
    Nonempty (ThreeGlobalResidualOwnerWitness k n d owner) := by
  have hone : 1 ∈ Finset.Icc 1 k := by
    simp [Finset.mem_Icc, hk]
  have hexP : ∃ p : ℕ, p ∈ d.primeFactors ∧
      globalResidualCleanExponent p (d.factorization p) k ≠ 0 := by
    by_contra hnone
    have hallZero : ∀ p ∈ d.primeFactors,
        globalResidualCleanExponent p (d.factorization p) k = 0 := by
      intro p hp
      by_contra hne
      exact hnone ⟨p, hp, hne⟩
    exact hnocover 1 1 ⟨hone, hone, fun p hp => Or.inl (hallZero p hp)⟩
  obtain ⟨p, hpMem, hpClean⟩ := hexP
  have hpOwner := (hassign p hpMem).1
  have hexQ : ∃ q : ℕ, q ∈ d.primeFactors ∧
      globalResidualCleanExponent q (d.factorization q) k ≠ 0 ∧
      owner q ≠ owner p := by
    by_contra hnone
    have hcovered : ∀ q ∈ d.primeFactors,
        globalResidualCleanExponent q (d.factorization q) k = 0 ∨
          owner q = owner p := by
      intro q hq
      by_cases hqClean :
          globalResidualCleanExponent q (d.factorization q) k = 0
      · exact Or.inl hqClean
      · right
        by_contra hqOwner
        exact hnone ⟨q, hq, hqClean, hqOwner⟩
    exact hnocover (owner p) (owner p)
      ⟨hpOwner, hpOwner, fun q hq =>
        (hcovered q hq).imp_right Or.inl⟩
  obtain ⟨q, hqMem, hqClean, hqpOwner⟩ := hexQ
  have hqOwner := (hassign q hqMem).1
  have hexR : ∃ r : ℕ, r ∈ d.primeFactors ∧
      globalResidualCleanExponent r (d.factorization r) k ≠ 0 ∧
      owner r ≠ owner p ∧ owner r ≠ owner q := by
    by_contra hnone
    have hcovered : ∀ r ∈ d.primeFactors,
        globalResidualCleanExponent r (d.factorization r) k = 0 ∨
          owner r = owner p ∨ owner r = owner q := by
      intro r hr
      by_cases hrClean :
          globalResidualCleanExponent r (d.factorization r) k = 0
      · exact Or.inl hrClean
      · right
        by_cases hrp : owner r = owner p
        · exact Or.inl hrp
        · right
          by_contra hrq
          exact hnone ⟨r, hr, hrClean, hrp, hrq⟩
    exact hnocover (owner p) (owner q) ⟨hpOwner, hqOwner, hcovered⟩
  obtain ⟨r, hrMem, hrClean, hrpOwner, hrqOwner⟩ := hexR
  have hrOwner := (hassign r hrMem).1
  have hpq : p ≠ q := by
    intro hpq
    subst q
    exact hqpOwner rfl
  have hpr : p ≠ r := by
    intro hpr
    subst r
    exact hrpOwner rfl
  have hqr : q ≠ r := by
    intro hqr
    subst r
    exact hrqOwner rfl
  have hpPrime := Nat.prime_of_mem_primeFactors hpMem
  have hqPrime := Nat.prime_of_mem_primeFactors hqMem
  have hrPrime := Nat.prime_of_mem_primeFactors hrMem
  exact ⟨{
    p := p
    q := q
    r := r
    hpMem := hpMem
    hqMem := hqMem
    hrMem := hrMem
    hpClean := hpClean
    hqClean := hqClean
    hrClean := hrClean
    hpOwner := hpOwner
    hqOwner := hqOwner
    hrOwner := hrOwner
    hpqOwner := hqpOwner.symm
    hprOwner := hrpOwner.symm
    hqrOwner := hrqOwner.symm
    hpFactor := (hassign p hpMem).2.1
    hqFactor := (hassign q hqMem).2.1
    hrFactor := (hassign r hrMem).2.1
    hpSquare := (hassign p hpMem).2.2
    hqSquare := (hassign q hqMem).2.2
    hrSquare := (hassign r hrMem).2.2
    hpqCoprime := Nat.coprime_pow_primes _ _ hpPrime hqPrime hpq
    hprCoprime := Nat.coprime_pow_primes _ _ hpPrime hrPrime hpr
    hqrCoprime := Nat.coprime_pow_primes _ _ hqPrime hrPrime hqr
  }⟩

/-- Equation-level composition: every target-size odd-row solution supplies
one certified assignment and three explicit distinct nonzero cleaned owners
inside that same assignment. -/
theorem exists_threeGlobalResidualOwnerWitness_of_target_size_solution
    {k n d C A : ℕ}
    (hk : k = 5 ∨ k = 7 ∨ k = 9 ∨ k = 11 ∨ k = 13 ∨ k = 15)
    (heq : blockProduct k (n + d) = 4 * blockProduct k n)
    (hbase : n + 1 < C * d)
    (hA : A = 3 * C + 2)
    (hA35 : A ≤ 35)
    (hlarge : 10 ^ 120 ≤ d) :
    ∃ owner : ℕ → ℕ,
      GlobalResidualOwnerAssignment k n d owner ∧
        Nonempty (ThreeGlobalResidualOwnerWitness k n d owner) := by
  obtain ⟨owner, hassign, hnocover⟩ :=
    exists_globalResidualOwnerAssignment_not_two_cover
      hk heq hbase hA hA35 hlarge
  have hk1 : 1 ≤ k := by
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> omega
  exact ⟨owner, hassign,
    threeGlobalResidualOwnerWitness_of_not_two_cover hk1 hassign hnocover⟩

#print axioms threeGlobalResidualOwnerWitness_of_not_two_cover
#print axioms exists_threeGlobalResidualOwnerWitness_of_target_size_solution

end Erdos686Variant
end Erdos686
