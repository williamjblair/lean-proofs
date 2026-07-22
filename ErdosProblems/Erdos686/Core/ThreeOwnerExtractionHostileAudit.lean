/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import ErdosProblems.Erdos686.Core.ThreeOwnerExtraction

/-!
# Hostile audit: Erdős 686 three-owner extraction

This audit module reconstructs the finite no-two-cover implication over an
abstract support, projects every mathematical field of the frozen witness,
and restates the exact equation-level theorem surface.  It deliberately does
not modify or strengthen the producer.
-/

namespace Erdos686
namespace Erdos686Variant

/-- Abstract reconstruction of the only combinatorial inference in the
producer.  A nonempty value type is represented by the explicit `anchor`.
No finiteness assumption on the value type is needed. -/
theorem hostile_three_live_values_of_no_two_cover
    {α β : Type*} {support : Finset α}
    {live : α → Prop} {value : α → β}
    (anchor : β)
    (hnocover : ∀ i j : β,
      ¬ ∀ x ∈ support, live x → value x = i ∨ value x = j) :
    ∃ p ∈ support, ∃ q ∈ support, ∃ r ∈ support,
      live p ∧ live q ∧ live r ∧
        value p ≠ value q ∧ value p ≠ value r ∧ value q ≠ value r := by
  classical
  have hexP : ∃ p ∈ support, live p := by
    by_contra hnone
    have hallDead : ∀ p ∈ support, ¬live p := by
      intro p hp
      by_contra hpLive
      exact hnone ⟨p, hp, hpLive⟩
    exact hnocover anchor anchor (by
      intro p hp hpLive
      exact (hallDead p hp hpLive).elim)
  obtain ⟨p, hpMem, hpLive⟩ := hexP
  have hexQ : ∃ q ∈ support, live q ∧ value q ≠ value p := by
    by_contra hnone
    have hallP : ∀ q ∈ support, live q → value q = value p := by
      intro q hq hqLive
      by_contra hqNe
      exact hnone ⟨q, hq, hqLive, hqNe⟩
    exact hnocover (value p) (value p) (by
      intro q hq hqLive
      exact Or.inl (hallP q hq hqLive))
  obtain ⟨q, hqMem, hqLive, hqNeP⟩ := hexQ
  have hexR : ∃ r ∈ support,
      live r ∧ value r ≠ value p ∧ value r ≠ value q := by
    by_contra hnone
    have hcovered : ∀ r ∈ support, live r →
        value r = value p ∨ value r = value q := by
      intro r hr hrLive
      by_cases hrp : value r = value p
      · exact Or.inl hrp
      · right
        by_contra hrq
        exact hnone ⟨r, hr, hrLive, hrp, hrq⟩
    exact hnocover (value p) (value q) hcovered
  obtain ⟨r, hrMem, hrLive, hrNeP, hrNeQ⟩ := hexR
  exact ⟨p, hpMem, q, hqMem, r, hrMem,
    hpLive, hqLive, hrLive, hqNeP.symm, hrNeP.symm, hrNeQ.symm⟩

/-- The frozen structure contains all and only the advertised mathematical
payload.  In particular, this projection says nothing about every other
prime factor or owner value. -/
theorem hostile_three_owner_witness_projects_all_fields
    {k n d : ℕ} {owner : ℕ → ℕ}
    (w : ThreeGlobalResidualOwnerWitness k n d owner) :
    w.p ∈ d.primeFactors ∧
    w.q ∈ d.primeFactors ∧
    w.r ∈ d.primeFactors ∧
    globalResidualCleanExponent w.p (d.factorization w.p) k ≠ 0 ∧
    globalResidualCleanExponent w.q (d.factorization w.q) k ≠ 0 ∧
    globalResidualCleanExponent w.r (d.factorization w.r) k ≠ 0 ∧
    owner w.p ∈ Finset.Icc 1 k ∧
    owner w.q ∈ Finset.Icc 1 k ∧
    owner w.r ∈ Finset.Icc 1 k ∧
    owner w.p ≠ owner w.q ∧
    owner w.p ≠ owner w.r ∧
    owner w.q ≠ owner w.r ∧
    w.p ^ globalResidualCleanExponent w.p (d.factorization w.p) k ∣
      n + owner w.p ∧
    w.q ^ globalResidualCleanExponent w.q (d.factorization w.q) k ∣
      n + owner w.q ∧
    w.r ^ globalResidualCleanExponent w.r (d.factorization w.r) k ∣
      n + owner w.r ∧
    (w.p ^ globalResidualCleanExponent w.p (d.factorization w.p) k) ^ 2 ∣
      localResidual n d (owner w.p) ∧
    (w.q ^ globalResidualCleanExponent w.q (d.factorization w.q) k) ^ 2 ∣
      localResidual n d (owner w.q) ∧
    (w.r ^ globalResidualCleanExponent w.r (d.factorization w.r) k) ^ 2 ∣
      localResidual n d (owner w.r) ∧
    (w.p ^ globalResidualCleanExponent w.p (d.factorization w.p) k).Coprime
      (w.q ^ globalResidualCleanExponent w.q (d.factorization w.q) k) ∧
    (w.p ^ globalResidualCleanExponent w.p (d.factorization w.p) k).Coprime
      (w.r ^ globalResidualCleanExponent w.r (d.factorization w.r) k) ∧
    (w.q ^ globalResidualCleanExponent w.q (d.factorization w.q) k).Coprime
      (w.r ^ globalResidualCleanExponent w.r (d.factorization w.r) k) := by
  exact ⟨w.hpMem, w.hqMem, w.hrMem,
    w.hpClean, w.hqClean, w.hrClean,
    w.hpOwner, w.hqOwner, w.hrOwner,
    w.hpqOwner, w.hprOwner, w.hqrOwner,
    w.hpFactor, w.hqFactor, w.hrFactor,
    w.hpSquare, w.hqSquare, w.hrSquare,
    w.hpqCoprime, w.hprCoprime, w.hqrCoprime⟩

/-- Pairwise-distinct owner values force the underlying prime-factor
witnesses themselves to be pairwise distinct. -/
theorem hostile_three_owner_witness_primes_pairwise_distinct
    {k n d : ℕ} {owner : ℕ → ℕ}
    (w : ThreeGlobalResidualOwnerWitness k n d owner) :
    w.p ≠ w.q ∧ w.p ≠ w.r ∧ w.q ≠ w.r := by
  exact ⟨
    fun hpq => w.hpqOwner (congrArg owner hpq),
    fun hpr => w.hprOwner (congrArg owner hpr),
    fun hqr => w.hqrOwner (congrArg owner hqr)⟩

/-- Exact restatement of the equation-level producer theorem.  The result is
existential in one assignment and `Nonempty` in one three-witness type. -/
theorem hostile_target_size_wrapper_exact_surface
    {k n d C A : ℕ}
    (hk : k = 5 ∨ k = 7 ∨ k = 9 ∨ k = 11 ∨ k = 13 ∨ k = 15)
    (heq : blockProduct k (n + d) = 4 * blockProduct k n)
    (hbase : n + 1 < C * d)
    (hA : A = 3 * C + 2)
    (hA35 : A ≤ 35)
    (hlarge : 10 ^ 120 ≤ d) :
    ∃ owner : ℕ → ℕ,
      GlobalResidualOwnerAssignment k n d owner ∧
        Nonempty (ThreeGlobalResidualOwnerWitness k n d owner) :=
  exists_threeGlobalResidualOwnerWitness_of_target_size_solution
    hk heq hbase hA hA35 hlarge

/-- A four-value finite model has no two-value cover. -/
theorem hostile_four_values_have_no_two_cover :
    ∀ i j : Fin 4, ¬ ∀ x : Fin 4, x = i ∨ x = j := by
  decide

/-- The same model is not covered by any three values.  Therefore extraction
of three witnesses cannot be read as an exactly-three-owner conclusion. -/
theorem hostile_four_values_not_covered_by_any_three :
    ∀ i j l : Fin 4, ¬ ∀ x : Fin 4, x = i ∨ x = j ∨ x = l := by
  decide

#check ThreeGlobalResidualOwnerWitness
#check ThreeGlobalResidualOwnerWitness.p
#check ThreeGlobalResidualOwnerWitness.q
#check ThreeGlobalResidualOwnerWitness.r
#check ThreeGlobalResidualOwnerWitness.hpMem
#check ThreeGlobalResidualOwnerWitness.hqMem
#check ThreeGlobalResidualOwnerWitness.hrMem
#check ThreeGlobalResidualOwnerWitness.hpClean
#check ThreeGlobalResidualOwnerWitness.hqClean
#check ThreeGlobalResidualOwnerWitness.hrClean
#check ThreeGlobalResidualOwnerWitness.hpOwner
#check ThreeGlobalResidualOwnerWitness.hqOwner
#check ThreeGlobalResidualOwnerWitness.hrOwner
#check ThreeGlobalResidualOwnerWitness.hpqOwner
#check ThreeGlobalResidualOwnerWitness.hprOwner
#check ThreeGlobalResidualOwnerWitness.hqrOwner
#check ThreeGlobalResidualOwnerWitness.hpFactor
#check ThreeGlobalResidualOwnerWitness.hqFactor
#check ThreeGlobalResidualOwnerWitness.hrFactor
#check ThreeGlobalResidualOwnerWitness.hpSquare
#check ThreeGlobalResidualOwnerWitness.hqSquare
#check ThreeGlobalResidualOwnerWitness.hrSquare
#check ThreeGlobalResidualOwnerWitness.hpqCoprime
#check ThreeGlobalResidualOwnerWitness.hprCoprime
#check ThreeGlobalResidualOwnerWitness.hqrCoprime
#check threeGlobalResidualOwnerWitness_of_not_two_cover
#check exists_threeGlobalResidualOwnerWitness_of_target_size_solution

#print ThreeGlobalResidualOwnerWitness
#print threeGlobalResidualOwnerWitness_of_not_two_cover
#print exists_threeGlobalResidualOwnerWitness_of_target_size_solution

#print axioms threeGlobalResidualOwnerWitness_of_not_two_cover
#print axioms exists_threeGlobalResidualOwnerWitness_of_target_size_solution
#print axioms hostile_three_live_values_of_no_two_cover
#print axioms hostile_three_owner_witness_projects_all_fields
#print axioms hostile_three_owner_witness_primes_pairwise_distinct
#print axioms hostile_target_size_wrapper_exact_surface
#print axioms hostile_four_values_have_no_two_cover
#print axioms hostile_four_values_not_covered_by_any_three

end Erdos686Variant
end Erdos686
