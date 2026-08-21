/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import ErdosProblems.Erdos730.ConsecutiveTransition

/-!
# Erdős 730 consecutive transition: kernel audit

This audit exposes Proposition 1 and its event-coverage corollary with every
quantifier expanded, so the audit surface does not hide the meaning of
`p^a ∥ N` or either cofactor condition behind a local abbreviation.  It also
checks the smallest simultaneous drop/entry boundary, `n=2`.
-/

namespace Erdos730
namespace ConsecutiveTransitionAudit

open KummerTransition ConsecutiveTransition

/-- Independent recurrence-facing audit: outside `n+1` and `2n+1`, an odd
prime has unchanged central-binomial support status. -/
theorem away_prime_stability_audit
    {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hsucc : ¬p ∣ n + 1) (htwo : ¬p ∣ 2 * n + 1) :
    p ∣ n.centralBinom ↔ p ∣ (n + 1).centralBinom := by
  exact (dvd_centralBinom_succ_iff_of_away hp hp2 hsucc htwo).symm

/-- Proposition 1 with equations (5) and (6) expanded literally. -/
theorem proposition_one_expanded_audit
    {n : ℕ} (hn : 0 < n) :
    n.centralBinom.primeFactors = (n + 1).centralBinom.primeFactors ↔
      ((∀ {p : ℕ}, p.Prime → p ≠ 2 → ∀ {a c : ℕ},
          (0 < a ∧ n + 1 = p ^ a * c ∧ ¬p ∣ c) →
            ¬LowerHalfDigits p c) ∧
       (∀ {p : ℕ}, p.Prime → p ≠ 2 → ∀ {a c : ℕ},
          (0 < a ∧ 2 * n + 1 = p ^ a * c ∧ ¬p ∣ c) →
            ¬LowerHalfDigits p ((c - 1) / 2))) := by
  simpa [TransitionConditions, DropCondition, EntryCondition,
    ExactPrimePowerCofactor] using
    (consecutive_primeFactors_eq_iff_transitionConditions hn)

/-- `Bad ⊆ E`, again with all event fields expanded. -/
theorem event_coverage_expanded_audit
    {n : ℕ} (hn : 0 < n)
    (hbad : n.centralBinom.primeFactors ≠
      (n + 1).centralBinom.primeFactors) :
    (∃ p a c,
      p.Prime ∧ p ≠ 2 ∧ 0 < a ∧
      n + 1 = p ^ a * c ∧ ¬p ∣ c ∧
      LowerHalfDigits p c) ∨
    (∃ p a c,
      p.Prime ∧ p ≠ 2 ∧ 0 < a ∧
      2 * n + 1 = p ^ a * c ∧ ¬p ∣ c ∧
      LowerHalfDigits p ((c - 1) / 2)) := by
  simpa [DropObstruction, EntryObstruction,
    ExactPrimePowerCofactor, and_assoc] using
    (exists_obstruction_of_primeFactors_ne hn hbad)

/-- Smallest nontrivial drop boundary: at `n=2`, `3^1 ∥ n+1` and its
cofactor `1` belongs to `D_3`. -/
theorem n_two_drop_boundary_audit : DropObstruction 2 3 1 1 := by
  norm_num [DropObstruction, ExactPrimePowerCofactor, LowerHalfDigits,
    Nat.digits, Nat.digitsAux, Nat.digitsAux1, Nat.digitsAux0]

/-- Smallest nontrivial entry boundary: at `n=2`, `5^1 ∥ 2n+1` and the
tested cofactor `(1-1)/2=0` belongs to `D_5`. -/
theorem n_two_entry_boundary_audit : EntryObstruction 2 5 1 1 := by
  norm_num [EntryObstruction, ExactPrimePowerCofactor, LowerHalfDigits,
    Nat.digits, Nat.digitsAux, Nat.digitsAux1, Nat.digitsAux0]

/-- Direct finite check that the two boundary obstructions really accompany
unequal supports: `B(2)=6` and `B(3)=20`. -/
theorem n_two_primeFactors_ne_audit :
    (Nat.centralBinom 2).primeFactors ≠
      (Nat.centralBinom 3).primeFactors := by
  have hB2 : Nat.centralBinom 2 = 6 := by
    norm_num [Nat.centralBinom, Nat.choose]
  have hB3 : Nat.centralBinom 3 = 20 := by
    norm_num [Nat.centralBinom, Nat.choose]
  intro heq
  have hmem : 3 ∈ (Nat.centralBinom 2).primeFactors := by
    rw [hB2, Nat.mem_primeFactors]
    norm_num
  have hnotmem : 3 ∉ (Nat.centralBinom 3).primeFactors := by
    rw [hB3, Nat.mem_primeFactors]
    norm_num
  rw [heq] at hmem
  exact hnotmem hmem

#print axioms away_prime_stability_audit
#print axioms proposition_one_expanded_audit
#print axioms event_coverage_expanded_audit
#print axioms n_two_drop_boundary_audit
#print axioms n_two_entry_boundary_audit
#print axioms n_two_primeFactors_ne_audit

end ConsecutiveTransitionAudit
end Erdos730
