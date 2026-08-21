/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import ErdosProblems.Erdos730.KummerTransition

/-!
# Erdős 730 Kummer transition: kernel audit

This audit independently specializes mathlib's Kummer theorem, restates the
paper's equation (4) without local abbreviations, and checks the zero and
first carry/no-carry boundary examples in base three.
-/

namespace Erdos730
namespace KummerTransitionAudit

open Finset KummerTransition

/-- Independent specialization of `Nat.factorization_choose'`. -/
theorem centralBinom_kummer_count_audit
    {p t b : ℕ} (hp : p.Prime) (hb : Nat.log p (2 * t) < b) :
    t.centralBinom.factorization p =
      #{i ∈ Finset.Ico 1 b |
        p ^ i ≤ t % p ^ i + t % p ^ i} := by
  simpa only [Nat.centralBinom, two_mul] using
    (Nat.factorization_choose' (n := t) (k := t) hp
      (by simpa [two_mul] using hb))

/-- Equation (4), exposed with the exact digit quantifier appearing in the
paper rather than through `LowerHalfDigits`. -/
theorem equation_four_audit
    {p t : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    ¬p ∣ t.centralBinom ↔
      ∀ d ∈ p.digits t, d ≤ (p - 1) / 2 := by
  exact not_dvd_centralBinom_iff_lowerHalfDigits hp hp2

/-- The empty digit expansion is a boundary member of every `D_p`. -/
theorem zero_lowerHalfDigits_audit (p : ℕ) :
    LowerHalfDigits p 0 := by
  simp [LowerHalfDigits]

/-- Base-three no-carry boundary: `4 = (11)_3`, and `3` is absent from
`B(4)=70`. -/
theorem base_three_noCarry_boundary_audit :
    LowerHalfDigits 3 4 ∧ ¬3 ∣ Nat.centralBinom 4 := by
  norm_num [LowerHalfDigits, Nat.digits, Nat.digitsAux, Nat.digitsAux1,
    Nat.digitsAux0, Nat.centralBinom, Nat.choose]

/-- Base-three carry boundary: `2 = (2)_3`, and `3` divides `B(2)=6`. -/
theorem base_three_carry_boundary_audit :
    ¬LowerHalfDigits 3 2 ∧ 3 ∣ Nat.centralBinom 2 := by
  norm_num [LowerHalfDigits, Nat.digits, Nat.digitsAux, Nat.digitsAux1,
    Nat.digitsAux0, Nat.centralBinom, Nat.choose]

/-- Independent surface audit of equation (8), including the exact
quantifiers and endpoint `(p-1)/2`. -/
theorem equation_eight_audit
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (a m : ℕ) :
    (∀ d ∈ p.digits (p ^ a * m + (p ^ a - 1) / 2),
        d ≤ (p - 1) / 2) ↔
      ∀ d ∈ p.digits m, d ≤ (p - 1) / 2 := by
  exact lowerHalfDigits_mul_pow_add_pow_sub_one_div_two_iff hp hp2 a m

/-- Audit of the forbidden units-digit endpoint used for `n+1` in (6). -/
theorem upper_half_block_exclusion_audit
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (a m : ℕ) :
    p ∣ (p ^ (a + 1) * m + (p ^ (a + 1) + 1) / 2).centralBinom := by
  exact dvd_centralBinom_upperHalfBlock hp hp2 a m

#print axioms centralBinom_kummer_count_audit
#print axioms equation_four_audit
#print axioms zero_lowerHalfDigits_audit
#print axioms base_three_noCarry_boundary_audit
#print axioms base_three_carry_boundary_audit
#print axioms equation_eight_audit
#print axioms upper_half_block_exclusion_audit

end KummerTransitionAudit
end Erdos730
