/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import ErdosProblems.Erdos686.K5.ExceptionalEquationFacing

/-!
# Erdős 686, k=5: an all-orders 5-adic exceptional obstruction

The characteristic-five cube lift does not, by itself, contradict the
simultaneous fully owned column equations.  This file records one exact
noncrossing placement (`j=2`, `i=2`, owner column `4`) which lifts through
every power of five.

This is deliberately a route obstruction, not an integral solution.  It says
that a contradiction in this exceptional branch must use information beyond
the original equation, the row cube lift, and localization of the fixed
factor five in the column quotient product.
-/

namespace Erdos686
namespace Erdos686Variant

/-- After putting the lower crossing coordinate at `X=5` and imposing the
column-four row target as `125t`, the gap is `D=13-125t`.  The original block
defect is `125` times this polynomial. -/
def k5ExceptionalJ2I2C4LiftPolynomial (t : ℤ) : ℤ :=
  -244140625*t^5 + 185546875*t^4 - 56328125*t^3 +
    8538125*t^2 - 646194*t + 19320

theorem k5_exceptional_j2_i2_c4_lift_polynomial_defect (t : ℤ) :
    k5ExceptionalEquationDefect 5 (13 - 125*t) 2 2 =
      125 * k5ExceptionalJ2I2C4LiftPolynomial t := by
  norm_num [k5ExceptionalEquationDefect, k5ShiftedBlockZ,
    k5ExceptionalJ2I2C4LiftPolynomial]
  ring

/-- The normalized defect has derivative `1` modulo five, uniformly in the
lift parameter.  The stronger exact finite-difference divisibility is the
elementary Hensel input used below. -/
theorem k5_exceptional_j2_i2_c4_lift_difference (t h : ℤ) :
    (5*h : ℤ) ∣
      k5ExceptionalJ2I2C4LiftPolynomial (t+h) -
        k5ExceptionalJ2I2C4LiftPolynomial t - h := by
  refine ⟨-(48828125*h^4 + 244140625*h^3*t - 37109375*h^3 +
      488281250*h^2*t^2 - 148437500*h^2*t + 11265625*h^2 +
      488281250*h*t^3 - 222656250*h*t^2 + 33796875*h*t -
      1707625*h + 244140625*t^4 - 148437500*t^3 +
      33796875*t^2 - 3415250*t + 129239), ?_⟩
  simp only [k5ExceptionalJ2I2C4LiftPolynomial]
  ring

/-- One exact Hensel step.  No completeness theorem for p-adic numbers is
used: the correction is the explicit quotient of the current defect by
`5^r`. -/
theorem k5_exceptional_j2_i2_c4_lift_step
    {r : ℕ} {t : ℤ}
    (ht : ((5 : ℤ) ^ r) ∣ k5ExceptionalJ2I2C4LiftPolynomial t) :
    ∃ t' : ℤ,
      ((5 : ℤ)^r) ∣ t' - t ∧
      ((5 : ℤ)^(r+1)) ∣ k5ExceptionalJ2I2C4LiftPolynomial t' := by
  rcases ht with ⟨q, hq⟩
  let h : ℤ := -((5 : ℤ)^r) * q
  refine ⟨t+h, ?_, ?_⟩
  · refine ⟨-q, ?_⟩
    dsimp [h]
    ring
  · rcases k5_exceptional_j2_i2_c4_lift_difference t h with ⟨a, ha⟩
    refine ⟨-q*a, ?_⟩
    rw [pow_succ]
    have hform : k5ExceptionalJ2I2C4LiftPolynomial (t+h) =
        k5ExceptionalJ2I2C4LiftPolynomial t + h + 5*h*a := by
      linear_combination ha
    rw [hform, hq]
    dsimp [h]
    ring

/-- Product of the eight non-five owner squares in the explicit nine-cell
row-column star below. -/
def k5ExceptionalJ2I2C4CrtModulus : ℤ := 44693900223539808241

/-- A simultaneous CRT solution for the eight non-five square conditions and
for `t = 0 (mod 5)`. -/
def k5ExceptionalJ2I2C4CrtSeed : ℤ := 3150244728706638145

/-- The full nine-cell square fixture.  The crossing owner `7` occurs in both
lists; the other owner bases are `11,13,5,17` in the row and
`19,23,29,31` off the crossing in the column. -/
def K5ExceptionalJ2I2C4SquareFixture (t : ℤ) : Prop :=
  (11:ℤ)^2 ∣ 22-125*t ∧
  (7:ℤ)^2 ∣ 2+125*t ∧
  (13:ℤ)^2 ∣ 49-125*t ∧
  (5:ℤ)^2 ∣ 125*t ∧
  (17:ℤ)^2 ∣ 26-125*t ∧
  (19:ℤ)^2 ∣ 82-125*t ∧
  (7:ℤ)^2 ∣ -2-125*t ∧
  (23:ℤ)^2 ∣ 102-375*t ∧
  (29:ℤ)^2 ∣ -10-125*t ∧
  (31:ℤ)^2 ∣ 146-125*t

/-- Membership in the explicit CRT class implies every row and column owner
square divisibility in the fixture. -/
theorem k5_exceptional_j2_i2_c4_square_fixture_of_crt
    {t : ℤ}
    (ht : k5ExceptionalJ2I2C4CrtModulus ∣
      t - k5ExceptionalJ2I2C4CrtSeed) :
    K5ExceptionalJ2I2C4SquareFixture t := by
  rcases ht with ⟨q, hq⟩
  have htform : t = k5ExceptionalJ2I2C4CrtSeed +
      k5ExceptionalJ2I2C4CrtModulus*q := by
    linear_combination hq
  rw [htform]
  simp only [K5ExceptionalJ2I2C4SquareFixture,
    k5ExceptionalJ2I2C4CrtSeed, k5ExceptionalJ2I2C4CrtModulus]
  constructor
  · exact ⟨-3254385050316774943-46171384528450215125*q, by ring⟩
  constructor
  · exact ⟨8036338593639383023+114015051590662776125*q, by ring⟩
  constructor
  · exact ⟨-2330062669161714604-33057618508535361125*q, by ring⟩
  constructor
  · exact ⟨15751223643533190725+223469501117699041205*q, by ring⟩
  constructor
  · exact ⟨-1362562598921556291-19331271722984346125*q, by ring⟩
  constructor
  · exact ⟨-1090804961463517363-15475727224217385125*q, by ring⟩
  constructor
  · exact ⟨-8036338593639383023-114015051590662776125*q, by ring⟩
  constructor
  · exact ⟨-2233160251918694337-31682821519522548375*q, by ring⟩
  constructor
  · exact ⟨-468229002483150735-6642969712178925125*q, by ring⟩
  · exact ⟨-409761281049250539-5813462568098310125*q, by ring⟩

/-- A Hensel correction which is a multiple of the entire non-five square
modulus.  Since that modulus is `1` modulo five, the correction still raises
the equation accuracy by one power of five. -/
theorem k5_exceptional_j2_i2_c4_lift_step_preserving_crt
    {r : ℕ} {t : ℤ}
    (hcrt : k5ExceptionalJ2I2C4CrtModulus ∣
      t - k5ExceptionalJ2I2C4CrtSeed)
    (ht : ((5 : ℤ) ^ r) ∣ k5ExceptionalJ2I2C4LiftPolynomial t) :
    ∃ t' : ℤ,
      k5ExceptionalJ2I2C4CrtModulus ∣
        t'-k5ExceptionalJ2I2C4CrtSeed ∧
      ((5 : ℤ)^(r+1)) ∣ k5ExceptionalJ2I2C4LiftPolynomial t' := by
  rcases ht with ⟨q, hq⟩
  let h : ℤ := -((5 : ℤ)^r) * k5ExceptionalJ2I2C4CrtModulus*q
  refine ⟨t+h, ?_, ?_⟩
  · have hh : k5ExceptionalJ2I2C4CrtModulus ∣ h := by
      refine ⟨-((5 : ℤ)^r)*q, ?_⟩
      dsimp [h]
      ring
    convert dvd_add hcrt hh using 1 <;> ring
  · rcases k5_exceptional_j2_i2_c4_lift_difference t h with ⟨a, ha⟩
    refine ⟨-8938780044707961648*q-
        k5ExceptionalJ2I2C4CrtModulus*q*a, ?_⟩
    rw [pow_succ]
    have hform : k5ExceptionalJ2I2C4LiftPolynomial (t+h) =
        k5ExceptionalJ2I2C4LiftPolynomial t + h + 5*h*a := by
      linear_combination ha
    rw [hform, hq]
    dsimp [h, k5ExceptionalJ2I2C4CrtModulus]
    ring

/-- The noncrossing cube-lift placement survives modulo every power of five.
The exponent is written as `r+4`: three powers come from the imposed target
and one from the initial normalized root. -/
theorem k5_exceptional_j2_i2_c4_all_five_powers (r : ℕ) :
    ∃ t : ℤ,
      ((5 : ℤ)^(r+4)) ∣
        k5ExceptionalEquationDefect 5 (13 - 125*t) 2 2 := by
  have hnormalized : ∀ s : ℕ, ∃ t : ℤ,
      ((5 : ℤ)^(s+1)) ∣ k5ExceptionalJ2I2C4LiftPolynomial t := by
    intro s
    induction s with
    | zero =>
        refine ⟨0, ?_⟩
        norm_num [k5ExceptionalJ2I2C4LiftPolynomial]
    | succ s ih =>
        rcases ih with ⟨t, ht⟩
        rcases k5_exceptional_j2_i2_c4_lift_step ht with ⟨t', -, ht'⟩
        simpa [Nat.add_assoc] using ⟨t', ht'⟩
  rcases hnormalized r with ⟨t, ht⟩
  refine ⟨t, ?_⟩
  rw [k5_exceptional_j2_i2_c4_lift_polynomial_defect]
  rcases ht with ⟨q, hq⟩
  refine ⟨q, ?_⟩
  rw [hq]
  norm_num [pow_succ]
  ring

/-- Strong route obstruction: all nine nontrivial owner-square congruences
are preserved while the original equation is solved modulo arbitrarily high
powers of five.  Thus neither the row cube lift nor the simultaneous column
square system supplies a finite 5-adic contradiction in this placement. -/
theorem k5_exceptional_j2_i2_c4_full_square_crt_all_five_powers (r : ℕ) :
    ∃ t : ℤ,
      K5ExceptionalJ2I2C4SquareFixture t ∧
      ((5 : ℤ)^(r+4)) ∣
        k5ExceptionalEquationDefect 5 (13-125*t) 2 2 := by
  have hnormalized : ∀ s : ℕ, ∃ t : ℤ,
      k5ExceptionalJ2I2C4CrtModulus ∣
        t-k5ExceptionalJ2I2C4CrtSeed ∧
      ((5 : ℤ)^(s+1)) ∣ k5ExceptionalJ2I2C4LiftPolynomial t := by
    intro s
    induction s with
    | zero =>
        refine ⟨k5ExceptionalJ2I2C4CrtSeed, by simp, ?_⟩
        norm_num [k5ExceptionalJ2I2C4LiftPolynomial,
          k5ExceptionalJ2I2C4CrtSeed]
    | succ s ih =>
        rcases ih with ⟨t, hcrt, ht⟩
        rcases k5_exceptional_j2_i2_c4_lift_step_preserving_crt hcrt ht with
          ⟨t', hcrt', ht'⟩
        simpa [Nat.add_assoc] using ⟨t', hcrt', ht'⟩
  rcases hnormalized r with ⟨t, hcrt, ht⟩
  refine ⟨t, k5_exceptional_j2_i2_c4_square_fixture_of_crt hcrt, ?_⟩
  rw [k5_exceptional_j2_i2_c4_lift_polynomial_defect]
  rcases ht with ⟨q, hq⟩
  refine ⟨q, ?_⟩
  rw [hq]
  norm_num [pow_succ]
  ring

private theorem five_not_dvd_of_add_five_mul
    (a b : ℤ) (ha : ¬ (5 : ℤ) ∣ a) :
    ¬ (5 : ℤ) ∣ a + 5*b := by
  intro h
  apply ha
  simpa only [add_sub_cancel_right] using dvd_sub h (dvd_mul_right 5 b)

/-- Exact local shape of the same family.  The chosen row target is
`125t`; the other four row targets and the fully owned upper coordinate are
5-adic units.  In the column star the row-four target, despite its owner being
a 5-adic unit, carries the fixed factor five.  Thus the column quotient can
absorb that factor without triggering a second owner cube lift. -/
theorem k5_exceptional_j2_i2_c4_local_five_pattern (t : ℤ) :
    3*5 - ((13-125*t) + 4-2) = 125*t ∧
    ¬ (5 : ℤ) ∣ (13-125*t) + 1-2 + 2*5 ∧
    ¬ (5 : ℤ) ∣ 3*5 - ((13-125*t) + 2-2) ∧
    ¬ (5 : ℤ) ∣ (13-125*t) + 3-2 + 7*5 ∧
    ¬ (5 : ℤ) ∣ (13-125*t) + 5-2 + 2*5 ∧
    ¬ (5 : ℤ) ∣ 5 + (13-125*t) ∧
    (5 + (13-125*t) - 4*(5+4-2) = -5*(2+25*t)) := by
  constructor
  · ring
  constructor
  · convert five_not_dvd_of_add_five_mul 22 (-25*t) (by norm_num) using 1 <;>
      ring
  constructor
  · convert five_not_dvd_of_add_five_mul 2 (25*t) (by norm_num) using 1 <;>
      ring
  constructor
  · convert five_not_dvd_of_add_five_mul 49 (-25*t) (by norm_num) using 1 <;>
      ring
  constructor
  · convert five_not_dvd_of_add_five_mul 26 (-25*t) (by norm_num) using 1 <;>
      ring
  constructor
  · convert five_not_dvd_of_add_five_mul 18 (-25*t) (by norm_num) using 1 <;>
      ring
  · ring

#print axioms k5_exceptional_j2_i2_c4_lift_polynomial_defect
#print axioms k5_exceptional_j2_i2_c4_lift_difference
#print axioms k5_exceptional_j2_i2_c4_lift_step
#print axioms k5_exceptional_j2_i2_c4_all_five_powers
#print axioms k5_exceptional_j2_i2_c4_square_fixture_of_crt
#print axioms k5_exceptional_j2_i2_c4_lift_step_preserving_crt
#print axioms k5_exceptional_j2_i2_c4_full_square_crt_all_five_powers
#print axioms k5_exceptional_j2_i2_c4_local_five_pattern

end Erdos686Variant
end Erdos686
