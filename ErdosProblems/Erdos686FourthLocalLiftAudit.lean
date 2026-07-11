/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import ErdosProblems.Erdos686FourthLocalLift

/-!
# Hostile kernel audit for the fourth local lift

The private identities below independently replay the denominator clearing,
the product of the two square-residual differences, and the coefficient
`6804 = 84 * 9^2`.  The final four prints expose the complete public theorem
surface of the producer module to the axiom gate.
-/

namespace Erdos686
namespace Erdos686Variant

private theorem audit_denominator_clearing_identity
    {H M A C D E F X : ℤ}
    (hrelation : 3 * X - M = A * H) :
    27 *
          (-C * A + D * ((X + M) ^ 2 - 4 * X ^ 2) +
            H * E * ((X + M) ^ 3 - 4 * X ^ 3) +
            H ^ 2 * F * ((X + M) ^ 4 - 4 * X ^ 4)) -
        (3 * (-3 * (3 * C * A - 4 * D * M ^ 2) +
              20 * E * H * M ^ 3) +
          H ^ 2 * (-9 * D * A ^ 2 + 36 * E * A * M ^ 2 +
            84 * F * M ^ 4)) =
      H ^ 3 *
        (80 * A * F * M ^ 3 +
          H * (-3 * A ^ 3 * E + 24 * A ^ 2 * F * M ^ 2) -
          A ^ 4 * F * H ^ 3) := by
  have hM : M = 3 * X - A * H := by linarith
  rw [hM]
  ring

private theorem audit_two_square_product
    {P Q R a b c deltaLeft deltaRight : ℤ}
    (hleft : a * P ^ 2 - b * Q ^ 2 = 3 * deltaLeft)
    (hright : a * P ^ 2 - c * R ^ 2 = 3 * deltaRight) :
    (b * Q ^ 2) * (c * R ^ 2) =
      a ^ 2 * P ^ 4 - 3 * a * P ^ 2 * (deltaLeft + deltaRight) +
        9 * deltaLeft * deltaRight := by
  have hB : b * Q ^ 2 = a * P ^ 2 - 3 * deltaLeft := by linarith
  have hC : c * R ^ 2 = a * P ^ 2 - 3 * deltaRight := by linarith
  rw [hB, hC]
  ring

private theorem audit_cubic_composition_coefficient
    (F g deltaLeft deltaRight : ℤ) :
    84 * F * g ^ 4 * (9 * deltaLeft * deltaRight) ^ 2 =
      6804 * F * g ^ 4 * (deltaLeft * deltaRight) ^ 2 := by
  ring

#check localOffsetCofactor_fourth_order
#check fourth_order_local_algebra
#check fourth_order_local_lift
#check three_bucket_fourth_obstruction_dvd_cube

#print axioms localOffsetCofactor_fourth_order
#print axioms fourth_order_local_algebra
#print axioms fourth_order_local_lift
#print axioms three_bucket_fourth_obstruction_dvd_cube

end Erdos686Variant
end Erdos686
