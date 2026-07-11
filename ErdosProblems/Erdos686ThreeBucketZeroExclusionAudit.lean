/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import ErdosProblems.Erdos686ThreeBucketShortCrtLcm
import ErdosProblems.Erdos686GlobalResidualTwoPrime

/-!
Standalone kernel algebra for the hostile audit of the frozen target-row
three-bucket zero-obstruction wrapper.

The producer module is deliberately not imported here: its fresh build fails
before producing an object file.  Consequently none of its seven public
declarations can be validly printed by an importer.  These anonymous examples
check the two intended signed conversions and the exact numeric cutoff against
the already-banked dependencies; the producer build failure and attempted
axiom output are recorded verbatim in the hostile audit report.
-/

namespace Erdos686
namespace Erdos686Variant

example (k owner zeroOwner other : ℕ) (t g : ℤ) :
    localSecondConstant k zeroOwner *
          (3 * (localSecondConstant k owner * t -
            12 * localSecondLinear k owner * g ^ 2 *
              (((owner : ℤ) - (zeroOwner : ℤ)) *
                ((owner : ℤ) - (other : ℤ))))) -
        localSecondConstant k owner *
          (3 * (localSecondConstant k zeroOwner * t -
            12 * localSecondLinear k zeroOwner * g ^ 2 *
              (((zeroOwner : ℤ) - (owner : ℤ)) *
                ((zeroOwner : ℤ) - (other : ℤ))))) =
      36 *
          (localSecondConstant k owner *
                localSecondLinear k zeroOwner *
                (((zeroOwner : ℤ) - (owner : ℤ)) *
                  ((zeroOwner : ℤ) - (other : ℤ))) -
            localSecondLinear k owner *
                (((owner : ℤ) - (zeroOwner : ℤ)) *
                  ((owner : ℤ) - (other : ℤ))) *
                localSecondConstant k zeroOwner) *
        g ^ 2 := by
  ring

example (k zeroOwner owner other : ℕ) (t g d : ℤ)
    (hzero :
      3 * (localSecondConstant k zeroOwner * t -
        12 * localSecondLinear k zeroOwner * g ^ 2 *
          (((zeroOwner : ℤ) - (owner : ℤ)) *
            ((zeroOwner : ℤ) - (other : ℤ)))) = 0) :
    -3 *
          (3 * (localSecondConstant k zeroOwner * t -
            12 * localSecondLinear k zeroOwner * g ^ 2 *
              (((zeroOwner : ℤ) - (owner : ℤ)) *
                ((zeroOwner : ℤ) - (other : ℤ))))) +
        180 * localThirdQuadratic k zeroOwner * g ^ 2 *
          (((zeroOwner : ℤ) - (owner : ℤ)) *
            ((zeroOwner : ℤ) - (other : ℤ))) * d =
      180 * localThirdQuadratic k zeroOwner *
        (((zeroOwner : ℤ) - (owner : ℤ)) *
          ((zeroOwner : ℤ) - (other : ℤ))) * g ^ 2 * d := by
  rw [hzero]
  ring

example :
    (10 ^ 30) ^ 2 * 10 ^ 18 * 18914575680 ^ 4 < 10 ^ 120 := by
  norm_num

example (g P Q R : ℕ) :
    g * P * Q * R = g * Q * R * P ∧
      g * P * Q * R = g * P * R * Q := by
  constructor <;> ring

end Erdos686Variant
end Erdos686

#print axioms Erdos686.Erdos686Variant.localSecondConstant_eq_table
#print axioms Erdos686.Erdos686Variant.localSecondLinear_eq_table
#print axioms Erdos686.Erdos686Variant.localThirdQuadratic_eq_table
#print axioms Erdos686.Erdos686Variant.second_obstruction_cross_dvd_of_other_zero
#print axioms Erdos686.Erdos686Variant.three_bucket_zero_owner_gap_dvd_lcm_power
#print axioms Erdos686.Erdos686Variant.three_bucket_zero_owner_gap_lt_of_lcm_bounds
#print axioms Erdos686.Erdos686Variant.twice_gap_lt_n_of_four_solution
