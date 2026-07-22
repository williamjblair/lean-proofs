/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import ErdosProblems.Erdos686.Core.ShortWindowQuotient

/-! Independent importer and kernel audit for the short-window quotient node. -/

namespace Erdos686
namespace Erdos686Variant

-- `k=5`, owner `1`, opposite owners `2,3`.
example :
    threeBucketReducedFourthCoefficient 24 50 35 10 (-1) (-2) =
      5656573440 := by
  norm_num [threeBucketReducedFourthCoefficient]

-- Every odd Taylor coefficient vanishes at the `k=5` center.
example :
    threeBucketReducedFourthCoefficient 4 0 (-5) 0 2 (-2) = 0 := by
  norm_num [threeBucketReducedFourthCoefficient]

#check three_bucket_reduced_fourth_identity
#check square_factor_cancel_from_cube_dvd
#check three_bucket_fourth_to_third_quotient
#check three_bucket_fourth_obstruction_to_quotient
#check three_bucket_reduced_fourth_quotient_dvd
#check three_bucket_fourth_obstruction_reduced_dvd
#check three_bucket_reduced_fourth_coefficient_eq_zero_of_odd_coefficients
#check common_component_third_quotient_dvd_fixed
#check common_component_opposite_cofactor_dvd_offset
#check three_third_quotient_lattice_identity
#check two_zero_third_quotient_gap_square_bound
#check two_zero_third_quotient_gap_lt_cutoff
#check third_quotient_bound_of_short_window

#print axioms three_bucket_reduced_fourth_identity
#print axioms square_factor_cancel_from_cube_dvd
#print axioms three_bucket_fourth_to_third_quotient
#print axioms three_bucket_fourth_obstruction_to_quotient
#print axioms three_bucket_reduced_fourth_quotient_dvd
#print axioms three_bucket_fourth_obstruction_reduced_dvd
#print axioms three_bucket_reduced_fourth_coefficient_eq_zero_of_odd_coefficients
#print axioms common_component_third_quotient_dvd_fixed
#print axioms common_component_opposite_cofactor_dvd_offset
#print axioms three_third_quotient_lattice_identity
#print axioms two_zero_third_quotient_gap_square_bound
#print axioms two_zero_third_quotient_gap_lt_cutoff
#print axioms third_quotient_bound_of_short_window

end Erdos686Variant
end Erdos686
