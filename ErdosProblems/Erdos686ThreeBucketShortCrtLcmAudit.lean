/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import ErdosProblems.Erdos686ThreeBucketShortCrtLcm

/-!
Independent kernel-surface audit for the three-bucket zero-obstruction LCM
filter.  The final print records the already-banked equation-level lower-gap
input used to assess whether the new `abc` thresholds add information.
-/

#print axioms Erdos686.Erdos686Variant.sq_dvd_self_mul_cancel
#print axioms Erdos686.Erdos686Variant.second_obstruction_cross_dvd_of_other_zero
#print axioms Erdos686.Erdos686Variant.pairwise_coprime_three_mul_dvd
#print axioms Erdos686.Erdos686Variant.zero_owner_third_component_dvd
#print axioms Erdos686.Erdos686Variant.three_bucket_zero_owner_gap_dvd_lcm_power
#print axioms Erdos686.Erdos686Variant.three_bucket_zero_owner_gap_lt_of_lcm_bounds
#print axioms Erdos686.Erdos686Variant.three_bucket_zero_owner_global_numeric_cutoff
#print axioms Erdos686.Erdos686Variant.three_bucket_zero_owner_coarse_numeric_cutoff
#print axioms Erdos686.Erdos686Variant.three_bucket_zero_owner_gap_lt_cutoff_of_coarse_coefficients
#print axioms Erdos686.Erdos686Variant.twice_gap_lt_n_of_four_solution
