/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import ErdosProblems.Erdos686.Core.ShortWindowLatticeSign

/-! Independent importer and kernel audit for the lattice-sign size bridge. -/

namespace Erdos686
namespace Erdos686Variant

-- Exact cutoff checks for every reflected open sliver found by the scan.
example : 14 * 86400 ^ 2 * 108 ^ 6 < 10 ^ 120 := by norm_num
example : 17 * 6858432 ^ 2 * 1620 ^ 6 < 10 ^ 120 := by norm_num
example : 23 * 757444608 ^ 2 * 136080 ^ 6 < 10 ^ 120 := by norm_num
example : 26 * 114789312000 ^ 2 * 1224720 ^ 6 < 10 ^ 120 := by norm_num
example : 26 * 4587466752 ^ 2 * 1224720 ^ 6 < 10 ^ 120 := by norm_num
example : 29 * 23117159669760 ^ 2 * 242494560 ^ 6 < 10 ^ 120 := by norm_num
example : 29 * 870772032000 ^ 2 * 242494560 ^ 6 < 10 ^ 120 := by norm_num
example : 35 * 6000400823316480 ^ 2 * 18914575680 ^ 6 < 10 ^ 120 := by norm_num
example : 35 * 211129881108480 ^ 2 * 18914575680 ^ 6 < 10 ^ 120 := by norm_num

-- Exact cutoff checks for the eight closed reflected zero boundaries.
example : 14 * 86400 * 37489271629676544 * 1 * 108 ^ 10 < 10 ^ 120 := by norm_num
example : 17 * 6858432 * 30377147165271015636860928 * 1 * 1620 ^ 10 < 10 ^ 120 := by norm_num
example : 23 * 995328 * 144950283561643585705211385172388216832 * 761 *
    136080 ^ 10 < 10 ^ 120 := by norm_num
example : 26 * 10948608 * 2491164671075202474309932966010553569902592 *
    419 * 1224720 ^ 10 < 10 ^ 120 := by norm_num

#check square_le_of_nonzero_weighted_term
#check two_component_short_window_gap_bound
#check two_component_short_window_gap_lt_cutoff
#check two_weighted_terms_short_window_gap_lt_cutoff
#check reflected_one_sided_short_window_gap_lt_cutoff
#check coprime_square_product_dvd_lcm
#check reflected_boundary_lcm_bound
#check reflected_one_zero_short_window_gap_bound
#check reflected_one_zero_short_window_gap_lt_cutoff

#print axioms square_le_of_nonzero_weighted_term
#print axioms two_component_short_window_gap_bound
#print axioms two_component_short_window_gap_lt_cutoff
#print axioms two_weighted_terms_short_window_gap_lt_cutoff
#print axioms reflected_one_sided_short_window_gap_lt_cutoff
#print axioms coprime_square_product_dvd_lcm
#print axioms reflected_boundary_lcm_bound
#print axioms reflected_one_zero_short_window_gap_bound
#print axioms reflected_one_zero_short_window_gap_lt_cutoff

end Erdos686Variant
end Erdos686
