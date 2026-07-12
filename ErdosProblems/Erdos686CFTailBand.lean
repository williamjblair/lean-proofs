/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import ErdosProblems.Erdos686CFTailBandCheck15

/-!
# Erdős 686: kernel certificate for the odd gap band below `10^1000`

The six generated Stern–Brocot trees extend the existing checked interval
from `d < 10^120` to `d < 10^1000`.  The headline theorem at the end closes
the new part of the nominal Target 1 tail for all six odd rows.  It does not
close gaps `d ≥ 10^1000`.
-/

namespace Erdos686

namespace Erdos686Variant

theorem no_gap_solution_four_five_below_e1000 {n d : ℕ}
    (hd : 221 ≤ d) (hB : d < 10 ^ 1000) :
    blockProduct 5 (n + d) ≠ 4 * blockProduct 5 n := by
  intro heq
  obtain ⟨hup, hlo⟩ := ratio_window_four_nat heq
  have h3d : 3 * d ≤ n + 1 := row_base_lower_k5 hd hup
  have h4d : n + 1 < 4 * d := row_base_upper_k5 hlo
  have hsol : K5CenteredEq (n + d + 3) (n + 3) := k5_centered_of_eq heq
  have hYlo : 665 ≤ n + 3 := by omega
  have hYmax : n + 3 ≤ 4 * 10 ^ 1000 := by
    generalize hP : (10 : ℕ) ^ 1000 = P at hB ⊢
    omega
  have hbr := k5_bracket_upper hsol hYlo
  have hlow : (n + 3) * 1 + 1 ≤ (n + d + 3) * 1 := by omega
  have hhigh : (n + d + 3) * 3 + 1 ≤ (n + 3) * 4 := by omega
  exact fareyCheck_sound (fun X Y h => k5EqRefuted_sound X Y h)
    (fun X Y hS h1 _h2 => k5_thue_window hS h1) hsol hYlo hYmax (by omega)
    CFTail1000.k5FareyCert 1 1 4 3 (by norm_num) k5FareyCert1000_check hlow hhigh

theorem no_gap_solution_four_seven_below_e1000 {n d : ℕ}
    (hd : 221 ≤ d) (hB : d < 10 ^ 1000) :
    blockProduct 7 (n + d) ≠ 4 * blockProduct 7 n := by
  intro heq
  obtain ⟨hup, hlo⟩ := ratio_window_four_nat heq
  have h4d : 4 * d ≤ n + 1 := row_base_lower_k7 hd hup
  have h5d : n + 1 < 5 * d := row_base_upper_k7 hlo
  have hn : 883 ≤ n := by omega
  have hsol : K7CenteredEq (n + d + 4) (n + 4) := k7_centered_of_eq heq
  have hbl := k7_scaled_lower hn hlo
  have hbu := k7_scaled_upper hn hup
  have hYlo : 887 ≤ n + 4 := by omega
  have hYmax : n + 4 ≤ 5 * 10 ^ 1000 := by
    generalize hP : (10 : ℕ) ^ 1000 = P at hB ⊢
    omega
  have hlow : (n + 4) * 1 + 1 ≤ (n + d + 4) * 1 := by omega
  have hhigh : (n + d + 4) * 4 + 1 ≤ (n + 4) * 5 := by omega
  exact fareyCheck_sound
    (Sol := fun X Y => K7CenteredEq X Y ∧
      121826 * Y < 100000 * X ∧ 100000 * X < 121977 * Y)
    (fun X Y h hS => k7EqRefuted_sound X Y h hS.1)
    (fun X Y hS h1 _h2 => k7_thue_window hS.1 hS.2.1 hS.2.2 h1)
    ⟨hsol, hbl, hbu⟩ hYlo hYmax (by omega)
    CFTail1000.k7FareyCert 1 1 5 4 (by norm_num) k7FareyCert1000_check hlow hhigh

theorem no_gap_solution_four_nine_below_e1000 {n d : ℕ}
    (hd : 221 ≤ d) (hB : d < 10 ^ 1000) :
    blockProduct 9 (n + d) ≠ 4 * blockProduct 9 n := by
  intro heq
  obtain ⟨hup, hlo⟩ := ratio_window_four_nat heq
  have hqd : 5 * d ≤ n + 1 := row_base_lower_k9 hd hup
  have hqd' : n + 1 < 7 * d := row_base_upper_k9 hlo
  have hn : 1104 ≤ n := by omega
  have hsol : K9CenteredEq (n + d + 5) (n + 5) := k9_centered_of_eq heq
  have hbl := k9_scaled_lower hn hlo
  have hbu := k9_scaled_upper hn hup
  have hYlo : 1109 ≤ n + 5 := by omega
  have hYmax : n + 5 ≤ 7 * 10 ^ 1000 := by
    generalize hP : (10 : ℕ) ^ 1000 = P at hB ⊢
    omega
  have hlow : (n + 5) * 1 + 1 ≤ (n + d + 5) * 1 := by omega
  have hhigh : (n + d + 5) * 5 + 1 ≤ (n + 5) * 6 := by omega
  exact fareyCheck_sound
    (Sol := fun X Y => K9CenteredEq X Y ∧
      116591 * Y < 100000 * X ∧ 100000 * X < 116714 * Y)
    (fun X Y h hS => k9EqRefuted_sound X Y h hS.1)
    (fun X Y hS h1 _h2 => k9_thue_window hS.1 hS.2.1 hS.2.2 h1)
    ⟨hsol, hbl, hbu⟩ hYlo hYmax (by omega)
    CFTail1000.k9FareyCert 1 1 6 5 (by norm_num) k9FareyCert1000_check hlow hhigh

theorem no_gap_solution_four_eleven_below_e1000 {n d : ℕ}
    (hd : 221 ≤ d) (hB : d < 10 ^ 1000) :
    blockProduct 11 (n + d) ≠ 4 * blockProduct 11 n := by
  intro heq
  obtain ⟨hup, hlo⟩ := ratio_window_four_nat heq
  have hqd : 7 * d ≤ n + 1 := row_base_lower_k11 hd hup
  have hqd' : n + 1 < 8 * d := row_base_upper_k11 hlo
  have hn : 1546 ≤ n := by omega
  have hsol : K11CenteredEq (n + d + 6) (n + 6) := k11_centered_of_eq heq
  have hbl := k11_scaled_lower hn hlo
  have hbu := k11_scaled_upper hn hup
  have hYlo : 1552 ≤ n + 6 := by omega
  have hYmax : n + 6 ≤ 8 * 10 ^ 1000 := by
    generalize hP : (10 : ℕ) ^ 1000 = P at hB ⊢
    omega
  have hlow : (n + 6) * 1 + 1 ≤ (n + d + 6) * 1 := by omega
  have hhigh : (n + d + 6) * 7 + 1 ≤ (n + 6) * 8 := by omega
  exact fareyCheck_sound
    (Sol := fun X Y => K11CenteredEq X Y ∧
      113387 * Y < 100000 * X ∧ 100000 * X < 113476 * Y)
    (fun X Y h hS => k11EqRefuted_sound X Y h hS.1)
    (fun X Y hS h1 _h2 => k11_thue_window hS.1 hS.2.1 hS.2.2 h1)
    ⟨hsol, hbl, hbu⟩ hYlo hYmax (by omega)
    CFTail1000.k11FareyCert 1 1 8 7 (by norm_num) k11FareyCert1000_check hlow hhigh

theorem no_gap_solution_four_thirteen_below_e1000 {n d : ℕ}
    (hd : 221 ≤ d) (hB : d < 10 ^ 1000) :
    blockProduct 13 (n + d) ≠ 4 * blockProduct 13 n := by
  intro heq
  obtain ⟨hup, hlo⟩ := ratio_window_four_nat heq
  have hqd : 8 * d ≤ n + 1 := row_base_lower_k13 hd hup
  have hqd' : n + 1 < 9 * d := row_base_upper_k13 hlo
  have hn : 1767 ≤ n := by omega
  have hsol : K13CenteredEq (n + d + 7) (n + 7) := k13_centered_of_eq heq
  have hbl := k13_scaled_lower hn hlo
  have hbu := k13_scaled_upper hn hup
  have hYlo : 1774 ≤ n + 7 := by omega
  have hYmax : n + 7 ≤ 9 * 10 ^ 1000 := by
    generalize hP : (10 : ℕ) ^ 1000 = P at hB ⊢
    omega
  have hlow : (n + 7) * 1 + 1 ≤ (n + d + 7) * 1 := by omega
  have hhigh : (n + d + 7) * 7 + 1 ≤ (n + 7) * 8 := by omega
  exact fareyCheck_sound
    (Sol := fun X Y => K13CenteredEq X Y ∧
      111214 * Y < 100000 * X ∧ 100000 * X < 111293 * Y)
    (fun X Y h hS => k13EqRefuted_sound X Y h hS.1)
    (fun X Y hS h1 _h2 => k13_thue_window hS.1 hS.2.1 hS.2.2 h1)
    ⟨hsol, hbl, hbu⟩ hYlo hYmax (by omega)
    CFTail1000.k13FareyCert 1 1 8 7 (by norm_num) k13FareyCert1000_check hlow hhigh

theorem no_gap_solution_four_fifteen_below_e1000 {n d : ℕ}
    (hd : 221 ≤ d) (hB : d < 10 ^ 1000) :
    blockProduct 15 (n + d) ≠ 4 * blockProduct 15 n := by
  intro heq
  obtain ⟨hup, hlo⟩ := ratio_window_four_nat heq
  have hqd : 10 * d ≤ n + 1 := row_base_lower_k15 hd hup
  have hqd' : n + 1 < 11 * d := row_base_upper_k15 hlo
  have hn : 2209 ≤ n := by omega
  have hsol : K15CenteredEq (n + d + 8) (n + 8) := k15_centered_of_eq heq
  have hbl := k15_scaled_lower hn hlo
  have hbu := k15_scaled_upper hn hup
  have hYlo : 2217 ≤ n + 8 := by omega
  have hYmax : n + 8 ≤ 11 * 10 ^ 1000 := by
    generalize hP : (10 : ℕ) ^ 1000 = P at hB ⊢
    omega
  have hlow : (n + 8) * 1 + 1 ≤ (n + d + 8) * 1 := by omega
  have hhigh : (n + d + 8) * 10 + 1 ≤ (n + 8) * 11 := by omega
  exact fareyCheck_sound
    (Sol := fun X Y => K15CenteredEq X Y ∧
      109651 * Y < 100000 * X ∧ 100000 * X < 109714 * Y)
    (fun X Y h hS => k15EqRefuted_sound X Y h hS.1)
    (fun X Y hS h1 _h2 => k15_thue_window hS.1 hS.2.1 hS.2.2 h1)
    ⟨hsol, hbl, hbu⟩ hYlo hYmax (by omega)
    CFTail1000.k15FareyCert 1 1 11 10 (by norm_num) k15FareyCert1000_check hlow hhigh

/-- Fully kernel-checked exclusion of the newly opened finite part of all six
odd tails. -/
theorem no_odd_target_gap_solution_below_e1000
    {k n d : ℕ} (hk : k ∈ ({5, 7, 9, 11, 13, 15} : Finset ℕ))
    (hd : 10 ^ 120 ≤ d) (hB : d < 10 ^ 1000) :
    blockProduct k (n + d) ≠ 4 * blockProduct k n := by
  have hd221 : 221 ≤ d := by
    have : (221 : ℕ) ≤ 10 ^ 120 := by norm_num
    omega
  simp only [Finset.mem_insert, Finset.mem_singleton] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl
  · exact no_gap_solution_four_five_below_e1000 hd221 hB
  · exact no_gap_solution_four_seven_below_e1000 hd221 hB
  · exact no_gap_solution_four_nine_below_e1000 hd221 hB
  · exact no_gap_solution_four_eleven_below_e1000 hd221 hB
  · exact no_gap_solution_four_thirteen_below_e1000 hd221 hB
  · exact no_gap_solution_four_fifteen_below_e1000 hd221 hB

#print axioms k5FareyCert1000_check
#print axioms k7FareyCert1000_check
#print axioms k9FareyCert1000_check
#print axioms k11FareyCert1000_check
#print axioms k13FareyCert1000_check
#print axioms k15FareyCert1000_check
#print axioms no_odd_target_gap_solution_below_e1000

end Erdos686Variant

end Erdos686
