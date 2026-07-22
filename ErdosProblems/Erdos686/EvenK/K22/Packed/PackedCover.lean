import ErdosProblems.Erdos686.EvenK.K22.Packed.PackedShards

import ErdosProblems.Erdos686.EvenK.K22.Core

namespace Erdos686.Erdos686Variant

private theorem even22_mod46_classes : ∀ r : Fin 46,
    even22A23 (-(33 * (r.val : ZMod 23))) = true → Odd r.val →
      r.val = 17 ∨ r.val = 21 ∨ r.val = 25 ∨ r.val = 29 := by decide

/-- The packed prime-field certificate excludes every positive odd
candidate in the exact d>=250 Runge window. -/
theorem even22_packed_candidate_impossible
    {w v : ℤ} {t : ℕ}
    (hS : evenTable22S w = 4 * evenTable22S v)
    (hm : -(33 * (t : ℤ)) = evenTable22T w - 2 * evenTable22T v)
    (htodd : Odd t) (htpos : 1 ≤ t) (htbound : t ≤ 3795146531) : False := by
  have hA23z := even22_allowed_int even22A23 even22_allowed_23 hS hm
  have hA23 : even22A23 (-(33 * (t : ZMod 23))) = true := by
    simpa using hA23z
  let q := t / 46
  let r := t % 46
  have hrlt : r < 46 := by dsimp [r]; exact Nat.mod_lt _ (by norm_num)
  let fr : Fin 46 := ⟨r, hrlt⟩
  have hdecomp : 46 * q + r = t := by
    dsimp [q, r]
    omega
  have hcast : (t : ZMod 23) = (r : ZMod 23) := by
    rw [← hdecomp]
    push_cast
    have h46 : (46 : ZMod 23) = 0 := by decide
    simp [h46]
  have hAr : even22A23 (-(33 * (fr.val : ZMod 23))) = true := by
    dsimp [fr]
    rw [← hcast]
    exact hA23
  have hrodd : Odd fr.val := by
    rw [Nat.odd_iff] at htodd ⊢
    dsimp [fr, r]
    have hdiv : 2 ∣ 46 := by norm_num
    rw [Nat.mod_mod_of_dvd _ hdiv]
    exact htodd
  rcases even22_mod46_classes fr hAr hrodd with h17 | h21 | h25 | h29
  · have ht : t = 46 * q + 17 := by dsimp [q, r, fr] at *; omega
    rw [ht] at hm htbound
    by_cases h0 : q < 16000000
    · exact even22_packed_b17_s0_no_centers (by omega) h0 hS hm
    by_cases h1 : q < 32000000
    · exact even22_packed_b17_s1_no_centers (by omega) h1 hS hm
    by_cases h2 : q < 48000000
    · exact even22_packed_b17_s2_no_centers (by omega) h2 hS hm
    by_cases h3 : q < 64000000
    · exact even22_packed_b17_s3_no_centers (by omega) h3 hS hm
    by_cases h4 : q < 80000000
    · exact even22_packed_b17_s4_no_centers (by omega) h4 hS hm
    · exact even22_packed_b17_s5_no_centers (by omega) (by omega) hS hm
  · have ht : t = 46 * q + 21 := by dsimp [q, r, fr] at *; omega
    rw [ht] at hm htbound
    by_cases h0 : q < 16000000
    · exact even22_packed_b21_s0_no_centers (by omega) h0 hS hm
    by_cases h1 : q < 32000000
    · exact even22_packed_b21_s1_no_centers (by omega) h1 hS hm
    by_cases h2 : q < 48000000
    · exact even22_packed_b21_s2_no_centers (by omega) h2 hS hm
    by_cases h3 : q < 64000000
    · exact even22_packed_b21_s3_no_centers (by omega) h3 hS hm
    by_cases h4 : q < 80000000
    · exact even22_packed_b21_s4_no_centers (by omega) h4 hS hm
    · exact even22_packed_b21_s5_no_centers (by omega) (by omega) hS hm
  · have ht : t = 46 * q + 25 := by dsimp [q, r, fr] at *; omega
    rw [ht] at hm htbound
    by_cases h0 : q < 16000000
    · exact even22_packed_b25_s0_no_centers (by omega) h0 hS hm
    by_cases h1 : q < 32000000
    · exact even22_packed_b25_s1_no_centers (by omega) h1 hS hm
    by_cases h2 : q < 48000000
    · exact even22_packed_b25_s2_no_centers (by omega) h2 hS hm
    by_cases h3 : q < 64000000
    · exact even22_packed_b25_s3_no_centers (by omega) h3 hS hm
    by_cases h4 : q < 80000000
    · exact even22_packed_b25_s4_no_centers (by omega) h4 hS hm
    · exact even22_packed_b25_s5_no_centers (by omega) (by omega) hS hm
  · have ht : t = 46 * q + 29 := by dsimp [q, r, fr] at *; omega
    rw [ht] at hm htbound
    by_cases h0 : q < 16000000
    · exact even22_packed_b29_s0_no_centers (by omega) h0 hS hm
    by_cases h1 : q < 32000000
    · exact even22_packed_b29_s1_no_centers (by omega) h1 hS hm
    by_cases h2 : q < 48000000
    · exact even22_packed_b29_s2_no_centers (by omega) h2 hS hm
    by_cases h3 : q < 64000000
    · exact even22_packed_b29_s3_no_centers (by omega) h3 hS hm
    by_cases h4 : q < 80000000
    · exact even22_packed_b29_s4_no_centers (by omega) h4 hS hm
    · exact even22_packed_b29_s5_no_centers (by omega) (by omega) hS hm

/-- The fully discharged k=22 row: the small-gap computation and the
packed large-gap certificate leave no solutions. -/
theorem no_gap_solution_four_even_twentytwo
    {n d : ℕ} (hd : 22 ≤ d) :
    blockProduct 22 (n + d) ≠ 4 * blockProduct 22 n := by
  apply no_gap_solution_four_even_twentytwo_of_large_obstruction ?_ hd
  intro w v t hS hm htpos htbound htodd
  exact even22_packed_candidate_impossible hS hm htodd htpos htbound

end Erdos686.Erdos686Variant
