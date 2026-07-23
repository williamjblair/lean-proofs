import Research.FourthPerturbationTail
import Research.FourthLateStripRate
import Mathlib.Tactic

set_option maxHeartbeats 600000

namespace Erdos521

lemma fourthEvenPerturbationVariance_pos (m : ℕ) :
    0 < finiteRademacherVariance (fourthEvenPerturbationWeight m) := by
  unfold finiteRademacherVariance
  let i : Fin (m + 1) × Fin 2 := (⟨m, by omega⟩, 0)
  have hi : i ∈ (Finset.univ : Finset (Fin (m + 1) × Fin 2)) := Finset.mem_univ i
  have hterm : 0 < fourthEvenPerturbationWeight m i ^ 2 := by
    dsimp [i, fourthEvenPerturbationWeight]
    norm_num
  exact hterm.trans_le (Finset.single_le_sum (fun j hj ↦ sq_nonneg _) hi)

lemma fourthOddPerturbationVariance_pos (m : ℕ) :
    0 < finiteRademacherVariance (fourthOddPerturbationWeight m) := by
  unfold finiteRademacherVariance
  let i : Fin (m + 1) × Fin 2 := (⟨m, by omega⟩, 0)
  have hi : i ∈ (Finset.univ : Finset (Fin (m + 1) × Fin 2)) := Finset.mem_univ i
  have hterm : 0 < fourthOddPerturbationWeight m i ^ 2 := by
    dsimp [i, fourthOddPerturbationWeight]
    norm_num
  exact hterm.trans_le (Finset.single_le_sum (fun j hj ↦ sq_nonneg _) hi)

lemma finiteRademacher_lateCutoff_tail_le {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (N : ℕ)
    (hVpos : 0 < finiteRademacherVariance w)
    (hV : finiteRademacherVariance w ≤ 128 * (N + 3 : ℝ) ^ 5) :
    finiteRademacherAbsTailProbability w (fourthLateCutoff N : ℝ) ≤
      2 / (N + 3 : ℝ) ^ 4 := by
  let x : ℝ := N + 3
  have hx : 0 < x := by dsimp [x]; positivity
  have hlog : 0 ≤ Real.log x := by
    dsimp [x]
    linarith [fourthLate_log_one_le N]
  have hT : 0 ≤ (fourthLateCutoff N : ℝ) := by positivity
  have hbase := fourthLateBase_sq N
  have hcut := fourthLateCutoff_lower N
  have hcut2 : 10000 * x ^ 5 * Real.log x ≤ (fourthLateCutoff N : ℝ) ^ 2 := by
    have hsq : (100 * fourthLateBase N) ^ 2 = 10000 * x ^ 5 * Real.log x := by
      rw [mul_pow, hbase]
      dsimp [x]
      ring
    rw [← hsq]
    exact (sq_le_sq₀ (by nlinarith [fourthLateBase_one_le N]) hT).2 hcut
  have hratio : 4 * Real.log x ≤
      (fourthLateCutoff N : ℝ) ^ 2 / (2 * finiteRademacherVariance w) := by
    apply (le_div_iff₀ (mul_pos (by norm_num) hVpos)).2
    calc
      4 * Real.log x * (2 * finiteRademacherVariance w) ≤
          4 * Real.log x * (2 * (128 * x ^ 5)) := by gcongr
      _ ≤ 10000 * x ^ 5 * Real.log x := by
        have hp : 0 ≤ x ^ 5 * Real.log x := mul_nonneg (by positivity) hlog
        ring_nf
        nlinarith
      _ ≤ _ := hcut2
  have hHoeffding := finiteRademacherAbsTailProbability_le w hT hVpos
  have hexp : 2 * Real.exp (-((fourthLateCutoff N : ℝ) ^ 2) /
      (2 * finiteRademacherVariance w)) ≤ 2 * Real.exp (-4 * Real.log x) := by
    gcongr
    calc
      -(fourthLateCutoff N : ℝ) ^ 2 / (2 * finiteRademacherVariance w) =
          -((fourthLateCutoff N : ℝ) ^ 2 / (2 * finiteRademacherVariance w)) := by ring
      _ ≤ -4 * Real.log x := by simpa only [neg_mul] using neg_le_neg hratio
  have heq : Real.exp (-4 * Real.log x) = 1 / x ^ 4 := by
    rw [show -4 * Real.log x =
      -(Real.log x + Real.log x + Real.log x + Real.log x) by ring,
      Real.exp_neg, Real.exp_add, Real.exp_add, Real.exp_add, Real.exp_log hx]
    ring
  calc
    finiteRademacherAbsTailProbability w (fourthLateCutoff N : ℝ) ≤
        2 * Real.exp (-((fourthLateCutoff N : ℝ) ^ 2) /
          (2 * finiteRademacherVariance w)) := hHoeffding
    _ ≤ 2 * Real.exp (-4 * Real.log x) := hexp
    _ = 2 / (N + 3 : ℝ) ^ 4 := by rw [heq]; dsimp [x]; ring

lemma fourthEvenPerturbation_late_density_le (m : ℕ) (hm : 1 ≤ m) :
    ((fourthEvenPerturbationWords m (fourthLateCutoff (2 * m - 2) : ℝ)).card : ℝ) /
        (4 : ℝ) ^ (m + 1) ≤ 2 / (2 * m + 1 : ℝ) ^ 4 := by
  rw [fourthEvenPerturbationWords_density_eq]
  have hV0 := fourthEvenPerturbationVariance_le m
  have hn : 2 * m - 2 + 3 = 2 * m + 1 := by omega
  have hnr : (((2 * m - 2 : ℕ) : ℝ) + 3) = (2 * m + 1 : ℕ) := by
    exact_mod_cast hn
  have hV : finiteRademacherVariance (fourthEvenPerturbationWeight m) ≤
      128 * (((2 * m - 2 : ℕ) : ℝ) + 3) ^ 5 := by
    rw [hnr]
    exact hV0.trans (by
      gcongr
      push_cast
      linarith)
  have h := finiteRademacher_lateCutoff_tail_le
    (fourthEvenPerturbationWeight m) (2 * m - 2)
    (fourthEvenPerturbationVariance_pos m) hV
  rw [hnr] at h
  convert h using 1 <;> norm_num

lemma fourthOddPerturbation_late_density_le (m : ℕ) (hm : 1 ≤ m) :
    ((fourthOddPerturbationWords m (fourthLateCutoff (2 * m - 1) : ℝ)).card : ℝ) /
        (4 : ℝ) ^ (m + 1) ≤ 2 / (2 * m + 2 : ℝ) ^ 4 := by
  rw [fourthOddPerturbationWords_density_eq]
  have hV0 := fourthOddPerturbationVariance_le m
  have hn : 2 * m - 1 + 3 = 2 * m + 2 := by omega
  have hnr : (((2 * m - 1 : ℕ) : ℝ) + 3) = (2 * m + 2 : ℕ) := by
    exact_mod_cast hn
  have hV : finiteRademacherVariance (fourthOddPerturbationWeight m) ≤
      128 * (((2 * m - 1 : ℕ) : ℝ) + 3) ^ 5 := by
    rw [hnr]
    exact hV0.trans (by
      gcongr
      push_cast
      linarith)
  have h := finiteRademacher_lateCutoff_tail_le
    (fourthOddPerturbationWeight m) (2 * m - 1)
    (fourthOddPerturbationVariance_pos m) hV
  rw [hnr] at h
  convert h using 1 <;> norm_num

end Erdos521
