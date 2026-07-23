import Mathlib
import Research.Statement
import Research.Growth
import Research.CountableConvergencePhases

namespace Erdos254.PowerShellCountablePhases

open Filter
open Erdos254
open Erdos254.CountableConvergencePhases

noncomputable section

lemma boundedPhases_separated_of_powerShells
    {C : Set ℕ}
    (hpower : Tendsto (fun j : ℕ => shellCount C (2 ^ j)) atTop atTop)
    (k : ℕ) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ θ ∈ boundedPhases C k, ∀ φ ∈ boundedPhases C k,
        θ ≠ φ → ε ≤ |θ - φ| := by
  let M : ℕ := 16 * k + 1
  obtain ⟨J, hJ⟩ := eventually_atTop.1 (tendsto_atTop.1 hpower M)
  let ε : ℝ := min (1 / 8) (1 / (4 * (2 : ℝ) ^ J))
  have hε : 0 < ε := by
    dsimp [ε]
    positivity
  refine ⟨ε, hε, ?_⟩
  intro θ hθ φ hφ hne
  by_contra hnot
  have hdist : |θ - φ| < ε := lt_of_not_ge hnot
  let δ : ℝ := |θ - φ|
  have hδ : 0 < δ := abs_pos.mpr (sub_ne_zero.mpr hne)
  have hδ8 : δ < 1 / 8 := hdist.trans_le (min_le_left _ _)
  have hδJ : δ < 1 / (4 * (2 : ℝ) ^ J) :=
    hdist.trans_le (min_le_right _ _)
  have hrone : 1 ≤ 1 / (4 * δ) := by
    rw [le_div_iff₀ (by positivity)]
    linarith
  obtain ⟨j, hjlo, hjhi⟩ := exists_nat_pow_near hrone
    (show (1 : ℝ) < 2 by norm_num)
  have hjJ : J ≤ j := by
    by_contra hnotj
    have hjlt : j < J := Nat.lt_of_not_ge hnotj
    have hp : (2 : ℝ) ^ (j + 1) ≤ (2 : ℝ) ^ J := by
      exact pow_le_pow_right₀ (by norm_num) (by omega)
    have hlarge : (2 : ℝ) ^ J < 1 / (4 * δ) := by
      rw [lt_div_iff₀ (by positivity)]
      have hprod : δ * (4 * (2 : ℝ) ^ J) < 1 :=
        (lt_div_iff₀ (by positivity)).mp hδJ
      nlinarith
    linarith
  let x : ℕ := 2 ^ j
  have hxlo : 1 / 8 ≤ (x : ℝ) * δ := by
    have hstrict : 1 / (8 * δ) < (2 : ℝ) ^ j := by
      have hnear := hjhi
      rw [pow_succ] at hnear
      have heq : 1 / (4 * δ) = 2 * (1 / (8 * δ)) := by
        field_simp
        norm_num
      nlinarith
    change 1 / 8 ≤ ((2 ^ j : ℕ) : ℝ) * δ
    rw [Nat.cast_pow, Nat.cast_ofNat]
    calc
      1 / 8 = (1 / (8 * δ)) * δ := by field_simp
      _ ≤ ((2 : ℝ) ^ j) * δ :=
        mul_le_mul_of_nonneg_right hstrict.le hδ.le
  have hxhi : (x : ℝ) * δ ≤ 1 / 4 := by
    change ((2 ^ j : ℕ) : ℝ) * δ ≤ 1 / 4
    rw [Nat.cast_pow, Nat.cast_ofNat]
    have hmul := mul_le_mul_of_nonneg_right hjlo hδ.le
    calc
      ((2 : ℝ) ^ j) * δ ≤ (1 / (4 * δ)) * δ := hmul
      _ = 1 / 4 := by field_simp
  have hlower := shell_phase_lower C x δ hδ hxlo hxhi
  have hcard : M ≤ shellCount C x := by
    dsimp [x]
    exact hJ j hjJ
  have hlower' : (2 * k : ℝ) < phasePartialSum C δ (2 * x) := by
    calc
      (2 * k : ℝ) < (M : ℝ) / 8 := by
        dsimp [M]
        push_cast
        linarith
      _ ≤ (shellCount C x : ℝ) / 8 := by
        apply div_le_div_of_nonneg_right
        · exact_mod_cast hcard
        · norm_num
      _ ≤ phasePartialSum C δ (2 * x) := hlower
  have htri : phasePartialSum C δ (2 * x) ≤
      phasePartialSum C θ (2 * x) + phasePartialSum C φ (2 * x) := by
    classical
    simp only [phasePartialSum]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro n hn
    rcases le_total φ θ with hφθ | hθφ
    · have hδeq : δ * (n : ℝ) = θ * (n : ℝ) - φ * (n : ℝ) := by
        dsimp [δ]
        rw [abs_of_nonneg (sub_nonneg.mpr hφθ)]
        ring
      rw [hδeq]
      exact nd_sub_le _ _
    · have hδeq : δ * (n : ℝ) = -(θ * (n : ℝ) - φ * (n : ℝ)) := by
        dsimp [δ]
        rw [abs_of_nonpos (sub_nonpos.mpr hθφ)]
        ring
      rw [hδeq, nd_neg]
      exact nd_sub_le _ _
  have hupp : phasePartialSum C θ (2 * x) +
      phasePartialSum C φ (2 * x) ≤ 2 * k := by
    linarith [hθ.2 (2 * x), hφ.2 (2 * x)]
  linarith

/-- Power-of-two shell multiplicity already suffices for countability of the
nearest-integer convergence-phase set. -/
theorem countable_bounded_phase_set_of_powerShells
    {C : Set ℕ}
    (hpower : Tendsto (fun j : ℕ => shellCount C (2 ^ j)) atTop atTop) :
    {θ : ℝ | θ ∈ Set.Icc (0 : ℝ) 1 ∧
      ∃ B : ℝ, ∀ N, phasePartialSum C θ N ≤ B}.Countable := by
  have hfinite : ∀ k : ℕ, (boundedPhases C k).Finite := by
    intro k
    obtain ⟨ε, hε, hsep⟩ := boundedPhases_separated_of_powerShells hpower k
    apply finite_of_totallyBounded_separated
      ((totallyBounded_Icc (0 : ℝ) 1).subset (fun θ hθ => hθ.1)) hε hsep
  refine (Set.countable_iUnion fun k => (hfinite k).countable).mono ?_
  rintro θ ⟨hθI, B, hB⟩
  obtain ⟨k, hk⟩ := exists_nat_ge B
  refine Set.mem_iUnion.mpr ⟨k, hθI, ?_⟩
  intro N
  exact (hB N).trans (by exact_mod_cast hk)

end

end Erdos254.PowerShellCountablePhases
