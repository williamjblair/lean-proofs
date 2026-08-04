import ResearchPNT.LowerComparison
import ResearchPNT.ParameterChoice

/-! # Final two-sided estimate -/

open Filter Asymptotics Real

namespace ResearchPNT

/-- The compatible-prime lower construction gives the full stopped-product
lower bound for `log S(N)`. -/
theorem exists_eventual_full_product_logS_lower :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop,
      c * ((N : ℝ) / Real.log N) *
          Research.renewalProduct N (Research.logLogNat N) ≤
        Research.logS N := by
  obtain ⟨C, hC, hlower⟩ := exists_eventual_full_product_tail_lower
  let c := C * Real.log 2
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨c, mul_pos hC hlog2, ?_⟩
  filter_upwards [hlower] with N hN
  have hcard : ((Research.tailCoeffGoodDenominators N).card : ℝ) ≤
      ((Research.goodDenominators N).card : ℝ) := by
    exact_mod_cast Research.tailCoeffGood_card_le_goodDenominators N
  have hcardLog : ((Research.tailCoeffGoodDenominators N).card : ℝ) *
      Real.log 2 ≤ ((Research.goodDenominators N).card : ℝ) * Real.log 2 :=
    mul_le_mul_of_nonneg_right hcard hlog2.le
  have hscaled := mul_le_mul_of_nonneg_right hN hlog2.le
  calc
    c * ((N : ℝ) / Real.log N) *
        Research.renewalProduct N (Research.logLogNat N) =
      (C * ((N : ℝ) / Real.log N) *
        Research.renewalProduct N (Research.logLogNat N)) * Real.log 2 := by
        dsimp [c]
        ring
    _ ≤ ((Research.tailCoeffGoodDenominators N).card : ℝ) * Real.log 2 := hscaled
    _ ≤ ((Research.goodDenominators N).card : ℝ) * Real.log 2 := hcardLog
    _ ≤ Research.logS N := Research.card_good_mul_log_two_le_logS N

/-- Repackage F-027 with `N` instead of `N+1` in the continuous prefactor. -/
theorem exists_eventual_full_product_logS_upper :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop,
      Research.logS N ≤
        C * ((N : ℝ) / Real.log N) *
          Research.renewalProduct N (Research.logLogNat N) := by
  obtain ⟨K, hK, M, hM, hupper⟩ := exists_full_depth_product_upper
  refine ⟨2 * K, mul_pos (by norm_num) hK, ?_⟩
  filter_upwards [(eventually_ge_atTop M : ∀ᶠ N : ℕ in atTop, M ≤ N)] with N hMN
  have hN : 1 ≤ N := le_trans (by omega) (le_trans hM hMN)
  have hlog : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hP : 0 ≤ Research.renewalProduct N (Research.logLogNat N) :=
    le_trans (by norm_num) (Research.one_le_renewalProduct N _)
  have hN1 : (((N + 1 : ℕ) : ℝ) / Real.log N) ≤
      2 * ((N : ℝ) / Real.log N) := by
    calc
      (((N + 1 : ℕ) : ℝ) / Real.log N) ≤
          (2 * (N : ℝ)) / Real.log N := by
        apply div_le_div_of_nonneg_right _ hlog.le
        norm_num only [Nat.cast_add, Nat.cast_one]
        have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
        nlinarith
      _ = 2 * ((N : ℝ) / Real.log N) := by ring
  calc
    Research.logS N ≤ K *
        (((N + 1 : ℕ) : ℝ) / Real.log N *
          Research.renewalProduct N (Research.logLogNat N)) := hupper N hMN
    _ ≤ K * (2 * ((N : ℝ) / Real.log N) *
          Research.renewalProduct N (Research.logLogNat N)) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hN1 hP) hK.le
    _ = (2 * K) * ((N : ℝ) / Real.log N) *
        Research.renewalProduct N (Research.logLogNat N) := by ring

/-- Final machine-checked estimate: `log S(N)` is bounded above and below by
positive constants times the fully stopped iterated-log product scale. -/
theorem exists_two_sided_full_product_estimate :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ᶠ N : ℕ in atTop,
      c * ((N : ℝ) / Real.log N) *
          Research.renewalProduct N (Research.logLogNat N) ≤ Research.logS N ∧
      Research.logS N ≤ C * ((N : ℝ) / Real.log N) *
          Research.renewalProduct N (Research.logLogNat N) := by
  obtain ⟨c, hc, hlower⟩ := exists_eventual_full_product_logS_lower
  obtain ⟨C, hC, hupper⟩ := exists_eventual_full_product_logS_upper
  refine ⟨c, C, hc, hC, ?_⟩
  filter_upwards [hlower, hupper] with N hl hu
  exact ⟨hl, hu⟩

#print axioms exists_eventual_full_product_logS_lower
#print axioms exists_two_sided_full_product_estimate

end ResearchPNT
