import Mathlib.Probability.BorelCantelli
import Mathlib.Data.Nat.Log
import Mathlib.Tactic

open Filter MeasureTheory Set
open scoped Topology ENNReal

namespace Erdos521

section DyadicMaximal

variable {Ω : Type*} [MeasurableSpace Ω]

/-- On the `k`th dyadic degree block, some value of `X` exceeds the reciprocal threshold indexed
by `m`. -/
def dyadicBad (X : ℕ → Ω → ℝ) (m k : ℕ) : Set Ω :=
  {ω | ∃ n : ℕ, 2 ^ k ≤ n ∧ n < 2 ^ (k + 1) ∧
    1 / ((m : ℝ) + 1) < |X n ω|}

/-- Abstract maximal Borel--Cantelli criterion. Summability of every reciprocal-threshold dyadic
maximal event forces almost-sure convergence of the entire sequence, not merely a lacunary
subsequence. -/
lemma ae_tendsto_zero_of_dyadicBad_summable (μ : Measure Ω) (X : ℕ → Ω → ℝ)
    (hsum : ∀ m : ℕ, (∑' k : ℕ, μ (dyadicBad X m k)) ≠ ∞) :
    ∀ᵐ ω ∂μ, Tendsto (fun n ↦ X n ω) atTop (𝓝 0) := by
  have hm (m : ℕ) : ∀ᵐ ω ∂μ, ∀ᶠ k : ℕ in atTop, ω ∉ dyadicBad X m k :=
    ae_eventually_notMem (hsum m)
  have hall : ∀ᵐ ω ∂μ, ∀ m : ℕ, ∀ᶠ k : ℕ in atTop, ω ∉ dyadicBad X m k :=
    ae_all_iff.mpr hm
  filter_upwards [hall] with ω hω
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨m, hmε⟩ := exists_nat_one_div_lt hε
  obtain ⟨K, hK⟩ := eventually_atTop.1 (hω m)
  refine ⟨2 ^ K, ?_⟩
  intro n hn
  have hnzero : n ≠ 0 := by
    have hpow : 0 < 2 ^ K := pow_pos (by omega) K
    omega
  let k := Nat.log 2 n
  have hkK : K ≤ k := by
    apply Nat.le_log_of_pow_le (by omega : 1 < 2)
    exact hn
  have hnot := hK k hkK
  have hnlo : 2 ^ k ≤ n := Nat.pow_log_le_self 2 hnzero
  have hnhi : n < 2 ^ (k + 1) := by
    simpa [Nat.succ_eq_add_one] using Nat.lt_pow_succ_log_self (by omega : 1 < 2) n
  have hbound : |X n ω| ≤ 1 / ((m : ℝ) + 1) := by
    by_contra hbad
    apply hnot
    exact ⟨n, hnlo, hnhi, lt_of_not_ge hbad⟩
  simpa [Real.dist_eq] using hbound.trans_lt hmε

end DyadicMaximal

end Erdos521
