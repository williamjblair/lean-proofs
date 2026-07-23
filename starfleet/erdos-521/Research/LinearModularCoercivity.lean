import Research.LinearModularEnergy
import Mathlib.Tactic

open scoped BigOperators

namespace Erdos521

/-- If a centered linear modular phase has energy below a fixed fraction of its length, then its
step is in the genuinely local regime `N|a|<1`. -/
lemma linearPhase_small_energy_forces_local (N : ℕ) (a b : ℝ) (m : ℕ → ℤ)
    (hN : 1 ≤ N) (ha0 : 0 < |a|) (ha : |a| ≤ 1 / 4)
    (henergy : 128 * (∑ q ∈ Finset.range N,
      (b + a * (q : ℝ) - (m q : ℝ) * Real.pi) ^ 2) < N) :
    (N : ℝ) * |a| < 1 := by
  by_contra hnot
  have hNa : 1 ≤ (N : ℝ) * |a| := le_of_not_gt hnot
  let L : ℕ := ⌊(1 / (2 * |a|) : ℝ)⌋₊
  have hden : 0 < 2 * |a| := by positivity
  have hfloor : (L : ℝ) ≤ 1 / (2 * |a|) := by
    dsimp [L]
    exact Nat.floor_le (by positivity)
  have hfloorNext : 1 / (2 * |a|) < (L : ℝ) + 1 := by
    dsimp [L]
    exact Nat.lt_floor_add_one _
  have hLagUpper : |a| * (L : ℝ) ≤ 1 / 2 := by
    calc
      |a| * (L : ℝ) ≤ |a| * (1 / (2 * |a|)) :=
        mul_le_mul_of_nonneg_left hfloor (abs_nonneg _)
      _ = 1 / 2 := by field_simp
  have hLagLower : 1 / 4 ≤ |a| * (L : ℝ) := by
    have ha_nonneg := abs_nonneg a
    have hm := (div_lt_iff₀ hden).mp hfloorNext
    nlinarith
  have hinvLe : 1 / (2 * |a|) ≤ (N : ℝ) / 2 := by
    apply (div_le_div_iff₀ hden (by norm_num : (0 : ℝ) < 2)).2
    nlinarith
  have hLhalf : (L : ℝ) ≤ (N : ℝ) / 2 := hfloor.trans hinvLe
  have hLN : L ≤ N := by
    exact_mod_cast (hLhalf.trans (by nlinarith : (N : ℝ) / 2 ≤ N))
  have hNsub : (N : ℝ) / 2 ≤ ((N - L : ℕ) : ℝ) := by
    rw [Nat.cast_sub hLN]
    linarith
  have hcenter : |a| * (L : ℝ) ≤ Real.pi / 2 :=
    hLagUpper.trans (by nlinarith [Real.pi_gt_three])
  have hpair := linearPhase_pair_lag_energy N L a b m hLN hcenter
  have haLagSq : (1 / 4 : ℝ) ^ 2 ≤ (a * (L : ℝ)) ^ 2 := by
    have habs : |a * (L : ℝ)| = |a| * (L : ℝ) := by
      rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (L : ℝ))]
    have h := hLagLower
    rw [← habs] at h
    exact sq_le_sq.mpr (by simpa using h)
  have hsum_nonneg : 0 ≤ ∑ q ∈ Finset.range N,
      (b + a * (q : ℝ) - (m q : ℝ) * Real.pi) ^ 2 :=
    Finset.sum_nonneg fun q hq ↦ sq_nonneg _
  have hNreal : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hlower : (N : ℝ) / 32 ≤
      ((N - L : ℕ) : ℝ) * (a * (L : ℝ)) ^ 2 := by
    nlinarith
  nlinarith

/-- Once in the local regime, the half-length lag gives cubic-in-length control of the slope. -/
lemma linearPhase_local_slope_energy (N : ℕ) (a b : ℝ) (m : ℕ → ℤ)
    (hN : 2 ≤ N) (hlocal : (N : ℝ) * |a| < 1) :
    (N : ℝ) ^ 3 * a ^ 2 ≤
      288 * ∑ q ∈ Finset.range N,
        (b + a * (q : ℝ) - (m q : ℝ) * Real.pi) ^ 2 := by
  let L := N / 2
  have hLN : L ≤ N := by dsimp [L]; omega
  have hLlower : (N : ℝ) / 3 ≤ (L : ℝ) := by
    have hc : (N : ℝ) ≤ 3 * (L : ℝ) := by
      exact_mod_cast (show N ≤ 3 * (N / 2) by omega)
    linarith
  have hNsub : (N : ℝ) / 2 ≤ ((N - L : ℕ) : ℝ) := by
    have hc : (N : ℝ) ≤ 2 * ((N - L : ℕ) : ℝ) := by
      exact_mod_cast (show N ≤ 2 * (N - N / 2) by omega)
    linarith
  have hcenter : |a| * (L : ℝ) ≤ Real.pi / 2 := by
    have hLcast : (L : ℝ) ≤ N := by exact_mod_cast hLN
    have : |a| * (L : ℝ) < 1 := by
      calc
        _ ≤ |a| * (N : ℝ) := mul_le_mul_of_nonneg_left hLcast (abs_nonneg _)
        _ = (N : ℝ) * |a| := by ring
        _ < 1 := hlocal
    nlinarith [Real.pi_gt_three]
  have hpair := linearPhase_pair_lag_energy N L a b m hLN hcenter
  have hsquares : (a * (L : ℝ)) ^ 2 = a ^ 2 * (L : ℝ) ^ 2 := by ring
  rw [hsquares] at hpair
  have ha2 : 0 ≤ a ^ 2 := sq_nonneg _
  have hN0 : 0 ≤ (N : ℝ) := by positivity
  have hL0 : 0 ≤ (L : ℝ) := by positivity
  have hLsq : ((N : ℝ) / 3) ^ 2 ≤ (L : ℝ) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hLlower 2
  have hbase : ((N : ℝ) / 2) * ((N : ℝ) / 3) ^ 2 ≤
      ((N - L : ℕ) : ℝ) * (L : ℝ) ^ 2 := by
    calc
      _ ≤ ((N - L : ℕ) : ℝ) * ((N : ℝ) / 3) ^ 2 :=
        mul_le_mul_of_nonneg_right hNsub (sq_nonneg _)
      _ ≤ ((N - L : ℕ) : ℝ) * (L : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_left hLsq (by positivity)
  have hprodLower : (N : ℝ) ^ 3 * a ^ 2 / 18 ≤
      ((N - L : ℕ) : ℝ) * (a ^ 2 * (L : ℝ) ^ 2) := by
    have hm := mul_le_mul_of_nonneg_right hbase ha2
    nlinarith
  nlinarith

end Erdos521
