/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import ErdosProblems.Erdos686ConstantQuotient

/-!
# Erdős Problem 686: the exceptional `k = 9`, quotient-5 branch

Closes the `k = 9`, row-1-quotient-5 branch of the small-`k` analysis of the
`N = 4` exclusion.  A hypothetical gap solution with `k = 9`, `d ≥ 221`, exact
ratio window `(n+d+9)⁹ ≤ 4·(n+9)⁹` and `4·(n+1)⁹ ≤ (n+d+1)⁹`, and row-1 base
quotient `(n+1)/d = 5` is confined to a finite box, where a kernel-checked
certificate produces a row escape.

The confinement is exact.  The rational bracket `1166530/1000000 > 4^(1/9)`
(certified by `4·1000000⁹ < 1166530⁹`; the numerator is minimal for this
denominator) linearizes the upper window inequality via
`ratio_window_linearize_of_pow_bracket` to
`1000000·(n+d+9) < 1166530·(n+9)`.  Writing `n+1 = 6d − u` with
`u = 6d − (n+1) ∈ [1, d]` (from the quotient hypothesis) and rearranging over
the integers gives `166530·u + 820·d < 1332240`, whence `u ≥ 1` forces
`d ≤ 1421` and `d ≥ 221` forces `u ≤ 6`.

The finite box `221 ≤ d ≤ 1421`, `1 ≤ u ≤ 6` (7206 points) is then decided by
the kernel: every point satisfying both ratio-window inequalities fails some
localized row divisibility `n+j ∣ shiftedDiffProductAt 9 d j` with
`j ∈ [1, 9]`.  The exact integer scan `compute/erdos686_e9_box_scan.py`
confirms the box independently: 4123 of the 7206 points pass the window, and
all of them escape at a row `j ≤ 3`.
-/

namespace Erdos686

namespace Erdos686Variant

/-- Base window of the row-1 quotient: `(n+1)/d = 5` pins `n+1` to
`[5d, 6d)`. -/
lemma k_nine_quotient_five_base_window
    {n d : ℕ} (hd : 0 < d) (hq : (n + 1) / d = 5) :
    5 * d ≤ n + 1 ∧ n + 1 < 6 * d := by
  have hdm := Nat.div_add_mod (n + 1) d
  have hmod := Nat.mod_lt (n + 1) hd
  rw [hq] at hdm
  omega

/-- Rational-bracket linearization of the `k = 9` upper ratio-window
inequality: `1166530/1000000` lies strictly above `4^(1/9)`, as certified by
the integer inequality `4·1000000⁹ < 1166530⁹`. -/
lemma k_nine_ratio_window_linear
    {n d : ℕ} (hup : (n + d + 9) ^ 9 ≤ 4 * (n + 9) ^ 9) :
    1000000 * (n + d + 9) < 1166530 * (n + 9) :=
  ratio_window_linearize_of_pow_bracket
    (N := 4) (A := 1166530) (B := 1000000) (k := 9) (n := n) (d := d)
    (by norm_num) (by norm_num) hup

/-- Finite-box confinement of the `k = 9`, quotient-5 branch: the linearized
upper window together with `5d ≤ n+1 < 6d` forces `d ≤ 1421` and
`6d − (n+1) ∈ [1, 6]`. -/
lemma k_nine_quotient_five_box_bounds
    {n d : ℕ} (hd : 221 ≤ d) (hq : (n + 1) / d = 5)
    (hup : (n + d + 9) ^ 9 ≤ 4 * (n + 9) ^ 9) :
    d ≤ 1421 ∧ 1 ≤ 6 * d - (n + 1) ∧ 6 * d - (n + 1) ≤ 6 := by
  obtain ⟨h5, h6⟩ := k_nine_quotient_five_base_window (by omega) hq
  have hlin := k_nine_ratio_window_linear hup
  omega

set_option maxRecDepth 400000 in
set_option maxHeartbeats 8000000 in
-- Exhaustive kernel-checked certificate over the box `221 ≤ d ≤ 1421`,
-- `1 ≤ 6d−(n+1) ≤ 6`, parametrized as `d = 221 + dr`, `n = 1319 + 6·dr + ur`
-- (so that `6d − (n+1) = 6 − ur ∈ [1, 6]`).
private theorem k_nine_q5_box_cert :
    ∀ (dr : Fin 1201) (ur : Fin 6),
      (1319 + 6 * (dr : ℕ) + (ur : ℕ) + (221 + (dr : ℕ)) + 9) ^ 9 ≤
          4 * (1319 + 6 * (dr : ℕ) + (ur : ℕ) + 9) ^ 9 →
      4 * (1319 + 6 * (dr : ℕ) + (ur : ℕ) + 1) ^ 9 ≤
          (1319 + 6 * (dr : ℕ) + (ur : ℕ) + (221 + (dr : ℕ)) + 1) ^ 9 →
      ∃ j, j ∈ Finset.Icc 1 9 ∧
        ¬ 1319 + 6 * (dr : ℕ) + (ur : ℕ) + j ∣
            shiftedDiffProductAt 9 (221 + (dr : ℕ)) j := by
  decide

/-- **`k = 9`, quotient-5 row escape.**  No `N = 4` ratio-window candidate
with `k = 9`, `d ≥ 221`, and row-1 base quotient `(n+1)/d = 5` satisfies all
localized row divisibilities: some row `j ∈ [1, 9]` has
`¬ n+j ∣ shiftedDiffProductAt 9 d j`. -/
theorem k_nine_quotient_five_row_escape
    {n d : ℕ} (hd : 221 ≤ d)
    (hq : (n + 1) / d = 5)
    (hup : (n + d + 9) ^ 9 ≤ 4 * (n + 9) ^ 9)
    (hlo : 4 * (n + 1) ^ 9 ≤ (n + d + 1) ^ 9) :
    ∃ j, j ∈ Finset.Icc 1 9 ∧ ¬ n + j ∣ shiftedDiffProductAt 9 d j := by
  obtain ⟨h5, h6⟩ := k_nine_quotient_five_base_window (by omega) hq
  obtain ⟨hD, hu1, hu6⟩ := k_nine_quotient_five_box_bounds hd hq hup
  have hdr : d - 221 < 1201 := by omega
  have hur : n + 7 - 6 * d < 6 := by omega
  have hd_eq : 221 + (d - 221) = d := by omega
  have hn_eq : 1319 + 6 * (d - 221) + (n + 7 - 6 * d) = n := by omega
  obtain ⟨j, hj, hnot⟩ :=
    k_nine_q5_box_cert ⟨d - 221, hdr⟩ ⟨n + 7 - 6 * d, hur⟩
      (by simpa [hd_eq, hn_eq] using hup)
      (by simpa [hd_eq, hn_eq] using hlo)
  exact ⟨j, hj, by simpa [hd_eq, hn_eq] using hnot⟩

end Erdos686Variant

end Erdos686
