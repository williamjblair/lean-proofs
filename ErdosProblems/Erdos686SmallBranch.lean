/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import ErdosProblems.Erdos686QuotientConfinement
import ErdosProblems.Erdos686ExceptionalNine
import ErdosProblems.Erdos686SmallCore
import ErdosProblems.Erdos686ConstantSurvivors

/-!
# Erdős Problem 686: small-`k` branch assembly

This module assembles the banked small-`k` components into the complete
conditional reduction.  The sole remaining obstruction of the
`5 ≤ k ≤ 15` branch is isolated as `ConstantCaseBoundHypothesis` — the
constant-quotient prefix-three bound — and, together with the open
`k ≥ 16` boundary statement `RowSixteenBoundaryHypothesis`, it implies
the full refutation of the universal Erdős 686 statement.

Pipeline for `5 ≤ k ≤ 15`, `k ≤ d`, exact `N = 4` ratio window:
* `d ≤ 220` — closed by the finite-core certificate
  `row_full_escape_small_k_d_le_220`.
* `d ≥ 221` — the row-1 base quotient is confined
  (`row_base_quotient_confined_of_window`); the `k = 9`, quotient-5
  branch is closed by `k_nine_quotient_five_row_escape`; in the eleven
  constant cases the deficiency parametrization plus the row→residual
  reduction feed the prefix-three bound hypothesis, the bounded
  survivor membership certificate, and the row-four escape, closing
  everything except the bound hypothesis itself; the `u = d` edge is
  closed by `constant_u_eq_d_no_prefix_three`.
-/

namespace Erdos686

namespace Erdos686Variant

/-- **The open constant-quotient prefix-three bound** (PROGRESS §16.1).
For each of the eleven constant cases, the three residual
divisibilities of rows one to three inside the exact ratio window force
the gap `d` below the tabulated bound.  This is the sole remaining
obstruction of the small-`k` branch. -/
def ConstantCaseBoundHypothesis : Prop :=
  ∀ k q d u A n : ℕ,
    constantQuotientPairMem k q →
    221 ≤ d → 1 ≤ u → u < d →
    A = (q + 1) * d - u →
    n + 1 = A →
    (n + d + k) ^ k ≤ 4 * (n + k) ^ k →
    4 * (n + 1) ^ k ≤ (n + d + 1) ^ k →
    ((A : ℤ) ∣ residualRowPoly k q (d - u)) →
    (((A + 1 : ℕ) : ℤ) ∣ residualRowPoly k q (d - u + (q + 1))) →
    (((A + 2 : ℕ) : ℤ) ∣ residualRowPoly k q (d - u + 2 * (q + 1))) →
    d ≤ constantPrefixThreeBound k q

/-- **The open large-`k` boundary statement** (PROGRESS §13): after
rows `1..15` of the divisor skeleton survive, row `16` must fail. -/
def RowSixteenBoundaryHypothesis : Prop :=
  ∀ k n d : ℕ, 16 ≤ k → k ≤ d →
    (n + d + k) ^ k ≤ 4 * (n + k) ^ k →
    4 * (n + 1) ^ k ≤ (n + d + 1) ^ k →
    (∀ j, j ∈ Finset.Icc 1 15 → n + j ∣ shiftedDiffProductAt k d j) →
    ¬ n + 16 ∣ shiftedDiffProductAt k d 16

/-- The eleven constant pairs contain `(k, constantQuotientOf k)` for
every `k ∈ [5, 15]`. -/
private lemma constantQuotientPairMem_of_table {k : ℕ}
    (hk5 : 5 ≤ k) (hk15 : k ≤ 15) :
    constantQuotientPairMem k (constantQuotientOf k) := by
  interval_cases k <;>
    simp [constantQuotientPairMem, constantQuotientPairs, constantQuotientOf]

/-- **Small-`k` row escape, conditional on the prefix-three bound.**
For `5 ≤ k ≤ 15` and the exact `N = 4` ratio window, some row of the
divisor skeleton fails. -/
theorem row_full_escape_small_k_in_ratio_window_of_constant_bound
    (hbound : ConstantCaseBoundHypothesis) :
    ∀ k n d : ℕ, 5 ≤ k → k ≤ 15 → k ≤ d →
      (n + d + k) ^ k ≤ 4 * (n + k) ^ k →
      4 * (n + 1) ^ k ≤ (n + d + 1) ^ k →
      ∃ j, j ∈ Finset.Icc 1 k ∧ ¬ n + j ∣ shiftedDiffProductAt k d j := by
  intro k n d hk5 hk15 hkd hup hlo
  by_cases hd220 : d ≤ 220
  · exact row_full_escape_small_k_d_le_220 hk5 hk15 hkd hd220 hup hlo
  by_contra hno
  have hall : ∀ j, j ∈ Finset.Icc 1 k → n + j ∣ shiftedDiffProductAt k d j := by
    intro j hj
    by_contra hdvd
    exact hno ⟨j, hj, hdvd⟩
  rcases row_base_quotient_confined_of_window hk5 hk15 (by omega) hup hlo with
    hq | ⟨hk9, hq5⟩
  · -- constant case with q = constantQuotientOf k
    have hkq := constantQuotientPairMem_of_table hk5 hk15
    obtain ⟨u, hu1, hud, hA⟩ :=
      exists_deficiency_of_row_base_quotient (by omega : 0 < d) hq
    have hrows4 : ∀ j, j ∈ Finset.Icc 1 4 →
        n + j ∣ shiftedDiffProductAt k d j := by
      intro j hj
      have hj' := Finset.mem_Icc.mp hj
      exact hall j (Finset.mem_Icc.mpr ⟨hj'.1, hj'.2.trans (by omega)⟩)
    have hres := residual_rows_of_row_prefix_four hud (by omega) hA hrows4
    have h0 : (((n + 1 : ℕ)) : ℤ) ∣
        residualRowPoly k (constantQuotientOf k) (d - u) := by
      simpa using hres 0 (by norm_num)
    have h1 : (((n + 1 + 1 : ℕ)) : ℤ) ∣
        residualRowPoly k (constantQuotientOf k)
          (d - u + (constantQuotientOf k + 1)) := by
      simpa using hres 1 (by norm_num)
    have h2 : (((n + 1 + 2 : ℕ)) : ℤ) ∣
        residualRowPoly k (constantQuotientOf k)
          (d - u + 2 * (constantQuotientOf k + 1)) := by
      have := hres 2 (by norm_num)
      simpa [two_mul, mul_comm] using this
    have h3 : (((n + 1 + 3 : ℕ)) : ℤ) ∣
        residualRowPoly k (constantQuotientOf k)
          (d - u + 3 * (constantQuotientOf k + 1)) := by
      have := hres 3 (by norm_num)
      simpa [mul_comm] using this
    rcases Nat.lt_or_ge u d with hult | hueq
    · -- interior u < d: bound, membership, row-four escape
      have hd_le := hbound k (constantQuotientOf k) d u (n + 1) n hkq
        (by omega) hu1 hult hA rfl hup hlo h0 h1 h2
      exact constant_case_row4_escape_of_prefix_three_bound hkq (by omega)
        hd_le hu1 hult hA rfl hup hlo h0 h1 h2 h3
    · -- top edge u = d
      have hu_eq : u = d := le_antisymm hud hueq
      have hAq : n + 1 = constantQuotientOf k * d := by
        have hmul : (constantQuotientOf k + 1) * d
            = constantQuotientOf k * d + d := by ring
        omega
      have hzero : d - u = 0 := by omega
      refine constant_u_eq_d_no_prefix_three hkq (by omega) hAq rfl hup ?_ ?_
      · simpa [hzero] using h1
      · simpa [hzero] using h2
  · -- k = 9 with row-1 quotient 5
    subst hk9
    obtain ⟨j, hj, hnd⟩ := k_nine_quotient_five_row_escape (by omega) hq5 hup hlo
    exact hnd (hall j hj)

/-- **The complete conditional reduction of Erdős 686.**  The two open
hypotheses — the constant-quotient prefix-three bound and the `k ≥ 16`
row-sixteen boundary — refute the universal positive statement. -/
theorem erdos686_false_of_constant_bound_and_boundary
    (hbound : ConstantCaseBoundHypothesis)
    (hboundary : RowSixteenBoundaryHypothesis) :
    ¬ ∀ N : ℕ, 2 ≤ N → ∃ k n m : ℕ,
      2 ≤ k ∧ m ≥ n + k ∧
      (N : ℚ) =
        (∏ i ∈ Finset.Icc 1 k, (((m + i : ℕ) : ℚ))) /
          (∏ i ∈ Finset.Icc 1 k, (((n + i : ℕ) : ℚ))) := by
  apply erdos686_false_of_row_prefix_sixteen_escape
  exact row_prefix_sixteen_escape_of_boundary_and_small_k_escape hboundary
    (row_full_escape_small_k_in_ratio_window_of_constant_bound hbound)

/-!
## Falsification of the row-sixteen boundary, and the repaired reduction

The fixed-prefix boundary statement `RowSixteenBoundaryHypothesis` is
**false**: the point `(k, n, d) = (984, 3177026, 4480)` lies in the
exact ratio window with `16 ≤ k ≤ d`, its divisor-skeleton rows `1..16`
all divide, and only row `17` fails (because
`n + 17 = 439 · 7237` and the prime `7237` exceeds the row-17 interval
maximum `d + k - 17 = 5447`).  Deep survivor clusters can evidently
pass arbitrarily long fixed prefixes, so the boundary hypothesis is
repaired to the unrestricted escape `LargeKEscapeHypothesis`, which is
all the banked skeleton bridge actually needs.
-/

/-- **The repaired open large-`k` hypothesis**: for `k ≥ 16` in the
exact ratio window, some divisor-skeleton row `j ≤ k` fails. -/
def LargeKEscapeHypothesis : Prop :=
  ∀ k n d : ℕ, 16 ≤ k → k ≤ d →
    (n + d + k) ^ k ≤ 4 * (n + k) ^ k →
    4 * (n + 1) ^ k ≤ (n + d + 1) ^ k →
    ∃ j, j ∈ Finset.Icc 1 k ∧ ¬ n + j ∣ shiftedDiffProductAt k d j

set_option maxRecDepth 4000 in
-- The witness verification kernel-reduces sixteen 984-factor products
-- and two exponent-984 window inequalities, far beyond the default
-- heartbeat budget.
set_option maxHeartbeats 4000000 in
set_option exponentiation.threshold 1000 in
/-- The row-sixteen boundary hypothesis is refuted by the exact-window
point `(984, 3177026, 4480)`, whose rows `1..16` all divide. -/
theorem row_sixteen_boundary_hypothesis_false :
    ¬ RowSixteenBoundaryHypothesis := by
  intro h
  refine h 984 3177026 4480 (by norm_num) (by norm_num)
    (by decide) (by decide) (fun j hj => ?_) (by decide)
  obtain ⟨hj1, hj2⟩ := Finset.mem_Icc.mp hj
  interval_cases j <;> decide

/-- **The repaired complete conditional reduction of Erdős 686.**
The constant-quotient prefix-three bound together with the
unrestricted large-`k` row escape refutes the universal positive
statement. -/
theorem erdos686_false_of_constant_bound_and_large_escape
    (hbound : ConstantCaseBoundHypothesis)
    (hlarge : LargeKEscapeHypothesis) :
    ¬ ∀ N : ℕ, 2 ≤ N → ∃ k n m : ℕ,
      2 ≤ k ∧ m ≥ n + k ∧
      (N : ℚ) =
        (∏ i ∈ Finset.Icc 1 k, (((m + i : ℕ) : ℚ))) /
          (∏ i ∈ Finset.Icc 1 k, (((n + i : ℕ) : ℚ))) := by
  apply erdos686_false_of_divisor_skeleton_escape
  intro k n d hk5 hkd hup hlo
  rcases Nat.lt_or_ge k 16 with hk16 | hk16
  · exact row_full_escape_small_k_in_ratio_window_of_constant_bound
      hbound k n d hk5 (by omega) hkd hup hlo
  · exact hlarge k n d hk16 hkd hup hlo

/-- The repaired conditional `N = 4` exclusion. -/
theorem no_solution_four_of_constant_bound_and_large_escape
    (hbound : ConstantCaseBoundHypothesis)
    (hlarge : LargeKEscapeHypothesis) :
    ¬ ∃ k n m : ℕ,
      2 ≤ k ∧ m ≥ n + k ∧
      (4 : ℚ) =
        (∏ i ∈ Finset.Icc 1 k, (((m + i : ℕ) : ℚ))) /
          (∏ i ∈ Finset.Icc 1 k, (((n + i : ℕ) : ℚ))) := by
  apply no_solution_four_of_divisor_skeleton_escape
  intro k n d hk5 hkd hup hlo
  rcases Nat.lt_or_ge k 16 with hk16 | hk16
  · exact row_full_escape_small_k_in_ratio_window_of_constant_bound
      hbound k n d hk5 (by omega) hkd hup hlo
  · exact hlarge k n d hk16 hkd hup hlo

/-- The `N = 4` no-solution statement, conditional on the same two
open hypotheses. -/
theorem no_solution_four_of_constant_bound_and_boundary
    (hbound : ConstantCaseBoundHypothesis)
    (hboundary : RowSixteenBoundaryHypothesis) :
    ¬ ∃ k n m : ℕ,
      2 ≤ k ∧ m ≥ n + k ∧
      (4 : ℚ) =
        (∏ i ∈ Finset.Icc 1 k, (((m + i : ℕ) : ℚ))) /
          (∏ i ∈ Finset.Icc 1 k, (((n + i : ℕ) : ℚ))) := by
  apply no_solution_four_of_row_prefix_sixteen_escape
  exact row_prefix_sixteen_escape_of_boundary_and_small_k_escape hboundary
    (row_full_escape_small_k_in_ratio_window_of_constant_bound hbound)

end Erdos686Variant

end Erdos686
