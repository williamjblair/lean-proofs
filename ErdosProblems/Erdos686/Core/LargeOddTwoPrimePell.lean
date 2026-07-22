/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import ErdosProblems.Erdos686.Core.LargePrimeGapComponent
import ErdosProblems.Erdos686.Core.TwoPrimeSecondLift
import ErdosProblems.Erdos686.Core.ReflectedHarmonicBridge

/-!
# Uniform two-large-prime Pell reduction in large odd rows

For every odd `k=2r+1>=17`, the exact large-row window gives
`n+1<k*d`.  Thus the existing bounded-Pell theorem applies uniformly with
`C=k` and `A=3k+2`; the elementary inequality `3k+2<k^2` supplies its only
coefficient-size side condition.

This file packages the resulting distinct-owner Pell data and composes the
two generic second-order local lifts.  It is a proper restriction, not a
closure of the remaining Pell/prime-power branch.
-/

namespace Erdos686
namespace Erdos686Variant

/-- Complete equation-facing Pell and second-lift certificate for one whole
two-large-prime gap in an odd row. -/
def LargeOddTwoPrimePellCertificate
    (p q e f r n d : ℕ) : Prop :=
  ∃ i j a b,
    i ∈ Finset.Icc 1 (2 * r + 1) ∧
    j ∈ Finset.Icc 1 (2 * r + 1) ∧
    i ≠ j ∧ 0 < a ∧ 0 < b ∧
    localResidual n d i = a * (p ^ e) ^ 2 ∧
    localResidual n d j = b * (q ^ f) ^ 2 ∧
    a * p ^ e < (3 * (2 * r + 1) + 2) * q ^ f ∧
    b * q ^ f < (3 * (2 * r + 1) + 2) * p ^ e ∧
    a * b < (3 * (2 * r + 1) + 2) ^ 2 ∧
    ((a * (p ^ e) ^ 2 : ℕ) : ℤ) - ((b * (q ^ f) ^ 2 : ℕ) : ℤ) =
      3 * ((i : ℤ) - (j : ℤ)) ∧
    ((p ^ e : ℕ) : ℤ) ∣
      secondObstructionLeft (2 * r + 1) i j (a * b) ∧
    ((q ^ f : ℕ) : ℤ) ∣
      secondObstructionRight (2 * r + 1) i j (a * b) ∧
    (i = r + 1 →
      (p ^ e) ^ 3 ∣ localResidual n d i ∧
        d < (3 * (2 * r + 1) + 2) ^ 5) ∧
    (j = r + 1 →
      (q ^ f) ^ 3 ∣ localResidual n d j ∧
        d < (3 * (2 * r + 1) + 2) ^ 5)

/-- For `r ≥ 2`, a Pell certificate in the row `k=2r+1 ≥ 5` exposes two
divisible second obstructions, and the reflected-harmonic bridge proves that
at least one is nonzero. -/
theorem LargeOddTwoPrimePellCertificate.exists_nonzero_second_obstruction
    {p q e f r n d : ℕ} (hr2 : 2 ≤ r)
    (hcert : LargeOddTwoPrimePellCertificate p q e f r n d) :
    ∃ i j a b,
      i ∈ Finset.Icc 1 (2 * r + 1) ∧
      j ∈ Finset.Icc 1 (2 * r + 1) ∧
      i ≠ j ∧
      ((p ^ e : ℕ) : ℤ) ∣
        secondObstructionLeft (2 * r + 1) i j (a * b) ∧
      ((q ^ f : ℕ) : ℤ) ∣
        secondObstructionRight (2 * r + 1) i j (a * b) ∧
      (secondObstructionLeft (2 * r + 1) i j (a * b) ≠ 0 ∨
        secondObstructionRight (2 * r + 1) i j (a * b) ≠ 0) := by
  rcases hcert with
    ⟨i, j, a, b, hi, hj, hij, _, _, _, _, _, _, _, _, hpObs, hqObs, _, _⟩
  refine ⟨i, j, a, b, hi, hj, hij, hpObs, hqObs, ?_⟩
  exact second_obstruction_pair_not_both_zero
    (by exact ⟨r, by omega⟩) (by omega) hi hj hij

/-- The `18/13` large-row window implies the convenient integral base bound
`n+1<k*d`. -/
lemma base_lt_row_mul_gap_of_large_odd_four_solution
    {r n d : ℕ} (hr8 : 8 ≤ r)
    (heq : blockProduct (2 * r + 1) (n + d) =
      4 * blockProduct (2 * r + 1) n) :
    n + 1 < (2 * r + 1) * d := by
  have hk16 : 16 ≤ 2 * r + 1 := by omega
  have hratio : 18 * (n + 1) < 13 * (2 * r + 1) * d :=
    eighteen_mul_n_add_one_lt_thirteen_mul_k_mul_gap_of_four_solution
      hk16 heq
  have hkdPos : 0 < (2 * r + 1) * d := by
    have hdPos : 0 < d := by
      by_contra hnot
      have hd0 : d = 0 := Nat.eq_zero_of_not_pos hnot
      subst d
      have hblockPos := blockProduct_pos (2 * r + 1) n
      omega
    exact Nat.mul_pos (by omega) hdPos
  nlinarith

/-- Uniform large-odd wrapper for the existing bounded-Pell theorem, with
both second-order obstruction divisibilities derived from the equation. -/
theorem large_odd_two_large_prime_pell_certificate
    {p q e f r n d : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (he : 0 < e) (hf : 0 < f)
    (hr8 : 8 ≤ r)
    (hpk : 2 * r + 1 ≤ p) (hqk : 2 * r + 1 ≤ q)
    (hgap : d = p ^ e * q ^ f)
    (heq : blockProduct (2 * r + 1) (n + d) =
      4 * blockProduct (2 * r + 1) n) :
    LargeOddTwoPrimePellCertificate p q e f r n d := by
  let k : ℕ := 2 * r + 1
  let A : ℕ := 3 * k + 2
  have hkEq : k = 2 * r + 1 := rfl
  have hAEq : A = 3 * k + 2 := rfl
  have hk17 : 17 ≤ k := by dsimp [k]; omega
  have hr2 : 2 ≤ r := by omega
  have hpPowPos : 0 < p ^ e := pow_pos hp.pos _
  have hqPowPos : 0 < q ^ f := pow_pos hq.pos _
  have hpLePow : p ≤ p ^ e := by
    simpa using Nat.pow_le_pow_right hp.pos (by omega : 1 ≤ e)
  have hkd : k ≤ d := by
    calc
      k = 2 * r + 1 := hkEq
      _ ≤ p := hpk
      _ ≤ p ^ e := hpLePow
      _ ≤ p ^ e * q ^ f := Nat.le_mul_of_pos_right _ hqPowPos
      _ = d := hgap.symm
  have hbase : n + 1 < k * d := by
    simpa [k] using base_lt_row_mul_gap_of_large_odd_four_solution hr8 heq
  have hAk : A < k ^ 2 := by
    dsimp [A]
    nlinarith
  obtain ⟨i, j, a, b, hi, hj, hij, hapos, hbpos, haeq, hbeq,
      haRatio, hbRatio, hab, hPell, hpCenter, hqCenter⟩ :=
    two_large_prime_support_bounded_pell
      (r := r) (C := k) (A := A)
      hp hq hpq he hf hr2 (by simpa [k] using hpk) (by simpa [k] using hqk)
      (by simpa [k] using hkd) hgap heq hbase hAEq (by simpa [k] using hAk)
  have hpDvdD : p ^ e ∣ d := by
    rw [hgap]
    exact dvd_mul_right _ _
  have hqDvdD : q ^ f ∣ d := by
    rw [hgap]
    exact dvd_mul_left _ _
  have hXiPos : 0 < localResidual n d i := by
    rw [haeq]
    positivity
  have hXjPos : 0 < localResidual n d j := by
    rw [hbeq]
    positivity
  have hpDvdXi : p ^ e ∣ localResidual n d i := by
    rw [haeq]
    refine ⟨a * p ^ e, ?_⟩
    ring
  have hqDvdXj : q ^ f ∣ localResidual n d j := by
    rw [hbeq]
    refine ⟨b * q ^ f, ?_⟩
    ring
  have hXiAdd : localResidual n d i + d = 3 * (n + i) := by
    unfold localResidual at hXiPos ⊢
    omega
  have hXjAdd : localResidual n d j + d = 3 * (n + j) := by
    unfold localResidual at hXjPos ⊢
    omega
  have hpDvdThree : p ^ e ∣ 3 * (n + i) := by
    rw [← hXiAdd]
    exact dvd_add hpDvdXi hpDvdD
  have hqDvdThree : q ^ f ∣ 3 * (n + j) := by
    rw [← hXjAdd]
    exact dvd_add hqDvdXj hqDvdD
  have hpNotDvdThree : ¬p ∣ 3 := by
    intro hp3
    have hpLe3 : p ≤ 3 := Nat.le_of_dvd (by norm_num) hp3
    omega
  have hqNotDvdThree : ¬q ∣ 3 := by
    intro hq3
    have hqLe3 : q ≤ 3 := Nat.le_of_dvd (by norm_num) hq3
    omega
  have hpFactor : p ^ e ∣ n + i :=
    (hp.coprime_pow_of_not_dvd (m := e) hpNotDvdThree).symm.dvd_of_dvd_mul_left
      hpDvdThree
  have hqFactor : q ^ f ∣ n + j :=
    (hq.coprime_pow_of_not_dvd (m := f) hqNotDvdThree).symm.dvd_of_dvd_mul_left
      hqDvdThree
  have hdi : d ≤ 3 * (n + i) := by
    unfold localResidual at hXiPos
    omega
  have hdj : d ≤ 3 * (n + j) := by
    unfold localResidual at hXjPos
    omega
  have hresI : 3 * ((n + i : ℕ) : ℤ) - (d : ℤ) =
      (a : ℤ) * (p ^ e : ℕ) ^ 2 := by
    calc
      3 * ((n + i : ℕ) : ℤ) - (d : ℤ) =
          ((3 * (n + i) - d : ℕ) : ℤ) := by
            rw [Int.ofNat_sub hdi]
            push_cast
            ring
      _ = (localResidual n d i : ℤ) := by rfl
      _ = (a * (p ^ e) ^ 2 : ℕ) := by rw [haeq]
      _ = (a : ℤ) * (p ^ e : ℕ) ^ 2 := by push_cast; ring
  have hresJ : 3 * ((n + j : ℕ) : ℤ) - (d : ℤ) =
      (b : ℤ) * (q ^ f : ℕ) ^ 2 := by
    calc
      3 * ((n + j : ℕ) : ℤ) - (d : ℤ) =
          ((3 * (n + j) - d : ℕ) : ℤ) := by
            rw [Int.ofNat_sub hdj]
            push_cast
            ring
      _ = (localResidual n d j : ℤ) := by rfl
      _ = (b * (q ^ f) ^ 2 : ℕ) := by rw [hbeq]
      _ = (b : ℤ) * (q ^ f : ℕ) ^ 2 := by push_cast; ring
  have hpLocal := second_order_local_lift hi hpPowPos hgap hpFactor hresI heq
  have hqLocal := second_order_local_lift hj hqPowPos
    (by simpa [mul_comm] using hgap) hqFactor hresJ heq
  have hPell' :
      (a : ℤ) * (p ^ e : ℕ) ^ 2 - (b : ℤ) * (q ^ f : ℕ) ^ 2 =
        3 * ((i : ℤ) - (j : ℤ)) := by
    simpa only [Nat.cast_mul, Nat.cast_pow] using hPell
  have hobs := second_obstruction_divisibilities hpLocal hqLocal hPell'
  have hpObs : (p ^ e : ℤ) ∣
      secondObstructionLeft (2 * r + 1) i j (a * b) := by
    simpa [secondObstructionLeft, mul_assoc] using hobs.1
  have hqObs : (q ^ f : ℤ) ∣
      secondObstructionRight (2 * r + 1) i j (a * b) := by
    simpa [secondObstructionRight, mul_assoc] using hobs.2
  refine ⟨i, j, a, b, hi, hj, hij, hapos, hbpos, haeq, hbeq,
    ?_, ?_, ?_, hPell, hpObs, hqObs, ?_, ?_⟩
  · simpa [A, k] using haRatio
  · simpa [A, k] using hbRatio
  · simpa [A, k] using hab
  · simpa [A, k] using hpCenter
  · simpa [A, k] using hqCenter

#print axioms base_lt_row_mul_gap_of_large_odd_four_solution
#print axioms large_odd_two_large_prime_pell_certificate
#print axioms LargeOddTwoPrimePellCertificate.exists_nonzero_second_obstruction

end Erdos686Variant
end Erdos686
