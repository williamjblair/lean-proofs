/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import ErdosProblems.Erdos686PrimeObstruction

/-!
# Erdős 686: an explicit large-k near-diagonal wedge

This module isolates the exact bridge from the published Nair--Shorey
greatest-prime-factor theorem to the remaining large-`k` branch.  The external
theorem is represented by `CompositeBlockPrime442Hypothesis`; it is not
asserted as an axiom.  Everything downstream of that interface is proved in
the kernel.

The unconditional new input is that an `N=4` solution with `k >= 16` must
satisfy `4*d < n`.  Combined with the already banked `(d+k-1)`-smoothness,
this makes every lower-block term composite and puts the block above 100 once
`k >= 25`.
-/

namespace Erdos686

namespace Erdos686Variant

/-- Exact `221/50 = 4.42` greatest-prime-factor interface in the range used
here.  This is the Nair--Shorey theorem specialized to blocks starting above
100 and lengths at least 25. -/
def CompositeBlockPrime442Hypothesis : Prop :=
  ∀ k n : ℕ, 25 ≤ k → 100 < n + 1 →
    (∀ i, i ∈ Finset.Icc 1 k → ¬ (n + i).Prime) →
    ∃ q : ℕ, q.Prime ∧ q ∣ blockProduct k n ∧ 221 * k < 50 * q

private lemma four_mul_five_pow_lt_six_pow {k : ℕ} (hk : 16 ≤ k) :
    4 * 5 ^ k < 6 ^ k := by
  refine Nat.le_induction ?base ?step k hk
  · norm_num
  · intro m hm ih
    calc
      4 * 5 ^ (m + 1) = 5 * (4 * 5 ^ m) := by ring
      _ < 5 * 6 ^ m := (Nat.mul_lt_mul_left (by norm_num : 0 < 5)).mpr ih
      _ < 6 * 6 ^ m :=
        (Nat.mul_lt_mul_right (Nat.pow_pos (by norm_num : 0 < 6))).mpr (by norm_num)
      _ = 6 ^ (m + 1) := by ring

/-- The upper ratio window forces `n > 4d` once `k >= 16` and `d >= k`. -/
lemma four_mul_gap_lt_n_of_ratio_window
    {k n d : ℕ} (hk : 16 ≤ k) (hd : k ≤ d)
    (hwin : (n + d + k) ^ k ≤ 4 * (n + k) ^ k) :
    4 * d < n := by
  by_contra hnot
  have hnle : n ≤ 4 * d := Nat.le_of_not_gt hnot
  have hlinear : 6 * (n + k) ≤ 5 * (n + d + k) := by omega
  have hpow := Nat.pow_le_pow_left hlinear k
  have hpow' : 6 ^ k * (n + k) ^ k ≤ 5 ^ k * (n + d + k) ^ k := by
    simpa [Nat.mul_pow, mul_assoc, mul_comm, mul_left_comm] using hpow
  have hcomb : 6 ^ k * (n + k) ^ k ≤ (4 * 5 ^ k) * (n + k) ^ k := by
    calc
      6 ^ k * (n + k) ^ k ≤ 5 ^ k * (n + d + k) ^ k := hpow'
      _ ≤ 5 ^ k * (4 * (n + k) ^ k) := Nat.mul_le_mul_left (5 ^ k) hwin
      _ = (4 * 5 ^ k) * (n + k) ^ k := by ring
  have hbase : 0 < (n + k) ^ k := Nat.pow_pos (by omega)
  have hcancel : 6 ^ k ≤ 4 * 5 ^ k := Nat.le_of_mul_le_mul_right hcomb hbase
  exact (Nat.not_lt_of_ge hcancel) (four_mul_five_pow_lt_six_pow hk)

/-- Equation-level version of `four_mul_gap_lt_n_of_ratio_window`. -/
lemma four_mul_gap_lt_n_of_four_solution
    {k n d : ℕ} (hk : 16 ≤ k) (hd : k ≤ d)
    (heq : blockProduct k (n + d) = 4 * blockProduct k n) :
    4 * d < n := by
  exact four_mul_gap_lt_n_of_ratio_window hk hd (ratio_window_four_nat heq).1

/-- Every lower-block term in a remaining `N=4` solution is composite: it is
larger than the common smoothness cap but all its prime factors are at most
that cap. -/
lemma lower_block_composite_of_four_solution
    {k n d i : ℕ} (hk : 5 ≤ k) (hd : k ≤ d)
    (hi : i ∈ Finset.Icc 1 k)
    (heq : blockProduct k (n + d) = 4 * blockProduct k n) :
    ¬ (n + i).Prime := by
  intro hprime
  have hsmooth := smooth_lower_block_four hk hd hi heq
  have hle : n + i ≤ d + k - 1 := hsmooth (n + i) hprime (dvd_refl (n + i))
  have hbelow := difference_block_below_n_of_four_solution hk hd heq
  have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
  omega

/-- Conditional, kernel-checked unbounded wedge supplied by the exact
`221/50` composite-block greatest-prime-factor theorem. -/
theorem no_gap_solution_large_k_near_diagonal_of_prime442
    (h442 : CompositeBlockPrime442Hypothesis)
    {k n d : ℕ} (hk : 25 ≤ k) (hd : k ≤ d)
    (hbudget : 50 * (d + k - 1) ≤ 221 * k) :
    blockProduct k (n + d) ≠ 4 * blockProduct k n := by
  intro heq
  have hk16 : 16 ≤ k := by omega
  have hk5 : 5 ≤ k := by omega
  have hn4 := four_mul_gap_lt_n_of_four_solution hk16 hd heq
  have hn100 : 100 < n + 1 := by omega
  have hcomposite : ∀ i, i ∈ Finset.Icc 1 k → ¬ (n + i).Prime := by
    intro i hi
    exact lower_block_composite_of_four_solution hk5 hd hi heq
  obtain ⟨q, hqprime, hqblock, hqbig⟩ := h442 k n hk hn100 hcomposite
  obtain ⟨i, hi, hqterm⟩ := (prime_dvd_blockProduct_iff hqprime).mp hqblock
  have hqle : q ≤ d + k - 1 :=
    lower_block_term_prime_le_difference_bound_four hk5 hd hi heq hqprime hqterm
  omega

end Erdos686Variant

end Erdos686
