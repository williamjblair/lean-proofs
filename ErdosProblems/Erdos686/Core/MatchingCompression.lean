/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import ErdosProblems.Erdos686.Core.PadicLift
import ErdosProblems.Erdos686.Core.LargeKWedge

/-!
# Erdős Problem 686: multiplicative owner compression

This module packages two multiplicative ownership consequences.  The full row
system gives a two-factorial lcm compression.  Matching maximum-valuation
owners directly between the two blocks of the equation improves this to one
factorial.
-/

namespace Erdos686

namespace Erdos686Variant

/-- The lcm of the `2*k-1` possible shifted differences
`d-(k-1), ..., d+(k-1)`. -/
def centeredDiffLcm (k d : ℕ) : ℕ :=
  (Finset.Icc 0 (2 * k - 2)).lcm (fun h => d + h - (k - 1))

lemma centeredDiffLcm_ne_zero {k d : ℕ} (hk : 1 ≤ k) (hd : k ≤ d) :
    centeredDiffLcm k d ≠ 0 := by
  intro hzero
  unfold centeredDiffLcm at hzero
  rw [Finset.lcm_eq_zero_iff] at hzero
  rcases hzero with ⟨h, hh, hfactor⟩
  have hh' := Finset.mem_Icc.mp hh
  have hpos : 0 < d + h - (k - 1) := by omega
  omega

/-- Every shifted difference in a row is one of the factors defining the
centered-difference lcm. -/
lemma shiftedDiffTerm_dvd_centeredDiffLcm
    {k d i j : ℕ} (hd : k ≤ d)
    (hi : i ∈ Finset.Icc 1 k) (hj : j ∈ Finset.Icc 1 k) :
    d + j - i ∣ centeredDiffLcm k d := by
  let h : ℕ := k + j - i - 1
  have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
  have hik : i ≤ k := (Finset.mem_Icc.mp hi).2
  have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
  have hjk : j ≤ k := (Finset.mem_Icc.mp hj).2
  have hh : h ∈ Finset.Icc 0 (2 * k - 2) := by
    rw [Finset.mem_Icc]
    dsimp [h]
    omega
  have hdvd : d + h - (k - 1) ∣ centeredDiffLcm k d := by
    unfold centeredDiffLcm
    exact Finset.dvd_lcm hh
  convert hdvd using 1
  dsimp [h]
  omega

/-- Multiplicative ownership compression.  If every lower factor divides its
localized shifted-difference row, then the complete lower block divides the
single centered lcm after allowing two universal consecutive-block losses. -/
theorem blockProduct_dvd_factorial_sq_mul_centeredDiffLcm_of_individual_skeleton
    {k n d : ℕ} (hk : 1 ≤ k) (hd : k ≤ d)
    (hall : ∀ i, i ∈ Finset.Icc 1 k →
      n + i ∣ shiftedDiffProductAt k d i) :
    blockProduct k n ∣ (k - 1).factorial ^ 2 * centeredDiffLcm k d := by
  have hblock0 : blockProduct k n ≠ 0 := by
    exact ne_of_gt (blockProduct_pos k n)
  have hlcm0 : centeredDiffLcm k d ≠ 0 :=
    centeredDiffLcm_ne_zero hk hd
  have hrhs0 : (k - 1).factorial ^ 2 * centeredDiffLcm k d ≠ 0 :=
    mul_ne_zero (pow_ne_zero 2 (Nat.factorial_ne_zero _)) hlcm0
  apply (Nat.factorization_le_iff_dvd hblock0 hrhs0).mp
  intro p
  by_cases hp : p.Prime
  · obtain ⟨i, hi, hblockConcentration⟩ :=
      exists_blockProduct_factorization_concentration hp hk (n := n)
    have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
    have hik : i ≤ k := (Finset.mem_Icc.mp hi).2
    have hid : i ≤ d := le_trans hik hd
    have hrow : n + i ∣ blockProduct k (d - i) := by
      rw [← shiftedDiffProductAt_eq_blockProduct
        (k := k) (d := d) (j := i) hid]
      exact hall i hi
    have hni0 : n + i ≠ 0 := by omega
    have hrowBlock0 : blockProduct k (d - i) ≠ 0 :=
      ne_of_gt (blockProduct_pos k (d - i))
    have hownerToRow :
        (n + i).factorization p ≤
          (blockProduct k (d - i)).factorization p :=
      ((Nat.factorization_le_iff_dvd hni0 hrowBlock0).mpr hrow) p
    obtain ⟨j, hj, hrowConcentration⟩ :=
      exists_blockProduct_factorization_concentration hp hk (n := d - i)
    have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
    have hterm0 : d - i + j ≠ 0 := by omega
    have htermDvd : d - i + j ∣ centeredDiffLcm k d := by
      have hdvd := shiftedDiffTerm_dvd_centeredDiffLcm hd hi hj
      convert hdvd using 1
      omega
    have htermToLcm :
        (d - i + j).factorization p ≤
          (centeredDiffLcm k d).factorization p :=
      ((Nat.factorization_le_iff_dvd hterm0 hlcm0).mpr htermDvd) p
    have hvaluation :
        (blockProduct k n).factorization p ≤
          (centeredDiffLcm k d).factorization p +
            2 * (k - 1).factorial.factorization p := by
      omega
    calc
      (blockProduct k n).factorization p
          ≤ (centeredDiffLcm k d).factorization p +
              2 * (k - 1).factorial.factorization p := hvaluation
      _ = ((k - 1).factorial ^ 2 * centeredDiffLcm k d).factorization p := by
        rw [Nat.factorization_mul
          (pow_ne_zero 2 (Nat.factorial_ne_zero _)) hlcm0,
          Nat.factorization_pow]
        simp [add_comm, mul_comm]
  · simp [Nat.factorization_eq_zero_of_not_prime _ hp]

private lemma four_mul_k_add_five_pow_lt_k_add_ten_pow
    {k : ℕ} (hk : 16 ≤ k) :
    4 * (k + 5) ^ k < (k + 10) ^ k := by
  let a : ℚ := 5 / (k + 5 : ℚ)
  have ha : (-2 : ℚ) ≤ a := by
    have ha0 : (0 : ℚ) ≤ a := by
      dsimp [a]
      positivity
    linarith
  have hbern : (1 : ℚ) + k * a ≤ (1 + a) ^ k :=
    one_add_mul_le_pow ha k
  have hlinear : (4 : ℚ) < 1 + k * a := by
    dsimp [a]
    have hkq : (15 : ℚ) < 2 * k := by exact_mod_cast (by omega : 15 < 2 * k)
    have hden : (0 : ℚ) < k + 5 := by positivity
    rw [show (1 : ℚ) + (k : ℚ) * (5 / (k + 5 : ℚ)) =
        (6 * k + 5) / (k + 5) by field_simp; ring]
    rw [lt_div_iff₀ hden]
    nlinarith
  have hratio : (4 : ℚ) < (((k : ℚ) + 10) / ((k : ℚ) + 5)) ^ k := by
    calc
      (4 : ℚ) < 1 + k * a := hlinear
      _ ≤ (1 + a) ^ k := hbern
      _ = (((k : ℚ) + 10) / ((k : ℚ) + 5)) ^ k := by
        congr 1
        dsimp [a]
        field_simp
        ring
  have hdenPow : (0 : ℚ) < (((k : ℚ) + 5) ^ k) := by positivity
  rw [div_pow] at hratio
  have hcross : (4 : ℚ) * ((k : ℚ) + 5) ^ k < ((k : ℚ) + 10) ^ k :=
    (lt_div_iff₀ hdenPow).mp hratio
  exact_mod_cast hcross

/-- The ratio window grows linearly with `k`: every separated `N=4`
large-`k` solution satisfies `k*d < 5*n`. -/
lemma k_mul_gap_lt_five_mul_n_of_ratio_window
    {k n d : ℕ} (hk : 16 ≤ k) (hd : k ≤ d)
    (hwin : (n + d + k) ^ k ≤ 4 * (n + k) ^ k) :
    k * d < 5 * n := by
  by_contra hnot
  have hnle : 5 * n ≤ k * d := Nat.le_of_not_gt hnot
  have hlinear : (k + 10) * (n + k) ≤ (k + 5) * (n + d + k) := by
    nlinarith
  have hpow := Nat.pow_le_pow_left hlinear k
  have hpow' :
      (k + 10) ^ k * (n + k) ^ k ≤
        (k + 5) ^ k * (n + d + k) ^ k := by
    simpa [Nat.mul_pow, mul_assoc, mul_comm, mul_left_comm] using hpow
  have hcomb :
      (k + 10) ^ k * (n + k) ^ k ≤
        (4 * (k + 5) ^ k) * (n + k) ^ k := by
    calc
      (k + 10) ^ k * (n + k) ^ k
          ≤ (k + 5) ^ k * (n + d + k) ^ k := hpow'
      _ ≤ (k + 5) ^ k * (4 * (n + k) ^ k) :=
        Nat.mul_le_mul_left ((k + 5) ^ k) hwin
      _ = (4 * (k + 5) ^ k) * (n + k) ^ k := by ring
  have hbase : 0 < (n + k) ^ k := Nat.pow_pos (by omega)
  have hcancel : (k + 10) ^ k ≤ 4 * (k + 5) ^ k :=
    Nat.le_of_mul_le_mul_right hcomb hbase
  exact (Nat.not_lt_of_ge hcancel)
    (four_mul_k_add_five_pow_lt_k_add_ten_pow hk)

lemma k_mul_gap_lt_five_mul_n_of_four_solution
    {k n d : ℕ} (hk : 16 ≤ k) (hd : k ≤ d)
    (heq : blockProduct k (n + d) = 4 * blockProduct k n) :
    k * d < 5 * n := by
  exact k_mul_gap_lt_five_mul_n_of_ratio_window hk hd
    (ratio_window_four_nat heq).1

/-- Equation-level specialization of multiplicative ownership compression. -/
theorem blockProduct_dvd_factorial_sq_mul_centeredDiffLcm_four
    {k n d : ℕ} (hk : 1 ≤ k) (hd : k ≤ d)
    (heq : blockProduct k (n + d) = 4 * blockProduct k n) :
    blockProduct k n ∣ (k - 1).factorial ^ 2 * centeredDiffLcm k d := by
  apply blockProduct_dvd_factorial_sq_mul_centeredDiffLcm_of_individual_skeleton hk hd
  intro i hi
  exact individual_divisor_skeleton_four hd hi heq

/-- Stronger equation-level matching compression.  The equation supplies a
maximum-valuation owner in each block.  Matching those two owners directly
costs only one copy of `(k-1)!`, including for primes at most `k`. -/
theorem blockProduct_dvd_factorial_mul_centeredDiffLcm_four
    {k n d : ℕ} (hk : 1 ≤ k) (hd : k ≤ d)
    (heq : blockProduct k (n + d) = 4 * blockProduct k n) :
    blockProduct k n ∣ (k - 1).factorial * centeredDiffLcm k d := by
  have hlower0 : blockProduct k n ≠ 0 :=
    ne_of_gt (blockProduct_pos k n)
  have hupper0 : blockProduct k (n + d) ≠ 0 :=
    ne_of_gt (blockProduct_pos k (n + d))
  have hlcm0 : centeredDiffLcm k d ≠ 0 :=
    centeredDiffLcm_ne_zero hk hd
  have hrhs0 : (k - 1).factorial * centeredDiffLcm k d ≠ 0 :=
    mul_ne_zero (Nat.factorial_ne_zero _) hlcm0
  have hlowerDvdUpper : blockProduct k n ∣ blockProduct k (n + d) := by
    rw [heq]
    exact dvd_mul_of_dvd_right (dvd_refl (blockProduct k n)) 4
  apply (Nat.factorization_le_iff_dvd hlower0 hrhs0).mp
  intro p
  by_cases hp : p.Prime
  · obtain ⟨i, hi, hlowerConcentration⟩ :=
      exists_blockProduct_factorization_concentration hp hk (n := n)
    obtain ⟨j, hj, hupperConcentration⟩ :=
      exists_blockProduct_factorization_concentration hp hk (n := n + d)
    have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
    have hik : i ≤ k := (Finset.mem_Icc.mp hi).2
    have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
    have hupperVal :
        (blockProduct k n).factorization p ≤
          (blockProduct k (n + d)).factorization p :=
      ((Nat.factorization_le_iff_dvd hlower0 hupper0).mpr hlowerDvdUpper) p
    let e : ℕ :=
      (blockProduct k n).factorization p -
        (k - 1).factorial.factorization p
    have heLower : e ≤ (n + i).factorization p := by
      dsimp [e]
      omega
    have heUpper : e ≤ (n + d + j).factorization p := by
      have hupperTermEq : n + d + j = (n + d) + j := by omega
      rw [hupperTermEq]
      dsimp [e]
      omega
    have hlowerTerm0 : n + i ≠ 0 := by omega
    have hupperTerm0 : n + d + j ≠ 0 := by omega
    have hpowLower : p ^ e ∣ n + i :=
      (hp.pow_dvd_iff_le_factorization hlowerTerm0).mpr heLower
    have hpowUpper : p ^ e ∣ n + d + j :=
      (hp.pow_dvd_iff_le_factorization hupperTerm0).mpr heUpper
    have hlowerLeUpper : n + i ≤ n + d + j := by omega
    have hpowDiff : p ^ e ∣ d + j - i := by
      have hsub := Nat.dvd_sub hpowUpper hpowLower
      have hdiffEq : (n + d + j) - (n + i) = d + j - i := by omega
      rwa [hdiffEq] at hsub
    have hdiffDvdLcm : d + j - i ∣ centeredDiffLcm k d :=
      shiftedDiffTerm_dvd_centeredDiffLcm hd hi hj
    have hpowLcm : p ^ e ∣ centeredDiffLcm k d :=
      dvd_trans hpowDiff hdiffDvdLcm
    have heLcm : e ≤ (centeredDiffLcm k d).factorization p :=
      (hp.pow_dvd_iff_le_factorization hlcm0).mp hpowLcm
    have hvaluation :
        (blockProduct k n).factorization p ≤
          (k - 1).factorial.factorization p +
            (centeredDiffLcm k d).factorization p := by
      dsimp [e] at heLcm
      omega
    calc
      (blockProduct k n).factorization p
          ≤ (k - 1).factorial.factorization p +
              (centeredDiffLcm k d).factorization p := hvaluation
      _ = ((k - 1).factorial * centeredDiffLcm k d).factorization p := by
        rw [Nat.factorization_mul (Nat.factorial_ne_zero _) hlcm0,
          Finsupp.add_apply]
  · simp [Nat.factorization_eq_zero_of_not_prime _ hp]

/-- `k`-scaled transition inequality.  This is stronger than the fixed
`9*d` transition once `k>45` and retains the exact one-factorial matching
loss. -/
theorem k_gap_pow_lt_five_pow_mul_factorial_mul_centeredDiffLcm_four
    {k n d : ℕ} (hk : 16 ≤ k) (hd : k ≤ d)
    (heq : blockProduct k (n + d) = 4 * blockProduct k n) :
    (k * d) ^ k <
      5 ^ k * ((k - 1).factorial * centeredDiffLcm k d) := by
  have hkn : k * d < 5 * n :=
    k_mul_gap_lt_five_mul_n_of_four_solution hk hd heq
  have hterm : ∀ i ∈ Finset.Icc 1 k, k * d < 5 * (n + i) := by
    intro i hi
    omega
  have hprodLt :
      (∏ i ∈ Finset.Icc 1 k, k * d) <
        ∏ i ∈ Finset.Icc 1 k, 5 * (n + i) := by
    apply Finset.prod_lt_prod
    · intro i hi
      have hdpos : 0 < d := by omega
      exact mul_pos (by omega) hdpos
    · intro i hi
      exact le_of_lt (hterm i hi)
    · exact ⟨1, Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩, hterm 1
        (Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩)⟩
  have hcard : (Finset.Icc 1 k).card = k := by
    rw [Nat.card_Icc]
    omega
  have hblockLt : (k * d) ^ k < 5 ^ k * blockProduct k n := by
    simpa [blockProduct, Finset.prod_const, hcard, Finset.prod_mul_distrib] using hprodLt
  have hdvd := blockProduct_dvd_factorial_mul_centeredDiffLcm_four
    (k := k) (n := n) (d := d) (by omega) hd heq
  have hrhsPos : 0 < (k - 1).factorial * centeredDiffLcm k d := by
    exact mul_pos (Nat.factorial_pos _)
      (Nat.pos_of_ne_zero (centeredDiffLcm_ne_zero (by omega) hd))
  have hblockLe : blockProduct k n ≤
      (k - 1).factorial * centeredDiffLcm k d :=
    Nat.le_of_dvd hrhsPos hdvd
  exact lt_of_lt_of_le hblockLt (Nat.mul_le_mul_left (5 ^ k) hblockLe)

/-- Exact transition inequality: an `N=4`, `k>=16` solution forces the
centered-difference lcm to carry more than `(9*d)^k` after the single
factorial loss. -/
theorem nine_gap_pow_lt_factorial_mul_centeredDiffLcm_four
    {k n d : ℕ} (hk : 16 ≤ k) (hd : k ≤ d)
    (heq : blockProduct k (n + d) = 4 * blockProduct k n) :
    (9 * d) ^ k < (k - 1).factorial * centeredDiffLcm k d := by
  have hn9 : 9 * d < n := nine_mul_gap_lt_n_of_four_solution hk hd heq
  have hdpos : 0 < d := by omega
  have hterm : ∀ i ∈ Finset.Icc 1 k, (9 * d) < n + i := by
    intro i hi
    omega
  have hprodLt :
      (∏ i ∈ Finset.Icc 1 k, 9 * d) <
        ∏ i ∈ Finset.Icc 1 k, (n + i) := by
    apply Finset.prod_lt_prod
    · intro i hi
      exact mul_pos (by norm_num) hdpos
    · intro i hi
      exact le_of_lt (hterm i hi)
    · exact ⟨1, Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩, hterm 1
        (Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩)⟩
  have hcard : (Finset.Icc 1 k).card = k := by
    rw [Nat.card_Icc]
    omega
  have hblockLt : (9 * d) ^ k < blockProduct k n := by
    simpa [blockProduct, Finset.prod_const, hcard] using hprodLt
  have hdvd := blockProduct_dvd_factorial_mul_centeredDiffLcm_four
    (k := k) (n := n) (d := d) (by omega) hd heq
  have hrhsPos : 0 < (k - 1).factorial * centeredDiffLcm k d := by
    exact mul_pos (Nat.factorial_pos _)
      (Nat.pos_of_ne_zero (centeredDiffLcm_ne_zero (by omega) hd))
  have hblockLe : blockProduct k n ≤
      (k - 1).factorial * centeredDiffLcm k d :=
    Nat.le_of_dvd hrhsPos hdvd
  exact lt_of_lt_of_le hblockLt hblockLe

end Erdos686Variant

end Erdos686
