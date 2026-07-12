/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import ErdosProblems.Erdos686LargeKWedge

/-!
# Erdős 686: the even row `k = 16`

This file tests the first genuinely large even row with the polynomial part
of the square root of the centered product.  Put

`S(W) = ∏_{1 ≤ j ≤ 8} (W²-(2j-1)²)`.

The integral polynomial part and its deficit are

`T(W) = W⁸-340W⁶+31926W⁴-862580W²-2167279`,

`D(W) = T(W)²-S(W)`.

At odd arguments `16384 ∣ T(W)`.  A hypothetical quotient-four solution
has odd centers `w,v`, satisfies `S(w)=4S(v)`, and hence the integer
`m=T(w)-2T(v)` obeys

`m(T(w)+2T(v)) = D(w)-4D(v)`.

The exact ratio window and `d ≥ 16` force `v ≥ 355`, after eight finite
boundary checks.  Shifted-coefficient inequalities then put
`-16384 < m < 0`, contradicting `16384 ∣ m`.
-/

namespace Erdos686

namespace Erdos686Variant

private def even16S (W : ℤ) : ℤ :=
  (W ^ 2 - 1) * (W ^ 2 - 9) * (W ^ 2 - 25) * (W ^ 2 - 49) *
    (W ^ 2 - 81) * (W ^ 2 - 121) * (W ^ 2 - 169) * (W ^ 2 - 225)

private def even16T (W : ℤ) : ℤ :=
  W ^ 8 - 340 * W ^ 6 + 31926 * W ^ 4 - 862580 * W ^ 2 - 2167279

private def even16D (W : ℤ) : ℤ :=
  2139095040 * W ^ 6 - 280506662912 * W ^ 4 +
    8679734640640 * W ^ 2 + 588267913216

private lemma even16_square_identity (W : ℤ) :
    even16T W ^ 2 = even16S W + even16D W := by
  simp only [even16T, even16S, even16D]
  ring

set_option maxHeartbeats 1000000 in
private lemma even16_centered_bridge (x : ℕ) :
    even16S (2 * (x : ℤ) + 17) = 65536 * (blockProduct 16 x : ℤ) := by
  have h := centeredBlockProduct_center 16 x
  norm_num [centeredBlockProduct, even16S, Finset.prod_Icc_succ_top,
    Finset.Icc_self, Finset.prod_singleton] at h ⊢
  ring_nf at h ⊢
  exact h

/-! The fixed divisor at odd arguments. -/

private def even16G (u : ℤ) : ℤ :=
  u ^ 4 - 42 * u ^ 3 + 483 * u ^ 2 - 1562 * u - 732

private lemma four_dvd_even16G (u : ℤ) : (4 : ℤ) ∣ even16G u := by
  rcases Int.even_or_odd u with ⟨z, hz⟩ | ⟨z, hz⟩
  · refine ⟨?_, ?_⟩
    · exact 4 * z ^ 4 - 84 * z ^ 3 + 483 * z ^ 2 - 781 * z - 183
    · rw [hz]
      simp only [even16G]
      ring
  · refine ⟨?_, ?_⟩
    · exact 4 * z ^ 4 - 76 * z ^ 3 + 363 * z ^ 2 - 359 * z - 463
    · rw [hz]
      simp only [even16G]
      ring

private lemma even16T_odd_fixed_divisor (a : ℤ) :
    (16384 : ℤ) ∣ even16T (2 * a + 1) := by
  rcases Int.even_or_odd a with ⟨z, hz⟩ | ⟨z, hz⟩
  · obtain ⟨q, hq⟩ := four_dvd_even16G (2 * z ^ 2 + z)
    refine ⟨q, ?_⟩
    rw [hz]
    calc
      even16T (2 * (z + z) + 1) =
          4096 * even16G (2 * z ^ 2 + z) := by
        simp only [even16T, even16G]
        ring
      _ = 16384 * q := by rw [hq]; ring
  · obtain ⟨q, hq⟩ := four_dvd_even16G (2 * z ^ 2 + 3 * z + 1)
    refine ⟨q, ?_⟩
    rw [hz]
    calc
      even16T (2 * (2 * z + 1) + 1) =
          4096 * even16G (2 * z ^ 2 + 3 * z + 1) := by
        simp only [even16T, even16G]
        ring
      _ = 16384 * q := by rw [hq]; ring

/-! Exact lower edge for the center. -/

private lemma even16_boundary_product (n : ℕ) (hnlo : 161 ≤ n)
    (hnhi : n ≤ 168) :
    4 * blockProduct 16 n < blockProduct 16 (n + 16) := by
  interval_cases n <;>
    norm_num [blockProduct, Finset.prod_Icc_succ_top, Finset.Icc_self,
      Finset.prod_singleton]

private lemma even16_base_ge_169 {n d : ℕ} (hd : 16 ≤ d)
    (hlin : 11 * (n + d + 16) < 12 * (n + 16))
    (heq : blockProduct 16 (n + d) = 4 * blockProduct 16 n) :
    169 ≤ n := by
  have hnlo : 161 ≤ n := by omega
  by_contra hnot
  have hnhi : n ≤ 168 := by omega
  have hbad := even16_boundary_product n hnlo hnhi
  have hmono := blockProduct_mono 16 (n + 16) (n + d) (by omega)
  rw [heq] at hmono
  omega

/-! Shifted-coefficient inequalities. -/

private lemma even16_T_pos {W : ℤ} (hW : 355 ≤ W) : 0 < even16T W := by
  obtain ⟨a, ha, rfl⟩ : ∃ a : ℤ, 0 ≤ a ∧ W = 355 + a :=
    ⟨W - 355, by omega, by omega⟩
  simp only [even16T]
  nlinarith [ha, pow_nonneg ha 2, pow_nonneg ha 3, pow_nonneg ha 4,
    pow_nonneg ha 5, pow_nonneg ha 6, pow_nonneg ha 7, pow_nonneg ha 8]

private lemma even16_D_pos {W : ℤ} (hW : 355 ≤ W) : 0 < even16D W := by
  obtain ⟨a, ha, rfl⟩ : ∃ a : ℤ, 0 ≤ a ∧ W = 355 + a :=
    ⟨W - 355, by omega, by omega⟩
  simp only [even16D]
  nlinarith [ha, pow_nonneg ha 2, pow_nonneg ha 3, pow_nonneg ha 4,
    pow_nonneg ha 5, pow_nonneg ha 6]

private lemma even16_delta_lower {v w : ℤ} (hv : 355 ≤ v)
    (hvw : v + 32 ≤ w) :
    0 < even16D w + 16384 * even16T w + 32768 * even16T v -
      4 * even16D v := by
  obtain ⟨a, ha, rfl⟩ : ∃ a : ℤ, 0 ≤ a ∧ v = 355 + a :=
    ⟨v - 355, by omega, by omega⟩
  obtain ⟨b, hb, rfl⟩ : ∃ b : ℤ, 0 ≤ b ∧ w = 355 + a + 32 + b :=
    ⟨w - (355 + a + 32), by omega, by omega⟩
  simp only [even16D, even16T]
  nlinarith [ha, hb,
    pow_nonneg ha 2, pow_nonneg ha 3, pow_nonneg ha 4,
    pow_nonneg ha 5, pow_nonneg ha 6, pow_nonneg ha 7, pow_nonneg ha 8,
    pow_nonneg hb 2, pow_nonneg hb 3, pow_nonneg hb 4,
    pow_nonneg hb 5, pow_nonneg hb 6, pow_nonneg hb 7, pow_nonneg hb 8,
    mul_nonneg ha hb]

private lemma even16_leading_delta {v : ℤ} (hv : 355 ≤ v) :
    2139095040 * 46656 * v ^ 6 +
        62500 * 280506662912 * v ^ 4 <
      62500 * 2139095040 * v ^ 6 := by
  obtain ⟨a, ha, rfl⟩ : ∃ a : ℤ, 0 ≤ a ∧ v = 355 + a :=
    ⟨v - 355, by omega, by omega⟩
  nlinarith [ha, pow_nonneg ha 2, pow_nonneg ha 3, pow_nonneg ha 4,
    pow_nonneg ha 5, pow_nonneg ha 6]

private lemma even16_delta_negative {v w : ℤ} (hv : 355 ≤ v)
    (hw : 0 ≤ w) (hupper : 5 * w ≤ 6 * v) :
    even16D w - 4 * even16D v < 0 := by
  have h6 : (5 * w) ^ 6 ≤ (6 * v) ^ 6 :=
    pow_le_pow_left₀ (by omega) hupper 6
  have h2 : w ^ 2 ≤ 4 * v ^ 2 := by nlinarith [sq_nonneg (2 * v - w)]
  have hw4 : 0 ≤ w ^ 4 := pow_nonneg hw 4
  have hlead := even16_leading_delta hv
  simp only [even16D]
  ring_nf at h6
  nlinarith

/-- There is no quotient-four gap solution in the first large even row
`k=16`, already without using the smoothness hypothesis. -/
theorem no_gap_solution_four_even_sixteen {n d : ℕ} (hd : 16 ≤ d) :
    blockProduct 16 (n + d) ≠ 4 * blockProduct 16 n := by
  intro heq
  obtain ⟨hup, _hlo⟩ := ratio_window_four_nat heq
  have hlin :=
    ratio_window_linearize_of_pow_bracket (N := 4) (A := 12) (B := 11)
      (k := 16) (n := n) (d := d) (by norm_num) (by norm_num) hup
  have hn169 : 169 ≤ n := even16_base_ge_169 hd hlin heq
  have hZ : ((blockProduct 16 (n + d) : ℕ) : ℤ) =
      4 * ((blockProduct 16 n : ℕ) : ℤ) := by exact_mod_cast heq
  let w : ℤ := 2 * ((n : ℤ) + (d : ℤ)) + 17
  let v : ℤ := 2 * (n : ℤ) + 17
  have hv : 355 ≤ v := by dsimp [v]; omega
  have hw : 355 ≤ w := by dsimp [w]; omega
  have hvw : v + 32 ≤ w := by dsimp [v, w]; omega
  have hupper : 5 * w ≤ 6 * v := by dsimp [v, w]; omega
  have hs1 := even16_centered_bridge (n + d)
  have hs2 := even16_centered_bridge n
  have hcw : 2 * ((n + d : ℕ) : ℤ) + 17 = w := by
    dsimp [w]
  have hcv : 2 * (n : ℤ) + 17 = v := by rfl
  rw [hcw] at hs1
  rw [hcv] at hs2
  have hS : even16S w = 4 * even16S v := by
    rw [hs1, hs2, hZ]
    ring
  let m := even16T w - 2 * even16T v
  let X := even16T w + 2 * even16T v
  have hTw : 0 < even16T w := even16_T_pos hw
  have hTv : 0 < even16T v := even16_T_pos hv
  have hXpos : 0 < X := by dsimp [X]; linarith
  have hmX : m * X = even16D w - 4 * even16D v := by
    dsimp [m, X]
    calc
      (even16T w - 2 * even16T v) * (even16T w + 2 * even16T v) =
          even16T w ^ 2 - 4 * even16T v ^ 2 := by ring
      _ = (even16S w + even16D w) -
          4 * (even16S v + even16D v) := by
        rw [even16_square_identity, even16_square_identity]
      _ = even16D w - 4 * even16D v := by rw [hS]; ring
  have hdeltaNeg : even16D w - 4 * even16D v < 0 :=
    even16_delta_negative hv (by omega) hupper
  have hdeltaLower : -16384 * X < even16D w - 4 * even16D v := by
    have h := even16_delta_lower hv hvw
    dsimp [X]
    linarith
  have hmneg : m < 0 := by
    by_contra hnot
    have := mul_nonneg (not_lt.mp hnot) hXpos.le
    rw [hmX] at this
    linarith
  have hmgt : -16384 < m := by
    by_contra hnot
    have hmul := mul_le_mul_of_nonneg_right (not_lt.mp hnot) hXpos.le
    rw [hmX] at hmul
    linarith
  have hmw := even16T_odd_fixed_divisor ((n : ℤ) + (d : ℤ) + 8)
  have hmv := even16T_odd_fixed_divisor ((n : ℤ) + 8)
  have hwodd : 2 * ((n : ℤ) + (d : ℤ) + 8) + 1 = w := by
    dsimp [w]
    ring
  have hvodd : 2 * ((n : ℤ) + 8) + 1 = v := by
    dsimp [v]
    ring
  rw [hwodd] at hmw
  rw [hvodd] at hmv
  have hmdiv : (16384 : ℤ) ∣ m := by
    dsimp [m]
    exact dvd_sub hmw (hmv.mul_left 2)
  obtain ⟨q, hq⟩ := hmdiv
  omega

#print axioms no_gap_solution_four_even_sixteen

end Erdos686Variant

end Erdos686
