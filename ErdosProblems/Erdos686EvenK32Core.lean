/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import ErdosProblems.Erdos686EvenK32FiniteStrip
import ErdosProblems.Erdos686EvenK32CandidateDefs

/-!
# Erdős 686: arithmetic core for the even row `k=32`

The proof splits at `d=128`.  The lower strip is a finite ordinary-kernel
certificate.  Above the split, an integral square-root polynomial traps its
error at `-1388955148309984 < m < 0`, while `3221225472 ∣ m`.
-/

namespace Erdos686
namespace Erdos686Variant

private abbrev even32S {R : Type} [CommRing R] (W : R) : R := evenTable32S W
private abbrev even32T {R : Type} [CommRing R] (W : R) : R := evenTable32T W

private def even32D (W : ℤ) : ℤ :=
  82747982211764142997504 * W ^ 14 -
    149323133602525446120931328 * W ^ 12 +
    100714780617924037893859311616 * W ^ 10 -
    31725719087519879657985757151232 * W ^ 8 +
    4807552178413097889258132964638720 * W ^ 6 -
    312266646810607902726297446674071552 * W ^ 4 +
    11577795560708127373619129466319011840 * W ^ 2 +
    1974692912846687924817127587954227675136

private lemma even32_square_identity (W : ℤ) :
    even32T W ^ 2 = even32S W + even32D W := by
  simp only [even32T, even32S, even32D, evenTable32T, evenTable32S]
  ring

set_option maxHeartbeats 5000000 in
-- Expansion of the sixteen centered quadratic factors.
private lemma even32_centered_poly (W : ℤ) :
    even32S W = centeredBlockProduct 32 W := by
  norm_num [centeredBlockProduct, even32S, evenTable32S,
    Finset.prod_Icc_succ_top, Finset.Icc_self, Finset.prod_singleton]
  ring

set_option maxHeartbeats 1000000 in
-- The centered product rescales the original block by `2^32`.
private lemma even32_centered_bridge (x : ℕ) :
    even32S (2 * (x : ℤ) + 33) =
      4294967296 * (blockProduct 32 x : ℤ) := by
  rw [even32_centered_poly]
  convert centeredBlockProduct_center 32 x using 1 <;> norm_num

private def even32H (u : ℤ) : ℤ :=
  u ^ 8 - 340 * u ^ 7 + 44778 * u ^ 6 - 2913392 * u ^ 5 +
    98931449 * u ^ 4 - 1706548332 * u ^ 3 + 13105771036 * u ^ 2 -
    58519363024 * u - 2656230164928

private lemma even32_H_even_mode_dvd_64 (z : ℤ) :
    (64 : ℤ) ∣ even32H (z * (2 * z + 1)) := by
  have hz : ((even32H (z * (2 * z + 1)) : ℤ) : ZMod 64) = 0 := by
    have hall : ∀ y : ZMod 64,
        y ^ 8 - 340 * y ^ 7 + 44778 * y ^ 6 - 2913392 * y ^ 5 +
          98931449 * y ^ 4 - 1706548332 * y ^ 3 + 13105771036 * y ^ 2 -
          58519363024 * y - 2656230164928 = 0 := by decide
    simpa [even32H] using hall ((z : ZMod 64) * (2 * (z : ZMod 64) + 1))
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ 64).mp hz

private lemma even32_H_odd_mode_dvd_64 (z : ℤ) :
    (64 : ℤ) ∣ even32H ((2 * z + 1) * (z + 1)) := by
  have hz : ((even32H ((2 * z + 1) * (z + 1)) : ℤ) : ZMod 64) = 0 := by
    have hall : ∀ y : ZMod 64,
        y ^ 8 - 340 * y ^ 7 + 44778 * y ^ 6 - 2913392 * y ^ 5 +
          98931449 * y ^ 4 - 1706548332 * y ^ 3 + 13105771036 * y ^ 2 -
          58519363024 * y - 2656230164928 = 0 := by decide
    simpa [even32H] using hall (((2 * (z : ZMod 64) + 1) * ((z : ZMod 64) + 1)))
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ 64).mp hz

private lemma even32_T_dvd_1073741824_at_odd (a : ℤ) :
    (1073741824 : ℤ) ∣ even32T (2 * a + 1) := by
  rcases Int.even_or_odd a with ⟨z, hz⟩ | ⟨z, hz⟩
  · obtain ⟨q, hq⟩ := even32_H_even_mode_dvd_64 z
    refine ⟨q, ?_⟩
    rw [hz]
    have hid : even32T (2 * (z + z) + 1) =
        16777216 * even32H (z * (2 * z + 1)) := by
      simp only [even32T, evenTable32T, even32H]
      ring
    rw [hid, hq]
    ring
  · obtain ⟨q, hq⟩ := even32_H_odd_mode_dvd_64 z
    refine ⟨q, ?_⟩
    rw [hz]
    have hid : even32T (2 * (2 * z + 1) + 1) =
        16777216 * even32H ((2 * z + 1) * (z + 1)) := by
      simp only [even32T, evenTable32T, even32H]
      ring
    rw [hid, hq]
    ring

private lemma even32_T_dvd_3 (x : ℤ) : (3 : ℤ) ∣ even32T x := by
  have hx : ((even32T x : ℤ) : ZMod 3) = 0 := by
    have hall : ∀ y : ZMod 3,
        y ^ 16 - 2728 * y ^ 14 + 2884860 * y ^ 12 -
          1508908632 * y ^ 10 + 412724580774 * y ^ 8 -
          57556042581528 * y ^ 6 + 3605806068591804 * y ^ 4 -
          129764586585016680 * y ^ 2 - 44437931297372228319 = 0 := by decide
    simpa [even32T, evenTable32T] using hall (x : ZMod 3)
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mp hx

private lemma even32_T_fixed_divisor (a : ℤ) :
    (3221225472 : ℤ) ∣ even32T (2 * a + 1) := by
  have h2 := even32_T_dvd_1073741824_at_odd a
  have h3 := even32_T_dvd_3 (2 * a + 1)
  have hcop : IsCoprime (1073741824 : ℤ) 3 :=
    ⟨1, -357913941, by norm_num⟩
  simpa using hcop.mul_dvd h2 h3

private lemma even32_T_pos {W : ℤ} (hW : 5603 ≤ W) : 0 < even32T W := by
  obtain ⟨a, ha, rfl⟩ : ∃ a : ℤ, 0 ≤ a ∧ W = 5603 + a :=
    ⟨W - 5603, by omega, by omega⟩
  simp only [even32T, evenTable32T]
  nlinarith [ha, pow_nonneg ha 2, pow_nonneg ha 3, pow_nonneg ha 4,
    pow_nonneg ha 5, pow_nonneg ha 6, pow_nonneg ha 7,
    pow_nonneg ha 8, pow_nonneg ha 9, pow_nonneg ha 10,
    pow_nonneg ha 11, pow_nonneg ha 12, pow_nonneg ha 13,
    pow_nonneg ha 14, pow_nonneg ha 15, pow_nonneg ha 16]

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 1000000 in
-- All 153 shifted coefficients are positive on the large-gap cone.
private lemma even32_delta_lower {v w : ℤ} (hv : 5603 ≤ v)
    (hvw : v + 256 ≤ w) :
    0 < even32D w + 1388955148309984 * even32T w +
      2777910296619968 * even32T v - 4 * even32D v := by
  obtain ⟨a, ha, rfl⟩ : ∃ a : ℤ, 0 ≤ a ∧ v = 5603 + a :=
    ⟨v - 5603, by omega, by omega⟩
  obtain ⟨b, hb, rfl⟩ : ∃ b : ℤ, 0 ≤ b ∧ w = 5603 + a + 256 + b :=
    ⟨w - (5603 + a + 256), by omega, by omega⟩
  simp only [even32D, even32T, evenTable32T]
  nlinarith [ha, hb,
    pow_nonneg ha 2, pow_nonneg ha 3, pow_nonneg ha 4,
    pow_nonneg ha 5, pow_nonneg ha 6, pow_nonneg ha 7,
    pow_nonneg ha 8, pow_nonneg ha 9, pow_nonneg ha 10,
    pow_nonneg ha 11, pow_nonneg ha 12, pow_nonneg ha 13,
    pow_nonneg ha 14, pow_nonneg ha 15, pow_nonneg ha 16,
    pow_nonneg hb 2, pow_nonneg hb 3, pow_nonneg hb 4,
    pow_nonneg hb 5, pow_nonneg hb 6, pow_nonneg hb 7,
    pow_nonneg hb 8, pow_nonneg hb 9, pow_nonneg hb 10,
    pow_nonneg hb 11, pow_nonneg hb 12, pow_nonneg hb 13,
    pow_nonneg hb 14, pow_nonneg hb 15, pow_nonneg hb 16,
    mul_nonneg ha hb]

set_option maxHeartbeats 5000000 in
-- Conservative termwise upper bound after `22*w ≤ 23*v`.
private lemma even32_negative_upper {v : ℤ} (hv : 5603 ≤ v) :
    (82747982211764142997504 * 23 ^ 14 -
        4 * 82747982211764142997504 * 22 ^ 14) * v ^ 14 +
      4 * 149323133602525446120931328 * 22 ^ 14 * v ^ 12 +
      100714780617924037893859311616 * 22 ^ 4 * 23 ^ 10 * v ^ 10 +
      4 * 31725719087519879657985757151232 * 22 ^ 14 * v ^ 8 +
      4807552178413097889258132964638720 * 22 ^ 8 * 23 ^ 6 * v ^ 6 +
      4 * 312266646810607902726297446674071552 * 22 ^ 14 * v ^ 4 +
      11577795560708127373619129466319011840 * 22 ^ 12 * 23 ^ 2 * v ^ 2 < 0 := by
  obtain ⟨a, ha, rfl⟩ : ∃ a : ℤ, 0 ≤ a ∧ v = 5603 + a :=
    ⟨v - 5603, by omega, by omega⟩
  nlinarith [ha, pow_nonneg ha 2, pow_nonneg ha 3, pow_nonneg ha 4,
    pow_nonneg ha 5, pow_nonneg ha 6, pow_nonneg ha 7,
    pow_nonneg ha 8, pow_nonneg ha 9, pow_nonneg ha 10,
    pow_nonneg ha 11, pow_nonneg ha 12, pow_nonneg ha 13,
    pow_nonneg ha 14]

private lemma even32_delta_negative {v w : ℤ} (hv : 5603 ≤ v)
    (hw : 0 ≤ w) (hupper : 22 * w ≤ 23 * v) :
    even32D w - 4 * even32D v < 0 := by
  have h14 : (22 * w) ^ 14 ≤ (23 * v) ^ 14 :=
    pow_le_pow_left₀ (by omega) hupper 14
  have h10 : (22 * w) ^ 10 ≤ (23 * v) ^ 10 :=
    pow_le_pow_left₀ (by omega) hupper 10
  have h6 : (22 * w) ^ 6 ≤ (23 * v) ^ 6 :=
    pow_le_pow_left₀ (by omega) hupper 6
  have h2 : (22 * w) ^ 2 ≤ (23 * v) ^ 2 :=
    pow_le_pow_left₀ (by omega) hupper 2
  have hw12 : 0 ≤ w ^ 12 := pow_nonneg hw 12
  have hw8 : 0 ≤ w ^ 8 := pow_nonneg hw 8
  have hw4 : 0 ≤ w ^ 4 := pow_nonneg hw 4
  have hneg := even32_negative_upper hv
  simp only [even32D]
  ring_nf at h14 h10 h6 h2
  nlinarith

private lemma lower_ratio_linearize_32
    {N A B k n d : ℕ}
    (hbracket : A ^ k < N * B ^ k)
    (hlo : N * (n + 1) ^ k ≤ (n + d + 1) ^ k) :
    A * (n + 1) < B * (n + d + 1) := by
  by_contra hnot
  have hle : B * (n + d + 1) ≤ A * (n + 1) := by omega
  have hpow := Nat.pow_le_pow_left hle k
  have hpow' : B ^ k * (n + d + 1) ^ k ≤
      A ^ k * (n + 1) ^ k := by
    simpa [Nat.mul_pow, mul_comm, mul_left_comm, mul_assoc] using hpow
  have hlomul : (N * B ^ k) * (n + 1) ^ k ≤
      B ^ k * (n + d + 1) ^ k := by
    calc
      (N * B ^ k) * (n + 1) ^ k =
          B ^ k * (N * (n + 1) ^ k) := by ring
      _ ≤ B ^ k * (n + d + 1) ^ k := Nat.mul_le_mul_left _ hlo
  have hbase : 0 < (n + 1) ^ k := Nat.pow_pos (by omega)
  have hstrict : A ^ k * (n + 1) ^ k <
      (N * B ^ k) * (n + 1) ^ k :=
    (Nat.mul_lt_mul_right hbase).2 hbracket
  omega

private lemma even32_small_gap_impossible {n d : ℕ} (hd : 32 ≤ d)
    (hd127 : d ≤ 127)
    (heq : blockProduct 32 (n + d) = 4 * blockProduct 32 n) : False := by
  obtain ⟨hup, hlo⟩ := ratio_window_four_nat heq
  have hlin :=
    ratio_window_linearize_of_pow_bracket (N := 4) (A := 23) (B := 22)
      (k := 32) (n := n) (d := d) (by norm_num) (by norm_num) hup
  have hlow := lower_ratio_linearize_32 (N := 4) (A := 49) (B := 47)
    (k := 32) (n := n) (d := d) (by norm_num) hlo
  have hn2984 : n < 2984 := by omega
  let fd : Fin 128 := ⟨d, by omega⟩
  let fn : Fin 2984 := ⟨n, hn2984⟩
  have hstrip := even32_finite_strip fd (by dsimp [fd]; omega) fn
    (by dsimp [fd, fn]; omega) (by dsimp [fd, fn]; omega)
  have hZ : ((blockProduct 32 (n + d) : ℕ) : ℤ) =
      4 * ((blockProduct 32 n : ℕ) : ℤ) := by exact_mod_cast heq
  have hs1 := even32_centered_bridge (n + d)
  have hs2 := even32_centered_bridge n
  dsimp [fd, fn] at hstrip
  push_cast at hs1 hs2
  apply hstrip
  change even32S (2 * ((n : ℤ) + (d : ℤ)) + 33) =
    4 * even32S (2 * (n : ℤ) + 33)
  rw [hs1, hs2, hZ]
  ring

private lemma even32_quotient_candidate {m q : ℤ}
    (hmgt : -1388955148309984 < m) (hmneg : m < 0)
    (hq : m = 3221225472 * q) :
    ∃ t : ℕ, m = -(3221225472 * (t : ℤ)) ∧ 1 ≤ t ∧ t ≤ 431188 := by
  have hqlo : -431189 < q := by rw [hq] at hmgt; omega
  have hqhi : q < 0 := by rw [hq] at hmneg; omega
  let t : ℕ := (-q).toNat
  have hqnonneg : 0 ≤ -q := by omega
  have htcast : (t : ℤ) = -q := by
    simp [t, Int.toNat_of_nonneg hqnonneg]
  have htpos : 1 ≤ t := by omega
  have htbound : t ≤ 431188 := by omega
  have hmt : m = -(3221225472 * (t : ℤ)) := by rw [hq, htcast]; ring
  exact ⟨t, hmt, htpos, htbound⟩

private lemma even32_large_gap_reduction {n d : ℕ} (hd128 : 128 ≤ d)
    (heq : blockProduct 32 (n + d) = 4 * blockProduct 32 n) :
    ∃ w v : ℤ, ∃ t : ℕ,
      evenTable32S w = 4 * evenTable32S v ∧
      -(3221225472 * (t : ℤ)) = evenTable32T w - 2 * evenTable32T v ∧
      1 ≤ t ∧ t ≤ 431188 := by
  obtain ⟨hup, _hlo⟩ := ratio_window_four_nat heq
  have hlin :=
    ratio_window_linearize_of_pow_bracket (N := 4) (A := 23) (B := 22)
      (k := 32) (n := n) (d := d) (by norm_num) (by norm_num) hup
  have hlinUpper :=
    ratio_window_linearize_of_pow_bracket (N := 4) (A := 47) (B := 45)
      (k := 32) (n := n) (d := d) (by norm_num) (by norm_num) hup
  have hn2785 : 2785 ≤ n := by omega
  have hZ : ((blockProduct 32 (n + d) : ℕ) : ℤ) =
      4 * ((blockProduct 32 n : ℕ) : ℤ) := by exact_mod_cast heq
  let w : ℤ := 2 * ((n : ℤ) + (d : ℤ)) + 33
  let v : ℤ := 2 * (n : ℤ) + 33
  have hv : 5603 ≤ v := by dsimp [v]; omega
  have hw : 5603 ≤ w := by dsimp [w]; omega
  have hvw : v + 256 ≤ w := by dsimp [v, w]; omega
  have hupper : 22 * w ≤ 23 * v := by dsimp [v, w]; omega
  have hs1 := even32_centered_bridge (n + d)
  have hs2 := even32_centered_bridge n
  have hcw : 2 * ((n + d : ℕ) : ℤ) + 33 = w := by dsimp [w]
  have hcv : 2 * (n : ℤ) + 33 = v := by rfl
  rw [hcw] at hs1
  rw [hcv] at hs2
  have hS : even32S w = 4 * even32S v := by rw [hs1, hs2, hZ]; ring
  let m : ℤ := even32T w - 2 * even32T v
  let X : ℤ := even32T w + 2 * even32T v
  have hTw : 0 < even32T w := even32_T_pos hw
  have hTv : 0 < even32T v := even32_T_pos hv
  have hXpos : 0 < X := by dsimp [X]; linarith
  have hmdef : m = even32T w - 2 * even32T v := rfl
  have hmX : m * X = even32D w - 4 * even32D v := by
    dsimp [m, X]
    calc
      (even32T w - 2 * even32T v) * (even32T w + 2 * even32T v) =
          even32T w ^ 2 - 4 * even32T v ^ 2 := by ring
      _ = (even32S w + even32D w) - 4 * (even32S v + even32D v) := by
        rw [even32_square_identity, even32_square_identity]
      _ = even32D w - 4 * even32D v := by rw [hS]; ring
  have hdeltaNeg := even32_delta_negative hv (by omega) hupper
  have hdeltaLower :
      -1388955148309984 * X < even32D w - 4 * even32D v := by
    have h := even32_delta_lower hv hvw
    dsimp [X]
    linarith
  have hmneg : m < 0 := by
    by_contra hnot
    have := mul_nonneg (not_lt.mp hnot) hXpos.le
    rw [hmX] at this
    linarith
  have hmgt : -1388955148309984 < m := by
    by_contra hnot
    have hmul := mul_le_mul_of_nonneg_right (not_lt.mp hnot) hXpos.le
    rw [hmX] at hmul
    linarith
  have hmw := even32_T_fixed_divisor ((n : ℤ) + (d : ℤ) + 16)
  have hmv := even32_T_fixed_divisor ((n : ℤ) + 16)
  have hwodd : 2 * ((n : ℤ) + (d : ℤ) + 16) + 1 = w := by dsimp [w]; ring
  have hvodd : 2 * ((n : ℤ) + 16) + 1 = v := by dsimp [v]; ring
  rw [hwodd] at hmw
  rw [hvodd] at hmv
  have hmdiv : (3221225472 : ℤ) ∣ m := by
    dsimp [m]
    exact dvd_sub hmw (hmv.mul_left 2)
  obtain ⟨q, hq⟩ := hmdiv
  obtain ⟨t, hmt, htpos, htbound⟩ :=
    even32_quotient_candidate hmgt hmneg hq
  have htarget : -(3221225472 * (t : ℤ)) = even32T w - 2 * even32T v := by
    rw [← hmdef, hmt]
  exact ⟨w, v, t, hS, htarget, htpos, htbound⟩

private lemma gap_lt_128_implies_le_127 {d : ℕ} (h : ¬128 ≤ d) : d ≤ 127 := by
  omega

/-- Conditional k=32 closure from the exact finite-field certificate. -/
theorem no_gap_solution_four_even_thirtytwo_of_cert
    (hallowed : ∀ {w v : ℤ} {t : ℕ},
      evenTable32S w = 4 * evenTable32S v →
      -(3221225472 * (t : ℤ)) = evenTable32T w - 2 * evenTable32T v →
      even32CandidateAllowed t = true)
    (hcover : ∀ t : ℕ, 1 ≤ t → t ≤ 431188 →
      even32CandidateAllowed t = false)
    {n d : ℕ} (hd : 32 ≤ d) :
    blockProduct 32 (n + d) ≠ 4 * blockProduct 32 n := by
  intro heq
  by_cases hd128 : 128 ≤ d
  · obtain ⟨w, v, t, hS, htarget, htpos, htbound⟩ :=
      even32_large_gap_reduction hd128 heq
    have hall := hallowed hS htarget
    have hfalse := hcover t htpos htbound
    rw [hfalse] at hall
    exact Bool.false_ne_true hall
  · exact even32_small_gap_impossible hd
      (gap_lt_128_implies_le_127 hd128) heq

end Erdos686Variant
end Erdos686
