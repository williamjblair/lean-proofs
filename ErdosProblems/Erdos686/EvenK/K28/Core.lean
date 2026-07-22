/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import ErdosProblems.Erdos686.EvenK.K28.FiniteStrip
import ErdosProblems.Erdos686.EvenK.K28.CandidateDefs

/-!
# Erdős 686: arithmetic core for the even row `k=28`

The proof splits at `d=384`.  The lower strip is an ordinary-kernel finite
certificate.  Above the split, the integral square-root polynomial traps its
error at `-52682724273 < m < 0`, while `50176 ∣ m`.
-/

namespace Erdos686
namespace Erdos686Variant

private abbrev even28S {R : Type} [CommRing R] (W : R) : R := evenTable28S W
private abbrev even28T {R : Type} [CommRing R] (W : R) : R := evenTable28T W

private def even28D (W : ℤ) : ℤ :=
  21098759979340624896 * W ^ 12 -
    23842979238602673723392 * W ^ 10 +
    9532983871938306010033152 * W ^ 8 -
    1628940093510881216919490560 * W ^ 6 +
    117251030005615363837162982400 * W ^ 4 -
    2066038537427621024959391275008 * W ^ 2 +
    236809527564209472536296346735616

private lemma even28_square_identity (W : ℤ) :
    even28T W ^ 2 = even28S W + even28D W := by
  simp only [even28T, even28S, even28D, evenTable28T, evenTable28S]
  ring

set_option maxHeartbeats 5000000 in
private lemma even28_centered_poly (W : ℤ) :
    even28S W = centeredBlockProduct 28 W := by
  norm_num [centeredBlockProduct, even28S, evenTable28S,
    Finset.prod_Icc_succ_top, Finset.Icc_self, Finset.prod_singleton]
  ring

set_option maxHeartbeats 1000000 in
private lemma even28_centered_bridge (x : ℕ) :
    even28S (2 * (x : ℤ) + 29) =
      268435456 * (blockProduct 28 x : ℤ) := by
  rw [even28_centered_poly]
  convert centeredBlockProduct_center 28 x using 1 <;> norm_num

private lemma even28_T_dvd_1024_at_odd (a : ℤ) :
    (1024 : ℤ) ∣ even28T (2 * a + 1) := by
  refine ⟨16 * a ^ 14 + 112 * a ^ 13 - 6944 * a ^ 12 - 43120 * a ^ 11 +
      1120952 * a ^ 10 + 6002696 * a ^ 9 - 84483144 * a ^ 8 -
      374427648 * a ^ 7 + 3047107518 * a ^ 6 + 10477509770 * a ^ 5 -
      48952249528 * a ^ 4 - 115816092574 * a ^ 3 +
      178964440405 * a ^ 2 + 238682980039 * a - 14965931688827, ?_⟩
  simp only [even28T, evenTable28T]
  ring

private lemma even28_T_dvd_49 (x : ℤ) : (49 : ℤ) ∣ even28T x := by
  have hx : ((even28T x : ℤ) : ZMod 49) = 0 := by
    have hall : ∀ y : ZMod 49,
        y ^ 14 - 1827 * y ^ 12 + 1240533 * y ^ 10 -
          392855199 * y ^ 8 + 59494839075 * y ^ 6 -
          3998126300553 * y ^ 4 + 68922176202951 * y ^ 2 -
          15390097202483829 = 0 := by decide
    simpa [even28T, evenTable28T] using hall (x : ZMod 49)
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ 49).mp hx

private lemma even28_T_fixed_divisor (a : ℤ) :
    (50176 : ℤ) ∣ even28T (2 * a + 1) := by
  have h2 := even28_T_dvd_1024_at_odd a
  have h49 := even28_T_dvd_49 (2 * a + 1)
  have hcop : IsCoprime (1024 : ℤ) 49 := ⟨-10, 209, by norm_num⟩
  simpa using hcop.mul_dvd h2 h49

private lemma even28_T_pos {W : ℤ} (hW : 14567 ≤ W) : 0 < even28T W := by
  obtain ⟨a, ha, rfl⟩ : ∃ a : ℤ, 0 ≤ a ∧ W = 14567 + a :=
    ⟨W - 14567, by omega, by omega⟩
  simp only [even28T, evenTable28T]
  nlinarith [ha, pow_nonneg ha 2, pow_nonneg ha 3, pow_nonneg ha 4,
    pow_nonneg ha 5, pow_nonneg ha 6, pow_nonneg ha 7,
    pow_nonneg ha 8, pow_nonneg ha 9, pow_nonneg ha 10,
    pow_nonneg ha 11, pow_nonneg ha 12, pow_nonneg ha 13,
    pow_nonneg ha 14]

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 1000000 in
private lemma even28_delta_lower {v w : ℤ} (hv : 14567 ≤ v)
    (hvw : v + 768 ≤ w) :
    0 < even28D w + 52682724273 * even28T w +
      105365448546 * even28T v - 4 * even28D v := by
  obtain ⟨a, ha, rfl⟩ : ∃ a : ℤ, 0 ≤ a ∧ v = 14567 + a :=
    ⟨v - 14567, by omega, by omega⟩
  obtain ⟨b, hb, rfl⟩ : ∃ b : ℤ, 0 ≤ b ∧ w = 14567 + a + 768 + b :=
    ⟨w - (14567 + a + 768), by omega, by omega⟩
  simp only [even28D, even28T, evenTable28T]
  nlinarith [ha, hb,
    pow_nonneg ha 2, pow_nonneg ha 3, pow_nonneg ha 4,
    pow_nonneg ha 5, pow_nonneg ha 6, pow_nonneg ha 7,
    pow_nonneg ha 8, pow_nonneg ha 9, pow_nonneg ha 10,
    pow_nonneg ha 11, pow_nonneg ha 12, pow_nonneg ha 13,
    pow_nonneg ha 14, pow_nonneg hb 2, pow_nonneg hb 3,
    pow_nonneg hb 4, pow_nonneg hb 5, pow_nonneg hb 6,
    pow_nonneg hb 7, pow_nonneg hb 8, pow_nonneg hb 9,
    pow_nonneg hb 10, pow_nonneg hb 11, pow_nonneg hb 12,
    pow_nonneg hb 13, pow_nonneg hb 14, mul_nonneg ha hb]

set_option maxHeartbeats 10000000 in
private lemma even28_negative_upper {v : ℤ} (hv : 14567 ≤ v) :
    -18178092884574502695716960553984 * v ^ 12 +
      95371916954410694893568000000000000 * v ^ 10 +
      20434797553797425773462812356229120000 * v ^ 8 +
      6515760374043524867677962240000000000000 * v ^ 6 +
      171667233031221454193990322531840000000000 * v ^ 4 +
      8264154149710484099837565100032000000000000 * v ^ 2 < 0 := by
  obtain ⟨a, ha, rfl⟩ : ∃ a : ℤ, 0 ≤ a ∧ v = 14567 + a :=
    ⟨v - 14567, by omega, by omega⟩
  nlinarith [ha, pow_nonneg ha 2, pow_nonneg ha 3, pow_nonneg ha 4,
    pow_nonneg ha 5, pow_nonneg ha 6, pow_nonneg ha 7,
    pow_nonneg ha 8, pow_nonneg ha 9, pow_nonneg ha 10,
    pow_nonneg ha 11, pow_nonneg ha 12]

private lemma even28_delta_negative {v w : ℤ} (hv : 14567 ≤ v)
    (hw : 0 ≤ w) (hupper : 10 * w ≤ 11 * v) :
    even28D w - 4 * even28D v < 0 := by
  have h12 : (10 * w) ^ 12 ≤ (11 * v) ^ 12 :=
    pow_le_pow_left₀ (by omega) hupper 12
  have h8 : (10 * w) ^ 8 ≤ (11 * v) ^ 8 :=
    pow_le_pow_left₀ (by omega) hupper 8
  have h4 : (10 * w) ^ 4 ≤ (11 * v) ^ 4 :=
    pow_le_pow_left₀ (by omega) hupper 4
  have hw10 : 0 ≤ w ^ 10 := pow_nonneg hw 10
  have hw6 : 0 ≤ w ^ 6 := pow_nonneg hw 6
  have hw2 : 0 ≤ w ^ 2 := pow_nonneg hw 2
  have hneg := even28_negative_upper hv
  simp only [even28D]
  ring_nf at h12 h8 h4
  nlinarith

private lemma lower_ratio_linearize_28
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

private lemma even28_small_gap_impossible {n d : ℕ} (hd : 28 ≤ d)
    (hd383 : d ≤ 383)
    (heq : blockProduct 28 (n + d) = 4 * blockProduct 28 n) : False := by
  obtain ⟨hup, hlo⟩ := ratio_window_four_nat heq
  have hlin :=
    ratio_window_linearize_of_pow_bracket (N := 4) (A := 20) (B := 19)
      (k := 28) (n := n) (d := d) (by norm_num) (by norm_num) hup
  have hlow := lower_ratio_linearize_28 (N := 4) (A := 83) (B := 79)
    (k := 28) (n := n) (d := d) (by norm_num) hlo
  have hn7564 : n < 7564 := by omega
  let fd : Fin 384 := ⟨d, by omega⟩
  let fn : Fin 7564 := ⟨n, hn7564⟩
  have hstrip := even28_finite_strip fd (by dsimp [fd]; omega) fn
    (by dsimp [fd, fn]; omega) (by dsimp [fd, fn]; omega)
  have hZ : ((blockProduct 28 (n + d) : ℕ) : ℤ) =
      4 * ((blockProduct 28 n : ℕ) : ℤ) := by exact_mod_cast heq
  have hs1 := even28_centered_bridge (n + d)
  have hs2 := even28_centered_bridge n
  dsimp [fd, fn] at hstrip
  push_cast at hs1 hs2
  apply hstrip
  change even28S (2 * ((n : ℤ) + (d : ℤ)) + 29) =
    4 * even28S (2 * (n : ℤ) + 29)
  rw [hs1, hs2, hZ]
  ring

private lemma even28_quotient_candidate {m q : ℤ}
    (hmgt : -52682724273 < m) (hmneg : m < 0)
    (hq : m = 50176 * q) :
    ∃ t : ℕ, m = -(50176 * (t : ℤ)) ∧ 1 ≤ t ∧ t ≤ 1049958 := by
  have hqlo : -1049959 < q := by rw [hq] at hmgt; omega
  have hqhi : q < 0 := by rw [hq] at hmneg; omega
  let t : ℕ := (-q).toNat
  have hqnonneg : 0 ≤ -q := by omega
  have htcast : (t : ℤ) = -q := by
    simp [t, Int.toNat_of_nonneg hqnonneg]
  have htpos : 1 ≤ t := by omega
  have htbound : t ≤ 1049958 := by omega
  have hmt : m = -(50176 * (t : ℤ)) := by rw [hq, htcast]; ring
  exact ⟨t, hmt, htpos, htbound⟩

private lemma even28_large_gap_reduction {n d : ℕ} (hd384 : 384 ≤ d)
    (heq : blockProduct 28 (n + d) = 4 * blockProduct 28 n) :
    ∃ w v : ℤ, ∃ t : ℕ,
      evenTable28S w = 4 * evenTable28S v ∧
      -(50176 * (t : ℤ)) = evenTable28T w - 2 * evenTable28T v ∧
      1 ≤ t ∧ t ≤ 1049958 := by
  obtain ⟨hup, _hlo⟩ := ratio_window_four_nat heq
  have hlin :=
    ratio_window_linearize_of_pow_bracket (N := 4) (A := 20) (B := 19)
      (k := 28) (n := n) (d := d) (by norm_num) (by norm_num) hup
  have hn7269 : 7269 ≤ n := by omega
  have hZ : ((blockProduct 28 (n + d) : ℕ) : ℤ) =
      4 * ((blockProduct 28 n : ℕ) : ℤ) := by exact_mod_cast heq
  let w : ℤ := 2 * ((n : ℤ) + (d : ℤ)) + 29
  let v : ℤ := 2 * (n : ℤ) + 29
  have hv : 14567 ≤ v := by dsimp [v]; omega
  have hw : 14567 ≤ w := by dsimp [w]; omega
  have hvw : v + 768 ≤ w := by dsimp [v, w]; omega
  have hupper : 10 * w ≤ 11 * v := by dsimp [v, w]; omega
  have hs1 := even28_centered_bridge (n + d)
  have hs2 := even28_centered_bridge n
  have hcw : 2 * ((n + d : ℕ) : ℤ) + 29 = w := by dsimp [w]
  have hcv : 2 * (n : ℤ) + 29 = v := by rfl
  rw [hcw] at hs1
  rw [hcv] at hs2
  have hS : even28S w = 4 * even28S v := by rw [hs1, hs2, hZ]; ring
  let m : ℤ := even28T w - 2 * even28T v
  let X : ℤ := even28T w + 2 * even28T v
  have hTw : 0 < even28T w := even28_T_pos hw
  have hTv : 0 < even28T v := even28_T_pos hv
  have hXpos : 0 < X := by dsimp [X]; linarith
  have hmdef : m = even28T w - 2 * even28T v := rfl
  have hmX : m * X = even28D w - 4 * even28D v := by
    dsimp [m, X]
    calc
      (even28T w - 2 * even28T v) * (even28T w + 2 * even28T v) =
          even28T w ^ 2 - 4 * even28T v ^ 2 := by ring
      _ = (even28S w + even28D w) - 4 * (even28S v + even28D v) := by
        rw [even28_square_identity, even28_square_identity]
      _ = even28D w - 4 * even28D v := by rw [hS]; ring
  have hdeltaNeg := even28_delta_negative hv (by omega) hupper
  have hdeltaLower :
      -52682724273 * X < even28D w - 4 * even28D v := by
    have h := even28_delta_lower hv hvw
    dsimp [X]
    linarith
  have hmneg : m < 0 := by
    by_contra hnot
    have := mul_nonneg (not_lt.mp hnot) hXpos.le
    rw [hmX] at this
    linarith
  have hmgt : -52682724273 < m := by
    by_contra hnot
    have hmul := mul_le_mul_of_nonneg_right (not_lt.mp hnot) hXpos.le
    rw [hmX] at hmul
    linarith
  have hmw := even28_T_fixed_divisor ((n : ℤ) + (d : ℤ) + 14)
  have hmv := even28_T_fixed_divisor ((n : ℤ) + 14)
  have hwodd : 2 * ((n : ℤ) + (d : ℤ) + 14) + 1 = w := by
    dsimp [w]
    ring
  have hvodd : 2 * ((n : ℤ) + 14) + 1 = v := by dsimp [v]; ring
  rw [hwodd] at hmw
  rw [hvodd] at hmv
  have hmdiv : (50176 : ℤ) ∣ m := by
    dsimp [m]
    exact dvd_sub hmw (hmv.mul_left 2)
  obtain ⟨q, hq⟩ := hmdiv
  obtain ⟨t, hmt, htpos, htbound⟩ :=
    even28_quotient_candidate hmgt hmneg hq
  have htarget : -(50176 * (t : ℤ)) = even28T w - 2 * even28T v := by
    rw [← hmdef, hmt]
  exact ⟨w, v, t, hS, htarget, htpos, htbound⟩

private lemma gap_lt_384_implies_le_383 {d : ℕ} (h : ¬384 ≤ d) : d ≤ 383 := by
  omega

/-- Conditional k=28 closure from the exact finite-field certificate. -/
theorem no_gap_solution_four_even_twentyeight_of_cert
    (hallowed : ∀ {w v : ℤ} {t : ℕ},
      evenTable28S w = 4 * evenTable28S v →
      -(50176 * (t : ℤ)) = evenTable28T w - 2 * evenTable28T v →
      even28CandidateAllowed t = true)
    (hcover : ∀ t : ℕ, 1 ≤ t → t ≤ 1049958 →
      even28CandidateAllowed t = false)
    {n d : ℕ} (hd : 28 ≤ d) :
    blockProduct 28 (n + d) ≠ 4 * blockProduct 28 n := by
  intro heq
  by_cases hd384 : 384 ≤ d
  · obtain ⟨w, v, t, hS, htarget, htpos, htbound⟩ :=
      even28_large_gap_reduction hd384 heq
    have hall := hallowed hS htarget
    have hfalse := hcover t htpos htbound
    rw [hfalse] at hall
    exact Bool.false_ne_true hall
  · exact even28_small_gap_impossible hd
      (gap_lt_384_implies_le_383 hd384) heq

end Erdos686Variant
end Erdos686
