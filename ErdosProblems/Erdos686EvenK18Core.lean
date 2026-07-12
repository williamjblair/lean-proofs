/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import ErdosProblems.Erdos686EvenK16
import ErdosProblems.Erdos686EvenK18FiniteStrip
import ErdosProblems.Erdos686EvenK18CandidateDefs

/-!
# Erdős 686: the even row `k=18`

The proof splits at `d=56`.  The lower strip has exactly 1,311 candidates
after the ratio window and is checked by ordinary kernel reduction.  Above
the split, an integral square-root polynomial traps its error at
`-242269137 < m < 0`, with `81 ∣ m`; 62 prime-field conditions, sharded into
bounded ordinary-`decide` certificates, cover all 2,990,976 possibilities.
-/

namespace Erdos686
namespace Erdos686Variant

private abbrev even18S {R : Type} [CommRing R] (W : R) : R := evenTable18S W
private abbrev even18T {R : Type} [CommRing R] (W : R) : R := evenTable18T W

private def even18D (W : ℤ) : ℤ :=
  78397083729792 * W ^ 8 - 16673477276146464 * W ^ 6 +
    945705074655002832 * W ^ 4 - 9110023357135451751 * W ^ 2 +
    19455213098280960000

private lemma even18_square_identity (W : ℤ) :
    even18T W ^ 2 = 16384 * even18S W + even18D W := by
  simp only [even18T, even18S, even18D, evenTable18T, evenTable18S]
  ring

set_option maxHeartbeats 2000000 in
-- Expansion of the nine centered quadratic factors.
private lemma even18_centered_poly (W : ℤ) :
    even18S W = centeredBlockProduct 18 W := by
  norm_num [centeredBlockProduct, even18S, evenTable18S,
    Finset.prod_Icc_succ_top, Finset.Icc_self, Finset.prod_singleton]
  ring

set_option maxHeartbeats 1000000 in
-- The centered product rescales the original block by `2^18`.
private lemma even18_centered_bridge (x : ℕ) :
    even18S (2 * (x : ℤ) + 19) =
      262144 * (blockProduct 18 x : ℤ) := by
  rw [even18_centered_poly]
  convert centeredBlockProduct_center 18 x using 1

private lemma even18_T_dvd_81 (x : ℤ) : (81 : ℤ) ∣ even18T x := by
  have hx : ((even18T x : ℤ) : ZMod 81) = 0 := by
    have hall : ∀ y : ZMod 81,
        128 * y ^ 9 - 62016 * y ^ 7 + 9038832 * y ^ 5 -
          439659848 * y ^ 3 + 3788405307 * y = 0 := by decide
    simpa [even18T, evenTable18T] using hall (x : ZMod 81)
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ 81).mp hx

private lemma even18_T_pos {W : ℤ} (hW : 1329 ≤ W) : 0 < even18T W := by
  obtain ⟨a, ha, rfl⟩ : ∃ a : ℤ, 0 ≤ a ∧ W = 1329 + a :=
    ⟨W - 1329, by omega, by omega⟩
  simp only [even18T, evenTable18T]
  nlinarith [ha, pow_nonneg ha 2, pow_nonneg ha 3, pow_nonneg ha 4,
    pow_nonneg ha 5, pow_nonneg ha 6, pow_nonneg ha 7,
    pow_nonneg ha 8, pow_nonneg ha 9]

private lemma even18_delta_lower {v w : ℤ} (hv : 1329 ≤ v)
    (hvw : v + 112 ≤ w) :
    0 < even18D w + 242269137 * even18T w + 484538274 * even18T v -
      4 * even18D v := by
  obtain ⟨a, ha, rfl⟩ : ∃ a : ℤ, 0 ≤ a ∧ v = 1329 + a :=
    ⟨v - 1329, by omega, by omega⟩
  obtain ⟨b, hb, rfl⟩ : ∃ b : ℤ, 0 ≤ b ∧ w = 1329 + a + 112 + b :=
    ⟨w - (1329 + a + 112), by omega, by omega⟩
  simp only [even18D, even18T, evenTable18T]
  nlinarith [ha, hb,
    pow_nonneg ha 2, pow_nonneg ha 3, pow_nonneg ha 4,
    pow_nonneg ha 5, pow_nonneg ha 6, pow_nonneg ha 7,
    pow_nonneg ha 8, pow_nonneg ha 9,
    pow_nonneg hb 2, pow_nonneg hb 3, pow_nonneg hb 4,
    pow_nonneg hb 5, pow_nonneg hb 6, pow_nonneg hb 7,
    pow_nonneg hb 8, pow_nonneg hb 9, mul_nonneg ha hb]

private lemma even18_negative_upper {v : ℤ} (hv : 1329 ≤ v) :
    (78397083729792 * 12 ^ 8 - 4 * 78397083729792 * 11 ^ 8) * v ^ 8 +
        4 * 16673477276146464 * 11 ^ 8 * v ^ 6 +
        945705074655002832 * 11 ^ 4 * 12 ^ 4 * v ^ 4 +
        4 * 9110023357135451751 * 11 ^ 8 * v ^ 2 < 0 := by
  obtain ⟨a, ha, rfl⟩ : ∃ a : ℤ, 0 ≤ a ∧ v = 1329 + a :=
    ⟨v - 1329, by omega, by omega⟩
  nlinarith [ha, pow_nonneg ha 2, pow_nonneg ha 3, pow_nonneg ha 4,
    pow_nonneg ha 5, pow_nonneg ha 6, pow_nonneg ha 7, pow_nonneg ha 8]

private lemma even18_delta_negative {v w : ℤ} (hv : 1329 ≤ v)
    (hw : 0 ≤ w) (hupper : 11 * w ≤ 12 * v) :
    even18D w - 4 * even18D v < 0 := by
  have h8 : (11 * w) ^ 8 ≤ (12 * v) ^ 8 :=
    pow_le_pow_left₀ (by omega) hupper 8
  have h4 : (11 * w) ^ 4 ≤ (12 * v) ^ 4 :=
    pow_le_pow_left₀ (by omega) hupper 4
  have hw6 : 0 ≤ w ^ 6 := pow_nonneg hw 6
  have hw2 : 0 ≤ w ^ 2 := pow_nonneg hw 2
  have hneg := even18_negative_upper hv
  simp only [even18D]
  ring_nf at h8 h4
  nlinarith

private lemma lower_ratio_linearize
    {N A B k n d : ℕ}
    (hbracket : A ^ k < N * B ^ k)
    (hlo : N * (n + 1) ^ k ≤ (n + d + 1) ^ k) :
    A * (n + 1) < B * (n + d + 1) := by
  by_contra hnot
  have hle : B * (n + d + 1) ≤ A * (n + 1) := by omega
  have hpow := Nat.pow_le_pow_left hle k
  have hpow' : B ^ k * (n + d + 1) ^ k ≤ A ^ k * (n + 1) ^ k := by
    simpa [Nat.mul_pow, mul_comm, mul_left_comm, mul_assoc] using hpow
  have hlomul : (N * B ^ k) * (n + 1) ^ k ≤
      B ^ k * (n + d + 1) ^ k := by
    calc
      (N * B ^ k) * (n + 1) ^ k = B ^ k * (N * (n + 1) ^ k) := by ring
      _ ≤ B ^ k * (n + d + 1) ^ k := Nat.mul_le_mul_left _ hlo
  have hbase : 0 < (n + 1) ^ k := Nat.pow_pos (by omega)
  have hstrict : A ^ k * (n + 1) ^ k <
      (N * B ^ k) * (n + 1) ^ k :=
    (Nat.mul_lt_mul_right hbase).2 hbracket
  omega

private lemma even18_small_gap_impossible {n d : ℕ} (hd : 18 ≤ d)
    (hd55 : d ≤ 55)
    (heq : blockProduct 18 (n + d) = 4 * blockProduct 18 n) : False := by
  obtain ⟨hup, hlo⟩ := ratio_window_four_nat heq
  have hlin :=
    ratio_window_linearize_of_pow_bracket (N := 4) (A := 13) (B := 12)
      (k := 18) (n := n) (d := d) (by norm_num) (by norm_num) hup
  have hlow := lower_ratio_linearize (N := 4) (A := 27) (B := 25)
    (k := 18) (n := n) (d := d) (by norm_num) hlo
  have hn687 : n < 687 := by omega
  let fd : Fin 56 := ⟨d, by omega⟩
  let fn : Fin 687 := ⟨n, hn687⟩
  have hstrip := even18_finite_strip fd (by dsimp [fd]; omega) fn
    (by dsimp [fd, fn]; omega) (by dsimp [fd, fn]; omega)
  have hZ : ((blockProduct 18 (n + d) : ℕ) : ℤ) =
      4 * ((blockProduct 18 n : ℕ) : ℤ) := by exact_mod_cast heq
  have hs1 := even18_centered_bridge (n + d)
  have hs2 := even18_centered_bridge n
  dsimp [fd, fn] at hstrip
  push_cast at hs1 hs2
  apply hstrip
  change even18S (2 * ((n : ℤ) + (d : ℤ)) + 19) =
    4 * even18S (2 * (n : ℤ) + 19)
  rw [hs1, hs2, hZ]
  ring

private lemma even18_quotient_candidate {m q : ℤ}
    (hmgt : -242269137 < m) (hmneg : m < 0) (hq : m = 81 * q) :
    ∃ t : ℕ, m = -(81 * (t : ℤ)) ∧ 1 ≤ t ∧ t ≤ 2990976 := by
  have hqlo : -2990977 < q := by rw [hq] at hmgt; omega
  have hqhi : q < 0 := by rw [hq] at hmneg; omega
  let t : ℕ := (-q).toNat
  have hqnonneg : 0 ≤ -q := by omega
  have htcast : (t : ℤ) = -q := by
    simp [t, Int.toNat_of_nonneg hqnonneg]
  have htpos : 1 ≤ t := by omega
  have htbound : t ≤ 2990976 := by omega
  have hmt : m = -(81 * (t : ℤ)) := by rw [hq, htcast]; ring
  exact ⟨t, hmt, htpos, htbound⟩

private lemma even18_large_gap_reduction {n d : ℕ} (hd56 : 56 ≤ d)
    (heq : blockProduct 18 (n + d) = 4 * blockProduct 18 n) :
    ∃ w v : ℤ, ∃ t : ℕ,
      evenTable18S w = 4 * evenTable18S v ∧
      -(81 * (t : ℤ)) = evenTable18T w - 2 * evenTable18T v ∧
      1 ≤ t ∧ t ≤ 2990976 := by
  obtain ⟨hup, _hlo⟩ := ratio_window_four_nat heq
  have hlin :=
    ratio_window_linearize_of_pow_bracket (N := 4) (A := 13) (B := 12)
      (k := 18) (n := n) (d := d) (by norm_num) (by norm_num) hup
  have hn655 : 655 ≤ n := by omega
  have hZ : ((blockProduct 18 (n + d) : ℕ) : ℤ) =
      4 * ((blockProduct 18 n : ℕ) : ℤ) := by exact_mod_cast heq
  let w : ℤ := 2 * ((n : ℤ) + (d : ℤ)) + 19
  let v : ℤ := 2 * (n : ℤ) + 19
  have hv : 1329 ≤ v := by dsimp [v]; omega
  have hw : 1329 ≤ w := by dsimp [w]; omega
  have hvw : v + 112 ≤ w := by dsimp [v, w]; omega
  have hupper : 11 * w ≤ 12 * v := by dsimp [v, w]; omega
  have hs1 := even18_centered_bridge (n + d)
  have hs2 := even18_centered_bridge n
  have hcw : 2 * ((n + d : ℕ) : ℤ) + 19 = w := by dsimp [w]
  have hcv : 2 * (n : ℤ) + 19 = v := by rfl
  rw [hcw] at hs1
  rw [hcv] at hs2
  have hS : even18S w = 4 * even18S v := by rw [hs1, hs2, hZ]; ring
  let m : ℤ := even18T w - 2 * even18T v
  let X : ℤ := even18T w + 2 * even18T v
  have hTw : 0 < even18T w := even18_T_pos hw
  have hTv : 0 < even18T v := even18_T_pos hv
  have hXpos : 0 < X := by dsimp [X]; linarith
  have hmdef : m = even18T w - 2 * even18T v := rfl
  have hmX : m * X = even18D w - 4 * even18D v := by
    dsimp [m, X]
    calc
      (even18T w - 2 * even18T v) * (even18T w + 2 * even18T v) =
          even18T w ^ 2 - 4 * even18T v ^ 2 := by ring
      _ = (16384 * even18S w + even18D w) -
          4 * (16384 * even18S v + even18D v) := by
        rw [even18_square_identity, even18_square_identity]
      _ = even18D w - 4 * even18D v := by rw [hS]; ring
  have hdeltaNeg := even18_delta_negative hv (by omega) hupper
  have hdeltaLower : -242269137 * X < even18D w - 4 * even18D v := by
    have h := even18_delta_lower hv hvw
    dsimp [X]
    linarith
  have hmneg : m < 0 := by
    by_contra hnot
    have := mul_nonneg (not_lt.mp hnot) hXpos.le
    rw [hmX] at this
    linarith
  have hmgt : -242269137 < m := by
    by_contra hnot
    have hmul := mul_le_mul_of_nonneg_right (not_lt.mp hnot) hXpos.le
    rw [hmX] at hmul
    linarith
  have hmw := even18_T_dvd_81 w
  have hmv := even18_T_dvd_81 v
  have hmdiv : (81 : ℤ) ∣ m := by
    dsimp [m]
    exact dvd_sub hmw (hmv.mul_left 2)
  obtain ⟨q, hq⟩ := hmdiv
  obtain ⟨t, hmt, htpos, htbound⟩ :=
    even18_quotient_candidate hmgt hmneg hq
  have htarget : -(81 * (t : ℤ)) = even18T w - 2 * even18T v := by
    rw [← hmdef, hmt]
  exact ⟨w, v, t, hS, htarget, htpos, htbound⟩

private lemma gap_lt_56_implies_le_55 {d : ℕ} (h : ¬56 ≤ d) : d ≤ 55 := by
  omega

/-- The row `k=18` has no quotient-four gap solution once `d≥18`. -/
theorem no_gap_solution_four_even_eighteen_of_cert
    (hallowed : ∀ {w v : ℤ} {t : ℕ},
      evenTable18S w = 4 * evenTable18S v →
      -(81 * (t : ℤ)) = evenTable18T w - 2 * evenTable18T v →
      even18CandidateAllowed t = true)
    (hcover : ∀ t : ℕ, 1 ≤ t → t ≤ 2990976 →
      even18CandidateAllowed t = false)
    {n d : ℕ} (hd : 18 ≤ d) :
    blockProduct 18 (n + d) ≠ 4 * blockProduct 18 n := by
  intro heq
  by_cases hd56 : 56 ≤ d
  · obtain ⟨w, v, t, hS, htarget, htpos, htbound⟩ :=
      even18_large_gap_reduction hd56 heq
    have hall := hallowed hS htarget
    have hfalse := hcover t htpos htbound
    rw [hfalse] at hall
    exact Bool.false_ne_true hall
  · exact even18_small_gap_impossible hd (gap_lt_56_implies_le_55 hd56) heq


end Erdos686Variant
end Erdos686
