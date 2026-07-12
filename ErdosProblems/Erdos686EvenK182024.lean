/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import ErdosProblems.Erdos686EvenK16
import ErdosProblems.Erdos686EvenKTable20P227
import ErdosProblems.Erdos686EvenKTable20P199
import ErdosProblems.Erdos686EvenKTable20P233
import ErdosProblems.Erdos686EvenKTable20P239
import ErdosProblems.Erdos686EvenKTable20P211
import ErdosProblems.Erdos686EvenKTable20P197
import ErdosProblems.Erdos686EvenKTable20P241
import ErdosProblems.Erdos686EvenKTable20Cover
import ErdosProblems.Erdos686EvenKTable24P13
import ErdosProblems.Erdos686EvenKTable24P191
import ErdosProblems.Erdos686EvenKTable24P157
import ErdosProblems.Erdos686EvenKTable24P227
import ErdosProblems.Erdos686EvenKTable24P239
import ErdosProblems.Erdos686EvenKTable24P241
import ErdosProblems.Erdos686EvenKTable24P131
import ErdosProblems.Erdos686EvenKTable24P197
import ErdosProblems.Erdos686EvenKTable24P71
import ErdosProblems.Erdos686EvenKTable24Cover

/-!
# Erdős 686: square-root closures at `k=18`, `k=20`, and `k=24`

This module continues the centered square-root polynomial-part method from
`Erdos686EvenK16`.  Every finite-field table is checked with ordinary
`decide`; `native_decide` is not used.
-/

namespace Erdos686
namespace Erdos686Variant

/-! ## The row `k=20` -/

private abbrev even20S {R : Type} [CommRing R] (W : R) : R := evenTable20S W

private abbrev even20T {R : Type} [CommRing R] (W : R) : R := evenTable20T W

private def even20D (W : ℤ) : ℤ :=
  3229057600000 * W ^ 8 - 1050408889600000 * W ^ 6 +
    98738651827200000 * W ^ 4 - 2417704523968000000 * W ^ 2 +
    31341350767572160000

private lemma even20_square_identity (W : ℤ) :
    even20T W ^ 2 = even20S W + even20D W := by
  simp only [even20T, even20S, even20D, evenTable20T, evenTable20S]
  ring

set_option maxHeartbeats 2000000 in
private lemma even20_centered_poly (W : ℤ) :
    even20S W = centeredBlockProduct 20 W := by
  norm_num [centeredBlockProduct, even20S, evenTable20S,
    Finset.prod_Icc_succ_top, Finset.Icc_self, Finset.prod_singleton]
  ring

set_option maxHeartbeats 1000000 in
private lemma even20_centered_bridge (x : ℕ) :
    even20S (2 * (x : ℤ) + 21) =
      1048576 * (blockProduct 20 x : ℤ) := by
  rw [even20_centered_poly]
  convert centeredBlockProduct_center 20 x using 1 <;> norm_num

private lemma even20_T_dvd_128_at_odd (a : ℤ) :
    (128 : ℤ) ∣ even20T (2 * a + 1) := by
  refine ⟨8 * a ^ 10 + 40 * a ^ 9 - 1240 * a ^ 8 - 5200 * a ^ 7 +
      61684 * a ^ 6 + 203420 * a ^ 5 - 1143560 * a ^ 4 -
      2632300 * a ^ 3 + 6098983 * a ^ 2 + 7449915 * a - 42087075, ?_⟩
  simp only [even20T, evenTable20T]
  ring

private lemma even20_T_dvd_25 (x : ℤ) : (25 : ℤ) ∣ even20T x := by
  have hx : ((even20T x : ℤ) : ZMod 25) = 0 := by
    have hall : ∀ y : ZMod 25,
        y ^ 10 - 665 * y ^ 8 + 141778 * y ^ 6 - 11228810 * y ^ 4 +
          260432221 * y ^ 2 - 5636490125 = 0 := by decide
    simpa [even20T, evenTable20T] using hall (x : ZMod 25)
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ 25).mp hx

private lemma even20_T_fixed_divisor (a : ℤ) :
    (3200 : ℤ) ∣ even20T (2 * a + 1) := by
  have h128 := even20_T_dvd_128_at_odd a
  have h25 := even20_T_dvd_25 (2 * a + 1)
  have hcop : IsCoprime (128 : ℤ) 25 := ⟨17, -87, by norm_num⟩
  simpa using hcop.mul_dvd h128 h25

set_option maxHeartbeats 2000000 in
private lemma even20_boundary_product (n : ℕ) (hnlo : 251 ≤ n)
    (hnhi : n ≤ 268) :
    4 * blockProduct 20 n < blockProduct 20 (n + 20) := by
  interval_cases n <;>
    norm_num [blockProduct, Finset.prod_Icc_succ_top, Finset.Icc_self,
      Finset.prod_singleton]

private lemma even20_base_ge_269 {n d : ℕ} (hd : 20 ≤ d)
    (hlin : 27 * (n + d + 20) < 29 * (n + 20))
    (heq : blockProduct 20 (n + d) = 4 * blockProduct 20 n) :
    269 ≤ n := by
  have hnlo : 251 ≤ n := by omega
  by_contra hnot
  have hnhi : n ≤ 268 := by omega
  have hbad := even20_boundary_product n hnlo hnhi
  have hmono := blockProduct_mono 20 (n + 20) (n + d) (by omega)
  rw [heq] at hmono
  omega

private lemma even20_T_pos {W : ℤ} (hW : 559 ≤ W) : 0 < even20T W := by
  obtain ⟨a, ha, rfl⟩ : ∃ a : ℤ, 0 ≤ a ∧ W = 559 + a :=
    ⟨W - 559, by omega, by omega⟩
  simp only [even20T, evenTable20T]
  nlinarith [ha, pow_nonneg ha 2, pow_nonneg ha 3, pow_nonneg ha 4,
    pow_nonneg ha 5, pow_nonneg ha 6, pow_nonneg ha 7, pow_nonneg ha 8,
    pow_nonneg ha 9, pow_nonneg ha 10]

private lemma even20_delta_lower {v w : ℤ} (hv : 559 ≤ v)
    (hvw : v + 40 ≤ w) :
    0 < even20D w + 5853806 * even20T w + 11707612 * even20T v -
      4 * even20D v := by
  obtain ⟨a, ha, rfl⟩ : ∃ a : ℤ, 0 ≤ a ∧ v = 559 + a :=
    ⟨v - 559, by omega, by omega⟩
  obtain ⟨b, hb, rfl⟩ : ∃ b : ℤ, 0 ≤ b ∧ w = 559 + a + 40 + b :=
    ⟨w - (559 + a + 40), by omega, by omega⟩
  simp only [even20D, even20T, evenTable20T]
  nlinarith [ha, hb,
    pow_nonneg ha 2, pow_nonneg ha 3, pow_nonneg ha 4, pow_nonneg ha 5,
    pow_nonneg ha 6, pow_nonneg ha 7, pow_nonneg ha 8, pow_nonneg ha 9,
    pow_nonneg ha 10, pow_nonneg hb 2, pow_nonneg hb 3, pow_nonneg hb 4,
    pow_nonneg hb 5, pow_nonneg hb 6, pow_nonneg hb 7, pow_nonneg hb 8,
    pow_nonneg hb 9, pow_nonneg hb 10, mul_nonneg ha hb]

private lemma even20_negative_upper {v : ℤ} (hv : 559 ≤ v) :
    (3229057600000 * 14 ^ 8 - 4 * 3229057600000 * 13 ^ 8) * v ^ 8 +
        4 * 1050408889600000 * 13 ^ 8 * v ^ 6 +
        98738651827200000 * 13 ^ 4 * 14 ^ 4 * v ^ 4 +
        4 * 2417704523968000000 * 13 ^ 8 * v ^ 2 < 0 := by
  obtain ⟨a, ha, rfl⟩ : ∃ a : ℤ, 0 ≤ a ∧ v = 559 + a :=
    ⟨v - 559, by omega, by omega⟩
  nlinarith [ha, pow_nonneg ha 2, pow_nonneg ha 3, pow_nonneg ha 4,
    pow_nonneg ha 5, pow_nonneg ha 6, pow_nonneg ha 7, pow_nonneg ha 8]

private lemma even20_delta_negative {v w : ℤ} (hv : 559 ≤ v)
    (hw : 0 ≤ w) (hupper : 13 * w ≤ 14 * v) :
    even20D w - 4 * even20D v < 0 := by
  have h8 : (13 * w) ^ 8 ≤ (14 * v) ^ 8 :=
    pow_le_pow_left₀ (by omega) hupper 8
  have h4 : (13 * w) ^ 4 ≤ (14 * v) ^ 4 :=
    pow_le_pow_left₀ (by omega) hupper 4
  have hw6 : 0 ≤ w ^ 6 := pow_nonneg hw 6
  have hw2 : 0 ≤ w ^ 2 := pow_nonneg hw 2
  have hneg := even20_negative_upper hv
  simp only [even20D]
  ring_nf at h8 h4
  nlinarith

/-! ### Exact finite-field cover for the trapped `k=20` center -/

private lemma k20_allowed_int
    {p : ℕ} [NeZero p] (A : ZMod p → Bool)
    (hallow : ∀ w v : ZMod p,
      even20S w = 4 * even20S v → A (even20T w - 2 * even20T v) = true)
    {w v m : ℤ} (hS : even20S w = 4 * even20S v)
    (hm : m = even20T w - 2 * even20T v) : A (m : ZMod p) = true := by
  have hSp : even20S (w : ZMod p) = 4 * even20S (v : ZMod p) := by
    have h := congrArg (fun z : ℤ => (z : ZMod p)) hS
    simpa [even20S, evenTable20S] using h
  subst m
  simpa [even20T, evenTable20T] using hallow (w : ZMod p) (v : ZMod p) hSp

/-- The row `k=20` has no quotient-four gap solution once `d≥20`. -/
theorem no_gap_solution_four_even_twenty {n d : ℕ} (hd : 20 ≤ d) :
    blockProduct 20 (n + d) ≠ 4 * blockProduct 20 n := by
  intro heq
  obtain ⟨hup, _hlo⟩ := ratio_window_four_nat heq
  have hlin :=
    ratio_window_linearize_of_pow_bracket (N := 4) (A := 29) (B := 27)
      (k := 20) (n := n) (d := d) (by norm_num) (by norm_num) hup
  have hn269 : 269 ≤ n := even20_base_ge_269 hd hlin heq
  have hZ : ((blockProduct 20 (n + d) : ℕ) : ℤ) =
      4 * ((blockProduct 20 n : ℕ) : ℤ) := by exact_mod_cast heq
  let w : ℤ := 2 * ((n : ℤ) + (d : ℤ)) + 21
  let v : ℤ := 2 * (n : ℤ) + 21
  have hv : 559 ≤ v := by dsimp [v]; omega
  have hw : 559 ≤ w := by dsimp [w]; omega
  have hvw : v + 40 ≤ w := by dsimp [v, w]; omega
  have hupper : 13 * w ≤ 14 * v := by dsimp [v, w]; omega
  have hs1 := even20_centered_bridge (n + d)
  have hs2 := even20_centered_bridge n
  have hcw : 2 * ((n + d : ℕ) : ℤ) + 21 = w := by dsimp [w]
  have hcv : 2 * (n : ℤ) + 21 = v := by rfl
  rw [hcw] at hs1
  rw [hcv] at hs2
  have hS : even20S w = 4 * even20S v := by rw [hs1, hs2, hZ]; ring
  let m : ℤ := even20T w - 2 * even20T v
  let X : ℤ := even20T w + 2 * even20T v
  have hTw : 0 < even20T w := even20_T_pos hw
  have hTv : 0 < even20T v := even20_T_pos hv
  have hXpos : 0 < X := by dsimp [X]; linarith
  have hmdef : m = even20T w - 2 * even20T v := rfl
  have hmX : m * X = even20D w - 4 * even20D v := by
    dsimp [m, X]
    calc
      (even20T w - 2 * even20T v) * (even20T w + 2 * even20T v) =
          even20T w ^ 2 - 4 * even20T v ^ 2 := by ring
      _ = (even20S w + even20D w) - 4 * (even20S v + even20D v) := by
        rw [even20_square_identity, even20_square_identity]
      _ = even20D w - 4 * even20D v := by rw [hS]; ring
  have hdeltaNeg := even20_delta_negative hv (by omega) hupper
  have hdeltaLower : -5853806 * X < even20D w - 4 * even20D v := by
    have h := even20_delta_lower hv hvw
    dsimp [X]
    linarith
  have hmneg : m < 0 := by
    by_contra hnot
    have := mul_nonneg (not_lt.mp hnot) hXpos.le
    rw [hmX] at this
    linarith
  have hmgt : -5853806 < m := by
    by_contra hnot
    have hmul := mul_le_mul_of_nonneg_right (not_lt.mp hnot) hXpos.le
    rw [hmX] at hmul
    linarith
  have hmw := even20_T_fixed_divisor ((n : ℤ) + (d : ℤ) + 10)
  have hmv := even20_T_fixed_divisor ((n : ℤ) + 10)
  have hwodd : 2 * ((n : ℤ) + (d : ℤ) + 10) + 1 = w := by dsimp [w]; ring
  have hvodd : 2 * ((n : ℤ) + 10) + 1 = v := by dsimp [v]; ring
  rw [hwodd] at hmw
  rw [hvodd] at hmv
  have hmdiv : (3200 : ℤ) ∣ m := by
    dsimp [m]
    exact dvd_sub hmw (hmv.mul_left 2)
  obtain ⟨q, hq⟩ := hmdiv
  have hqlo : -1830 < q := by rw [hq] at hmgt; omega
  have hqhi : q < 0 := by rw [hq] at hmneg; omega
  let t : ℕ := (-q).toNat
  have hqnonneg : 0 ≤ -q := by omega
  have htcast : (t : ℤ) = -q := by simp [t, Int.toNat_of_nonneg hqnonneg]
  have htpos : 0 < t := by omega
  have htlt : t < 1830 := by omega
  let ft : Fin 1830 := ⟨t, htlt⟩
  have hcover := even20_candidate_cover ft (by dsimp [ft]; omega)
  have hmt : m = -(3200 * (t : ℤ)) := by rw [hq, htcast]; ring
  have h227 := k20_allowed_int even20A227 even20_allowed_227 hS hmdef
  have h199 := k20_allowed_int even20A199 even20_allowed_199 hS hmdef
  have h233 := k20_allowed_int even20A233 even20_allowed_233 hS hmdef
  have h239 := k20_allowed_int even20A239 even20_allowed_239 hS hmdef
  have h211 := k20_allowed_int even20A211 even20_allowed_211 hS hmdef
  have h197 := k20_allowed_int even20A197 even20_allowed_197 hS hmdef
  have h241 := k20_allowed_int even20A241 even20_allowed_241 hS hmdef
  have hall : even20CandidateAllowed ft = true := by
    rw [hmt] at h227 h199 h233 h239 h211 h197 h241
    dsimp [even20CandidateAllowed, ft]
    simp only [Bool.and_eq_true]
    exact ⟨⟨⟨⟨⟨⟨h227, h199⟩, h233⟩, h239⟩, h211⟩, h197⟩, h241⟩
  have : False := by simpa [hcover] using hall
  exact this.elim

#print axioms no_gap_solution_four_even_twenty

/-! ## The row `k=24` -/

private abbrev even24S {R : Type} [CommRing R] (W : R) : R := evenTable24S W
private abbrev even24T {R : Type} [CommRing R] (W : R) : R := evenTable24T W

private def even24D (W : ℤ) : ℤ :=
  7057203580108800 * W ^ 10 - 4570482388374650880 * W ^ 8 +
    967347850298838220800 * W ^ 6 - 75155627950280722612224 * W ^ 4 +
    2044513741960343715840000 * W ^ 2 + 42678667773313061643878400

private lemma even24_square_identity (W : ℤ) :
    even24T W ^ 2 = even24S W + even24D W := by
  simp only [even24T, even24S, even24D, evenTable24T, evenTable24S]
  ring

set_option maxHeartbeats 3000000 in
private lemma even24_centered_poly (W : ℤ) :
    even24S W = centeredBlockProduct 24 W := by
  norm_num [centeredBlockProduct, even24S, evenTable24S,
    Finset.prod_Icc_succ_top, Finset.Icc_self, Finset.prod_singleton]
  ring

set_option maxHeartbeats 1000000 in
private lemma even24_centered_bridge (x : ℕ) :
    even24S (2 * (x : ℤ) + 25) =
      16777216 * (blockProduct 24 x : ℤ) := by
  rw [even24_centered_poly]
  convert centeredBlockProduct_center 24 x using 1 <;> norm_num

private def even24G (u : ℤ) : ℤ :=
  2 * u ^ 6 - 286 * u ^ 5 + 14300 * u ^ 4 - 304590 * u ^ 3 +
    2644785 * u ^ 2 - 8297991 * u - 50979537

private lemma even24_T_dvd_131072_at_odd (a : ℤ) :
    (131072 : ℤ) ∣ even24T (2 * a + 1) := by
  rcases Int.even_or_odd a with ⟨z, hz⟩ | ⟨z, hz⟩
  · refine ⟨even24G (2 * z ^ 2 + z), ?_⟩
    rw [hz]
    simp only [even24T, evenTable24T, even24G]
    ring
  · refine ⟨even24G (2 * z ^ 2 + 3 * z + 1), ?_⟩
    rw [hz]
    simp only [even24T, evenTable24T, even24G]
    ring

private lemma even24_T_dvd_81 (x : ℤ) : (81 : ℤ) ∣ even24T x := by
  have hx : ((even24T x : ℤ) : ZMod 81) = 0 := by
    have hall : ∀ y : ZMod 81,
        y ^ 12 - 1150 * y ^ 10 + 463335 * y ^ 8 - 79816900 * y ^ 6 +
          5653201855 * y ^ 4 - 147023085150 * y ^ 2 - 6540540635655 = 0 := by
      decide
    simpa [even24T, evenTable24T] using hall (x : ZMod 81)
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ 81).mp hx

private lemma even24_T_fixed_divisor (a : ℤ) :
    (10616832 : ℤ) ∣ even24T (2 * a + 1) := by
  have h2 := even24_T_dvd_131072_at_odd a
  have h81 := even24_T_dvd_81 (2 * a + 1)
  have hcop : IsCoprime (131072 : ℤ) 81 := ⟨29, -46927, by norm_num⟩
  simpa using hcop.mul_dvd h2 h81

set_option maxHeartbeats 3000000 in
private lemma even24_boundary_product (n : ℕ) (hnlo : 373 ≤ n)
    (hnhi : n ≤ 391) :
    4 * blockProduct 24 n < blockProduct 24 (n + 24) := by
  interval_cases n <;>
    norm_num [blockProduct, Finset.prod_Icc_succ_top, Finset.Icc_self,
      Finset.prod_singleton]

private lemma even24_base_ge_392 {n d : ℕ} (hd : 24 ≤ d)
    (hlin : 33 * (n + d + 24) < 35 * (n + 24))
    (heq : blockProduct 24 (n + d) = 4 * blockProduct 24 n) :
    392 ≤ n := by
  have hnlo : 373 ≤ n := by omega
  by_contra hnot
  have hnhi : n ≤ 391 := by omega
  have hbad := even24_boundary_product n hnlo hnhi
  have hmono := blockProduct_mono 24 (n + 24) (n + d) (by omega)
  rw [heq] at hmono
  omega

private lemma even24_T_pos {W : ℤ} (hW : 809 ≤ W) : 0 < even24T W := by
  obtain ⟨a, ha, rfl⟩ : ∃ a : ℤ, 0 ≤ a ∧ W = 809 + a :=
    ⟨W - 809, by omega, by omega⟩
  simp only [even24T, evenTable24T]
  nlinarith [ha, pow_nonneg ha 2, pow_nonneg ha 3, pow_nonneg ha 4,
    pow_nonneg ha 5, pow_nonneg ha 6, pow_nonneg ha 7, pow_nonneg ha 8,
    pow_nonneg ha 9, pow_nonneg ha 10, pow_nonneg ha 11, pow_nonneg ha 12]

private lemma even24_delta_lower {v w : ℤ} (hv : 809 ≤ v)
    (hvw : v + 48 ≤ w) :
    0 < even24D w + 5993518490 * even24T w + 11987036980 * even24T v -
      4 * even24D v := by
  obtain ⟨a, ha, rfl⟩ : ∃ a : ℤ, 0 ≤ a ∧ v = 809 + a :=
    ⟨v - 809, by omega, by omega⟩
  obtain ⟨b, hb, rfl⟩ : ∃ b : ℤ, 0 ≤ b ∧ w = 809 + a + 48 + b :=
    ⟨w - (809 + a + 48), by omega, by omega⟩
  simp only [even24D, even24T, evenTable24T]
  nlinarith [ha, hb,
    pow_nonneg ha 2, pow_nonneg ha 3, pow_nonneg ha 4, pow_nonneg ha 5,
    pow_nonneg ha 6, pow_nonneg ha 7, pow_nonneg ha 8, pow_nonneg ha 9,
    pow_nonneg ha 10, pow_nonneg ha 11, pow_nonneg ha 12,
    pow_nonneg hb 2, pow_nonneg hb 3, pow_nonneg hb 4, pow_nonneg hb 5,
    pow_nonneg hb 6, pow_nonneg hb 7, pow_nonneg hb 8, pow_nonneg hb 9,
    pow_nonneg hb 10, pow_nonneg hb 11, pow_nonneg hb 12, mul_nonneg ha hb]

private lemma even24_negative_upper {v : ℤ} (hv : 809 ≤ v) :
    (7057203580108800 * 17 ^ 10 - 4 * 7057203580108800 * 16 ^ 10) * v ^ 10 +
        4 * 4570482388374650880 * 16 ^ 10 * v ^ 8 +
        967347850298838220800 * 16 ^ 4 * 17 ^ 6 * v ^ 6 +
        4 * 75155627950280722612224 * 16 ^ 10 * v ^ 4 +
        2044513741960343715840000 * 16 ^ 8 * 17 ^ 2 * v ^ 2 < 0 := by
  obtain ⟨a, ha, rfl⟩ : ∃ a : ℤ, 0 ≤ a ∧ v = 809 + a :=
    ⟨v - 809, by omega, by omega⟩
  nlinarith [ha, pow_nonneg ha 2, pow_nonneg ha 3, pow_nonneg ha 4,
    pow_nonneg ha 5, pow_nonneg ha 6, pow_nonneg ha 7, pow_nonneg ha 8,
    pow_nonneg ha 9, pow_nonneg ha 10]

private lemma even24_delta_negative {v w : ℤ} (hv : 809 ≤ v)
    (hw : 0 ≤ w) (hupper : 16 * w ≤ 17 * v) :
    even24D w - 4 * even24D v < 0 := by
  have h10 : (16 * w) ^ 10 ≤ (17 * v) ^ 10 :=
    pow_le_pow_left₀ (by omega) hupper 10
  have h6 : (16 * w) ^ 6 ≤ (17 * v) ^ 6 :=
    pow_le_pow_left₀ (by omega) hupper 6
  have h2 : (16 * w) ^ 2 ≤ (17 * v) ^ 2 :=
    pow_le_pow_left₀ (by omega) hupper 2
  have hw8 : 0 ≤ w ^ 8 := pow_nonneg hw 8
  have hw4 : 0 ≤ w ^ 4 := pow_nonneg hw 4
  have hneg := even24_negative_upper hv
  simp only [even24D]
  ring_nf at h10 h6 h2
  nlinarith

private lemma k24_allowed_int
    {p : ℕ} [NeZero p] (A : ZMod p → Bool)
    (hallow : ∀ w v : ZMod p,
      even24S w = 4 * even24S v → A (even24T w - 2 * even24T v) = true)
    {w v m : ℤ} (hS : even24S w = 4 * even24S v)
    (hm : m = even24T w - 2 * even24T v) : A (m : ZMod p) = true := by
  have hSp : even24S (w : ZMod p) = 4 * even24S (v : ZMod p) := by
    have h := congrArg (fun z : ℤ => (z : ZMod p)) hS
    simpa [even24S, evenTable24S] using h
  subst m
  simpa [even24T, evenTable24T] using hallow (w : ZMod p) (v : ZMod p) hSp

/-- The row `k=24` has no quotient-four gap solution once `d≥24`. -/
theorem no_gap_solution_four_even_twentyfour {n d : ℕ} (hd : 24 ≤ d) :
    blockProduct 24 (n + d) ≠ 4 * blockProduct 24 n := by
  intro heq
  obtain ⟨hup, _hlo⟩ := ratio_window_four_nat heq
  have hlin :=
    ratio_window_linearize_of_pow_bracket (N := 4) (A := 35) (B := 33)
      (k := 24) (n := n) (d := d) (by norm_num) (by norm_num) hup
  have hn392 : 392 ≤ n := even24_base_ge_392 hd hlin heq
  have hZ : ((blockProduct 24 (n + d) : ℕ) : ℤ) =
      4 * ((blockProduct 24 n : ℕ) : ℤ) := by exact_mod_cast heq
  let w : ℤ := 2 * ((n : ℤ) + (d : ℤ)) + 25
  let v : ℤ := 2 * (n : ℤ) + 25
  have hv : 809 ≤ v := by dsimp [v]; omega
  have hw : 809 ≤ w := by dsimp [w]; omega
  have hvw : v + 48 ≤ w := by dsimp [v, w]; omega
  have hupper : 16 * w ≤ 17 * v := by dsimp [v, w]; omega
  have hs1 := even24_centered_bridge (n + d)
  have hs2 := even24_centered_bridge n
  have hcw : 2 * ((n + d : ℕ) : ℤ) + 25 = w := by dsimp [w]
  have hcv : 2 * (n : ℤ) + 25 = v := by rfl
  rw [hcw] at hs1
  rw [hcv] at hs2
  have hS : even24S w = 4 * even24S v := by rw [hs1, hs2, hZ]; ring
  let m : ℤ := even24T w - 2 * even24T v
  let X : ℤ := even24T w + 2 * even24T v
  have hTw : 0 < even24T w := even24_T_pos hw
  have hTv : 0 < even24T v := even24_T_pos hv
  have hXpos : 0 < X := by dsimp [X]; linarith
  have hmdef : m = even24T w - 2 * even24T v := rfl
  have hmX : m * X = even24D w - 4 * even24D v := by
    dsimp [m, X]
    calc
      (even24T w - 2 * even24T v) * (even24T w + 2 * even24T v) =
          even24T w ^ 2 - 4 * even24T v ^ 2 := by ring
      _ = (even24S w + even24D w) - 4 * (even24S v + even24D v) := by
        rw [even24_square_identity, even24_square_identity]
      _ = even24D w - 4 * even24D v := by rw [hS]; ring
  have hdeltaNeg := even24_delta_negative hv (by omega) hupper
  have hdeltaLower : -5993518490 * X < even24D w - 4 * even24D v := by
    have h := even24_delta_lower hv hvw
    dsimp [X]
    linarith
  have hmneg : m < 0 := by
    by_contra hnot
    have := mul_nonneg (not_lt.mp hnot) hXpos.le
    rw [hmX] at this
    linarith
  have hmgt : -5993518490 < m := by
    by_contra hnot
    have hmul := mul_le_mul_of_nonneg_right (not_lt.mp hnot) hXpos.le
    rw [hmX] at hmul
    linarith
  have hmw := even24_T_fixed_divisor ((n : ℤ) + (d : ℤ) + 12)
  have hmv := even24_T_fixed_divisor ((n : ℤ) + 12)
  have hwodd : 2 * ((n : ℤ) + (d : ℤ) + 12) + 1 = w := by dsimp [w]; ring
  have hvodd : 2 * ((n : ℤ) + 12) + 1 = v := by dsimp [v]; ring
  rw [hwodd] at hmw
  rw [hvodd] at hmv
  have hmdiv : (10616832 : ℤ) ∣ m := by
    dsimp [m]
    exact dvd_sub hmw (hmv.mul_left 2)
  obtain ⟨q, hq⟩ := hmdiv
  have hqlo : -565 < q := by rw [hq] at hmgt; omega
  have hqhi : q < 0 := by rw [hq] at hmneg; omega
  let t : ℕ := (-q).toNat
  have hqnonneg : 0 ≤ -q := by omega
  have htcast : (t : ℤ) = -q := by simp [t, Int.toNat_of_nonneg hqnonneg]
  have htpos : 0 < t := by omega
  have htlt : t < 565 := by omega
  let ft : Fin 565 := ⟨t, htlt⟩
  have hcover := even24_candidate_cover ft (by dsimp [ft]; omega)
  have hmt : m = -(10616832 * (t : ℤ)) := by rw [hq, htcast]; ring
  have h13 := k24_allowed_int even24A13 even24_allowed_13 hS hmdef
  have h191 := k24_allowed_int even24A191 even24_allowed_191 hS hmdef
  have h157 := k24_allowed_int even24A157 even24_allowed_157 hS hmdef
  have h227 := k24_allowed_int even24A227 even24_allowed_227 hS hmdef
  have h239 := k24_allowed_int even24A239 even24_allowed_239 hS hmdef
  have h241 := k24_allowed_int even24A241 even24_allowed_241 hS hmdef
  have h131 := k24_allowed_int even24A131 even24_allowed_131 hS hmdef
  have h197 := k24_allowed_int even24A197 even24_allowed_197 hS hmdef
  have h71 := k24_allowed_int even24A71 even24_allowed_71 hS hmdef
  have hall : even24CandidateAllowed ft = true := by
    rw [hmt] at h13 h191 h157 h227 h239 h241 h131 h197 h71
    dsimp [even24CandidateAllowed, ft]
    simp only [Bool.and_eq_true]
    exact ⟨⟨⟨⟨⟨⟨⟨⟨h13, h191⟩, h157⟩, h227⟩, h239⟩, h241⟩, h131⟩, h197⟩, h71⟩
  have : False := by simpa [hcover] using hall
  exact this.elim

#print axioms no_gap_solution_four_even_twentyfour

end Erdos686Variant
end Erdos686
