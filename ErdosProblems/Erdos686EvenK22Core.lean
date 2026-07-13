/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import ErdosProblems.Erdos686EvenK22FiniteStrip
import ErdosProblems.Erdos686CenterComponentLogStrip

/-!
# Erdős 686: Archimedean and finite-strip core for the even row `k=22`

Gaps `22 ≤ d ≤ 26` use the quadratic strip.  Gaps `27 ≤ d ≤ 249`
are certified by exact ordinary-kernel tables.  For `d ≥ 250`, the centered
square-root polynomial reduces a solution to an odd candidate
`1 ≤ t ≤ 3795146531` with error `-33t`.
-/

namespace Erdos686
namespace Erdos686Variant

def evenTable22D (W : ℤ) : ℤ :=
  463278576995462272 * W ^ 10
     - 216425162804858318080 * W ^ 8
     + 31355359404386247301764 * W ^ 6
     - 1470309582711394865435644 * W ^ 4
     + 21668018076062298043697209 * W ^ 2
     + 12389157521837708451840000

theorem even22_square_identity (W : ℤ) :
    evenTable22T W ^ 2 = 65536 * evenTable22S W + evenTable22D W := by
  simp only [evenTable22T, evenTable22S, evenTable22D]
  ring

set_option maxHeartbeats 5000000 in
private lemma even22_centered_poly (W : ℤ) :
    evenTable22S W = centeredBlockProduct 22 W := by
  norm_num [centeredBlockProduct, evenTable22S,
    Finset.prod_Icc_succ_top, Finset.Icc_self, Finset.prod_singleton]
  ring

set_option maxHeartbeats 1000000 in
theorem even22_centered_bridge (x : ℕ) :
    evenTable22S (2 * (x : ℤ) + 23) =
      4194304 * (blockProduct 22 x : ℤ) := by
  rw [even22_centered_poly]
  convert centeredBlockProduct_center 22 x using 1 <;> norm_num

theorem even22_T_fixed_divisor (a : ℤ) :
    (33 : ℤ) ∣ evenTable22T (2 * a + 1) := by
  have hx : ((evenTable22T (2 * a + 1) : ℤ) : ZMod 33) = 0 := by
    have hall : ∀ y : ZMod 33, evenTable22T (2 * y + 1) = 0 := by decide
    simp only [evenTable22T] at hall ⊢
    push_cast
    exact hall (a : ZMod 33)
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ 33).mp hx

theorem even22_T_fixed_divisor_maximal (c : ℤ)
    (hc : ∀ a : ℤ, c ∣ evenTable22T (2 * a + 1)) : c ∣ 33 := by
  have h1 := hc 0
  have h3 := hc 1
  have hcomb := dvd_add (h1.mul_left (-72113493154))
    (h3.mul_left 39309729457)
  norm_num [evenTable22T] at hcomb
  exact hcomb

theorem even22_T_odd_at_odd (a : ℤ) :
    Odd (evenTable22T (2 * a + 1)) := by
  refine ⟨128 * (2 * a + 1) ^ 11 - 113344 * (2 * a + 1) ^ 9 +
      33804848 * (2 * a + 1) ^ 7 - 4055681080 * (2 * a + 1) ^ 5 +
      176248689155 * (2 * a + 1) ^ 3 -
      3027835453227 * (2 * a + 1) + a, ?_⟩
  simp only [evenTable22T]
  ring

private lemma even22_T_pos {W : ℤ} (hW : 7481 ≤ W) :
    0 < evenTable22T W := by
  obtain ⟨a, ha, rfl⟩ : ∃ a : ℤ, 0 ≤ a ∧ W = 7481 + a :=
    ⟨W - 7481, by omega, by omega⟩
  simp only [evenTable22T]
  ring_nf
  positivity

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 1000000 in
private lemma even22_delta_lower {v w : ℤ} (hv : 7481 ≤ v)
    (hvw : v + 500 ≤ w) :
    0 < evenTable22D w + 125239835548 * evenTable22T w +
      250479671096 * evenTable22T v - 4 * evenTable22D v := by
  obtain ⟨a, ha, rfl⟩ : ∃ a : ℤ, 0 ≤ a ∧ v = 7481 + a :=
    ⟨v - 7481, by omega, by omega⟩
  obtain ⟨b, hb, rfl⟩ : ∃ b : ℤ, 0 ≤ b ∧ w = 7481 + a + 500 + b :=
    ⟨w - (7481 + a + 500), by omega, by omega⟩
  simp only [evenTable22D, evenTable22T]
  ring_nf
  positivity

set_option maxHeartbeats 10000000 in
private lemma even22_negative_upper {v : ℤ} (hv : 7481 ≤ v) :
    - 268872167393751302818690261888 * v ^ 10
     + 250407943180975684851176251064320 * v ^ 8
     + 13720548717729993963362320089000000 * v ^ 6
     + 1701175564220364225541140612609458176 * v ^ 4
     + 7194920386919155881097173934487558400 * v ^ 2 < 0 := by
  obtain ⟨a, ha, rfl⟩ : ∃ a : ℤ, 0 ≤ a ∧ v = 7481 + a :=
    ⟨v - 7481, by omega, by omega⟩
  nlinarith [ha, pow_nonneg ha 2, pow_nonneg ha 3, pow_nonneg ha 4,
    pow_nonneg ha 5, pow_nonneg ha 6, pow_nonneg ha 7,
    pow_nonneg ha 8, pow_nonneg ha 9, pow_nonneg ha 10]

private lemma even22_delta_negative {v w : ℤ} (hv : 7481 ≤ v)
    (hw : 0 ≤ w) (hupper : 14 * w ≤ 15 * v) :
    evenTable22D w - 4 * evenTable22D v < 0 := by
  have h10 : (14 * w) ^ 10 ≤ (15 * v) ^ 10 :=
    pow_le_pow_left₀ (by omega) hupper 10
  have h6 : (14 * w) ^ 6 ≤ (15 * v) ^ 6 :=
    pow_le_pow_left₀ (by omega) hupper 6
  have h2 : (14 * w) ^ 2 ≤ (15 * v) ^ 2 :=
    pow_le_pow_left₀ (by omega) hupper 2
  have hw8 : 0 ≤ w ^ 8 := pow_nonneg hw 8
  have hw4 : 0 ≤ w ^ 4 := pow_nonneg hw 4
  have hneg := even22_negative_upper hv
  simp only [evenTable22D]
  ring_nf at h10 h6 h2
  nlinarith

private lemma lower_ratio_linearize_22
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

theorem even22_small_gap_impossible {n d : ℕ} (hd : 22 ≤ d)
    (hd249 : d ≤ 249)
    (heq : blockProduct 22 (n + d) = 4 * blockProduct 22 n) : False := by
  by_cases hd26 : d ≤ 26
  · exact (no_four_solution_of_quadratic_strip
      (k := 22) (n := n) (d := d) (by norm_num) hd (by omega)) heq
  · obtain ⟨hup, hlo⟩ := ratio_window_four_nat heq
    have hlin :=
      ratio_window_linearize_of_pow_bracket (N := 4) (A := 16) (B := 15)
        (k := 22) (n := n) (d := d) (by norm_num) (by norm_num) hup
    have hlow := lower_ratio_linearize_22 (N := 4) (A := 82) (B := 77)
      (k := 22) (n := n) (d := d) (by norm_num) hlo
    have hn3834 : n < 3834 := by omega
    let fd : Fin 250 := ⟨d, by omega⟩
    let fn : Fin 3834 := ⟨n, hn3834⟩
    have hstrip := even22_finite_strip fd (by dsimp [fd]; omega) fn
      (by dsimp [fd, fn]; omega) (by dsimp [fd, fn]; omega)
    have hZ : ((blockProduct 22 (n + d) : ℕ) : ℤ) =
        4 * ((blockProduct 22 n : ℕ) : ℤ) := by exact_mod_cast heq
    have hs1 := even22_centered_bridge (n + d)
    have hs2 := even22_centered_bridge n
    dsimp [fd, fn] at hstrip
    push_cast at hs1 hs2
    apply hstrip
    change evenTable22S (2 * ((n : ℤ) + (d : ℤ)) + 23) =
      4 * evenTable22S (2 * (n : ℤ) + 23)
    rw [hs1, hs2, hZ]
    ring

private lemma even22_quotient_candidate {m q : ℤ}
    (hmgt : -125239835548 < m) (hmneg : m < 0)
    (hq : m = 33 * q) :
    ∃ t : ℕ, m = -(33 * (t : ℤ)) ∧ 1 ≤ t ∧
      t ≤ 3795146531 := by
  have hqlo : -3795146532 < q := by
    rw [hq] at hmgt
    omega
  have hqhi : q < 0 := by
    rw [hq] at hmneg
    omega
  let t : ℕ := (-q).toNat
  have hqnonneg : 0 ≤ -q := by omega
  have htcast : (t : ℤ) = -q := by
    simp [t, Int.toNat_of_nonneg hqnonneg]
  have htpos : 1 ≤ t := by omega
  have htbound : t ≤ 3795146531 := by omega
  have hmt : m = -(33 * (t : ℤ)) := by rw [hq, htcast]; ring
  exact ⟨t, hmt, htpos, htbound⟩

/-- The exact large-gap k=22 Archimedean reduction consumed by the packed cover. -/
theorem even22_large_gap_reduction {n d : ℕ} (hd250 : 250 ≤ d)
    (heq : blockProduct 22 (n + d) = 4 * blockProduct 22 n) :
    ∃ w v : ℤ, ∃ t : ℕ,
      evenTable22S w = 4 * evenTable22S v ∧
      -(33 * (t : ℤ)) = evenTable22T w - 2 * evenTable22T v ∧
      1 ≤ t ∧ t ≤ 3795146531 ∧ Odd t := by
  obtain ⟨hup, _hlo⟩ := ratio_window_four_nat heq
  have hlin :=
    ratio_window_linearize_of_pow_bracket (N := 4) (A := 16) (B := 15)
      (k := 22) (n := n) (d := d) (by norm_num) (by norm_num) hup
  have hn3729 : 3729 ≤ n := by omega
  have hZ : ((blockProduct 22 (n + d) : ℕ) : ℤ) =
      4 * ((blockProduct 22 n : ℕ) : ℤ) := by exact_mod_cast heq
  let w : ℤ := 2 * ((n : ℤ) + (d : ℤ)) + 23
  let v : ℤ := 2 * (n : ℤ) + 23
  have hv : 7481 ≤ v := by dsimp [v]; omega
  have hw : 7481 ≤ w := by dsimp [w]; omega
  have hvw : v + 500 ≤ w := by dsimp [v, w]; omega
  have hupper : 14 * w ≤ 15 * v := by dsimp [v, w]; omega
  have hs1 := even22_centered_bridge (n + d)
  have hs2 := even22_centered_bridge n
  have hcw : 2 * ((n + d : ℕ) : ℤ) + 23 = w := by dsimp [w]
  have hcv : 2 * (n : ℤ) + 23 = v := by rfl
  rw [hcw] at hs1
  rw [hcv] at hs2
  have hS : evenTable22S w = 4 * evenTable22S v := by
    rw [hs1, hs2, hZ]
    ring
  let m : ℤ := evenTable22T w - 2 * evenTable22T v
  let X : ℤ := evenTable22T w + 2 * evenTable22T v
  have hTw : 0 < evenTable22T w := even22_T_pos hw
  have hTv : 0 < evenTable22T v := even22_T_pos hv
  have hXpos : 0 < X := by dsimp [X]; linarith
  have hmdef : m = evenTable22T w - 2 * evenTable22T v := rfl
  have hmX : m * X = evenTable22D w - 4 * evenTable22D v := by
    dsimp [m, X]
    calc
      (evenTable22T w - 2 * evenTable22T v) *
          (evenTable22T w + 2 * evenTable22T v) =
          evenTable22T w ^ 2 - 4 * evenTable22T v ^ 2 := by ring
      _ = (65536 * evenTable22S w + evenTable22D w) -
          4 * (65536 * evenTable22S v + evenTable22D v) := by
        rw [even22_square_identity, even22_square_identity]
      _ = evenTable22D w - 4 * evenTable22D v := by rw [hS]; ring
  have hdeltaNeg := even22_delta_negative hv (by omega) hupper
  have hdeltaLower :
      -125239835548 * X < evenTable22D w - 4 * evenTable22D v := by
    have h := even22_delta_lower hv hvw
    dsimp [X]
    linarith
  have hmneg : m < 0 := by
    by_contra hnot
    have hnonneg := mul_nonneg (not_lt.mp hnot) hXpos.le
    rw [hmX] at hnonneg
    linarith
  have hmgt : -125239835548 < m := by
    by_contra hnot
    have hmul := mul_le_mul_of_nonneg_right (not_lt.mp hnot) hXpos.le
    rw [hmX] at hmul
    linarith
  have hmw := even22_T_fixed_divisor ((n : ℤ) + (d : ℤ) + 11)
  have hmv := even22_T_fixed_divisor ((n : ℤ) + 11)
  have hwodd : 2 * ((n : ℤ) + (d : ℤ) + 11) + 1 = w := by
    dsimp [w]
    ring
  have hvodd : 2 * ((n : ℤ) + 11) + 1 = v := by
    dsimp [v]
    ring
  rw [hwodd] at hmw
  rw [hvodd] at hmv
  have hmdiv : (33 : ℤ) ∣ m := by
    dsimp [m]
    exact dvd_sub hmw (hmv.mul_left 2)
  obtain ⟨q, hq⟩ := hmdiv
  obtain ⟨t, hmt, htpos, htbound⟩ :=
    even22_quotient_candidate hmgt hmneg hq
  have htarget : -(33 * (t : ℤ)) = evenTable22T w - 2 * evenTable22T v := by
    rw [← hmdef, hmt]
  have hmwOdd : Odd (evenTable22T w) := by
    rw [← hwodd]
    exact even22_T_odd_at_odd ((n : ℤ) + (d : ℤ) + 11)
  have hmOdd : Odd m := by
    dsimp [m]
    exact hmwOdd.sub_even (even_two_mul (evenTable22T v))
  have hprodOdd : Odd ((33 : ℤ) * (t : ℤ)) := by
    simpa [hmt] using hmOdd.neg
  have htOdd : Odd t := by
    rcases Nat.even_or_odd t with htEven | htOdd
    · obtain ⟨u, hu⟩ := htEven
      have hucast : (t : ℤ) = 2 * (u : ℤ) := by
        push_cast
        omega
      obtain ⟨z, hz⟩ := hprodOdd
      rw [hucast] at hz
      omega
    · exact htOdd
  exact ⟨w, v, t, hS, htarget, htpos, htbound, htOdd⟩

/-- Conditional row closure from any contradiction for the exact odd candidate surface. -/
theorem no_gap_solution_four_even_twentytwo_of_large_obstruction
    (hobstruct : ∀ {w v : ℤ} {t : ℕ},
      evenTable22S w = 4 * evenTable22S v →
      -(33 * (t : ℤ)) = evenTable22T w - 2 * evenTable22T v →
      1 ≤ t → t ≤ 3795146531 → Odd t → False)
    {n d : ℕ} (hd : 22 ≤ d) :
    blockProduct 22 (n + d) ≠ 4 * blockProduct 22 n := by
  intro heq
  by_cases hd250 : 250 ≤ d
  · obtain ⟨w, v, t, hS, htarget, htpos, htbound, htOdd⟩ :=
      even22_large_gap_reduction hd250 heq
    exact hobstruct hS htarget htpos htbound htOdd
  · exact even22_small_gap_impossible hd (by omega) heq

end Erdos686Variant
end Erdos686
