/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import ErdosProblems.Erdos686.Core.EvenTailRunge

/-!
# Erdős 686: generic coefficient certificate for every even Runge tail

This module kernel-banks the coefficientwise part of the arbitrary even-row
Runge argument.  It deliberately does not construct the polynomial part of
the square root for every row.  Instead, an explicit integral polynomial
certificate supplies that finite algebraic data and this file proves that
the data exclude quotient four beyond its stated threshold.
-/

namespace Erdos686
namespace Erdos686Variant

open Polynomial

/-- The exact `ℓ¹` norm of the coefficients of `P` in degrees `< m`. -/
def coefficientAbsSumBelow (P : Polynomial ℤ) (m : ℕ) : ℤ :=
  ∑ i ∈ Finset.range m, |P.coeff i|

lemma coefficientAbsSumBelow_nonneg (P : Polynomial ℤ) (m : ℕ) :
    0 ≤ coefficientAbsSumBelow P m := by
  exact Finset.sum_nonneg fun _ _ => abs_nonneg _

/-- Coefficientwise evaluation bound at a positive integral argument. -/
theorem polynomial_eval_abs_le_coefficientAbsSumBelow_mul_pow
    {P : Polynomial ℤ} {q : ℕ} {W : ℤ}
    (hdeg : P.natDegree ≤ q) (hW : 1 ≤ W) :
    |P.eval W| ≤ coefficientAbsSumBelow P (q + 1) * W ^ q := by
  have hWabs : |W| = W := abs_of_nonneg (by omega)
  rw [Polynomial.eval_eq_sum_range' (Nat.lt_succ_iff.mpr hdeg)]
  calc
    |∑ i ∈ Finset.range (q + 1), P.coeff i * W ^ i|
        ≤ ∑ i ∈ Finset.range (q + 1), |P.coeff i * W ^ i| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i ∈ Finset.range (q + 1), |P.coeff i| * W ^ i := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [abs_mul, abs_pow, hWabs]
    _ ≤ ∑ i ∈ Finset.range (q + 1), |P.coeff i| * W ^ q := by
      apply Finset.sum_le_sum
      intro i hi
      apply mul_le_mul_of_nonneg_left
      · exact pow_le_pow_right₀ hW (by simpa using hi)
      · exact abs_nonneg _
    _ = coefficientAbsSumBelow P (q + 1) * W ^ q := by
      rw [← Finset.sum_mul]
      rfl

/-- The lower-degree part of `P(W)` is bounded by its exact coefficient norm.
This formulation also covers `q=0`, where both sides vanish. -/
theorem polynomial_eval_sub_leading_abs_le
    {P : Polynomial ℤ} {q : ℕ} {W : ℤ}
    (hdeg : P.natDegree ≤ q) (hW : 1 ≤ W) :
    |P.eval W - P.coeff q * W ^ q| ≤
      coefficientAbsSumBelow P q * W ^ (q - 1) := by
  have hWabs : |W| = W := abs_of_nonneg (by omega)
  rw [Polynomial.eval_eq_sum_range' (Nat.lt_succ_iff.mpr hdeg)]
  rw [Finset.sum_range_succ]
  simp only [add_sub_cancel_right]
  by_cases hq : q = 0
  · subst q
    simp [coefficientAbsSumBelow]
  · have hqpos : 0 < q := Nat.pos_of_ne_zero hq
    calc
      |∑ i ∈ Finset.range q, P.coeff i * W ^ i|
          ≤ ∑ i ∈ Finset.range q, |P.coeff i * W ^ i| :=
        Finset.abs_sum_le_sum_abs _ _
      _ = ∑ i ∈ Finset.range q, |P.coeff i| * W ^ i := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [abs_mul, abs_pow, hWabs]
      _ ≤ ∑ i ∈ Finset.range q, |P.coeff i| * W ^ (q - 1) := by
        apply Finset.sum_le_sum
        intro i hi
        apply mul_le_mul_of_nonneg_left
        · exact pow_le_pow_right₀ hW (by
            have hiq : i < q := Finset.mem_range.mp hi
            omega)
        · exact abs_nonneg _
      _ = coefficientAbsSumBelow P q * W ^ (q - 1) := by
        rw [← Finset.sum_mul]
        rfl

/-- A positive leading coefficient and the explicit lower-coefficient norm
force the polynomial part above half of `W^r`. -/
theorem polynomial_part_two_mul_eval_gt_pow
    {T : Polynomial ℤ} {r : ℕ} {C W A : ℤ}
    (hr : 1 ≤ r) (hdeg : T.natDegree ≤ r) (hlead : T.coeff r = C)
    (hC : 1 ≤ C) (hA : A = coefficientAbsSumBelow T r)
    (hW : 1 ≤ W) (hthreshold : 2 * A < W) :
    W ^ r < 2 * T.eval W := by
  have hA0 : 0 ≤ A := by
    rw [hA]
    exact coefficientAbsSumBelow_nonneg T r
  have hUpos : 0 < W ^ (r - 1) := pow_pos (by omega) _
  have hpow : W ^ r = W ^ (r - 1) * W := by
    calc
      W ^ r = W ^ (r - 1 + 1) := by congr 1; omega
      _ = W ^ (r - 1) * W := pow_succ _ _
  have hrem := polynomial_eval_sub_leading_abs_le
    (P := T) (q := r) (W := W) hdeg hW
  rw [hlead, ← hA] at hrem
  have hlower : -(A * W ^ (r - 1)) ≤ T.eval W - C * W ^ r :=
    (neg_le_of_abs_le hrem)
  have hsmall : 2 * A * W ^ (r - 1) < W ^ r := by
    rw [hpow]
    nlinarith
  have hCpow : W ^ r ≤ C * W ^ r := by
    have hpow0 : 0 ≤ W ^ r := le_of_lt (pow_pos (by omega) _)
    nlinarith
  nlinarith

/-- Exact leading-term domination for a nonzero lower-degree deficit.  The
scaled form avoids every rational or asymptotic constant. -/
theorem deficit_six_seven_eight_dominance
    {D : Polynomial ℤ} {q : ℕ} {L W F : ℤ}
    (hdeg : D.natDegree ≤ q) (hlead : D.coeff q = L) (hL : L ≠ 0)
    (hF : F = coefficientAbsSumBelow D q)
    (hW : 1 ≤ W) (hthreshold : 7 * F < W) :
    6 * |L| * W ^ q < 7 * |D.eval W| ∧
      7 * |D.eval W| < 8 * |L| * W ^ q := by
  have hF0 : 0 ≤ F := by
    rw [hF]
    exact coefficientAbsSumBelow_nonneg D q
  have hLabs : 0 < |L| := abs_pos.mpr hL
  have hWabs : |W| = W := abs_of_nonneg (by omega)
  have hrem := polynomial_eval_sub_leading_abs_le
    (P := D) (q := q) (W := W) hdeg hW
  rw [hlead, ← hF] at hrem
  have hremStrict :
      7 * |D.eval W - L * W ^ q| < |L| * W ^ q := by
    by_cases hq : q = 0
    · subst q
      have hFzero : F = 0 := by
        simpa [coefficientAbsSumBelow] using hF
      simp only [pow_zero, Nat.zero_sub, mul_one] at hrem ⊢
      have hremzero : D.eval W - L = 0 := by
        rw [hFzero] at hrem
        simpa using (abs_eq_zero.mp (le_antisymm hrem (abs_nonneg _)))
      rw [hremzero, abs_zero]
      simpa using hLabs
    · have hqpos : 0 < q := Nat.pos_of_ne_zero hq
      have hUpos : 0 < W ^ (q - 1) := pow_pos (by omega) _
      have hpow : W ^ q = W ^ (q - 1) * W := by
        calc
          W ^ q = W ^ (q - 1 + 1) := by congr 1; omega
          _ = W ^ (q - 1) * W := pow_succ _ _
      have hsmall : 7 * F * W ^ (q - 1) < W ^ q := by
        rw [hpow]
        nlinarith
      have hleadLarge : W ^ q ≤ |L| * W ^ q := by
        have hpow0 : 0 ≤ W ^ q := le_of_lt (pow_pos (by omega) _)
        have hLone : 1 ≤ |L| := by omega
        nlinarith
      nlinarith
  have hleadAbs : |L * W ^ q| = |L| * W ^ q := by
    rw [abs_mul, abs_pow, hWabs]
  have hupperTriangle :
      |D.eval W| ≤ |D.eval W - L * W ^ q| + |L * W ^ q| := by
    calc
      |D.eval W| = |(D.eval W - L * W ^ q) + L * W ^ q| := by ring_nf
      _ ≤ |D.eval W - L * W ^ q| + |L * W ^ q| := abs_add_le _ _
  have hlowerTriangle :
      |L * W ^ q| ≤ |D.eval W - L * W ^ q| + |D.eval W| := by
    calc
      |L * W ^ q| = |-(D.eval W - L * W ^ q) + D.eval W| := by ring_nf
      _ ≤ |-(D.eval W - L * W ^ q)| + |D.eval W| := abs_add_le _ _
      _ = |D.eval W - L * W ^ q| + |D.eval W| := by rw [abs_neg]
  rw [hleadAbs] at hupperTriangle hlowerTriangle
  constructor <;> nlinarith

/-- A finite, auditable certificate for the Runge tail of the even row
`k=2r`.  Every norm and threshold is explicit data; no asymptotic notation
or hidden uniformity appears in the structure. -/
structure EvenTailCoefficientCertificate (r : ℕ) where
  S : Polynomial ℤ
  T : Polynomial ℤ
  D : Polynomial ℤ
  C : ℤ
  q : ℕ
  L : ℤ
  A : ℤ
  E : ℤ
  F : ℤ
  threshold : ℕ
  square_identity : T ^ 2 = Polynomial.C (C ^ 2) * S + D
  centered_bridge : ∀ x : ℕ,
    S.eval (2 * (x : ℤ) + (2 * r : ℤ) + 1) =
      centeredBlockProduct (2 * r) (2 * (x : ℤ) + (2 * r : ℤ) + 1)
  q_lt : q < r
  T_natDegree_le : T.natDegree ≤ r
  T_coeff_r : T.coeff r = C
  C_pos : 1 ≤ C
  D_natDegree_le : D.natDegree ≤ q
  D_coeff_q : D.coeff q = L
  L_ne_zero : L ≠ 0
  A_eq : A = coefficientAbsSumBelow T r
  E_eq : E = coefficientAbsSumBelow D (q + 1)
  F_eq : F = coefficientAbsSumBelow D q
  twice_A_lt : 2 * A < (threshold : ℤ)
  seven_F_lt : 7 * F < (threshold : ℤ)
  ten_E_lt : 10 * E < (threshold : ℤ)

lemma EvenTailCoefficientCertificate.eval_square_identity
    {r : ℕ} (cert : EvenTailCoefficientCertificate r) (W : ℤ) :
    cert.T.eval W ^ 2 = cert.C ^ 2 * cert.S.eval W + cert.D.eval W := by
  have h := congrArg (Polynomial.eval W) cert.square_identity
  simpa using h

private lemma gap_le_even_center_of_four_solution
    {r n d : ℕ} (hr : 2 ≤ r)
    (heq : blockProduct (2 * r) (n + d) =
      4 * blockProduct (2 * r) n) :
    d ≤ 2 * n + (2 * r + 1) := by
  have hwindow := two_r_mul_gap_lt_two_mul_n_add_two_r_of_four_solution
    (r := r) (n := n) (d := d) hr heq
  nlinarith

/-- A supplied explicit coefficient certificate excludes quotient four in
its whole even-row tail.  This is the equation-facing reusable theorem: the
only row-specific work left is constructing the finite certificate. -/
theorem no_even_tail_solution_of_coefficient_certificate
    {r : ℕ} (hr : 2 ≤ r) (cert : EvenTailCoefficientCertificate r)
    {n d : ℕ} (hd : max (2 * r) cert.threshold ≤ d) :
    blockProduct (2 * r) (n + d) ≠ 4 * blockProduct (2 * r) n := by
  intro heq
  have hdrow : 2 * r ≤ d := le_trans (le_max_left _ _) hd
  have hdthreshold : cert.threshold ≤ d :=
    le_trans (le_max_right _ _) hd
  let v : ℕ := 2 * n + (2 * r + 1)
  let w : ℕ := 2 * (n + d) + (2 * r + 1)
  have hvpos : 0 < v := by dsimp [v]; omega
  have hvw : v ≤ w := by dsimp [v, w]; omega
  have hdv : d ≤ v := by
    dsimp [v]
    exact gap_le_even_center_of_four_solution hr heq
  have hMv : cert.threshold ≤ v := le_trans hdthreshold hdv
  have hMw : cert.threshold ≤ w := le_trans hMv hvw
  have hvZ : (1 : ℤ) ≤ (v : ℤ) := by exact_mod_cast hvpos
  have hwZ : (1 : ℤ) ≤ (w : ℤ) := by exact_mod_cast (lt_of_lt_of_le hvpos hvw)
  have hTA_v : 2 * cert.A < (v : ℤ) := by
    exact lt_of_lt_of_le cert.twice_A_lt (by exact_mod_cast hMv)
  have hTA_w : 2 * cert.A < (w : ℤ) := by
    exact lt_of_lt_of_le cert.twice_A_lt (by exact_mod_cast hMw)
  have hTF_v : 7 * cert.F < (v : ℤ) := by
    exact lt_of_lt_of_le cert.seven_F_lt (by exact_mod_cast hMv)
  have hTF_w : 7 * cert.F < (w : ℤ) := by
    exact lt_of_lt_of_le cert.seven_F_lt (by exact_mod_cast hMw)
  have hTE_w : 10 * cert.E < (w : ℤ) := by
    exact lt_of_lt_of_le cert.ten_E_lt (by exact_mod_cast hMw)
  have hTpow_v : (v : ℤ) ^ r < 2 * cert.T.eval (v : ℤ) :=
    polynomial_part_two_mul_eval_gt_pow (by omega) cert.T_natDegree_le
      cert.T_coeff_r cert.C_pos cert.A_eq hvZ hTA_v
  have hTpow_w : (w : ℤ) ^ r < 2 * cert.T.eval (w : ℤ) :=
    polynomial_part_two_mul_eval_gt_pow (by omega) cert.T_natDegree_le
      cert.T_coeff_r cert.C_pos cert.A_eq hwZ hTA_w
  have hTvpos : 0 < cert.T.eval (v : ℤ) := by
    have : (0 : ℤ) < (v : ℤ) ^ r := pow_pos (by omega) _
    nlinarith
  have hTwpos : 0 < cert.T.eval (w : ℤ) := by
    have : (0 : ℤ) < (w : ℤ) ^ r := pow_pos (by omega) _
    nlinarith
  have hDnorm_v : |cert.D.eval (v : ℤ)| ≤ cert.E * (v : ℤ) ^ cert.q := by
    simpa [cert.E_eq] using
      (polynomial_eval_abs_le_coefficientAbsSumBelow_mul_pow
        cert.D_natDegree_le hvZ)
  have hDnorm_w : |cert.D.eval (w : ℤ)| ≤ cert.E * (w : ℤ) ^ cert.q := by
    simpa [cert.E_eq] using
      (polynomial_eval_abs_le_coefficientAbsSumBelow_mul_pow
        cert.D_natDegree_le hwZ)
  have hE0 : 0 ≤ cert.E := by
    rw [cert.E_eq]
    exact coefficientAbsSumBelow_nonneg cert.D (cert.q + 1)
  have hvwZ : (v : ℤ) ≤ (w : ℤ) := by exact_mod_cast hvw
  have hvq_le_hwq : (v : ℤ) ^ cert.q ≤ (w : ℤ) ^ cert.q :=
    pow_le_pow_left₀ (by omega) hvwZ cert.q
  have hDnorm_v_w : |cert.D.eval (v : ℤ)| ≤
      cert.E * (w : ℤ) ^ cert.q := by
    exact le_trans hDnorm_v (mul_le_mul_of_nonneg_left hvq_le_hwq hE0)
  have hqsucc : cert.q + 1 ≤ r := Nat.succ_le_iff.mpr cert.q_lt
  have hpow_qsucc_le_r : (w : ℤ) ^ (cert.q + 1) ≤ (w : ℤ) ^ r :=
    pow_le_pow_right₀ hwZ hqsucc
  have hten :
      10 * cert.E * (w : ℤ) ^ cert.q < (w : ℤ) ^ (cert.q + 1) := by
    have hwqpos : 0 < (w : ℤ) ^ cert.q := pow_pos (by omega) _
    calc
      10 * cert.E * (w : ℤ) ^ cert.q
          < (w : ℤ) * (w : ℤ) ^ cert.q :=
        mul_lt_mul_of_pos_right hTE_w hwqpos
      _ = (w : ℤ) ^ (cert.q + 1) := by rw [pow_succ]; ring
  have hfive : 5 * cert.E * (w : ℤ) ^ cert.q < cert.T.eval (w : ℤ) := by
    have htenTw : 10 * cert.E * (w : ℤ) ^ cert.q <
        2 * cert.T.eval (w : ℤ) :=
      lt_of_lt_of_le hten (le_trans hpow_qsucc_le_r (le_of_lt hTpow_w))
    nlinarith only [htenTw]
  have hdiffTriangle :
      |cert.D.eval (w : ℤ) - 4 * cert.D.eval (v : ℤ)| ≤
        |cert.D.eval (w : ℤ)| + 4 * |cert.D.eval (v : ℤ)| := by
    calc
      |cert.D.eval (w : ℤ) - 4 * cert.D.eval (v : ℤ)|
          ≤ |cert.D.eval (w : ℤ)| + |4 * cert.D.eval (v : ℤ)| := abs_sub _ _
      _ = |cert.D.eval (w : ℤ)| + 4 * |cert.D.eval (v : ℤ)| := by norm_num
  have hsmall :
      |cert.D.eval (w : ℤ) - 4 * cert.D.eval (v : ℤ)| <
        cert.T.eval (w : ℤ) + 2 * cert.T.eval (v : ℤ) := by
    have hsum : |cert.D.eval (w : ℤ)| + 4 * |cert.D.eval (v : ℤ)| ≤
        5 * cert.E * (w : ℤ) ^ cert.q := by
      have hfour := mul_le_mul_of_nonneg_left hDnorm_v_w (by norm_num : (0 : ℤ) ≤ 4)
      calc
        |cert.D.eval (w : ℤ)| + 4 * |cert.D.eval (v : ℤ)|
            ≤ cert.E * (w : ℤ) ^ cert.q +
                4 * (cert.E * (w : ℤ) ^ cert.q) := add_le_add hDnorm_w hfour
        _ = 5 * cert.E * (w : ℤ) ^ cert.q := by ring
    exact lt_of_le_of_lt (le_trans hdiffTriangle hsum)
      (lt_trans hfive (by nlinarith only [hTvpos]))
  obtain ⟨hdomVlower, hdomVupper⟩ := deficit_six_seven_eight_dominance
    cert.D_natDegree_le cert.D_coeff_q cert.L_ne_zero cert.F_eq hvZ hTF_v
  obtain ⟨hdomWlower, hdomWupper⟩ := deficit_six_seven_eight_dominance
    cert.D_natDegree_le cert.D_coeff_q cert.L_ne_zero cert.F_eq hwZ hTF_w
  have hpowNat := even_center_pow_lt_three_of_four_solution
    (r := r) (q := cert.q) (n := n) (d := d) hr hdrow cert.q_lt heq
  have hpowZ : (w : ℤ) ^ cert.q < 3 * (v : ℤ) ^ cert.q := by
    exact_mod_cast hpowNat
  have hLpos : (0 : ℤ) < |cert.L| := abs_pos.mpr cert.L_ne_zero
  have hpowScaled : |cert.L| * (w : ℤ) ^ cert.q <
      3 * (|cert.L| * (v : ℤ) ^ cert.q) := by
    calc
      |cert.L| * (w : ℤ) ^ cert.q
          < |cert.L| * (3 * (v : ℤ) ^ cert.q) :=
        mul_lt_mul_of_pos_left hpowZ hLpos
      _ = 3 * (|cert.L| * (v : ℤ) ^ cert.q) := by ring
  have hratio : |cert.D.eval (w : ℤ)| <
      4 * |cert.D.eval (v : ℤ)| := by
    have hchain : 7 * |cert.D.eval (w : ℤ)| <
        28 * |cert.D.eval (v : ℤ)| := by
      calc
        7 * |cert.D.eval (w : ℤ)|
            < 8 * |cert.L| * (w : ℤ) ^ cert.q := hdomWupper
        _ = 8 * (|cert.L| * (w : ℤ) ^ cert.q) := by ring
        _ < 8 * (3 * (|cert.L| * (v : ℤ) ^ cert.q)) :=
          mul_lt_mul_of_pos_left hpowScaled (by norm_num)
        _ = 4 * (6 * |cert.L| * (v : ℤ) ^ cert.q) := by ring
        _ < 4 * (7 * |cert.D.eval (v : ℤ)|) :=
          mul_lt_mul_of_pos_left hdomVlower (by norm_num)
        _ = 28 * |cert.D.eval (v : ℤ)| := by ring
    nlinarith only [hchain]
  have hS : cert.S.eval (w : ℤ) = 4 * cert.S.eval (v : ℤ) := by
    have heqZ : (blockProduct (2 * r) (n + d) : ℤ) =
        4 * (blockProduct (2 * r) n : ℤ) := by exact_mod_cast heq
    have hbridgeW : cert.S.eval (w : ℤ) =
        (2 ^ (2 * r) : ℤ) * (blockProduct (2 * r) (n + d) : ℤ) := by
      calc
        cert.S.eval (w : ℤ) = centeredBlockProduct (2 * r)
            (2 * ((n + d : ℕ) : ℤ) + (2 * r : ℤ) + 1) := by
          dsimp [w]
          simpa [Nat.cast_add, Nat.cast_mul, add_assoc] using
            cert.centered_bridge (n + d)
        _ = (2 ^ (2 * r) : ℤ) * (blockProduct (2 * r) (n + d) : ℤ) :=
          centeredBlockProduct_center (2 * r) (n + d)
    have hbridgeV : cert.S.eval (v : ℤ) =
        (2 ^ (2 * r) : ℤ) * (blockProduct (2 * r) n : ℤ) := by
      calc
        cert.S.eval (v : ℤ) = centeredBlockProduct (2 * r)
            (2 * (n : ℤ) + (2 * r : ℤ) + 1) := by
          dsimp [v]
          simpa [Nat.cast_add, Nat.cast_mul, add_assoc] using
            cert.centered_bridge n
        _ = (2 ^ (2 * r) : ℤ) * (blockProduct (2 * r) n : ℤ) :=
          centeredBlockProduct_center (2 * r) n
    rw [hbridgeW, hbridgeV, heqZ]
    ring
  exact integral_runge_trap hTwpos hTvpos
    (cert.eval_square_identity (w : ℤ))
    (cert.eval_square_identity (v : ℤ)) hS hsmall hratio

/-- Uniform wrapper: any constructive certificate supply gives an effective
tail theorem for every even row. -/
theorem no_even_tail_solution_of_coefficient_certificate_supply
    (supply : ∀ r : ℕ, 2 ≤ r → EvenTailCoefficientCertificate r)
    {r n d : ℕ} (hr : 2 ≤ r)
    (hd : max (2 * r) (supply r hr).threshold ≤ d) :
    blockProduct (2 * r) (n + d) ≠ 4 * blockProduct (2 * r) n :=
  no_even_tail_solution_of_coefficient_certificate hr (supply r hr) hd

#print axioms polynomial_eval_abs_le_coefficientAbsSumBelow_mul_pow
#print axioms polynomial_eval_sub_leading_abs_le
#print axioms polynomial_part_two_mul_eval_gt_pow
#print axioms deficit_six_seven_eight_dominance
#print axioms EvenTailCoefficientCertificate.eval_square_identity
#print axioms no_even_tail_solution_of_coefficient_certificate
#print axioms no_even_tail_solution_of_coefficient_certificate_supply

end Erdos686Variant
end Erdos686
