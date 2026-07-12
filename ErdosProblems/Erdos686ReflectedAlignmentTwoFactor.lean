/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import ErdosProblems.Erdos686ReflectedAlignmentSquareLift

/-!
# Erdős 686: exclusion of a two-factor large reflection center

The reflected square lift becomes rigid when the whole reflection center is
the product of two coprime large-prime-power components.  This module first
proves the exact arithmetic core; the equation-level specialization follows
from the center square-lift theorem.
-/

namespace Erdos686
namespace Erdos686Variant

def evenReflectedLinearNat (k n d i : ℕ) : ℕ :=
  n + d + (k + 1 - i) + 4 * (n + i)

def oddReflectedLinearNat (k n d i : ℕ) : ℕ :=
  4 * (n + i) - (n + d + (k + 1 - i))

private lemma coprime_localBlockCoefficientNat_of_large_support
    {k q i : ℕ} (hi : i ∈ Finset.Icc 1 k)
    (hsupport : ∀ p, p.Prime → p ∣ q → k < p) :
    q.Coprime (localBlockCoefficientNat k i) := by
  by_contra hnot
  obtain ⟨p, hp, hpq, hpCoeff⟩ :=
    Nat.Prime.not_coprime_iff_dvd.mp hnot
  exact prime_not_dvd_localBlockCoefficientNat hp
    (Nat.le_of_lt (hsupport p hp hpq)) hi hpCoeff

private lemma even_reflected_linear_eq
    {k n d i : ℕ} (hi : i ∈ Finset.Icc 1 k) :
    evenReflectedLinearNat k n d i = 5 * n + d + k + 1 + 3 * i := by
  have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
  have hik : i ≤ k := (Finset.mem_Icc.mp hi).2
  unfold evenReflectedLinearNat
  omega

private lemma odd_reflected_linear_eq
    {k n d i : ℕ} (hk : 16 ≤ k) (hd : k ≤ d) (hn9 : 9 * d < n)
    (hi : i ∈ Finset.Icc 1 k) :
    oddReflectedLinearNat k n d i = 3 * n - d - k - 1 + 5 * i := by
  have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
  have hik : i ≤ k := (Finset.mem_Icc.mp hi).2
  unfold oddReflectedLinearNat
  omega

private lemma even_reflected_linear_pos_le
    {k n d i : ℕ} (hk : 16 ≤ k) (hd : k ≤ d) (hn9 : 9 * d < n)
    (hi : i ∈ Finset.Icc 1 k) :
    0 < evenReflectedLinearNat k n d i ∧
      evenReflectedLinearNat k n d i ≤ 7 * n := by
  rw [even_reflected_linear_eq hi]
  have hik : i ≤ k := (Finset.mem_Icc.mp hi).2
  constructor <;> omega

private lemma odd_reflected_linear_pos_le
    {k n d i : ℕ} (hk : 16 ≤ k) (hd : k ≤ d) (hn9 : 9 * d < n)
    (hi : i ∈ Finset.Icc 1 k) :
    0 < oddReflectedLinearNat k n d i ∧
      oddReflectedLinearNat k n d i ≤ 7 * n := by
  rw [odd_reflected_linear_eq hk hd hn9 hi]
  have hik : i ≤ k := (Finset.mem_Icc.mp hi).2
  constructor <;> omega

private lemma even_reflected_product_bounds
    {k n d i j : ℕ} (hk : 16 ≤ k) (hd : k ≤ d) (hn9 : 9 * d < n)
    (hi : i ∈ Finset.Icc 1 k) (hj : j ∈ Finset.Icc 1 k) :
    5 * (2 * n + d + k + 1) ^ 2 <
        evenReflectedLinearNat k n d i * evenReflectedLinearNat k n d j ∧
      evenReflectedLinearNat k n d i * evenReflectedLinearNat k n d j <
        8 * (2 * n + d + k + 1) ^ 2 := by
  let S := 2 * n + d + k + 1
  let Li := evenReflectedLinearNat k n d i
  let Lj := evenReflectedLinearNat k n d j
  have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
  have hik : i ≤ k := (Finset.mem_Icc.mp hi).2
  have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
  have hjk : j ≤ k := (Finset.mem_Icc.mp hj).2
  have hSpos : 0 < S := by dsimp [S]; omega
  have hLipos : 0 < Li := by dsimp [Li, evenReflectedLinearNat]; omega
  have hLjpos : 0 < Lj := by dsimp [Lj, evenReflectedLinearNat]; omega
  have hLiLower : 9 * S < 4 * Li := by
    dsimp [Li]
    rw [even_reflected_linear_eq hi]
    dsimp [S]
    omega
  have hLjLower : 9 * S < 4 * Lj := by
    dsimp [Lj]
    rw [even_reflected_linear_eq hj]
    dsimp [S]
    omega
  have hLiUpper : 5 * Li < 14 * S := by
    dsimp [Li]
    rw [even_reflected_linear_eq hi]
    dsimp [S]
    omega
  have hLjUpper : 5 * Lj < 14 * S := by
    dsimp [Lj]
    rw [even_reflected_linear_eq hj]
    dsimp [S]
    omega
  have hlowerMul : (9 * S) * (9 * S) < (4 * Li) * (4 * Lj) :=
    mul_lt_mul hLiLower (le_of_lt hLjLower) (by positivity) (by positivity)
  have hupperMul : (5 * Li) * (5 * Lj) < (14 * S) * (14 * S) :=
    mul_lt_mul hLiUpper (le_of_lt hLjUpper) (by positivity) (by positivity)
  constructor <;> dsimp [S, Li, Lj] at * <;> nlinarith

private lemma odd_reflected_product_bounds
    {k n d i j : ℕ} (hk : 16 ≤ k) (hd : k ≤ d) (hn9 : 9 * d < n)
    (hi : i ∈ Finset.Icc 1 k) (hj : j ∈ Finset.Icc 1 k) :
    (2 * n + d + k + 1) ^ 2 <
        oddReflectedLinearNat k n d i * oddReflectedLinearNat k n d j ∧
      oddReflectedLinearNat k n d i * oddReflectedLinearNat k n d j <
        4 * (2 * n + d + k + 1) ^ 2 := by
  let S := 2 * n + d + k + 1
  let Mi := oddReflectedLinearNat k n d i
  let Mj := oddReflectedLinearNat k n d j
  have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
  have hik : i ≤ k := (Finset.mem_Icc.mp hi).2
  have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
  have hjk : j ≤ k := (Finset.mem_Icc.mp hj).2
  have hSpos : 0 < S := by dsimp [S]; omega
  have hMipos : 0 < Mi := by
    dsimp [Mi]
    rw [odd_reflected_linear_eq hk hd hn9 hi]
    omega
  have hMjpos : 0 < Mj := by
    dsimp [Mj]
    rw [odd_reflected_linear_eq hk hd hn9 hj]
    omega
  have hMiLower : 5 * S < 4 * Mi := by
    dsimp [Mi]
    rw [odd_reflected_linear_eq hk hd hn9 hi]
    dsimp [S]
    omega
  have hMjLower : 5 * S < 4 * Mj := by
    dsimp [Mj]
    rw [odd_reflected_linear_eq hk hd hn9 hj]
    dsimp [S]
    omega
  have hMiUpper : Mi < 2 * S := by
    dsimp [Mi]
    rw [odd_reflected_linear_eq hk hd hn9 hi]
    dsimp [S]
    omega
  have hMjUpper : Mj < 2 * S := by
    dsimp [Mj]
    rw [odd_reflected_linear_eq hk hd hn9 hj]
    dsimp [S]
    omega
  have hlowerMul : (5 * S) * (5 * S) < (4 * Mi) * (4 * Mj) :=
    mul_lt_mul hMiLower (le_of_lt hMjLower) (by positivity) (by positivity)
  have hupperMul : Mi * Mj < (2 * S) * (2 * S) :=
    mul_lt_mul hMiUpper (le_of_lt hMjUpper) (by positivity) (by positivity)
  constructor <;> dsimp [S, Mi, Mj] at * <;> nlinarith

private lemma nonzero_sq_mod_three (x : ZMod 3) (hx : x ≠ 0) : x ^ 2 = 1 := by
  decide +revert

private lemma mod_five_square_ratio_not_two_or_three
    (q r : ZMod 5) (hq : q ≠ 0) (hr : r ≠ 0) :
    q ^ 2 ≠ 2 * r ^ 2 ∧ 2 * q ^ 2 ≠ r ^ 2 ∧
      q ^ 2 ≠ 3 * r ^ 2 ∧ 3 * q ^ 2 ≠ r ^ 2 := by
  decide +revert

private lemma seven_close_forces_five_r_lt_two_q
    {k q r i j : ℕ} (hk : 16 ≤ k) (hqk : k < q) (hrk : k < r)
    (hi1 : 1 ≤ i) (hj : j ≤ k)
    (hdiff : q ^ 2 + 3 * j = 7 * r ^ 2 + 3 * i) :
    5 * r < 2 * q := by
  by_contra hnot
  have hratioLow : 2 * q ≤ 5 * r := by omega
  have hsquare : (2 * q) ^ 2 ≤ (5 * r) ^ 2 :=
    Nat.pow_le_pow_left hratioLow 2
  have hsquare' : 4 * q ^ 2 ≤ 25 * r ^ 2 := by
    simpa [mul_pow] using hsquare
  have hrLower : (k + 1) ^ 2 ≤ r ^ 2 :=
    Nat.pow_le_pow_left (by omega : k + 1 ≤ r) 2
  have hkQuad : 4 * (k - 1) < (k + 1) ^ 2 := by
    nlinarith [sq_nonneg (k - 1)]
  have hrBig : 4 * (k - 1) < r ^ 2 := lt_of_lt_of_le hkQuad hrLower
  omega

private lemma seven_close_forces_five_q_lt_two_r
    {k q r i j : ℕ} (hk : 16 ≤ k) (hqk : k < q) (hrk : k < r)
    (hi : i ≤ k) (hj1 : 1 ≤ j)
    (hdiff : r ^ 2 + 3 * i = 7 * q ^ 2 + 3 * j) :
    5 * q < 2 * r := by
  exact seven_close_forces_five_r_lt_two_q
    (k := k) (q := r) (r := q) (i := j) (j := i)
    hk hrk hqk hj1 hi hdiff

private lemma coefficient_one_forces_two_q_lt_five_r
    {k n d q r i : ℕ} (hd : k ≤ d) (hi : i ∈ Finset.Icc 1 k)
    (hcenter : 2 * n + d + k + 1 = q * r)
    (hqEq : q ^ 2 = evenReflectedLinearNat k n d i) :
    2 * q < 5 * r := by
  have hqEq' := hqEq
  rw [even_reflected_linear_eq hi] at hqEq'
  clear hqEq
  have hik := (Finset.mem_Icc.mp hi).2
  have hDle : 2 * i ≤ d + k + 1 := by omega
  have hrel :
      2 * q ^ 2 + 3 * (d + k + 1 - 2 * i) =
        5 * (2 * n + d + k + 1) := by
    omega
  have hgapPos : 0 < d + k + 1 - 2 * i := by
    omega
  have hprod : 2 * q ^ 2 < 5 * (q * r) := by
    rw [← hcenter]
    omega
  have hmul : q * (2 * q) < q * (5 * r) := by
    simpa [pow_two, mul_assoc, mul_comm, mul_left_comm] using hprod
  have hq0 : q ≠ 0 := by
    intro hzero
    subst q
    simp at hcenter
  exact (Nat.mul_lt_mul_left (Nat.pos_of_ne_zero hq0)).mp hmul

private lemma coefficient_one_forces_two_r_lt_five_q
    {k n d q r j : ℕ} (hd : k ≤ d) (hj : j ∈ Finset.Icc 1 k)
    (hcenter : 2 * n + d + k + 1 = q * r)
    (hrEq : r ^ 2 = evenReflectedLinearNat k n d j) :
    2 * r < 5 * q := by
  have hcenter' : 2 * n + d + k + 1 = r * q := by
    simpa [mul_comm] using hcenter
  exact coefficient_one_forces_two_q_lt_five_r
    (k := k) (n := n) (d := d) (q := r) (r := q) (i := j)
    hd hj hcenter' hrEq

/-- Pure arithmetic core for even `k`: two large center factors carrying the
two reflected square lifts are impossible. -/
theorem no_even_two_factor_reflected_square_lifts
    {k n d q r i j : ℕ}
    (hk : 16 ≤ k) (hkeven : Even k) (hd : k ≤ d) (hn9 : 9 * d < n)
    (hqk : k < q) (hrk : k < r)
    (hq3 : ¬ 3 ∣ q) (hr3 : ¬ 3 ∣ r)
    (hi : i ∈ Finset.Icc 1 k) (hj : j ∈ Finset.Icc 1 k)
    (hcenter : 2 * n + d + k + 1 = q * r)
    (hqLift : q ^ 2 ∣ evenReflectedLinearNat k n d i)
    (hrLift : r ^ 2 ∣ evenReflectedLinearNat k n d j) : False := by
  obtain ⟨u, hu⟩ := hqLift
  obtain ⟨v, hv⟩ := hrLift
  have hbounds := even_reflected_product_bounds hk hd hn9 hi hj
  have hSpos : 0 < 2 * n + d + k + 1 := by omega
  have hupos : 0 < u := by
    by_contra h
    have : u = 0 := by omega
    rw [this, mul_zero] at hu
    have hLiPos : 0 < evenReflectedLinearNat k n d i := by
      unfold evenReflectedLinearNat
      omega
    omega
  have hvpos : 0 < v := by
    by_contra h
    have : v = 0 := by omega
    rw [this, mul_zero] at hv
    have hLjPos : 0 < evenReflectedLinearNat k n d j := by
      unfold evenReflectedLinearNat
      omega
    omega
  have hprodEq :
      evenReflectedLinearNat k n d i * evenReflectedLinearNat k n d j =
        (2 * n + d + k + 1) ^ 2 * (u * v) := by
    rw [hu, hv, hcenter]
    ring
  have huvLower : 5 < u * v := by
    rw [hprodEq] at hbounds
    nlinarith [sq_pos_of_pos hSpos]
  have huvUpper : u * v < 8 := by
    rw [hprodEq] at hbounds
    nlinarith [sq_pos_of_pos hSpos]
  have huvCases : u * v = 6 ∨ u * v = 7 := by omega
  rcases huvCases with huv6 | huv7
  · have hmod : ((q : ZMod 3) ^ 2) * (u : ZMod 3) =
        ((r : ZMod 3) ^ 2) * (v : ZMod 3) := by
      have hLi : evenReflectedLinearNat k n d i = q ^ 2 * u := hu
      have hLj : evenReflectedLinearNat k n d j = r ^ 2 * v := hv
      have hlinMod : evenReflectedLinearNat k n d i ≡
          evenReflectedLinearNat k n d j [MOD 3] := by
        rw [even_reflected_linear_eq hi, even_reflected_linear_eq hj]
        let T := 5 * n + d + k + 1
        have hi0 : T + 3 * i ≡ T [MOD 3] := by
          simpa [T, add_comm] using
            (Nat.ModEq.modulus_mul_add (m := 3) (a := i) (b := T))
        have hj0 : T + 3 * j ≡ T [MOD 3] := by
          simpa [T, add_comm] using
            (Nat.ModEq.modulus_mul_add (m := 3) (a := j) (b := T))
        exact hi0.trans hj0.symm
      have hprodMod : q ^ 2 * u ≡ r ^ 2 * v [MOD 3] := by
        rw [← hLi, ← hLj]
        exact hlinMod
      have hz := (ZMod.natCast_eq_natCast_iff
        (q ^ 2 * u) (r ^ 2 * v) 3).mpr hprodMod
      simpa [Nat.cast_mul, Nat.cast_pow] using hz
    have hq0 : (q : ZMod 3) ≠ 0 := by
      intro hzero
      exact hq3 ((ZMod.natCast_eq_zero_iff q 3).mp hzero)
    have hr0 : (r : ZMod 3) ≠ 0 := by
      intro hzero
      exact hr3 ((ZMod.natCast_eq_zero_iff r 3).mp hzero)
    rw [nonzero_sq_mod_three _ hq0, nonzero_sq_mod_three _ hr0] at hmod
    have hpairs :
        (u = 1 ∧ v = 6) ∨ (u = 2 ∧ v = 3) ∨
          (u = 3 ∧ v = 2) ∨ (u = 6 ∧ v = 1) := by
      have huLe : u ≤ 6 := by nlinarith
      interval_cases u <;> omega
    rcases hpairs with h | h | h | h
    · rcases h with ⟨rfl, rfl⟩
      exact (by decide : (1 : ZMod 3) ≠ 6) (by simpa using hmod)
    · rcases h with ⟨rfl, rfl⟩
      exact (by decide : (2 : ZMod 3) ≠ 3) (by simpa using hmod)
    · rcases h with ⟨rfl, rfl⟩
      exact (by decide : (3 : ZMod 3) ≠ 2) (by simpa using hmod)
    · rcases h with ⟨rfl, rfl⟩
      exact (by decide : (6 : ZMod 3) ≠ 1) (by simpa using hmod)
  · have hpairs : (u = 1 ∧ v = 7) ∨ (u = 7 ∧ v = 1) := by
      have huLe : u ≤ 7 := by nlinarith
      interval_cases u <;> omega
    rcases hpairs with h | h
    · rcases h with ⟨rfl, rfl⟩
      have hqEq : q ^ 2 = evenReflectedLinearNat k n d i := by
        simpa using hu.symm
      have hrEq : 7 * r ^ 2 = evenReflectedLinearNat k n d j := by
        simpa [mul_comm] using hv.symm
      have hratioHigh : 5 * r < 2 * q := by
        have hqEq' := hqEq
        have hrEq' := hrEq
        rw [even_reflected_linear_eq hi] at hqEq'
        rw [even_reflected_linear_eq hj] at hrEq'
        have hdiff : q ^ 2 + 3 * j = 7 * r ^ 2 + 3 * i := by omega
        exact seven_close_forces_five_r_lt_two_q hk hqk hrk
          (Finset.mem_Icc.mp hi).1 (Finset.mem_Icc.mp hj).2 hdiff
      have hratioLow : 2 * q < 5 * r :=
        coefficient_one_forces_two_q_lt_five_r hd
          hi hcenter hqEq
      omega
    · rcases h with ⟨rfl, rfl⟩
      have hqEq : 7 * q ^ 2 = evenReflectedLinearNat k n d i := by
        simpa [mul_comm] using hu.symm
      have hrEq : r ^ 2 = evenReflectedLinearNat k n d j := by
        simpa using hv.symm
      have hratioHigh : 5 * q < 2 * r := by
        have hqEq' := hqEq
        have hrEq' := hrEq
        rw [even_reflected_linear_eq hi] at hqEq'
        rw [even_reflected_linear_eq hj] at hrEq'
        have hdiff : r ^ 2 + 3 * i = 7 * q ^ 2 + 3 * j := by omega
        exact seven_close_forces_five_q_lt_two_r hk hqk hrk
          (Finset.mem_Icc.mp hi).2 (Finset.mem_Icc.mp hj).1 hdiff
      have hratioLow : 2 * r < 5 * q :=
        coefficient_one_forces_two_r_lt_five_q hd
          hj hcenter hrEq
      omega

/-- Pure arithmetic core for odd `k`. -/
theorem no_odd_two_factor_reflected_square_lifts
    {k n d q r i j : ℕ}
    (hk : 16 ≤ k) (hkodd : Odd k) (hd : k ≤ d) (hn9 : 9 * d < n)
    (hqk : k < q) (hrk : k < r)
    (hq5 : ¬ 5 ∣ q) (hr5 : ¬ 5 ∣ r)
    (hi : i ∈ Finset.Icc 1 k) (hj : j ∈ Finset.Icc 1 k)
    (hcenter : 2 * n + d + k + 1 = q * r)
    (hqLift : q ^ 2 ∣ oddReflectedLinearNat k n d i)
    (hrLift : r ^ 2 ∣ oddReflectedLinearNat k n d j) : False := by
  obtain ⟨u, hu⟩ := hqLift
  obtain ⟨v, hv⟩ := hrLift
  have hbounds := odd_reflected_product_bounds hk hd hn9 hi hj
  have hSpos : 0 < 2 * n + d + k + 1 := by omega
  have hupos : 0 < u := by
    have hMiPos : 0 < oddReflectedLinearNat k n d i := by
      rw [odd_reflected_linear_eq hk hd hn9 hi]
      omega
    nlinarith
  have hvpos : 0 < v := by
    have hMjPos : 0 < oddReflectedLinearNat k n d j := by
      rw [odd_reflected_linear_eq hk hd hn9 hj]
      omega
    nlinarith
  have hprodEq :
      oddReflectedLinearNat k n d i * oddReflectedLinearNat k n d j =
        (2 * n + d + k + 1) ^ 2 * (u * v) := by
    rw [hu, hv, hcenter]
    ring
  have huvLower : 1 < u * v := by
    rw [hprodEq] at hbounds
    nlinarith [sq_pos_of_pos hSpos]
  have huvUpper : u * v < 4 := by
    rw [hprodEq] at hbounds
    nlinarith [sq_pos_of_pos hSpos]
  have huvCases : u * v = 2 ∨ u * v = 3 := by omega
  have hmod : ((q : ZMod 5) ^ 2) * (u : ZMod 5) =
      ((r : ZMod 5) ^ 2) * (v : ZMod 5) := by
    have hMi : oddReflectedLinearNat k n d i = q ^ 2 * u := hu
    have hMj : oddReflectedLinearNat k n d j = r ^ 2 * v := hv
    have hlinMod : oddReflectedLinearNat k n d i ≡
        oddReflectedLinearNat k n d j [MOD 5] := by
      rw [odd_reflected_linear_eq hk hd hn9 hi,
        odd_reflected_linear_eq hk hd hn9 hj]
      let T := 3 * n - d - k - 1
      have hi0 : T + 5 * i ≡ T [MOD 5] := by
        simpa [T, add_comm] using
          (Nat.ModEq.modulus_mul_add (m := 5) (a := i) (b := T))
      have hj0 : T + 5 * j ≡ T [MOD 5] := by
        simpa [T, add_comm] using
          (Nat.ModEq.modulus_mul_add (m := 5) (a := j) (b := T))
      exact hi0.trans hj0.symm
    have hprodMod : q ^ 2 * u ≡ r ^ 2 * v [MOD 5] := by
      rw [← hMi, ← hMj]
      exact hlinMod
    have hz := (ZMod.natCast_eq_natCast_iff
      (q ^ 2 * u) (r ^ 2 * v) 5).mpr hprodMod
    simpa [Nat.cast_mul, Nat.cast_pow] using hz
  have hq0 : (q : ZMod 5) ≠ 0 := by
    intro hzero
    exact hq5 ((ZMod.natCast_eq_zero_iff q 5).mp hzero)
  have hr0 : (r : ZMod 5) ≠ 0 := by
    intro hzero
    exact hr5 ((ZMod.natCast_eq_zero_iff r 5).mp hzero)
  have hfinite := mod_five_square_ratio_not_two_or_three
    (q : ZMod 5) (r : ZMod 5) hq0 hr0
  rcases huvCases with huv2 | huv3
  · have hpairs : (u = 1 ∧ v = 2) ∨ (u = 2 ∧ v = 1) := by
      have huLe : u ≤ 2 := by nlinarith
      interval_cases u <;> omega
    rcases hpairs with h | h
    · rcases h with ⟨rfl, rfl⟩
      exact hfinite.1 (by simpa [mul_comm] using hmod)
    · rcases h with ⟨rfl, rfl⟩
      exact hfinite.2.1 (by simpa [mul_comm] using hmod)
  · have hpairs : (u = 1 ∧ v = 3) ∨ (u = 3 ∧ v = 1) := by
      have huLe : u ≤ 3 := by nlinarith
      interval_cases u <;> omega
    rcases hpairs with h | h
    · rcases h with ⟨rfl, rfl⟩
      exact hfinite.2.2.1 (by simpa [mul_comm] using hmod)
    · rcases h with ⟨rfl, rfl⟩
      exact hfinite.2.2.2 (by simpa [mul_comm] using hmod)

private theorem reflected_owner_even_weighted_nat_square_lift
    {q k n d i : ℕ} (hkeven : Even k)
    (hi : i ∈ Finset.Icc 1 k)
    (hlower : q ∣ n + i)
    (hupper : q ∣ n + d + (k + 1 - i))
    (heq : blockProduct k (n + d) = 4 * blockProduct k n) :
    q ^ 2 ∣ localBlockCoefficientNat k i *
      evenReflectedLinearNat k n d i := by
  have hkoddPred : Odd (k - 1) :=
    Nat.Even.sub_odd (by
      have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
      have hik : i ≤ k := (Finset.mem_Icc.mp hi).2
      omega) hkeven (by norm_num)
  have hsign : (-1 : ℤ) ^ (k - 1) = -1 :=
    Odd.neg_one_pow hkoddPred
  have hraw := reflected_owner_local_coefficientNat_dvd_sq
    hi hlower hupper heq
  have hpositive : (((q ^ 2 : ℕ) : ℤ)) ∣
      (((localBlockCoefficientNat k i *
        evenReflectedLinearNat k n d i : ℕ) : ℤ)) := by
    have hneg := dvd_neg.mpr hraw
    convert hneg using 1
    simp only [hsign, evenReflectedLinearNat, Nat.cast_add,
      Nat.cast_mul, Nat.cast_ofNat]
    ring
  have hnat : q ^ 2 ∣
      localBlockCoefficientNat k i * evenReflectedLinearNat k n d i :=
    Int.natCast_dvd_natCast.mp hpositive
  exact hnat

private theorem large_supported_center_even_nat_square_lift
    {q k n d i : ℕ}
    (hkeven : Even k) (hi : i ∈ Finset.Icc 1 k)
    (hsupport : ∀ p, p.Prime → p ∣ q → k < p)
    (hlower : q ∣ n + i)
    (hupper : q ∣ n + d + (k + 1 - i))
    (heq : blockProduct k (n + d) = 4 * blockProduct k n) :
    q ^ 2 ∣ evenReflectedLinearNat k n d i := by
  have hnat := reflected_owner_even_weighted_nat_square_lift
    hkeven hi hlower hupper heq
  have hcop := coprime_localBlockCoefficientNat_of_large_support hi hsupport
  have hcopSq : (q ^ 2).Coprime (localBlockCoefficientNat k i) := by
    simpa using Nat.Coprime.pow 2 1 hcop
  exact hcopSq.dvd_of_dvd_mul_left hnat

private theorem reflected_owner_odd_weighted_nat_square_lift
    {q k n d i : ℕ}
    (hk : 16 ≤ k) (hkodd : Odd k) (hd : k ≤ d)
    (hi : i ∈ Finset.Icc 1 k)
    (hlower : q ∣ n + i)
    (hupper : q ∣ n + d + (k + 1 - i))
    (heq : blockProduct k (n + d) = 4 * blockProduct k n) :
    q ^ 2 ∣ localBlockCoefficientNat k i *
      oddReflectedLinearNat k n d i := by
  have hkevenPred : Even (k - 1) :=
    Nat.Odd.sub_odd hkodd (by norm_num)
  have hsign : (-1 : ℤ) ^ (k - 1) = 1 :=
    Even.neg_one_pow hkevenPred
  have hn9 := nine_mul_gap_lt_n_of_four_solution hk hd heq
  have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
  have hik : i ≤ k := (Finset.mem_Icc.mp hi).2
  have hBA : n + d + (k + 1 - i) ≤ 4 * (n + i) := by omega
  have hraw := reflected_owner_local_coefficientNat_dvd_sq
    hi hlower hupper heq
  have hpositive : (((q ^ 2 : ℕ) : ℤ)) ∣
      (((localBlockCoefficientNat k i *
        oddReflectedLinearNat k n d i : ℕ) : ℤ)) := by
    have hneg := dvd_neg.mpr hraw
    convert hneg using 1
    simp [hsign, oddReflectedLinearNat, Nat.cast_sub hBA,
      Nat.cast_add, Nat.cast_mul]
    ring
  have hnat : q ^ 2 ∣
      localBlockCoefficientNat k i * oddReflectedLinearNat k n d i :=
    Int.natCast_dvd_natCast.mp hpositive
  exact hnat

private theorem large_supported_center_odd_nat_square_lift
    {q k n d i : ℕ}
    (hk : 16 ≤ k) (hkodd : Odd k) (hd : k ≤ d)
    (hi : i ∈ Finset.Icc 1 k)
    (hsupport : ∀ p, p.Prime → p ∣ q → k < p)
    (hlower : q ∣ n + i)
    (hupper : q ∣ n + d + (k + 1 - i))
    (heq : blockProduct k (n + d) = 4 * blockProduct k n) :
    q ^ 2 ∣ oddReflectedLinearNat k n d i := by
  have hnat := reflected_owner_odd_weighted_nat_square_lift
    hk hkodd hd hi hlower hupper heq
  have hcop := coprime_localBlockCoefficientNat_of_large_support hi hsupport
  have hcopSq : (q ^ 2).Coprime (localBlockCoefficientNat k i) := by
    simpa using Nat.Coprime.pow 2 1 hcop
  exact hcopSq.dvd_of_dvd_mul_left hnat

/-- Owner-count strengthening of the two-factor core.  The factors `q` and
`r` may each aggregate arbitrarily many complete center prime powers.  It is
enough that every prime in either aggregate is above `k`, the two aggregates
occupy two reflected owners, and together they are the whole center. -/
theorem no_four_solution_of_two_large_supported_reflected_owner_factors
    {k n d q r i j : ℕ}
    (hk : 16 ≤ k) (hd : k ≤ d)
    (hqk : k < q) (hrk : k < r)
    (hqSupport : ∀ p, p.Prime → p ∣ q → k < p)
    (hrSupport : ∀ p, p.Prime → p ∣ r → k < p)
    (hi : i ∈ Finset.Icc 1 k) (hj : j ∈ Finset.Icc 1 k)
    (hcenter : 2 * n + d + k + 1 = q * r)
    (hqLower : q ∣ n + i)
    (hqUpper : q ∣ n + d + (k + 1 - i))
    (hrLower : r ∣ n + j)
    (hrUpper : r ∣ n + d + (k + 1 - j)) :
    blockProduct k (n + d) ≠ 4 * blockProduct k n := by
  intro heq
  have hn9 := nine_mul_gap_lt_n_of_four_solution hk hd heq
  by_cases hkeven : Even k
  · have hqLift := large_supported_center_even_nat_square_lift
      hkeven hi hqSupport hqLower hqUpper heq
    have hrLift := large_supported_center_even_nat_square_lift
      hkeven hj hrSupport hrLower hrUpper heq
    have hq3 : ¬ 3 ∣ q := by
      intro h3
      have := hqSupport 3 (by norm_num) h3
      omega
    have hr3 : ¬ 3 ∣ r := by
      intro h3
      have := hrSupport 3 (by norm_num) h3
      omega
    exact no_even_two_factor_reflected_square_lifts
      hk hkeven hd hn9 hqk hrk hq3 hr3 hi hj hcenter hqLift hrLift
  · have hkodd : Odd k := Nat.not_even_iff_odd.mp hkeven
    have hqLift := large_supported_center_odd_nat_square_lift
      hk hkodd hd hi hqSupport hqLower hqUpper heq
    have hrLift := large_supported_center_odd_nat_square_lift
      hk hkodd hd hj hrSupport hrLower hrUpper heq
    have hq5 : ¬ 5 ∣ q := by
      intro h5
      have := hqSupport 5 (by norm_num) h5
      omega
    have hr5 : ¬ 5 ∣ r := by
      intro h5
      have := hrSupport 5 (by norm_num) h5
      omega
    exact no_odd_two_factor_reflected_square_lifts
      hk hkodd hd hn9 hqk hrk hq5 hr5 hi hj hcenter hqLift hrLift

/-- One-owner companion to the aggregate theorem.  If the whole center has
large prime support and all of it lands on one reflected owner, its aggregate
square already exceeds the corresponding linear form. -/
theorem no_four_solution_of_one_large_supported_reflected_owner_factor
    {k n d q i : ℕ}
    (hk : 16 ≤ k) (hd : k ≤ d)
    (hqSupport : ∀ p, p.Prime → p ∣ q → k < p)
    (hi : i ∈ Finset.Icc 1 k)
    (hcenter : 2 * n + d + k + 1 = q)
    (hqLower : q ∣ n + i)
    (hqUpper : q ∣ n + d + (k + 1 - i)) :
    blockProduct k (n + d) ≠ 4 * blockProduct k n := by
  intro heq
  have hn9 := nine_mul_gap_lt_n_of_four_solution hk hd heq
  have hqSquareLe : q ^ 2 ≤ 7 * n := by
    by_cases hkeven : Even k
    · have hlift := large_supported_center_even_nat_square_lift
        hkeven hi hqSupport hqLower hqUpper heq
      have hline := even_reflected_linear_pos_le hk hd hn9 hi
      exact le_trans (Nat.le_of_dvd hline.1 hlift) hline.2
    · have hkodd : Odd k := Nat.not_even_iff_odd.mp hkeven
      have hlift := large_supported_center_odd_nat_square_lift
        hk hkodd hd hi hqSupport hqLower hqUpper heq
      have hline := odd_reflected_linear_pos_le hk hd hn9 hi
      exact le_trans (Nat.le_of_dvd hline.1 hlift) hline.2
  have hn2 : 2 ≤ n := by omega
  have hcenterGt : 2 * n < 2 * n + d + k + 1 := by omega
  have hsevenLt : 7 * n < (2 * n) ^ 2 := by nlinarith
  have hsquareLt : (2 * n) ^ 2 < (2 * n + d + k + 1) ^ 2 :=
    Nat.pow_lt_pow_left hcenterGt (by norm_num)
  have hcenterSquareLt : 7 * n < (2 * n + d + k + 1) ^ 2 :=
    lt_trans hsevenLt hsquareLt
  have hcenterSquareLe : (2 * n + d + k + 1) ^ 2 ≤ 7 * n := by
    rw [hcenter]
    exact hqSquareLe
  omega

/-- Every prime, including bases at most `k`, has a quantitatively controlled
residual center power after the exact reflection-coefficient and factorial
loss.  A non-reflected residual is at most `k-1`; a reflected residual has
its square bounded by one local factorial weight times `7n`. -/
theorem center_residual_power_small_or_weighted_square_bound
    {p k n d : ℕ} (hp : p.Prime) (hk : 16 ≤ k) (hd : k ≤ d)
    (heq : blockProduct k (n + d) = 4 * blockProduct k n) :
    p ^ reflectionResidualExponent p k n d ≤ k - 1 ∨
      (p ^ reflectionResidualExponent p k n d) ^ 2 ≤
        (k - 1).factorial * (7 * n) := by
  let h := p ^ reflectionResidualExponent p k n d
  obtain ⟨i, hi, j, hj, hlower, hupper, hreflection, hcentered⟩ :=
    exists_reflection_owner_correlation_four hp (by omega) hd heq
  have hcorr := reflection_owner_correlation_offset_and_lcm
    (p := p) (n := n) (d := d) (by omega : 1 ≤ k) hd hi hj
      hreflection hcentered
  by_cases hsum : i + j = k + 1
  · right
    have hjEq : j = k + 1 - i := by
      have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
      have hik : i ≤ k := (Finset.mem_Icc.mp hi).2
      omega
    have hupperReflected : h ∣ n + d + (k + 1 - i) := by
      simpa [h, hjEq] using hupper
    have hlower' : h ∣ n + i := by simpa [h] using hlower
    have hn9 := nine_mul_gap_lt_n_of_four_solution hk hd heq
    have hcoeffPos : 0 < localBlockCoefficientNat k i := by
      unfold localBlockCoefficientNat
      exact Nat.mul_pos (Nat.factorial_pos _) (Nat.factorial_pos _)
    have hcoeffDvd : localBlockCoefficientNat k i ∣ (k - 1).factorial :=
      localBlockCoefficientNat_dvd_factorial_pred hi
    have hcoeffLe : localBlockCoefficientNat k i ≤ (k - 1).factorial :=
      Nat.le_of_dvd (Nat.factorial_pos _) hcoeffDvd
    by_cases hkeven : Even k
    · have hlift := reflected_owner_even_weighted_nat_square_lift
        hkeven hi hlower' hupperReflected heq
      have hline := even_reflected_linear_pos_le hk hd hn9 hi
      have hsqLe : h ^ 2 ≤ localBlockCoefficientNat k i *
          evenReflectedLinearNat k n d i :=
        Nat.le_of_dvd (Nat.mul_pos hcoeffPos hline.1) hlift
      exact le_trans hsqLe (Nat.mul_le_mul hcoeffLe hline.2)
    · have hkodd : Odd k := Nat.not_even_iff_odd.mp hkeven
      have hlift := reflected_owner_odd_weighted_nat_square_lift
        hk hkodd hd hi hlower' hupperReflected heq
      have hline := odd_reflected_linear_pos_le hk hd hn9 hi
      have hsqLe : h ^ 2 ≤ localBlockCoefficientNat k i *
          oddReflectedLinearNat k n d i :=
        Nat.le_of_dvd (Nat.mul_pos hcoeffPos hline.1) hlift
      exact le_trans hsqLe (Nat.mul_le_mul hcoeffLe hline.2)
  · left
    have hdistPos : 0 < Nat.dist (i + j) (k + 1) :=
      Nat.dist_pos_of_ne hsum
    have hhLe : h ≤ Nat.dist (i + j) (k + 1) :=
      Nat.le_of_dvd hdistPos (by simpa [h] using hcorr.1)
    have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
    have hik : i ≤ k := (Finset.mem_Icc.mp hi).2
    have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
    have hjk : j ≤ k := (Finset.mem_Icc.mp hj).2
    have hdistLe : Nat.dist (i + j) (k + 1) ≤ k - 1 := by
      by_cases hle : i + j ≤ k + 1
      · rw [Nat.dist_eq_sub_of_le hle]
        omega
      · have hge : k + 1 ≤ i + j := by omega
        rw [Nat.dist_eq_sub_of_le_right hge]
        omega
    exact le_trans hhLe hdistLe

/-- Full center prime-power bound with every small-base valuation loss made
explicit.  This is unconditional in the prime base. -/
theorem center_prime_power_sq_le_with_explicit_reflection_loss
    {p k n d : ℕ} (hp : p.Prime) (hk : 16 ≤ k) (hd : k ≤ d)
    (heq : blockProduct k (n + d) = 4 * blockProduct k n) :
    (p ^ (2 * n + d + k + 1).factorization p) ^ 2 ≤
      p ^ (2 * ((reflectionCoeff k).factorization p +
        (k - 1).factorial.factorization p)) *
      ((k - 1) ^ 2 + (k - 1).factorial * (7 * n)) := by
  let E := (2 * n + d + k + 1).factorization p
  let L := (reflectionCoeff k).factorization p +
    (k - 1).factorial.factorization p
  let e := reflectionResidualExponent p k n d
  let h := p ^ e
  let q := p ^ E
  have heEq : e = E - L := by
    dsimp [e, E, L, reflectionResidualExponent]
    omega
  have hexp : E ≤ L + e := by rw [heEq]; omega
  have hqLe : q ≤ p ^ L * h := by
    calc
      q = p ^ E := rfl
      _ ≤ p ^ (L + e) := Nat.pow_le_pow_right hp.pos hexp
      _ = p ^ L * h := by simp [h, pow_add]
  have hresidual := center_residual_power_small_or_weighted_square_bound
    hp hk hd heq
  have hhBound : h ^ 2 ≤
      (k - 1) ^ 2 + (k - 1).factorial * (7 * n) := by
    rcases hresidual with hsmall | hweighted
    · have hsquare := Nat.pow_le_pow_left (by simpa [h, e] using hsmall) 2
      exact le_trans hsquare (Nat.le_add_right _ _)
    · exact le_trans (by simpa [h, e] using hweighted)
        (Nat.le_add_left _ _)
  have hqSquare := Nat.pow_le_pow_left hqLe 2
  calc
    q ^ 2 ≤ (p ^ L * h) ^ 2 := hqSquare
    _ = p ^ (2 * L) * h ^ 2 := by
      simp only [mul_pow, ← pow_mul]
      congr 2 <;> omega
    _ ≤ p ^ (2 * L) *
        ((k - 1) ^ 2 + (k - 1).factorial * (7 * n)) :=
      Nat.mul_le_mul_left _ hhBound
    _ = p ^ (2 * ((reflectionCoeff k).factorization p +
          (k - 1).factorial.factorization p)) *
        ((k - 1) ^ 2 + (k - 1).factorial * (7 * n)) := by
      rfl

private theorem exists_large_prime_center_even_nat_square_lift
    {p k n d : ℕ}
    (hp : p.Prime) (hk : 16 ≤ k) (hkeven : Even k) (hd : k ≤ d)
    (hkp : k < p) (hpS : p ∣ 2 * n + d + k + 1)
    (heq : blockProduct k (n + d) = 4 * blockProduct k n) :
    ∃ i, i ∈ Finset.Icc 1 k ∧
      (p ^ (2 * n + d + k + 1).factorization p) ^ 2 ∣
        evenReflectedLinearNat k n d i := by
  obtain ⟨i, hi, hlift⟩ :=
    exists_large_prime_reflection_center_square_lift_four
      hp hk hd hkp hpS heq
  let q := p ^ (2 * n + d + k + 1).factorization p
  have hkoddPred : Odd (k - 1) :=
    Nat.Even.sub_odd (by omega : 1 ≤ k) hkeven (by norm_num)
  have hsign : (-1 : ℤ) ^ (k - 1) = -1 :=
    Odd.neg_one_pow hkoddPred
  have hneg := dvd_neg.mpr hlift
  have hcast : ((q ^ 2 : ℕ) : ℤ) ∣
      (evenReflectedLinearNat k n d i : ℤ) := by
    convert hneg using 1
    simp only [hsign, evenReflectedLinearNat, Nat.cast_add, Nat.cast_mul,
      Nat.cast_ofNat, one_mul]
    ring
  exact ⟨i, hi, Int.natCast_dvd_natCast.mp hcast⟩

private theorem exists_large_prime_center_odd_nat_square_lift
    {p k n d : ℕ}
    (hp : p.Prime) (hk : 16 ≤ k) (hkodd : Odd k) (hd : k ≤ d)
    (hkp : k < p) (hpS : p ∣ 2 * n + d + k + 1)
    (heq : blockProduct k (n + d) = 4 * blockProduct k n) :
    ∃ i, i ∈ Finset.Icc 1 k ∧
      (p ^ (2 * n + d + k + 1).factorization p) ^ 2 ∣
        oddReflectedLinearNat k n d i := by
  obtain ⟨i, hi, hlift⟩ :=
    exists_large_prime_reflection_center_square_lift_four
      hp hk hd hkp hpS heq
  let q := p ^ (2 * n + d + k + 1).factorization p
  have hkevenPred : Even (k - 1) :=
    Nat.Odd.sub_odd hkodd (by norm_num)
  have hsign : (-1 : ℤ) ^ (k - 1) = 1 :=
    Even.neg_one_pow hkevenPred
  have hn9 := nine_mul_gap_lt_n_of_four_solution hk hd heq
  have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
  have hik : i ≤ k := (Finset.mem_Icc.mp hi).2
  have hBA : n + d + (k + 1 - i) ≤ 4 * (n + i) := by omega
  have hneg := dvd_neg.mpr hlift
  have hcast : ((q ^ 2 : ℕ) : ℤ) ∣
      (oddReflectedLinearNat k n d i : ℤ) := by
    simpa [q, hsign, oddReflectedLinearNat, Nat.cast_pow,
      Nat.cast_sub hBA, Nat.cast_add, Nat.cast_mul] using hneg
  exact ⟨i, hi, Int.natCast_dvd_natCast.mp hcast⟩

private lemma prime_power_not_dvd_three_of_large
    {p e k : ℕ} (hp : p.Prime) (hk : 16 ≤ k) (hkp : k < p) :
    ¬ 3 ∣ p ^ e := by
  intro hdiv
  have hp3 : 3 ∣ p := (by norm_num : Nat.Prime 3).dvd_of_dvd_pow hdiv
  rcases (Nat.dvd_prime hp).mp hp3 with h | h
  · omega
  · omega

private lemma prime_power_not_dvd_five_of_large
    {p e k : ℕ} (hp : p.Prime) (hk : 16 ≤ k) (hkp : k < p) :
    ¬ 5 ∣ p ^ e := by
  intro hdiv
  have hp5 : 5 ∣ p := (by norm_num : Nat.Prime 5).dvd_of_dvd_pow hdiv
  rcases (Nat.dvd_prime hp).mp hp5 with h | h
  · omega
  · omega

/-- Explicit one-component boundary.  A target-range reflection center cannot
itself be one complete prime-power component with base above `k`: the square
lift gives `S^2 ≤ 7n`, whereas `S>2n` and `n>9d` give `S^2>7n`. -/
theorem no_four_solution_of_reflection_center_one_large_prime_power
    {p k n d : ℕ}
    (hp : p.Prime) (hk : 16 ≤ k) (hd : k ≤ d) (hkp : k < p)
    (hpS : p ∣ 2 * n + d + k + 1)
    (hone : 2 * n + d + k + 1 =
      p ^ (2 * n + d + k + 1).factorization p) :
    blockProduct k (n + d) ≠ 4 * blockProduct k n := by
  intro heq
  obtain ⟨_i, _hi, hpower⟩ :=
    exists_large_prime_reflection_center_power_sq_le
      hp hk hd hkp hpS heq
  have hn9 := nine_mul_gap_lt_n_of_four_solution hk hd heq
  have hn2 : 2 ≤ n := by omega
  have hcenterGt : 2 * n < 2 * n + d + k + 1 := by omega
  have hsevenLt : 7 * n < (2 * n) ^ 2 := by nlinarith
  have hsquareLt : (2 * n) ^ 2 < (2 * n + d + k + 1) ^ 2 :=
    Nat.pow_lt_pow_left hcenterGt (by norm_num)
  have hcenterSquareLt : 7 * n < (2 * n + d + k + 1) ^ 2 :=
    lt_trans hsevenLt hsquareLt
  have hcenterSquareLe : (2 * n + d + k + 1) ^ 2 ≤ 7 * n := by
    rw [hone]
    exact hpower
  omega

/-- Equation-level two-factor exclusion.  A target-range reflection center
cannot consist of exactly two complete prime-power components whose prime
bases both exceed the block length. -/
theorem no_four_solution_of_reflection_center_two_large_prime_powers
    {p r k n d : ℕ}
    (hp : p.Prime) (hr : r.Prime) (hk : 16 ≤ k) (hd : k ≤ d)
    (hkp : k < p) (hkr : k < r)
    (hpS : p ∣ 2 * n + d + k + 1)
    (hrS : r ∣ 2 * n + d + k + 1)
    (htwo : 2 * n + d + k + 1 =
      p ^ (2 * n + d + k + 1).factorization p *
        r ^ (2 * n + d + k + 1).factorization r) :
    blockProduct k (n + d) ≠ 4 * blockProduct k n := by
  intro heq
  let q := p ^ (2 * n + d + k + 1).factorization p
  let s := r ^ (2 * n + d + k + 1).factorization r
  have hS0 : 2 * n + d + k + 1 ≠ 0 := by omega
  have hEp : 0 < (2 * n + d + k + 1).factorization p :=
    hp.factorization_pos_of_dvd hS0 hpS
  have hEr : 0 < (2 * n + d + k + 1).factorization r :=
    hr.factorization_pos_of_dvd hS0 hrS
  have hpq : p ∣ q := by
    dsimp [q]
    simpa using (pow_dvd_pow p (by omega : 1 ≤
      (2 * n + d + k + 1).factorization p))
  have hrs : r ∣ s := by
    dsimp [s]
    simpa using (pow_dvd_pow r (by omega : 1 ≤
      (2 * n + d + k + 1).factorization r))
  have hqk : k < q := lt_of_lt_of_le hkp
    (Nat.le_of_dvd (by dsimp [q]; exact pow_pos hp.pos _) hpq)
  have hsk : k < s := lt_of_lt_of_le hkr
    (Nat.le_of_dvd (by dsimp [s]; exact pow_pos hr.pos _) hrs)
  have hn9 := nine_mul_gap_lt_n_of_four_solution hk hd heq
  by_cases hkeven : Even k
  · obtain ⟨i, hi, hqLift⟩ :=
      exists_large_prime_center_even_nat_square_lift
        hp hk hkeven hd hkp hpS heq
    obtain ⟨j, hj, hsLift⟩ :=
      exists_large_prime_center_even_nat_square_lift
        hr hk hkeven hd hkr hrS heq
    exact no_even_two_factor_reflected_square_lifts
      hk hkeven hd hn9 hqk hsk
      (prime_power_not_dvd_three_of_large hp hk hkp)
      (prime_power_not_dvd_three_of_large hr hk hkr)
      hi hj (by simpa [q, s] using htwo) hqLift hsLift
  · have hkodd : Odd k := Nat.not_even_iff_odd.mp hkeven
    obtain ⟨i, hi, hqLift⟩ :=
      exists_large_prime_center_odd_nat_square_lift
        hp hk hkodd hd hkp hpS heq
    obtain ⟨j, hj, hsLift⟩ :=
      exists_large_prime_center_odd_nat_square_lift
        hr hk hkodd hd hkr hrS heq
    exact no_odd_two_factor_reflected_square_lifts
      hk hkodd hd hn9 hqk hsk
      (prime_power_not_dvd_five_of_large hp hk hkp)
      (prime_power_not_dvd_five_of_large hr hk hkr)
      hi hj (by simpa [q, s] using htwo) hqLift hsLift

#print axioms no_even_two_factor_reflected_square_lifts
#print axioms no_odd_two_factor_reflected_square_lifts
#print axioms no_four_solution_of_two_large_supported_reflected_owner_factors
#print axioms no_four_solution_of_one_large_supported_reflected_owner_factor
#print axioms center_residual_power_small_or_weighted_square_bound
#print axioms center_prime_power_sq_le_with_explicit_reflection_loss
#print axioms no_four_solution_of_reflection_center_one_large_prime_power
#print axioms no_four_solution_of_reflection_center_two_large_prime_powers

end Erdos686Variant
end Erdos686
