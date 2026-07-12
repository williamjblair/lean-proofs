/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import ErdosProblems.Erdos686ReflectedAlignmentSquareLift
import ErdosProblems.Erdos686TwoPrimeSecondLift
import ErdosProblems.Erdos686GlobalResidualTwoPrime

/-!
# Erdős 686: the next reflected-owner lift

The reflected square lift fixes the first residual digit.  Retaining the
linear coefficient of both reflected local cofactors fixes the next digit.
This file keeps the small-prime loss modulus explicit: no primality,
coprimality, or `h = 1` assumption occurs in the algebraic core.
-/

namespace Erdos686
namespace Erdos686Variant

open scoped BigOperators

/-- Exact reflection of the full local cofactor, not merely of its constant
term.  This identity is what fixes the sign of the linear coefficient in the
next lift. -/
lemma localOffsetCofactor_reflected_agent
    {k i : ℕ} (hi : i ∈ Finset.Icc 1 k) (z : ℤ) :
    localOffsetCofactor k (k + 1 - i) z =
      (-1 : ℤ) ^ (k - 1) * localOffsetCofactor k i (-z) := by
  have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
  have hik : i ≤ k := (Finset.mem_Icc.mp hi).2
  have hj : k + 1 - i ∈ Finset.Icc 1 k := by
    rw [Finset.mem_Icc]
    constructor <;> omega
  have hreflect :
      (∏ j ∈ (Finset.Icc 1 k).erase (k + 1 - i),
          (z + (j : ℤ) - ((k + 1 - i : ℕ) : ℤ))) =
        ∏ a ∈ (Finset.Icc 1 k).erase i,
          -((-z) + (a : ℤ) - (i : ℤ)) := by
    refine Finset.prod_bij'
      (fun j _hj => k + 1 - j) (fun a _ha => k + 1 - a)
        ?_ ?_ ?_ ?_ ?_
    · intro j hjmem
      simp only [Finset.mem_erase, Finset.mem_Icc] at hjmem ⊢
      rcases hjmem with ⟨hjne, hj1, hjk⟩
      constructor
      · intro heq
        apply hjne
        omega
      · constructor <;> omega
    · intro a hamem
      simp only [Finset.mem_erase, Finset.mem_Icc] at hamem ⊢
      rcases hamem with ⟨hane, ha1, hak⟩
      constructor
      · intro heq
        apply hane
        omega
      · constructor <;> omega
    · intro j hjmem
      simp only [Finset.mem_erase, Finset.mem_Icc] at hjmem
      rcases hjmem with ⟨_hjne, hj1, hjk⟩
      change k + 1 - (k + 1 - j) = j
      omega
    · intro a hamem
      simp only [Finset.mem_erase, Finset.mem_Icc] at hamem
      rcases hamem with ⟨_hane, ha1, hak⟩
      change k + 1 - (k + 1 - a) = a
      omega
    · intro j hjmem
      simp only [Finset.mem_erase, Finset.mem_Icc] at hjmem
      rcases hjmem with ⟨_hjne, hj1, hjk⟩
      rw [Nat.cast_sub (by omega : i ≤ k + 1),
        Nat.cast_sub (by omega : j ≤ k + 1)]
      push_cast
      ring
  unfold localOffsetCofactor
  rw [hreflect, Finset.prod_neg]
  have hcard : ((Finset.Icc 1 k).erase i).card = k - 1 := by
    rw [Finset.card_erase_of_mem hi, Nat.card_Icc]
    omega
  rw [hcard]

/-- Pure integer algebra for an even reflected row.  Here the lower and
upper omitted factors are `H*X` and `H*(M-X)`.  Reflection changes
`(C,D)` to `(-C,D)`, and the square residual is `M+3X=H*A`. -/
theorem even_reflected_second_order_algebra
    {H X M A C D QL QU : ℤ}
    (hH : H ≠ 0)
    (hres : M + 3 * X = H * A)
    (heq : (H * (M - X)) * QU = 4 * (H * X) * QL)
    (hQL : H ^ 2 ∣ QL - C - D * (H * X))
    (hQU : H ^ 2 ∣ QU + C - D * (H * (M - X))) :
    H ∣ C * A - 12 * D * X ^ 2 := by
  let EL : ℤ := QL - C - D * (H * X)
  let EU : ℤ := QU + C - D * (H * (M - X))
  have hLower : H ^ 3 ∣ (H * X) * EL := by
    have hmul := mul_dvd_mul (dvd_mul_right H X) hQL
    convert hmul using 1 <;> ring
  have hUpper : H ^ 3 ∣ (H * (M - X)) * EU := by
    have hmul := mul_dvd_mul (dvd_mul_right H (M - X)) hQU
    convert hmul using 1 <;> ring
  have hbase : H ^ 3 ∣
      (H * (M - X)) * (-C + D * (H * (M - X))) -
        4 * (H * X) * (C + D * (H * X)) := by
    have hid :
        (H * (M - X)) * (-C + D * (H * (M - X))) -
            4 * (H * X) * (C + D * (H * X)) =
          4 * ((H * X) * EL) - (H * (M - X)) * EU := by
      dsimp [EL, EU]
      linear_combination heq
    rw [hid]
    exact dvd_sub (dvd_mul_of_dvd_right hLower 4) hUpper
  have hscaled : H ^ 3 ∣
      H ^ 2 * (-C * A + D * ((M - X) ^ 2 - 4 * X ^ 2)) := by
    have hEq :
        (H * (M - X)) * (-C + D * (H * (M - X))) -
            4 * (H * X) * (C + D * (H * X)) =
          H ^ 2 * (-C * A + D * ((M - X) ^ 2 - 4 * X ^ 2)) := by
      calc
        (H * (M - X)) * (-C + D * (H * (M - X))) -
            4 * (H * X) * (C + D * (H * X)) =
            H ^ 2 * D * ((M - X) ^ 2 - 4 * X ^ 2) -
              C * H * (M + 3 * X) := by ring
        _ = H ^ 2 * D * ((M - X) ^ 2 - 4 * X ^ 2) -
              C * H * (H * A) := by rw [hres]
        _ = H ^ 2 * (-C * A + D * ((M - X) ^ 2 - 4 * X ^ 2)) := by ring
    rw [← hEq]
    exact hbase
  have hfirst : H ∣ -C * A + D * ((M - X) ^ 2 - 4 * X ^ 2) := by
    rcases hscaled with ⟨q, hq⟩
    refine ⟨q, ?_⟩
    apply mul_left_cancel₀ (pow_ne_zero 2 hH)
    calc
      H ^ 2 * (-C * A + D * ((M - X) ^ 2 - 4 * X ^ 2)) =
          H ^ 3 * q := hq
      _ = H ^ 2 * (H * q) := by ring
  have hresDvd : H ∣ M + 3 * X := ⟨A, hres⟩
  have hsqDvd : H ∣ (M + 3 * X) * (M - 5 * X) :=
    dvd_mul_of_dvd_left hresDvd (M - 5 * X)
  have hcombine := dvd_add
    (dvd_mul_of_dvd_right hfirst (-1))
    (dvd_mul_of_dvd_right hsqDvd D)
  convert hcombine using 1 <;> ring

/-- Pure integer algebra for an odd reflected row.  Reflection changes
`(C,D)` to `(C,-D)`, and the square residual is `5X-M=H*A`. -/
theorem odd_reflected_second_order_algebra
    {H X M A C D QL QU : ℤ}
    (hH : H ≠ 0)
    (hres : 5 * X - M = H * A)
    (heq : (H * (M - X)) * QU = 4 * (H * X) * QL)
    (hQL : H ^ 2 ∣ QL - C - D * (H * X))
    (hQU : H ^ 2 ∣ QU - C + D * (H * (M - X))) :
    H ∣ C * A + 20 * D * X ^ 2 := by
  let EL : ℤ := QL - C - D * (H * X)
  let EU : ℤ := QU - C + D * (H * (M - X))
  have hLower : H ^ 3 ∣ (H * X) * EL := by
    have hmul := mul_dvd_mul (dvd_mul_right H X) hQL
    convert hmul using 1 <;> ring
  have hUpper : H ^ 3 ∣ (H * (M - X)) * EU := by
    have hmul := mul_dvd_mul (dvd_mul_right H (M - X)) hQU
    convert hmul using 1 <;> ring
  have hbase : H ^ 3 ∣
      (H * (M - X)) * (C - D * (H * (M - X))) -
        4 * (H * X) * (C + D * (H * X)) := by
    have hid :
        (H * (M - X)) * (C - D * (H * (M - X))) -
            4 * (H * X) * (C + D * (H * X)) =
          4 * ((H * X) * EL) - (H * (M - X)) * EU := by
      dsimp [EL, EU]
      linear_combination heq
    rw [hid]
    exact dvd_sub (dvd_mul_of_dvd_right hLower 4) hUpper
  have hscaled : H ^ 3 ∣
      H ^ 2 * (-C * A - D * ((M - X) ^ 2 + 4 * X ^ 2)) := by
    have hEq :
        (H * (M - X)) * (C - D * (H * (M - X))) -
            4 * (H * X) * (C + D * (H * X)) =
          H ^ 2 * (-C * A - D * ((M - X) ^ 2 + 4 * X ^ 2)) := by
      calc
        (H * (M - X)) * (C - D * (H * (M - X))) -
            4 * (H * X) * (C + D * (H * X)) =
            C * H * (M - 5 * X) -
              H ^ 2 * D * ((M - X) ^ 2 + 4 * X ^ 2) := by ring
        _ = C * H * (-(H * A)) -
              H ^ 2 * D * ((M - X) ^ 2 + 4 * X ^ 2) := by
              rw [show M - 5 * X = -(H * A) by
                calc
                  M - 5 * X = -(5 * X - M) := by ring
                  _ = -(H * A) := by rw [hres]]
        _ = H ^ 2 * (-C * A - D * ((M - X) ^ 2 + 4 * X ^ 2)) := by ring
    rw [← hEq]
    exact hbase
  have hfirst : H ∣ -C * A - D * ((M - X) ^ 2 + 4 * X ^ 2) := by
    rcases hscaled with ⟨q, hq⟩
    refine ⟨q, ?_⟩
    apply mul_left_cancel₀ (pow_ne_zero 2 hH)
    calc
      H ^ 2 * (-C * A - D * ((M - X) ^ 2 + 4 * X ^ 2)) =
          H ^ 3 * q := hq
      _ = H ^ 2 * (H * q) := by ring
  have hresDvd : H ∣ 5 * X - M := ⟨A, hres⟩
  have hsqDvd : H ∣ (5 * X - M) * (M + 3 * X) :=
    dvd_mul_of_dvd_left hresDvd (M + 3 * X)
  have hcombine := dvd_add
    (dvd_mul_of_dvd_right hfirst (-1))
    (dvd_mul_of_dvd_right hsqDvd D)
  convert hcombine using 1 <;> ring

/-- Third-order even reflected lift.  The quadratic cofactor coefficient is
`E`.  The conclusion is kept as a square divisibility, so no quotient or
implicit cancellation is hidden. -/
theorem even_reflected_third_order_algebra
    {H X M A C D E QL QU : ℤ}
    (hH : H ≠ 0)
    (hres : M + 3 * X = H * A)
    (heq : (H * (M - X)) * QU = 4 * (H * X) * QL)
    (hQL : H ^ 3 ∣ QL - C - D * (H * X) - E * (H * X) ^ 2)
    (hQU : H ^ 3 ∣ QU + C - D * (H * (M - X)) +
      E * (H * (M - X)) ^ 2) :
    H ^ 2 ∣ C * A - 12 * D * X ^ 2 +
      H * (8 * D * A * X - 60 * E * X ^ 3) := by
  let EL : ℤ := QL - C - D * (H * X) - E * (H * X) ^ 2
  let EU : ℤ := QU + C - D * (H * (M - X)) + E * (H * (M - X)) ^ 2
  let T : ℤ := -C * A + D * ((M - X) ^ 2 - 4 * X ^ 2) -
    H * E * ((M - X) ^ 3 + 4 * X ^ 3)
  have hLower : H ^ 4 ∣ (H * X) * EL := by
    have hmul := mul_dvd_mul (dvd_mul_right H X) hQL
    convert hmul using 1 <;> ring
  have hUpper : H ^ 4 ∣ (H * (M - X)) * EU := by
    have hmul := mul_dvd_mul (dvd_mul_right H (M - X)) hQU
    convert hmul using 1 <;> ring
  have hbase : H ^ 4 ∣
      (H * (M - X)) *
          (-C + D * (H * (M - X)) - E * (H * (M - X)) ^ 2) -
        4 * (H * X) * (C + D * (H * X) + E * (H * X) ^ 2) := by
    have hid :
        (H * (M - X)) *
            (-C + D * (H * (M - X)) - E * (H * (M - X)) ^ 2) -
          4 * (H * X) * (C + D * (H * X) + E * (H * X) ^ 2) =
        4 * ((H * X) * EL) - (H * (M - X)) * EU := by
      dsimp [EL, EU]
      linear_combination heq
    rw [hid]
    exact dvd_sub (dvd_mul_of_dvd_right hLower 4) hUpper
  have hscaled : H ^ 4 ∣ H ^ 2 * T := by
    have hEq :
        (H * (M - X)) *
            (-C + D * (H * (M - X)) - E * (H * (M - X)) ^ 2) -
          4 * (H * X) * (C + D * (H * X) + E * (H * X) ^ 2) =
          H ^ 2 * T := by
      dsimp [T]
      calc
        (H * (M - X)) *
            (-C + D * (H * (M - X)) - E * (H * (M - X)) ^ 2) -
          4 * (H * X) * (C + D * (H * X) + E * (H * X) ^ 2) =
            H ^ 2 * (D * ((M - X) ^ 2 - 4 * X ^ 2) -
              H * E * ((M - X) ^ 3 + 4 * X ^ 3)) -
              C * H * (M + 3 * X) := by ring
        _ = H ^ 2 * (D * ((M - X) ^ 2 - 4 * X ^ 2) -
              H * E * ((M - X) ^ 3 + 4 * X ^ 3)) -
              C * H * (H * A) := by rw [hres]
        _ = H ^ 2 * T := by dsimp [T]; ring
    rw [← hEq]
    exact hbase
  have hT : H ^ 2 ∣ T := by
    rcases hscaled with ⟨q, hq⟩
    refine ⟨q, ?_⟩
    apply mul_left_cancel₀ (pow_ne_zero 2 hH)
    calc
      H ^ 2 * T = H ^ 4 * q := hq
      _ = H ^ 2 * (H ^ 2 * q) := by ring
  let K : ℤ := (M - X) ^ 2 - 4 * X * (M - X) + 16 * X ^ 2
  have hfactor : (M - X) ^ 3 + 64 * X ^ 3 = (M + 3 * X) * K := by
    dsimp [K]
    ring
  have hcorrection : H ^ 2 ∣
      (C * A - 12 * D * X ^ 2 +
          H * (8 * D * A * X - 60 * E * X ^ 3)) + T := by
    refine ⟨A * (D * A - E * K), ?_⟩
    calc
      (C * A - 12 * D * X ^ 2 +
          H * (8 * D * A * X - 60 * E * X ^ 3)) + T =
          D * (M + 3 * X) * (M - 5 * X) +
            H * (8 * D * A * X -
              E * ((M - X) ^ 3 + 64 * X ^ 3)) := by
              dsimp [T]
              ring
      _ = D * (H * A) * (M - 5 * X) +
            H * (8 * D * A * X - E * ((H * A) * K)) := by
            rw [hfactor, hres]
      _ = H ^ 2 * (A * (D * A - E * K)) := by
            linear_combination (D * H * A) * hres
  convert dvd_sub hcorrection hT using 1 <;> ring

/-- Third-order odd reflected lift. -/
theorem odd_reflected_third_order_algebra
    {H X M A C D E QL QU : ℤ}
    (hH : H ≠ 0)
    (hres : 5 * X - M = H * A)
    (heq : (H * (M - X)) * QU = 4 * (H * X) * QL)
    (hQL : H ^ 3 ∣ QL - C - D * (H * X) - E * (H * X) ^ 2)
    (hQU : H ^ 3 ∣ QU - C + D * (H * (M - X)) -
      E * (H * (M - X)) ^ 2) :
    H ^ 2 ∣ C * A + 20 * D * X ^ 2 -
      H * (8 * D * A * X + 60 * E * X ^ 3) := by
  let EL : ℤ := QL - C - D * (H * X) - E * (H * X) ^ 2
  let EU : ℤ := QU - C + D * (H * (M - X)) - E * (H * (M - X)) ^ 2
  let T : ℤ := -C * A - D * ((M - X) ^ 2 + 4 * X ^ 2) +
    H * E * ((M - X) ^ 3 - 4 * X ^ 3)
  have hLower : H ^ 4 ∣ (H * X) * EL := by
    have hmul := mul_dvd_mul (dvd_mul_right H X) hQL
    convert hmul using 1 <;> ring
  have hUpper : H ^ 4 ∣ (H * (M - X)) * EU := by
    have hmul := mul_dvd_mul (dvd_mul_right H (M - X)) hQU
    convert hmul using 1 <;> ring
  have hbase : H ^ 4 ∣
      (H * (M - X)) *
          (C - D * (H * (M - X)) + E * (H * (M - X)) ^ 2) -
        4 * (H * X) * (C + D * (H * X) + E * (H * X) ^ 2) := by
    have hid :
        (H * (M - X)) *
            (C - D * (H * (M - X)) + E * (H * (M - X)) ^ 2) -
          4 * (H * X) * (C + D * (H * X) + E * (H * X) ^ 2) =
        4 * ((H * X) * EL) - (H * (M - X)) * EU := by
      dsimp [EL, EU]
      linear_combination heq
    rw [hid]
    exact dvd_sub (dvd_mul_of_dvd_right hLower 4) hUpper
  have hscaled : H ^ 4 ∣ H ^ 2 * T := by
    have hEq :
        (H * (M - X)) *
            (C - D * (H * (M - X)) + E * (H * (M - X)) ^ 2) -
          4 * (H * X) * (C + D * (H * X) + E * (H * X) ^ 2) =
          H ^ 2 * T := by
      dsimp [T]
      calc
        (H * (M - X)) *
            (C - D * (H * (M - X)) + E * (H * (M - X)) ^ 2) -
          4 * (H * X) * (C + D * (H * X) + E * (H * X) ^ 2) =
            C * H * (M - 5 * X) -
              H ^ 2 * D * ((M - X) ^ 2 + 4 * X ^ 2) +
              H ^ 3 * E * ((M - X) ^ 3 - 4 * X ^ 3) := by ring
        _ = C * H * (-(H * A)) -
              H ^ 2 * D * ((M - X) ^ 2 + 4 * X ^ 2) +
              H ^ 3 * E * ((M - X) ^ 3 - 4 * X ^ 3) := by
                rw [show M - 5 * X = -(H * A) by
                  calc
                    M - 5 * X = -(5 * X - M) := by ring
                    _ = -(H * A) := by rw [hres]]
        _ = H ^ 2 * T := by dsimp [T]; ring
    rw [← hEq]
    exact hbase
  have hT : H ^ 2 ∣ T := by
    rcases hscaled with ⟨q, hq⟩
    refine ⟨q, ?_⟩
    apply mul_left_cancel₀ (pow_ne_zero 2 hH)
    calc
      H ^ 2 * T = H ^ 4 * q := hq
      _ = H ^ 2 * (H ^ 2 * q) := by ring
  let K : ℤ := (M - X) ^ 2 + 4 * X * (M - X) + 16 * X ^ 2
  have hfactor : (M - X) ^ 3 - 64 * X ^ 3 = (M - 5 * X) * K := by
    dsimp [K]
    ring
  have hcorrection : H ^ 2 ∣
      (C * A + 20 * D * X ^ 2 -
          H * (8 * D * A * X + 60 * E * X ^ 3)) + T := by
    refine ⟨-A * (D * A + E * K), ?_⟩
    have hm5 : M - 5 * X = -(H * A) := by
      calc
        M - 5 * X = -(5 * X - M) := by ring
        _ = -(H * A) := by rw [hres]
    calc
      (C * A + 20 * D * X ^ 2 -
          H * (8 * D * A * X + 60 * E * X ^ 3)) + T =
          D * (5 * X - M) * (M + 3 * X) +
            H * (-8 * D * A * X +
              E * ((M - X) ^ 3 - 64 * X ^ 3)) := by
              dsimp [T]
              ring
      _ = D * (H * A) * (M + 3 * X) +
            H * (-8 * D * A * X + E * (-(H * A) * K)) := by
            rw [hfactor, hres, hm5]
      _ = H ^ 2 * (-A * (D * A + E * K)) := by
            linear_combination -(D * H * A) * hres
  convert dvd_sub hcorrection hT using 1 <;> ring

/-- Clear the even reflected third lift using `3x = P*a-G`. -/
theorem even_reflected_third_lift_cleaned
    {P a x G C D E : ℤ}
    (hthird : P ^ 2 ∣ C * a - 12 * D * x ^ 2 +
      P * (8 * D * a * x - 60 * E * x ^ 3))
    (hres : P * a = G + 3 * x) :
    P ^ 2 ∣ 27 * C * a - 36 * D * G ^ 2 + 60 * E * P * G ^ 3 := by
  have hmain := dvd_mul_of_dvd_right hthird 27
  have hdiff : P ^ 2 ∣
      (27 * C * a - 36 * D * G ^ 2 + 60 * E * P * G ^ 3) -
        27 * (C * a - 12 * D * x ^ 2 +
          P * (8 * D * a * x - 60 * E * x ^ 3)) := by
    refine ⟨-(36 * D * a ^ 2 - 180 * E * G ^ 2 * a +
      180 * E * G * P * a ^ 2 - 60 * E * P ^ 2 * a ^ 3), ?_⟩
    rw [show G = P * a - 3 * x by linarith [hres]]
    ring
  convert dvd_add hmain hdiff using 1 <;> ring

/-- Clear the odd reflected third lift using `5x = P*a+G`. -/
theorem odd_reflected_third_lift_cleaned
    {P a x G C D E : ℤ}
    (hthird : P ^ 2 ∣ C * a + 20 * D * x ^ 2 -
      P * (8 * D * a * x + 60 * E * x ^ 3))
    (hres : P * a = 5 * x - G) :
    P ^ 2 ∣ 125 * C * a + 100 * D * G ^ 2 - 60 * E * P * G ^ 3 := by
  have hmain := dvd_mul_of_dvd_right hthird 125
  have hdiff : P ^ 2 ∣
      (125 * C * a + 100 * D * G ^ 2 - 60 * E * P * G ^ 3) -
        125 * (C * a + 20 * D * x ^ 2 -
          P * (8 * D * a * x + 60 * E * x ^ 3)) := by
    refine ⟨100 * D * a ^ 2 + 180 * E * G ^ 2 * a +
      180 * E * G * P * a ^ 2 + 60 * E * P ^ 2 * a ^ 3, ?_⟩
    rw [show G = 5 * x - P * a by linarith [hres]]
    ring
  convert dvd_add hmain hdiff using 1 <;> ring

private lemma product_congr_of_dvd_add
    {P U V A B : ℤ} (hU : P ∣ U + A) (hV : P ∣ V + B) :
    P ∣ U * V - A * B := by
  have hleft : P ∣ (U + A) * V := dvd_mul_of_dvd_left hU V
  have hright : P ∣ A * (V + B) := dvd_mul_of_dvd_right hV A
  convert dvd_sub hleft hright using 1 <;> ring

/-- One component of the cyclic even `P^2` composition. -/
theorem even_reflected_third_three_owner_component
    {P Q R a b c g C D E deltaQ deltaR : ℤ}
    (hthird : P ^ 2 ∣
      27 * C * a - 36 * D * g ^ 2 * Q ^ 2 * R ^ 2 +
        60 * E * P * g ^ 3 * Q ^ 3 * R ^ 3)
    (hdiffQ : a * P ^ 2 - b * Q ^ 2 = 3 * deltaQ)
    (hdiffR : a * P ^ 2 - c * R ^ 2 = 3 * deltaR) :
    P ^ 2 ∣ 27 * (C * a * b * c -
      12 * D * g ^ 2 * deltaQ * deltaR +
      20 * E * g ^ 3 * P * Q * R * deltaQ * deltaR) := by
  have hQ : P ^ 2 ∣ b * Q ^ 2 + 3 * deltaQ := by
    refine ⟨a, ?_⟩
    linear_combination -hdiffQ
  have hR : P ^ 2 ∣ c * R ^ 2 + 3 * deltaR := by
    refine ⟨a, ?_⟩
    linear_combination -hdiffR
  have hprod : P ^ 2 ∣
      (b * Q ^ 2) * (c * R ^ 2) - (3 * deltaQ) * (3 * deltaR) :=
    product_congr_of_dvd_add hQ hR
  have hmain := dvd_mul_of_dvd_right hthird (b * c)
  have hD := dvd_mul_of_dvd_right hprod (36 * D * g ^ 2)
  have hE := dvd_mul_of_dvd_right hprod (-60 * E * g ^ 3 * P * Q * R)
  convert dvd_add (dvd_add hmain hD) hE using 1 <;> ring

/-- One component of the cyclic odd `P^2` composition. -/
theorem odd_reflected_third_three_owner_component
    {P Q R a b c g C D E deltaQ deltaR : ℤ}
    (hthird : P ^ 2 ∣
      125 * C * a + 100 * D * g ^ 2 * Q ^ 2 * R ^ 2 -
        60 * E * P * g ^ 3 * Q ^ 3 * R ^ 3)
    (hdiffQ : a * P ^ 2 - b * Q ^ 2 = 5 * deltaQ)
    (hdiffR : a * P ^ 2 - c * R ^ 2 = 5 * deltaR) :
    P ^ 2 ∣ 125 * (C * a * b * c +
      20 * D * g ^ 2 * deltaQ * deltaR -
      12 * E * g ^ 3 * P * Q * R * deltaQ * deltaR) := by
  have hQ : P ^ 2 ∣ b * Q ^ 2 + 5 * deltaQ := by
    refine ⟨a, ?_⟩
    linear_combination -hdiffQ
  have hR : P ^ 2 ∣ c * R ^ 2 + 5 * deltaR := by
    refine ⟨a, ?_⟩
    linear_combination -hdiffR
  have hprod : P ^ 2 ∣
      (b * Q ^ 2) * (c * R ^ 2) - (5 * deltaQ) * (5 * deltaR) :=
    product_congr_of_dvd_add hQ hR
  have hmain := dvd_mul_of_dvd_right hthird (b * c)
  have hD := dvd_mul_of_dvd_right hprod (-100 * D * g ^ 2)
  have hE := dvd_mul_of_dvd_right hprod (60 * E * g ^ 3 * P * Q * R)
  convert dvd_add (dvd_add hmain hD) hE using 1 <;> ring

/-- Full cyclic even `P^2,Q^2,R^2` composition. -/
theorem even_reflected_third_three_owner_composition
    {P Q R a b c g Cᵢ Dᵢ Eᵢ Cⱼ Dⱼ Eⱼ Cₗ Dₗ Eₗ i j l : ℤ}
    (hcopPQ : IsCoprime P Q) (hcopPR : IsCoprime P R)
    (hcopQR : IsCoprime Q R)
    (hP : P ^ 2 ∣ 27 * Cᵢ * a - 36 * Dᵢ * g ^ 2 * Q ^ 2 * R ^ 2 +
      60 * Eᵢ * P * g ^ 3 * Q ^ 3 * R ^ 3)
    (hQ : Q ^ 2 ∣ 27 * Cⱼ * b - 36 * Dⱼ * g ^ 2 * P ^ 2 * R ^ 2 +
      60 * Eⱼ * Q * g ^ 3 * P ^ 3 * R ^ 3)
    (hR : R ^ 2 ∣ 27 * Cₗ * c - 36 * Dₗ * g ^ 2 * P ^ 2 * Q ^ 2 +
      60 * Eₗ * R * g ^ 3 * P ^ 3 * Q ^ 3)
    (hPQ : a * P ^ 2 - b * Q ^ 2 = 3 * (i - j))
    (hPR : a * P ^ 2 - c * R ^ 2 = 3 * (i - l))
    (hQR : b * Q ^ 2 - c * R ^ 2 = 3 * (j - l)) :
    P ^ 2 ∣ 27 * (Cᵢ * a * b * c - 12 * Dᵢ * g ^ 2 * (i - j) * (i - l) +
      20 * Eᵢ * g ^ 3 * P * Q * R * (i - j) * (i - l)) ∧
    Q ^ 2 ∣ 27 * (Cⱼ * a * b * c - 12 * Dⱼ * g ^ 2 * (j - i) * (j - l) +
      20 * Eⱼ * g ^ 3 * P * Q * R * (j - i) * (j - l)) ∧
    R ^ 2 ∣ 27 * (Cₗ * a * b * c - 12 * Dₗ * g ^ 2 * (l - i) * (l - j) +
      20 * Eₗ * g ^ 3 * P * Q * R * (l - i) * (l - j)) := by
  clear hcopPQ hcopPR hcopQR
  refine ⟨even_reflected_third_three_owner_component hP hPQ hPR, ?_, ?_⟩
  · have hdiff : b * Q ^ 2 - a * P ^ 2 = 3 * (j - i) := by
      linear_combination -hPQ
    have hraw := even_reflected_third_three_owner_component
      (P := Q) (Q := P) (R := R) (a := b) (b := a) (c := c) (g := g)
      (C := Cⱼ) (D := Dⱼ) (E := Eⱼ) (deltaQ := j - i) (deltaR := j - l)
      hQ hdiff hQR
    simpa [mul_comm, mul_left_comm, mul_assoc] using hraw
  · have hdiff1 : c * R ^ 2 - a * P ^ 2 = 3 * (l - i) := by
      linear_combination -hPR
    have hdiff2 : c * R ^ 2 - b * Q ^ 2 = 3 * (l - j) := by
      linear_combination -hQR
    have hraw := even_reflected_third_three_owner_component
      (P := R) (Q := P) (R := Q) (a := c) (b := a) (c := b) (g := g)
      (C := Cₗ) (D := Dₗ) (E := Eₗ) (deltaQ := l - i) (deltaR := l - j)
      hR hdiff1 hdiff2
    simpa [mul_comm, mul_left_comm, mul_assoc] using hraw

/-- Full cyclic odd `P^2,Q^2,R^2` composition. -/
theorem odd_reflected_third_three_owner_composition
    {P Q R a b c g Cᵢ Dᵢ Eᵢ Cⱼ Dⱼ Eⱼ Cₗ Dₗ Eₗ i j l : ℤ}
    (hcopPQ : IsCoprime P Q) (hcopPR : IsCoprime P R)
    (hcopQR : IsCoprime Q R)
    (hP : P ^ 2 ∣ 125 * Cᵢ * a + 100 * Dᵢ * g ^ 2 * Q ^ 2 * R ^ 2 -
      60 * Eᵢ * P * g ^ 3 * Q ^ 3 * R ^ 3)
    (hQ : Q ^ 2 ∣ 125 * Cⱼ * b + 100 * Dⱼ * g ^ 2 * P ^ 2 * R ^ 2 -
      60 * Eⱼ * Q * g ^ 3 * P ^ 3 * R ^ 3)
    (hR : R ^ 2 ∣ 125 * Cₗ * c + 100 * Dₗ * g ^ 2 * P ^ 2 * Q ^ 2 -
      60 * Eₗ * R * g ^ 3 * P ^ 3 * Q ^ 3)
    (hPQ : a * P ^ 2 - b * Q ^ 2 = 5 * (i - j))
    (hPR : a * P ^ 2 - c * R ^ 2 = 5 * (i - l))
    (hQR : b * Q ^ 2 - c * R ^ 2 = 5 * (j - l)) :
    P ^ 2 ∣ 125 * (Cᵢ * a * b * c + 20 * Dᵢ * g ^ 2 * (i - j) * (i - l) -
      12 * Eᵢ * g ^ 3 * P * Q * R * (i - j) * (i - l)) ∧
    Q ^ 2 ∣ 125 * (Cⱼ * a * b * c + 20 * Dⱼ * g ^ 2 * (j - i) * (j - l) -
      12 * Eⱼ * g ^ 3 * P * Q * R * (j - i) * (j - l)) ∧
    R ^ 2 ∣ 125 * (Cₗ * a * b * c + 20 * Dₗ * g ^ 2 * (l - i) * (l - j) -
      12 * Eₗ * g ^ 3 * P * Q * R * (l - i) * (l - j)) := by
  clear hcopPQ hcopPR hcopQR
  refine ⟨odd_reflected_third_three_owner_component hP hPQ hPR, ?_, ?_⟩
  · have hdiff : b * Q ^ 2 - a * P ^ 2 = 5 * (j - i) := by
      linear_combination -hPQ
    have hraw := odd_reflected_third_three_owner_component
      (P := Q) (Q := P) (R := R) (a := b) (b := a) (c := c) (g := g)
      (C := Cⱼ) (D := Dⱼ) (E := Eⱼ) (deltaQ := j - i) (deltaR := j - l)
      hQ hdiff hQR
    simpa [mul_comm, mul_left_comm, mul_assoc] using hraw
  · have hdiff1 : c * R ^ 2 - a * P ^ 2 = 5 * (l - i) := by
      linear_combination -hPR
    have hdiff2 : c * R ^ 2 - b * Q ^ 2 = 5 * (l - j) := by
      linear_combination -hQR
    have hraw := odd_reflected_third_three_owner_component
      (P := R) (Q := P) (R := Q) (a := c) (b := a) (c := b) (g := g)
      (C := Cₗ) (D := Dₗ) (E := Eₗ) (deltaQ := l - i) (deltaR := l - j)
      hR hdiff1 hdiff2
    simpa [mul_comm, mul_left_comm, mul_assoc] using hraw

/-- Replace the lower quotient in the even second lift by the other two
cleaned center components.  The small-prime loss `g` is retained exactly. -/
theorem even_reflected_second_lift_cleaned
    {P Q R a x g C D : ℤ}
    (hsecond : P ∣ C * a - 12 * D * x ^ 2)
    (hres : P * a = g * Q * R + 3 * x) :
    P ∣ 3 * C * a - 4 * D * g ^ 2 * Q ^ 2 * R ^ 2 := by
  have hlinear : P ∣ 3 * x + g * Q * R := by
    refine ⟨a, ?_⟩
    linear_combination -hres
  have hsquare : P ∣ (3 * x) ^ 2 - (g * Q * R) ^ 2 := by
    have hfactor : P ∣ (3 * x + g * Q * R) * (3 * x - g * Q * R) :=
      dvd_mul_of_dvd_left hlinear (3 * x - g * Q * R)
    convert hfactor using 1 <;> ring
  have hcombine := dvd_add
    (dvd_mul_of_dvd_right hsecond 3)
    (dvd_mul_of_dvd_right hsquare (4 * D))
  convert hcombine using 1 <;> ring

/-- Odd analogue of `even_reflected_second_lift_cleaned`. -/
theorem odd_reflected_second_lift_cleaned
    {P Q R a x g C D : ℤ}
    (hsecond : P ∣ C * a + 20 * D * x ^ 2)
    (hres : P * a = 5 * x - g * Q * R) :
    P ∣ 5 * C * a + 4 * D * g ^ 2 * Q ^ 2 * R ^ 2 := by
  have hlinear : P ∣ 5 * x - g * Q * R := ⟨a, hres.symm⟩
  have hsquare : P ∣ (5 * x) ^ 2 - (g * Q * R) ^ 2 := by
    have hfactor : P ∣ (5 * x - g * Q * R) * (5 * x + g * Q * R) :=
      dvd_mul_of_dvd_left hlinear (5 * x + g * Q * R)
    convert hfactor using 1 <;> ring
  have hcombine := dvd_sub
    (dvd_mul_of_dvd_right hsecond 5)
    (dvd_mul_of_dvd_right hsquare (4 * D))
  convert hcombine using 1 <;> ring

/-- Composition at one even reflected owner.  The step-three square
differences eliminate both opposite residual quotients and leave the exact
fixed-owner obstruction. -/
theorem even_reflected_three_owner_component
    {P Q R a b c g C D deltaQ deltaR : ℤ}
    (hsecond : P ∣ 3 * C * a - 4 * D * g ^ 2 * Q ^ 2 * R ^ 2)
    (hdiffQ : a * P ^ 2 - b * Q ^ 2 = 3 * deltaQ)
    (hdiffR : a * P ^ 2 - c * R ^ 2 = 3 * deltaR) :
    P ∣ 3 * (C * a * b * c - 12 * D * g ^ 2 * deltaQ * deltaR) := by
  have hQ : P ∣ b * Q ^ 2 + 3 * deltaQ := by
    refine ⟨a * P, ?_⟩
    calc
      b * Q ^ 2 + 3 * deltaQ = a * P ^ 2 := by
        linear_combination -hdiffQ
      _ = P * (a * P) := by ring
  have hR : P ∣ c * R ^ 2 + 3 * deltaR := by
    refine ⟨a * P, ?_⟩
    calc
      c * R ^ 2 + 3 * deltaR = a * P ^ 2 := by
        linear_combination -hdiffR
      _ = P * (a * P) := by ring
  have hprod : P ∣
      (b * Q ^ 2) * (c * R ^ 2) - (3 * deltaQ) * (3 * deltaR) :=
    product_congr_of_dvd_add hQ hR
  have hmain : P ∣
      b * c * (3 * C * a - 4 * D * g ^ 2 * Q ^ 2 * R ^ 2) :=
    dvd_mul_of_dvd_right hsecond (b * c)
  have hcombine := dvd_add hmain
    (dvd_mul_of_dvd_right hprod (4 * D * g ^ 2))
  convert hcombine using 1 <;> ring

/-- Composition at one odd reflected owner.  Here the residual differences
have step five and the correction constant is `20`. -/
theorem odd_reflected_three_owner_component
    {P Q R a b c g C D deltaQ deltaR : ℤ}
    (hsecond : P ∣ 5 * C * a + 4 * D * g ^ 2 * Q ^ 2 * R ^ 2)
    (hdiffQ : a * P ^ 2 - b * Q ^ 2 = 5 * deltaQ)
    (hdiffR : a * P ^ 2 - c * R ^ 2 = 5 * deltaR) :
    P ∣ 5 * (C * a * b * c + 20 * D * g ^ 2 * deltaQ * deltaR) := by
  have hQ : P ∣ b * Q ^ 2 + 5 * deltaQ := by
    refine ⟨a * P, ?_⟩
    calc
      b * Q ^ 2 + 5 * deltaQ = a * P ^ 2 := by
        linear_combination -hdiffQ
      _ = P * (a * P) := by ring
  have hR : P ∣ c * R ^ 2 + 5 * deltaR := by
    refine ⟨a * P, ?_⟩
    calc
      c * R ^ 2 + 5 * deltaR = a * P ^ 2 := by
        linear_combination -hdiffR
      _ = P * (a * P) := by ring
  have hprod : P ∣
      (b * Q ^ 2) * (c * R ^ 2) - (5 * deltaQ) * (5 * deltaR) :=
    product_congr_of_dvd_add hQ hR
  have hmain : P ∣
      b * c * (5 * C * a + 4 * D * g ^ 2 * Q ^ 2 * R ^ 2) :=
    dvd_mul_of_dvd_right hsecond (b * c)
  have hcombine := dvd_sub hmain
    (dvd_mul_of_dvd_right hprod (4 * D * g ^ 2))
  convert hcombine using 1 <;> ring

/-- Cyclic even three-owner composition.  Pairwise coprimality is included
because it is part of the cleaned-bucket interface, although the three local
divisibilities themselves do not need it. -/
theorem even_reflected_three_owner_composition
    {P Q R a b c g Cᵢ Dᵢ Cⱼ Dⱼ Cₗ Dₗ i j l : ℤ}
    (hcopPQ : IsCoprime P Q) (hcopPR : IsCoprime P R)
    (hcopQR : IsCoprime Q R)
    (hP : P ∣ 3 * Cᵢ * a - 4 * Dᵢ * g ^ 2 * Q ^ 2 * R ^ 2)
    (hQ : Q ∣ 3 * Cⱼ * b - 4 * Dⱼ * g ^ 2 * P ^ 2 * R ^ 2)
    (hR : R ∣ 3 * Cₗ * c - 4 * Dₗ * g ^ 2 * P ^ 2 * Q ^ 2)
    (hPQ : a * P ^ 2 - b * Q ^ 2 = 3 * (i - j))
    (hPR : a * P ^ 2 - c * R ^ 2 = 3 * (i - l))
    (hQR : b * Q ^ 2 - c * R ^ 2 = 3 * (j - l)) :
    P ∣ 3 * (Cᵢ * a * b * c - 12 * Dᵢ * g ^ 2 * (i - j) * (i - l)) ∧
    Q ∣ 3 * (Cⱼ * a * b * c - 12 * Dⱼ * g ^ 2 * (j - i) * (j - l)) ∧
    R ∣ 3 * (Cₗ * a * b * c - 12 * Dₗ * g ^ 2 * (l - i) * (l - j)) := by
  clear hcopPQ hcopPR hcopQR
  refine ⟨even_reflected_three_owner_component hP hPQ hPR, ?_, ?_⟩
  · have hdiff1 : b * Q ^ 2 - a * P ^ 2 = 3 * (j - i) := by
      linear_combination -hPQ
    have hraw := even_reflected_three_owner_component
      (P := Q) (Q := P) (R := R) (a := b) (b := a) (c := c)
      (g := g) (C := Cⱼ) (D := Dⱼ) (deltaQ := j - i) (deltaR := j - l)
      hQ hdiff1 hQR
    simpa [mul_comm, mul_left_comm, mul_assoc] using hraw
  · have hdiff1 : c * R ^ 2 - a * P ^ 2 = 3 * (l - i) := by
      linear_combination -hPR
    have hdiff2 : c * R ^ 2 - b * Q ^ 2 = 3 * (l - j) := by
      linear_combination -hQR
    have hraw := even_reflected_three_owner_component
      (P := R) (Q := P) (R := Q) (a := c) (b := a) (c := b)
      (g := g) (C := Cₗ) (D := Dₗ) (deltaQ := l - i) (deltaR := l - j)
      hR hdiff1 hdiff2
    simpa [mul_comm, mul_left_comm, mul_assoc] using hraw

/-- Cyclic odd three-owner composition. -/
theorem odd_reflected_three_owner_composition
    {P Q R a b c g Cᵢ Dᵢ Cⱼ Dⱼ Cₗ Dₗ i j l : ℤ}
    (hcopPQ : IsCoprime P Q) (hcopPR : IsCoprime P R)
    (hcopQR : IsCoprime Q R)
    (hP : P ∣ 5 * Cᵢ * a + 4 * Dᵢ * g ^ 2 * Q ^ 2 * R ^ 2)
    (hQ : Q ∣ 5 * Cⱼ * b + 4 * Dⱼ * g ^ 2 * P ^ 2 * R ^ 2)
    (hR : R ∣ 5 * Cₗ * c + 4 * Dₗ * g ^ 2 * P ^ 2 * Q ^ 2)
    (hPQ : a * P ^ 2 - b * Q ^ 2 = 5 * (i - j))
    (hPR : a * P ^ 2 - c * R ^ 2 = 5 * (i - l))
    (hQR : b * Q ^ 2 - c * R ^ 2 = 5 * (j - l)) :
    P ∣ 5 * (Cᵢ * a * b * c + 20 * Dᵢ * g ^ 2 * (i - j) * (i - l)) ∧
    Q ∣ 5 * (Cⱼ * a * b * c + 20 * Dⱼ * g ^ 2 * (j - i) * (j - l)) ∧
    R ∣ 5 * (Cₗ * a * b * c + 20 * Dₗ * g ^ 2 * (l - i) * (l - j)) := by
  clear hcopPQ hcopPR hcopQR
  refine ⟨odd_reflected_three_owner_component hP hPQ hPR, ?_, ?_⟩
  · have hdiff1 : b * Q ^ 2 - a * P ^ 2 = 5 * (j - i) := by
      linear_combination -hPQ
    have hraw := odd_reflected_three_owner_component
      (P := Q) (Q := P) (R := R) (a := b) (b := a) (c := c)
      (g := g) (C := Cⱼ) (D := Dⱼ) (deltaQ := j - i) (deltaR := j - l)
      hQ hdiff1 hQR
    simpa [mul_comm, mul_left_comm, mul_assoc] using hraw
  · have hdiff1 : c * R ^ 2 - a * P ^ 2 = 5 * (l - i) := by
      linear_combination -hPR
    have hdiff2 : c * R ^ 2 - b * Q ^ 2 = 5 * (l - j) := by
      linear_combination -hQR
    have hraw := odd_reflected_three_owner_component
      (P := R) (Q := P) (R := Q) (a := c) (b := a) (c := b)
      (g := g) (C := Cₗ) (D := Dₗ) (deltaQ := l - i) (deltaR := l - j)
      hR hdiff1 hdiff2
    simpa [mul_comm, mul_left_comm, mul_assoc] using hraw

/-- Complete even composition starting from the three raw reflected second
lifts.  The intermediate multiplication by `3` is explicit in
`even_reflected_second_lift_cleaned`; no inverse of `3` is used. -/
theorem even_reflected_three_owner_from_raw_second_lifts
    {P Q R a b c x y z g Cᵢ Dᵢ Cⱼ Dⱼ Cₗ Dₗ i j l : ℤ}
    (hcopPQ : IsCoprime P Q) (hcopPR : IsCoprime P R)
    (hcopQR : IsCoprime Q R)
    (hPraw : P ∣ Cᵢ * a - 12 * Dᵢ * x ^ 2)
    (hQraw : Q ∣ Cⱼ * b - 12 * Dⱼ * y ^ 2)
    (hRraw : R ∣ Cₗ * c - 12 * Dₗ * z ^ 2)
    (hPres : P * a = g * Q * R + 3 * x)
    (hQres : Q * b = g * P * R + 3 * y)
    (hRres : R * c = g * P * Q + 3 * z)
    (hPQ : a * P ^ 2 - b * Q ^ 2 = 3 * (i - j))
    (hPR : a * P ^ 2 - c * R ^ 2 = 3 * (i - l))
    (hQR : b * Q ^ 2 - c * R ^ 2 = 3 * (j - l)) :
    P ∣ 3 * (Cᵢ * a * b * c - 12 * Dᵢ * g ^ 2 * (i - j) * (i - l)) ∧
    Q ∣ 3 * (Cⱼ * a * b * c - 12 * Dⱼ * g ^ 2 * (j - i) * (j - l)) ∧
    R ∣ 3 * (Cₗ * a * b * c - 12 * Dₗ * g ^ 2 * (l - i) * (l - j)) := by
  have hP := even_reflected_second_lift_cleaned hPraw hPres
  have hQ := even_reflected_second_lift_cleaned
    (P := Q) (Q := P) (R := R) hQraw hQres
  have hR := even_reflected_second_lift_cleaned
    (P := R) (Q := P) (R := Q) hRraw (by
      simpa [mul_comm, mul_left_comm, mul_assoc] using hRres)
  exact even_reflected_three_owner_composition
    hcopPQ hcopPR hcopQR hP hQ
      (by simpa [mul_comm, mul_left_comm, mul_assoc] using hR)
      hPQ hPR hQR

/-- Complete odd composition starting from the raw second lifts.  Again the
factor `5` is multiplied through rather than inverted. -/
theorem odd_reflected_three_owner_from_raw_second_lifts
    {P Q R a b c x y z g Cᵢ Dᵢ Cⱼ Dⱼ Cₗ Dₗ i j l : ℤ}
    (hcopPQ : IsCoprime P Q) (hcopPR : IsCoprime P R)
    (hcopQR : IsCoprime Q R)
    (hPraw : P ∣ Cᵢ * a + 20 * Dᵢ * x ^ 2)
    (hQraw : Q ∣ Cⱼ * b + 20 * Dⱼ * y ^ 2)
    (hRraw : R ∣ Cₗ * c + 20 * Dₗ * z ^ 2)
    (hPres : P * a = 5 * x - g * Q * R)
    (hQres : Q * b = 5 * y - g * P * R)
    (hRres : R * c = 5 * z - g * P * Q)
    (hPQ : a * P ^ 2 - b * Q ^ 2 = 5 * (i - j))
    (hPR : a * P ^ 2 - c * R ^ 2 = 5 * (i - l))
    (hQR : b * Q ^ 2 - c * R ^ 2 = 5 * (j - l)) :
    P ∣ 5 * (Cᵢ * a * b * c + 20 * Dᵢ * g ^ 2 * (i - j) * (i - l)) ∧
    Q ∣ 5 * (Cⱼ * a * b * c + 20 * Dⱼ * g ^ 2 * (j - i) * (j - l)) ∧
    R ∣ 5 * (Cₗ * a * b * c + 20 * Dₗ * g ^ 2 * (l - i) * (l - j)) := by
  have hP := odd_reflected_second_lift_cleaned hPraw hPres
  have hQ := odd_reflected_second_lift_cleaned
    (P := Q) (Q := P) (R := R) hQraw hQres
  have hR := odd_reflected_second_lift_cleaned
    (P := R) (Q := P) (R := Q) hRraw (by
      simpa [mul_comm, mul_left_comm, mul_assoc] using hRres)
  exact odd_reflected_three_owner_composition
    hcopPQ hcopPR hcopQR hP hQ
      (by simpa [mul_comm, mul_left_comm, mul_assoc] using hR)
      hPQ hPR hQR

/-- Exact growth bound for the three residual cofactors in the balanced
three-owner regime.  It is deliberately linear in the center `S`; hence it
records the remaining unbounded regime rather than pretending to be a
cutoff. -/
theorem reflected_three_owner_cofactor_product_growth
    {S n g P Q R a b c : ℕ}
    (hg : 0 < g)
    (hcenter : S = g * P * Q * R)
    (hcenterLower : 2 * n < S)
    (hPa : P ^ 2 * a ≤ 7 * n)
    (hQb : Q ^ 2 * b ≤ 7 * n)
    (hRc : R ^ 2 * c ≤ 7 * n) :
    8 * a * b * c < 343 * g ^ 2 * S := by
  have hprodRaw :
      (P ^ 2 * a) * (Q ^ 2 * b) * (R ^ 2 * c) ≤
        (7 * n) * (7 * n) * (7 * n) :=
    Nat.mul_le_mul (Nat.mul_le_mul hPa hQb) hRc
  have hprod : (P * Q * R) ^ 2 * (a * b * c) ≤ 343 * n ^ 3 := by
    convert hprodRaw using 1 <;> ring
  have hscaledRaw := Nat.mul_le_mul_left (g ^ 2) hprod
  have hscaled : S ^ 2 * (a * b * c) ≤ 343 * g ^ 2 * n ^ 3 := by
    calc
      S ^ 2 * (a * b * c) =
          g ^ 2 * ((P * Q * R) ^ 2 * (a * b * c)) := by
            rw [hcenter]
            ring
      _ ≤ g ^ 2 * (343 * n ^ 3) := hscaledRaw
      _ = 343 * g ^ 2 * n ^ 3 := by ring
  have hcube : 8 * n ^ 3 < S ^ 3 := by
    have hpow := Nat.pow_lt_pow_left hcenterLower (by norm_num : 3 ≠ 0)
    convert hpow using 1 <;> ring
  have hscalePos : 0 < 343 * g ^ 2 := by positivity
  have hcubeScaled :
      343 * g ^ 2 * (8 * n ^ 3) < 343 * g ^ 2 * S ^ 3 :=
    Nat.mul_lt_mul_of_pos_left hcube hscalePos
  have hSpos : 0 < S := by omega
  have hbig :
      S ^ 2 * (8 * a * b * c) < S ^ 2 * (343 * g ^ 2 * S) := by
    calc
      S ^ 2 * (8 * a * b * c) = 8 * (S ^ 2 * (a * b * c)) := by ring
      _ ≤ 8 * (343 * g ^ 2 * n ^ 3) := Nat.mul_le_mul_left 8 hscaled
      _ = 343 * g ^ 2 * (8 * n ^ 3) := by ring
      _ < 343 * g ^ 2 * S ^ 3 := hcubeScaled
      _ = S ^ 2 * (343 * g ^ 2 * S) := by ring
  exact (Nat.mul_lt_mul_left (sq_pos_of_pos hSpos)).mp (by
    simpa [mul_assoc] using hbig)

/-- Equation-facing even-row wrapper.  `x` is the lower owner quotient,
`m` is the quotient of the reflection center (the sum of the two omitted
factors), and `a` is the quotient supplied by the reflected square lift. -/
theorem even_reflected_second_lift
    {k n d i h x m a : ℕ}
    (hkeven : Even k)
    (hi : i ∈ Finset.Icc 1 k)
    (hh : 0 < h)
    (hlower : n + i = h * x)
    (hcenter : (n + i) + (n + d + (k + 1 - i)) = h * m)
    (hres : m + 3 * x = h * a)
    (heq : blockProduct k (n + d) = 4 * blockProduct k n) :
    (h : ℤ) ∣
      localSecondConstant k i * (a : ℤ) -
        12 * localSecondLinear k i * (x : ℤ) ^ 2 := by
  let H : ℤ := (h : ℤ)
  let L : ℤ := ((n + i : ℕ) : ℤ)
  let U : ℤ := ((n + d + (k + 1 - i) : ℕ) : ℤ)
  let X : ℤ := (x : ℤ)
  let M : ℤ := (m : ℤ)
  let A : ℤ := (a : ℤ)
  let C : ℤ := localSecondConstant k i
  let D : ℤ := localSecondLinear k i
  let QL : ℤ := localBlockCofactor k i (n : ℤ)
  let QU : ℤ := localBlockCofactor k (k + 1 - i) ((n + d : ℕ) : ℤ)
  have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
  have hik : i ≤ k := (Finset.mem_Icc.mp hi).2
  have hj : k + 1 - i ∈ Finset.Icc 1 k := by
    rw [Finset.mem_Icc]
    constructor <;> omega
  have hH : H ≠ 0 := by
    dsimp [H]
    exact_mod_cast (Nat.ne_of_gt hh)
  have hL : L = H * X := by
    dsimp [L, H, X]
    exact_mod_cast hlower
  have hsum : L + U = H * M := by
    dsimp [L, U, H, M]
    exact_mod_cast hcenter
  have hU : U = H * (M - X) := by
    rw [hL] at hsum
    linear_combination hsum
  have hresInt : M + 3 * X = H * A := by
    dsimp [M, X, H, A]
    exact_mod_cast hres
  have heqInt :
      intBlockProduct k ((n + d : ℕ) : ℤ) =
        4 * intBlockProduct k (n : ℤ) := by
    rw [intBlockProduct_natCast, intBlockProduct_natCast]
    exact_mod_cast heq
  have heqLocal : U * QU = 4 * L * QL := by
    rw [intBlockProduct_eq_factor_mul_localBlockCofactor
        ((n + d : ℕ) : ℤ) hj,
      intBlockProduct_eq_factor_mul_localBlockCofactor (n : ℤ) hi] at heqInt
    dsimp [U, L, QU, QL]
    push_cast at heqInt ⊢
    convert heqInt using 1 <;> ring
  have hHL : H ∣ L := ⟨X, hL⟩
  have hHU : H ∣ U := ⟨M - X, hU⟩
  have hHsqLsq : H ^ 2 ∣ L ^ 2 := by
    simpa [pow_two] using mul_dvd_mul hHL hHL
  have hHsqUsq : H ^ 2 ∣ U ^ 2 := by
    simpa [pow_two] using mul_dvd_mul hHU hHU
  have hQLexp : L ^ 2 ∣ QL - C - D * L := by
    have hraw := localOffsetCofactor_second_order k i L
    have hrel : localOffsetCofactor k i L = QL := by
      dsimp [L, QL]
      exact localOffsetCofactor_eq_localBlockCofactor
    simpa [hrel, C, D] using hraw
  have hQL : H ^ 2 ∣ QL - C - D * L := dvd_trans hHsqLsq hQLexp
  have hkoddPred : Odd (k - 1) :=
    Nat.Even.sub_odd (by omega : 1 ≤ k) hkeven (by norm_num)
  have hsign : (-1 : ℤ) ^ (k - 1) = -1 :=
    Odd.neg_one_pow hkoddPred
  have hupperRel : localOffsetCofactor k (k + 1 - i) U = QU := by
    dsimp [U, QU]
    exact localOffsetCofactor_eq_localBlockCofactor
  have hreflect := localOffsetCofactor_reflected_agent hi U
  rw [hsign, hupperRel] at hreflect
  have hQUexp : U ^ 2 ∣ QU + C - D * U := by
    have hraw := localOffsetCofactor_second_order k i (-U)
    have hneg := dvd_neg.mpr hraw
    convert hneg using 1 <;> try ring
    linear_combination hreflect
  have hQU : H ^ 2 ∣ QU + C - D * U := dvd_trans hHsqUsq hQUexp
  have hlocal := even_reflected_second_order_algebra
    hH hresInt
    (by simpa [hL, hU] using heqLocal)
    (by simpa [hL] using hQL)
    (by simpa [hU] using hQU)
  simpa [H, X, A, C, D] using hlocal

/-- Equation-facing odd-row wrapper, with the same explicit quotient data as
the even theorem. -/
theorem odd_reflected_second_lift
    {k n d i h x m a : ℕ}
    (hkodd : Odd k)
    (hi : i ∈ Finset.Icc 1 k)
    (hh : 0 < h)
    (hlower : n + i = h * x)
    (hcenter : (n + i) + (n + d + (k + 1 - i)) = h * m)
    (hmx : m ≤ 5 * x)
    (hres : 5 * x - m = h * a)
    (heq : blockProduct k (n + d) = 4 * blockProduct k n) :
    (h : ℤ) ∣
      localSecondConstant k i * (a : ℤ) +
        20 * localSecondLinear k i * (x : ℤ) ^ 2 := by
  let H : ℤ := (h : ℤ)
  let L : ℤ := ((n + i : ℕ) : ℤ)
  let U : ℤ := ((n + d + (k + 1 - i) : ℕ) : ℤ)
  let X : ℤ := (x : ℤ)
  let M : ℤ := (m : ℤ)
  let A : ℤ := (a : ℤ)
  let C : ℤ := localSecondConstant k i
  let D : ℤ := localSecondLinear k i
  let QL : ℤ := localBlockCofactor k i (n : ℤ)
  let QU : ℤ := localBlockCofactor k (k + 1 - i) ((n + d : ℕ) : ℤ)
  have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
  have hik : i ≤ k := (Finset.mem_Icc.mp hi).2
  have hj : k + 1 - i ∈ Finset.Icc 1 k := by
    rw [Finset.mem_Icc]
    constructor <;> omega
  have hH : H ≠ 0 := by
    dsimp [H]
    exact_mod_cast (Nat.ne_of_gt hh)
  have hL : L = H * X := by
    dsimp [L, H, X]
    exact_mod_cast hlower
  have hsum : L + U = H * M := by
    dsimp [L, U, H, M]
    exact_mod_cast hcenter
  have hU : U = H * (M - X) := by
    rw [hL] at hsum
    linear_combination hsum
  have hresInt : 5 * X - M = H * A := by
    have hresCast : (((5 * x - m : ℕ) : ℤ)) = ((h * a : ℕ) : ℤ) := by
      exact_mod_cast hres
    rw [Nat.cast_sub hmx] at hresCast
    simpa [M, X, H, A] using hresCast
  have heqInt :
      intBlockProduct k ((n + d : ℕ) : ℤ) =
        4 * intBlockProduct k (n : ℤ) := by
    rw [intBlockProduct_natCast, intBlockProduct_natCast]
    exact_mod_cast heq
  have heqLocal : U * QU = 4 * L * QL := by
    rw [intBlockProduct_eq_factor_mul_localBlockCofactor
        ((n + d : ℕ) : ℤ) hj,
      intBlockProduct_eq_factor_mul_localBlockCofactor (n : ℤ) hi] at heqInt
    dsimp [U, L, QU, QL]
    push_cast at heqInt ⊢
    convert heqInt using 1 <;> ring
  have hHL : H ∣ L := ⟨X, hL⟩
  have hHU : H ∣ U := ⟨M - X, hU⟩
  have hHsqLsq : H ^ 2 ∣ L ^ 2 := by
    simpa [pow_two] using mul_dvd_mul hHL hHL
  have hHsqUsq : H ^ 2 ∣ U ^ 2 := by
    simpa [pow_two] using mul_dvd_mul hHU hHU
  have hQLexp : L ^ 2 ∣ QL - C - D * L := by
    have hraw := localOffsetCofactor_second_order k i L
    have hrel : localOffsetCofactor k i L = QL := by
      dsimp [L, QL]
      exact localOffsetCofactor_eq_localBlockCofactor
    simpa [hrel, C, D] using hraw
  have hQL : H ^ 2 ∣ QL - C - D * L := dvd_trans hHsqLsq hQLexp
  have hkevenPred : Even (k - 1) :=
    Nat.Odd.sub_odd hkodd (by norm_num)
  have hsign : (-1 : ℤ) ^ (k - 1) = 1 :=
    Even.neg_one_pow hkevenPred
  have hupperRel : localOffsetCofactor k (k + 1 - i) U = QU := by
    dsimp [U, QU]
    exact localOffsetCofactor_eq_localBlockCofactor
  have hreflect := localOffsetCofactor_reflected_agent hi U
  rw [hsign, one_mul, hupperRel] at hreflect
  have hQUexp : U ^ 2 ∣ QU - C + D * U := by
    have hraw := localOffsetCofactor_second_order k i (-U)
    convert hraw using 1 <;> try ring
    linear_combination hreflect
  have hQU : H ^ 2 ∣ QU - C + D * U := dvd_trans hHsqUsq hQUexp
  have hlocal := odd_reflected_second_order_algebra
    hH hresInt
    (by simpa [hL, hU] using heqLocal)
    (by simpa [hL] using hQL)
    (by simpa [hU] using hQU)
  simpa [H, X, A, C, D] using hlocal

/-- Equation-facing even third-order reflected lift. -/
theorem even_reflected_third_lift
    {k n d i h x m a : ℕ}
    (hkeven : Even k) (hi : i ∈ Finset.Icc 1 k) (hh : 0 < h)
    (hlower : n + i = h * x)
    (hcenter : (n + i) + (n + d + (k + 1 - i)) = h * m)
    (hres : m + 3 * x = h * a)
    (heq : blockProduct k (n + d) = 4 * blockProduct k n) :
    (h : ℤ) ^ 2 ∣
      localSecondConstant k i * (a : ℤ) -
        12 * localSecondLinear k i * (x : ℤ) ^ 2 +
        (h : ℤ) * (8 * localSecondLinear k i * (a : ℤ) * (x : ℤ) -
          60 * localThirdQuadratic k i * (x : ℤ) ^ 3) := by
  let H : ℤ := (h : ℤ)
  let L : ℤ := ((n + i : ℕ) : ℤ)
  let U : ℤ := ((n + d + (k + 1 - i) : ℕ) : ℤ)
  let X : ℤ := (x : ℤ)
  let M : ℤ := (m : ℤ)
  let A : ℤ := (a : ℤ)
  let C := localSecondConstant k i
  let D := localSecondLinear k i
  let E := localThirdQuadratic k i
  let QL : ℤ := localBlockCofactor k i (n : ℤ)
  let QU : ℤ := localBlockCofactor k (k + 1 - i) ((n + d : ℕ) : ℤ)
  have hj : k + 1 - i ∈ Finset.Icc 1 k := by
    rw [Finset.mem_Icc]
    have hi1 := (Finset.mem_Icc.mp hi).1
    have hik := (Finset.mem_Icc.mp hi).2
    constructor <;> omega
  have hH : H ≠ 0 := by dsimp [H]; exact_mod_cast (Nat.ne_of_gt hh)
  have hL : L = H * X := by dsimp [L, H, X]; exact_mod_cast hlower
  have hsum : L + U = H * M := by
    dsimp [L, U, H, M]
    exact_mod_cast hcenter
  have hU : U = H * (M - X) := by rw [hL] at hsum; linear_combination hsum
  have hresInt : M + 3 * X = H * A := by
    dsimp [M, X, H, A]
    exact_mod_cast hres
  have heqInt : intBlockProduct k ((n + d : ℕ) : ℤ) =
      4 * intBlockProduct k (n : ℤ) := by
    rw [intBlockProduct_natCast, intBlockProduct_natCast]
    exact_mod_cast heq
  have heqLocal : U * QU = 4 * L * QL := by
    rw [intBlockProduct_eq_factor_mul_localBlockCofactor
        ((n + d : ℕ) : ℤ) hj,
      intBlockProduct_eq_factor_mul_localBlockCofactor (n : ℤ) hi] at heqInt
    dsimp [U, L, QU, QL]
    push_cast at heqInt ⊢
    convert heqInt using 1 <;> ring
  have hHL : H ∣ L := ⟨X, hL⟩
  have hHU : H ∣ U := ⟨M - X, hU⟩
  have hHcubeLcube : H ^ 3 ∣ L ^ 3 := pow_dvd_pow_of_dvd hHL 3
  have hHcubeUcube : H ^ 3 ∣ U ^ 3 := pow_dvd_pow_of_dvd hHU 3
  have hQLexp : L ^ 3 ∣ QL - C - D * L - E * L ^ 2 := by
    have hraw := localOffsetCofactor_third_order k i L
    have hrel : localOffsetCofactor k i L = QL := by
      dsimp [L, QL]
      exact localOffsetCofactor_eq_localBlockCofactor
    simpa [hrel, C, D, E] using hraw
  have hQL : H ^ 3 ∣ QL - C - D * L - E * L ^ 2 :=
    dvd_trans hHcubeLcube hQLexp
  have hkoddPred : Odd (k - 1) := Nat.Even.sub_odd
    (by
      have hi1 := (Finset.mem_Icc.mp hi).1
      have hik := (Finset.mem_Icc.mp hi).2
      omega : 1 ≤ k) hkeven (by norm_num)
  have hsign : (-1 : ℤ) ^ (k - 1) = -1 := Odd.neg_one_pow hkoddPred
  have hupperRel : localOffsetCofactor k (k + 1 - i) U = QU := by
    dsimp [U, QU]
    exact localOffsetCofactor_eq_localBlockCofactor
  have hreflect := localOffsetCofactor_reflected_agent hi U
  rw [hsign, hupperRel] at hreflect
  have hQUexp : U ^ 3 ∣ QU + C - D * U + E * U ^ 2 := by
    have hraw := localOffsetCofactor_third_order k i (-U)
    have hneg := dvd_neg.mpr hraw
    have hneg' : U ^ 3 ∣
        -(localOffsetCofactor k i (-U) - localSecondConstant k i -
          localSecondLinear k i * (-U) - localThirdQuadratic k i * (-U) ^ 2) := by
      have hdiv : U ^ 3 ∣ (-U) ^ 3 := ⟨-1, by ring⟩
      exact dvd_trans hdiv hneg
    convert hneg' using 1 <;> try ring
    linear_combination hreflect
  have hQU : H ^ 3 ∣ QU + C - D * U + E * U ^ 2 :=
    dvd_trans hHcubeUcube hQUexp
  have hlocal := even_reflected_third_order_algebra hH hresInt
    (by simpa [hL, hU] using heqLocal)
    (by simpa [hL] using hQL)
    (by simpa [hU] using hQU)
  simpa [H, X, A, C, D, E] using hlocal

/-- Equation-facing odd third-order reflected lift. -/
theorem odd_reflected_third_lift
    {k n d i h x m a : ℕ}
    (hkodd : Odd k) (hi : i ∈ Finset.Icc 1 k) (hh : 0 < h)
    (hlower : n + i = h * x)
    (hcenter : (n + i) + (n + d + (k + 1 - i)) = h * m)
    (hmx : m ≤ 5 * x) (hres : 5 * x - m = h * a)
    (heq : blockProduct k (n + d) = 4 * blockProduct k n) :
    (h : ℤ) ^ 2 ∣
      localSecondConstant k i * (a : ℤ) +
        20 * localSecondLinear k i * (x : ℤ) ^ 2 -
        (h : ℤ) * (8 * localSecondLinear k i * (a : ℤ) * (x : ℤ) +
          60 * localThirdQuadratic k i * (x : ℤ) ^ 3) := by
  let H : ℤ := (h : ℤ)
  let L : ℤ := ((n + i : ℕ) : ℤ)
  let U : ℤ := ((n + d + (k + 1 - i) : ℕ) : ℤ)
  let X : ℤ := (x : ℤ)
  let M : ℤ := (m : ℤ)
  let A : ℤ := (a : ℤ)
  let C := localSecondConstant k i
  let D := localSecondLinear k i
  let E := localThirdQuadratic k i
  let QL : ℤ := localBlockCofactor k i (n : ℤ)
  let QU : ℤ := localBlockCofactor k (k + 1 - i) ((n + d : ℕ) : ℤ)
  have hj : k + 1 - i ∈ Finset.Icc 1 k := by
    rw [Finset.mem_Icc]
    have hi1 := (Finset.mem_Icc.mp hi).1
    have hik := (Finset.mem_Icc.mp hi).2
    constructor <;> omega
  have hH : H ≠ 0 := by dsimp [H]; exact_mod_cast (Nat.ne_of_gt hh)
  have hL : L = H * X := by dsimp [L, H, X]; exact_mod_cast hlower
  have hsum : L + U = H * M := by
    dsimp [L, U, H, M]
    exact_mod_cast hcenter
  have hU : U = H * (M - X) := by rw [hL] at hsum; linear_combination hsum
  have hresCast : (((5 * x - m : ℕ) : ℤ)) = ((h * a : ℕ) : ℤ) := by
    exact_mod_cast hres
  rw [Nat.cast_sub hmx] at hresCast
  have hresInt : 5 * X - M = H * A := by simpa [X, M, H, A] using hresCast
  have heqInt : intBlockProduct k ((n + d : ℕ) : ℤ) =
      4 * intBlockProduct k (n : ℤ) := by
    rw [intBlockProduct_natCast, intBlockProduct_natCast]
    exact_mod_cast heq
  have heqLocal : U * QU = 4 * L * QL := by
    rw [intBlockProduct_eq_factor_mul_localBlockCofactor
        ((n + d : ℕ) : ℤ) hj,
      intBlockProduct_eq_factor_mul_localBlockCofactor (n : ℤ) hi] at heqInt
    dsimp [U, L, QU, QL]
    push_cast at heqInt ⊢
    convert heqInt using 1 <;> ring
  have hHL : H ∣ L := ⟨X, hL⟩
  have hHU : H ∣ U := ⟨M - X, hU⟩
  have hHcubeLcube : H ^ 3 ∣ L ^ 3 := pow_dvd_pow_of_dvd hHL 3
  have hHcubeUcube : H ^ 3 ∣ U ^ 3 := pow_dvd_pow_of_dvd hHU 3
  have hQLexp : L ^ 3 ∣ QL - C - D * L - E * L ^ 2 := by
    have hraw := localOffsetCofactor_third_order k i L
    have hrel : localOffsetCofactor k i L = QL := by
      dsimp [L, QL]
      exact localOffsetCofactor_eq_localBlockCofactor
    simpa [hrel, C, D, E] using hraw
  have hQL : H ^ 3 ∣ QL - C - D * L - E * L ^ 2 :=
    dvd_trans hHcubeLcube hQLexp
  have hkevenPred : Even (k - 1) := Nat.Odd.sub_odd hkodd (by norm_num)
  have hsign : (-1 : ℤ) ^ (k - 1) = 1 := Even.neg_one_pow hkevenPred
  have hupperRel : localOffsetCofactor k (k + 1 - i) U = QU := by
    dsimp [U, QU]
    exact localOffsetCofactor_eq_localBlockCofactor
  have hreflect := localOffsetCofactor_reflected_agent hi U
  rw [hsign, one_mul, hupperRel] at hreflect
  have hQUexp : U ^ 3 ∣ QU - C + D * U - E * U ^ 2 := by
    have hraw := localOffsetCofactor_third_order k i (-U)
    have hraw' : U ^ 3 ∣
        localOffsetCofactor k i (-U) - localSecondConstant k i -
          localSecondLinear k i * (-U) - localThirdQuadratic k i * (-U) ^ 2 := by
      have hdiv : U ^ 3 ∣ (-U) ^ 3 := ⟨-1, by ring⟩
      exact dvd_trans hdiv hraw
    convert hraw' using 1 <;> try ring
    linear_combination hreflect
  have hQU : H ^ 3 ∣ QU - C + D * U - E * U ^ 2 :=
    dvd_trans hHcubeUcube hQUexp
  have hlocal := odd_reflected_third_order_algebra hH hresInt
    (by simpa [hL, hU] using heqLocal)
    (by simpa [hL] using hQL)
    (by simpa [hU] using hQU)
  simpa [H, X, A, C, D, E] using hlocal

#print axioms localOffsetCofactor_reflected_agent
#print axioms even_reflected_second_order_algebra
#print axioms odd_reflected_second_order_algebra
#print axioms even_reflected_third_order_algebra
#print axioms odd_reflected_third_order_algebra
#print axioms even_reflected_third_lift_cleaned
#print axioms odd_reflected_third_lift_cleaned
#print axioms even_reflected_third_three_owner_component
#print axioms odd_reflected_third_three_owner_component
#print axioms even_reflected_third_three_owner_composition
#print axioms odd_reflected_third_three_owner_composition
#print axioms even_reflected_second_lift_cleaned
#print axioms odd_reflected_second_lift_cleaned
#print axioms even_reflected_three_owner_component
#print axioms odd_reflected_three_owner_component
#print axioms even_reflected_three_owner_composition
#print axioms odd_reflected_three_owner_composition
#print axioms even_reflected_three_owner_from_raw_second_lifts
#print axioms odd_reflected_three_owner_from_raw_second_lifts
#print axioms reflected_three_owner_cofactor_product_growth
#print axioms even_reflected_second_lift
#print axioms odd_reflected_second_lift
#print axioms even_reflected_third_lift
#print axioms odd_reflected_third_lift

end Erdos686Variant
end Erdos686
