/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import ErdosProblems.Erdos686.Core.ReflectedSecondLift

/-!
# Erdős 686: reflected three-owner third composition

This module records the exact next-order composition in the balanced
three-owner reflection-center branch.  The raw reflected lift at one owner
has modulus square.  Multiplying by the two opposite residual cofactors and
using both step-three (even row) or step-five (odd row) residual differences
eliminates the local quotient.  The result is affine in the two common
variables `t = a*b*c` and `S = g*P*Q*R`, so three owners support the same
rank-two determinant analysis as the odd-tail three-bucket package.

The coprimality assumptions with `3` and `5` are automatic in the intended
large-prime-support branch (`P` is supported on primes above `k >= 16`).
-/

namespace Erdos686
namespace Erdos686Variant

private theorem product_congr_sq_of_two_differences
    {P U V A B : ℤ}
    (hU : P ^ 2 ∣ U + A) (hV : P ^ 2 ∣ V + B) :
    P ^ 2 ∣ U * V - A * B := by
  have hleft : P ^ 2 ∣ (U + A) * V := dvd_mul_of_dvd_left hU V
  have hright : P ^ 2 ∣ A * (V + B) := dvd_mul_of_dvd_right hV A
  convert dvd_sub hleft hright using 1 <;> ring

private theorem dvd_of_coprime_square_mul
    {P c W : ℤ} (hcop : IsCoprime P c) (hdiv : P ∣ c ^ 2 * W) :
    P ∣ W := by
  have hcopSq : IsCoprime P (c ^ 2) := hcop.pow_right
  exact hcopSq.dvd_of_dvd_mul_left hdiv

/-- Even-row third composition at one reflected owner.

`hraw` is the raw next-order reflected lift after the second quotient has
been named.  The conclusion keeps every numerical coefficient and the
cleaning loss `g` explicit; no division by `3` occurs without `hcop3`. -/
theorem even_reflected_third_composition_component
    {P Q R a b c x g C D E S deltaQ deltaR : ℤ}
    (hcop3 : IsCoprime P 3)
    (hraw : P ^ 2 ∣
      C * a - 12 * D * x ^ 2 +
        P * (8 * D * a * x - 60 * E * x ^ 3))
    (hres : P * a = g * Q * R + 3 * x)
    (hdiffQ : a * P ^ 2 - b * Q ^ 2 = 3 * deltaQ)
    (hdiffR : a * P ^ 2 - c * R ^ 2 = 3 * deltaR)
    (hcenter : S = g * P * Q * R) :
    P ^ 2 ∣
      9 * C * (a * b * c) -
        108 * D * g ^ 2 * deltaQ * deltaR +
        180 * E * g ^ 2 * deltaQ * deltaR * S := by
  have hQ : P ^ 2 ∣ b * Q ^ 2 + 3 * deltaQ := by
    refine ⟨a, ?_⟩
    linear_combination -hdiffQ
  have hR : P ^ 2 ∣ c * R ^ 2 + 3 * deltaR := by
    refine ⟨a, ?_⟩
    linear_combination -hdiffR
  have hprod : P ^ 2 ∣
      (b * Q ^ 2) * (c * R ^ 2) -
        (3 * deltaQ) * (3 * deltaR) :=
    product_congr_sq_of_two_differences hQ hR
  have hprodScaled := dvd_mul_of_dvd_right hprod (g ^ 2)
  have htrivial : P ^ 2 ∣ P ^ 2 * (b * c * a ^ 2) :=
    dvd_mul_right (P ^ 2) (b * c * a ^ 2)
  have hsq : P ^ 2 ∣
      9 * b * c * x ^ 2 - 6 * P * (a * b * c) * x -
        9 * g ^ 2 * deltaQ * deltaR := by
    have hdiff := dvd_sub hprodScaled htrivial
    have hgqr : g * Q * R = P * a - 3 * x := by
      linarith
    have hid :
        g ^ 2 * (b * Q ^ 2 * (c * R ^ 2) -
            3 * deltaQ * (3 * deltaR)) - P ^ 2 * (b * c * a ^ 2) =
          9 * b * c * x ^ 2 - 6 * P * (a * b * c) * x -
            9 * g ^ 2 * deltaQ * deltaR := by
      calc
        g ^ 2 * (b * Q ^ 2 * (c * R ^ 2) -
              3 * deltaQ * (3 * deltaR)) - P ^ 2 * (b * c * a ^ 2) =
            b * c * (g * Q * R) ^ 2 - 9 * g ^ 2 * deltaQ * deltaR -
              P ^ 2 * (b * c * a ^ 2) := by ring
        _ = b * c * (P * a - 3 * x) ^ 2 -
              9 * g ^ 2 * deltaQ * deltaR -
              P ^ 2 * (b * c * a ^ 2) := by rw [hgqr]
        _ = 9 * b * c * x ^ 2 - 6 * P * (a * b * c) * x -
              9 * g ^ 2 * deltaQ * deltaR := by ring
    rw [← hid]
    exact hdiff
  have hsqMod : P ∣
      9 * (b * c * x ^ 2 - g ^ 2 * deltaQ * deltaR) := by
    have hrawMod := dvd_trans (dvd_pow_self P (by norm_num)) hsq
    have hmiddle : P ∣ -6 * P * (a * b * c) * x := by
      refine ⟨-6 * (a * b * c) * x, ?_⟩
      ring
    have hremove := dvd_sub hrawMod hmiddle
    convert hremove using 1 <;> ring
  have hbc : P ∣ b * c * x ^ 2 - g ^ 2 * deltaQ * deltaR :=
    dvd_of_coprime_square_mul hcop3 (by simpa [pow_two] using hsqMod)
  have hxpart : P ∣
      3 * b * c * x ^ 3 - 3 * g ^ 2 * deltaQ * deltaR * x := by
    convert dvd_mul_of_dvd_right hbc (3 * x) using 1 <;> ring
  have hresMod : P ∣ g * Q * R + 3 * x := ⟨a, hres.symm⟩
  have hcenterPart : P ∣
      g ^ 3 * deltaQ * deltaR * Q * R +
        3 * g ^ 2 * deltaQ * deltaR * x := by
    convert dvd_mul_of_dvd_right hresMod (g ^ 2 * deltaQ * deltaR) using 1 <;>
      ring
  have hcubic : P ∣
      3 * b * c * x ^ 3 + g ^ 3 * deltaQ * deltaR * Q * R := by
    convert dvd_add hxpart hcenterPart using 1 <;> ring
  have hcubicSq : P ^ 2 ∣
      P * (180 * E) *
        (3 * b * c * x ^ 3 + g ^ 3 * deltaQ * deltaR * Q * R) := by
    rcases hcubic with ⟨q, hq⟩
    refine ⟨180 * E * q, ?_⟩
    rw [hq]
    ring
  have hrawScaled := dvd_mul_of_dvd_right hraw (9 * b * c)
  have hsqScaled := dvd_mul_of_dvd_right hsq (12 * D)
  have hsum := dvd_add (dvd_add hrawScaled hsqScaled) hcubicSq
  convert hsum using 1 <;> rw [hcenter] <;> ring

/-- Odd-row analogue of `even_reflected_third_composition_component`. -/
theorem odd_reflected_third_composition_component
    {P Q R a b c x g C D E S deltaQ deltaR : ℤ}
    (hcop5 : IsCoprime P 5)
    (hraw : P ^ 2 ∣
      C * a + 20 * D * x ^ 2 +
        P * (-8 * D * a * x - 60 * E * x ^ 3))
    (hres : P * a = 5 * x - g * Q * R)
    (hdiffQ : a * P ^ 2 - b * Q ^ 2 = 5 * deltaQ)
    (hdiffR : a * P ^ 2 - c * R ^ 2 = 5 * deltaR)
    (hcenter : S = g * P * Q * R) :
    P ^ 2 ∣
      5 * C * (a * b * c) +
        100 * D * g ^ 2 * deltaQ * deltaR -
        60 * E * g ^ 2 * deltaQ * deltaR * S := by
  have hQ : P ^ 2 ∣ b * Q ^ 2 + 5 * deltaQ := by
    refine ⟨a, ?_⟩
    linear_combination -hdiffQ
  have hR : P ^ 2 ∣ c * R ^ 2 + 5 * deltaR := by
    refine ⟨a, ?_⟩
    linear_combination -hdiffR
  have hprod : P ^ 2 ∣
      (b * Q ^ 2) * (c * R ^ 2) -
        (5 * deltaQ) * (5 * deltaR) :=
    product_congr_sq_of_two_differences hQ hR
  have hprodScaled := dvd_mul_of_dvd_right hprod (g ^ 2)
  have htrivial : P ^ 2 ∣ P ^ 2 * (b * c * a ^ 2) :=
    dvd_mul_right (P ^ 2) (b * c * a ^ 2)
  have hsq : P ^ 2 ∣
      25 * b * c * x ^ 2 - 10 * P * (a * b * c) * x -
        25 * g ^ 2 * deltaQ * deltaR := by
    have hdiff := dvd_sub hprodScaled htrivial
    have hgqr : g * Q * R = 5 * x - P * a := by
      linarith
    have hid :
        g ^ 2 * (b * Q ^ 2 * (c * R ^ 2) -
            5 * deltaQ * (5 * deltaR)) - P ^ 2 * (b * c * a ^ 2) =
          25 * b * c * x ^ 2 - 10 * P * (a * b * c) * x -
            25 * g ^ 2 * deltaQ * deltaR := by
      calc
        g ^ 2 * (b * Q ^ 2 * (c * R ^ 2) -
              5 * deltaQ * (5 * deltaR)) - P ^ 2 * (b * c * a ^ 2) =
            b * c * (g * Q * R) ^ 2 - 25 * g ^ 2 * deltaQ * deltaR -
              P ^ 2 * (b * c * a ^ 2) := by ring
        _ = b * c * (5 * x - P * a) ^ 2 -
              25 * g ^ 2 * deltaQ * deltaR -
              P ^ 2 * (b * c * a ^ 2) := by rw [hgqr]
        _ = 25 * b * c * x ^ 2 - 10 * P * (a * b * c) * x -
              25 * g ^ 2 * deltaQ * deltaR := by ring
    rw [← hid]
    exact hdiff
  have hsqMod : P ∣
      25 * (b * c * x ^ 2 - g ^ 2 * deltaQ * deltaR) := by
    have hrawMod := dvd_trans (dvd_pow_self P (by norm_num)) hsq
    have hmiddle : P ∣ -10 * P * (a * b * c) * x := by
      refine ⟨-10 * (a * b * c) * x, ?_⟩
      ring
    have hremove := dvd_sub hrawMod hmiddle
    convert hremove using 1 <;> ring
  have hbc : P ∣ b * c * x ^ 2 - g ^ 2 * deltaQ * deltaR :=
    dvd_of_coprime_square_mul hcop5 (by simpa [pow_two] using hsqMod)
  have hxpart : P ∣
      5 * b * c * x ^ 3 - 5 * g ^ 2 * deltaQ * deltaR * x := by
    convert dvd_mul_of_dvd_right hbc (5 * x) using 1 <;> ring
  have hresMod : P ∣ 5 * x - g * Q * R := ⟨a, hres.symm⟩
  have hcenterPart : P ∣
      5 * g ^ 2 * deltaQ * deltaR * x -
        g ^ 3 * deltaQ * deltaR * Q * R := by
    convert dvd_mul_of_dvd_right hresMod (g ^ 2 * deltaQ * deltaR) using 1 <;>
      ring
  have hcubic : P ∣
      5 * b * c * x ^ 3 - g ^ 3 * deltaQ * deltaR * Q * R := by
    convert dvd_add hxpart hcenterPart using 1 <;> ring
  have hcubicSq : P ^ 2 ∣
      P * (60 * E) *
        (5 * b * c * x ^ 3 - g ^ 3 * deltaQ * deltaR * Q * R) := by
    rcases hcubic with ⟨q, hq⟩
    refine ⟨60 * E * q, ?_⟩
    rw [hq]
    ring
  have hrawScaled := dvd_mul_of_dvd_right hraw (5 * b * c)
  have hsqScaled := dvd_mul_of_dvd_right hsq (-4 * D)
  have hsum := dvd_add (dvd_add hrawScaled hsqScaled) hcubicSq
  convert hsum using 1 <;> rw [hcenter] <;> ring

/-- First cofactor in the cross product of three affine coefficient rows. -/
def reflectedThirdWeightOne (A₂ B₂ A₃ B₃ : ℤ) : ℤ :=
  A₂ * B₃ - A₃ * B₂

def reflectedThirdWeightTwo (A₁ B₁ A₃ B₃ : ℤ) : ℤ :=
  A₃ * B₁ - A₁ * B₃

def reflectedThirdWeightThree (A₁ B₁ A₂ B₂ : ℤ) : ℤ :=
  A₁ * B₂ - A₂ * B₁

/-- Cross-product identity for three affine reflected third compositions.
It eliminates both common variables `t` and `S`, retaining the exact finite
correction. -/
theorem reflected_third_composition_lattice_identity
    (A₁ A₂ A₃ B₁ B₂ B₃ G₁ G₂ G₃ t S : ℤ) :
    reflectedThirdWeightOne A₂ B₂ A₃ B₃ *
          (A₁ * t + B₁ * S + G₁) +
        reflectedThirdWeightTwo A₁ B₁ A₃ B₃ *
          (A₂ * t + B₂ * S + G₂) +
        reflectedThirdWeightThree A₁ B₁ A₂ B₂ *
          (A₃ * t + B₃ * S + G₃) =
      reflectedThirdWeightOne A₂ B₂ A₃ B₃ * G₁ +
        reflectedThirdWeightTwo A₁ B₁ A₃ B₃ * G₂ +
        reflectedThirdWeightThree A₁ B₁ A₂ B₂ * G₃ := by
  simp [reflectedThirdWeightOne, reflectedThirdWeightTwo,
    reflectedThirdWeightThree]
  ring

#print axioms even_reflected_third_composition_component
#print axioms odd_reflected_third_composition_component
#print axioms reflected_third_composition_lattice_identity

end Erdos686Variant
end Erdos686
