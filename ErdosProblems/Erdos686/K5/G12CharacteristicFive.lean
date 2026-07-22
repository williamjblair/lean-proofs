/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import ErdosProblems.Erdos686.K5.G12PrimitiveQuotient
import ErdosProblems.Erdos686.K5.IntegralLift

/-!
# Erdős 686, k=5: the exact characteristic-five branch

The exceptional quotient branch with `5 | Q` and `5 | K` is not eliminated
by the original equation.  After cancelling the unique common owner `Q`, the
centered quintic equation modulo `25` does show that `K` has exactly one
factor of five: `25` cannot divide it.
-/

namespace Erdos686
namespace Erdos686Variant

/-- In the characteristic-five exceptional branch, the complement quotient
`K` is divisible by `5` but not by `25`.  Thus its exact 5-adic valuation is
one. -/
theorem k5_G12_characteristic_five_K_not_dvd_twenty_five
    {n d t : ℕ}
    (data : CanonicalOwnerData 5 n d t)
    (hfour : 4 ∣ n + d + t)
    (heq : blockProduct 5 (n + d) = 4 * blockProduct 5 n)
    (hprofile : K5G12ZeroResidualProfile data) :
    let P := canonicalOwnerCell data 4 1
    let Q := canonicalOwnerCell data 2 3
    let R := (n + 4) / P
    let C := (n + d + 1) / P
    let K := (R + C) / (P * Q)
    5 ∣ Q → 5 ∣ K → ¬25 ∣ K := by
  dsimp only
  let P := canonicalOwnerCell data 4 1
  let Q := canonicalOwnerCell data 2 3
  let R := (n + 4) / P
  let C := (n + d + 1) / P
  let K := (R + C) / (P * Q)
  let S := (n + 2) / Q
  let D := (n + d + 3) / Q
  intro h5Q _h5K h25K
  have h5Qsaved : 5 ∣ Q := h5Q
  have hprimitive :=
    k5_G12_exceptional_complement_quotient_gcd_Q_dvd_five
      data hfour heq hprofile
  have hrowQ : n + 2 = Q * S := hprimitive.2.1
  have hcolumnQ : n + d + 3 = Q * D := hprimitive.2.2.1
  have hSD : S + D = P ^ 2 * K := hprimitive.2.2.2.1
  have hcopQS : Nat.Coprime Q S := hprimitive.2.2.2.2.2.1
  have hQpos : 0 < Q := by
    dsimp [Q]
    exact canonicalOwnerCell_pos data
  have hcenter : K5CenteredEq (n + d + 3) (n + 3) :=
    k5_centered_of_eq heq
  have hpoly := k5_centered_eq_iff_integer_polynomial.mp hcenter
  have hvZ : ((n + d + 3 : ℕ) : ℤ) = (Q : ℤ) * (D : ℤ) := by
    exact_mod_cast hcolumnQ
  have huNat : n + 3 = Q * S + 1 := by omega
  have huZ : ((n + 3 : ℕ) : ℤ) = (Q : ℤ) * (S : ℤ) + 1 := by
    exact_mod_cast huNat
  rw [hvZ, huZ] at hpoly
  have hcanceled :
      (D : ℤ) * (((Q : ℤ) * D) ^ 2 - 1) *
          (((Q : ℤ) * D) ^ 2 - 4) =
        4 * (S : ℤ) * ((Q : ℤ) * S + 1) *
          ((Q : ℤ) * S + 2) * ((Q : ℤ) * S - 1) *
          ((Q : ℤ) * S + 3) := by
    apply mul_left_cancel₀ (show (Q : ℤ) ≠ 0 by exact_mod_cast hQpos.ne')
    calc
      (Q : ℤ) *
          ((D : ℤ) * (((Q : ℤ) * D) ^ 2 - 1) *
            (((Q : ℤ) * D) ^ 2 - 4)) =
          k5PolynomialZ ((Q : ℤ) * D) := by
            unfold k5PolynomialZ
            ring
      _ = 4 * k5PolynomialZ ((Q : ℤ) * S + 1) := hpoly
      _ = (Q : ℤ) *
          (4 * (S : ℤ) * ((Q : ℤ) * S + 1) *
            ((Q : ℤ) * S + 2) * ((Q : ℤ) * S - 1) *
            ((Q : ℤ) * S + 3)) := by
              unfold k5PolynomialZ
              ring
  obtain ⟨q, hQraw⟩ := h5Q
  have hQ : Q = 5 * q := by simpa [Q] using hQraw
  have hcanceled25 := congrArg (fun z : ℤ => (z : ZMod 25)) hcanceled
  have hzmod (a : ℕ) (ha : 25 ∣ a) : (a : ZMod 25) = 0 :=
    (ZMod.natCast_eq_zero_iff a 25).2 ha
  have h24 : (24 : ZMod 25) = -1 := by
    apply eq_neg_of_add_eq_zero_left
    norm_num only [← Nat.cast_add]
    exact hzmod 25 (dvd_refl 25)
  have h100 : (100 : ZMod 25) = 0 := hzmod 100 (by norm_num)
  have h125 : (125 : ZMod 25) = 0 := hzmod 125 (by norm_num)
  have h500 : (500 : ZMod 25) = 0 := hzmod 500 (by norm_num)
  have h625 : (625 : ZMod 25) = 0 := hzmod 625 (by norm_num)
  have h2500 : (2500 : ZMod 25) = 0 := hzmod 2500 (by norm_num)
  have hmod25 : (4 : ZMod 25) * (D : ZMod 25) = (S : ZMod 25) := by
    rw [hQ] at hcanceled25
    push_cast at hcanceled25
    ring_nf at hcanceled25 ⊢
    simp only [h100, h125, h500, h625, h2500, h24, mul_zero,
      add_zero, sub_zero, neg_zero] at hcanceled25
    simpa using hcanceled25
  obtain ⟨k, hKraw⟩ := h25K
  have hK : K = 25 * k := by simpa [K] using hKraw
  have hsum25 : (S : ZMod 25) + (D : ZMod 25) = 0 := by
    have hcast := congrArg (fun z : ℕ => (z : ZMod 25)) hSD
    rw [hK] at hcast
    push_cast at hcast
    ring_nf at hcast ⊢
    exact hcast
  have hfiveSzero : ((5 * S : ℕ) : ZMod 25) = 0 := by
    push_cast
    linear_combination 4 * hsum25 - hmod25
  have h25fiveS : 25 ∣ 5 * S :=
    (ZMod.natCast_eq_zero_iff (5 * S) 25).mp hfiveSzero
  have h5S : 5 ∣ S := by
    obtain ⟨w, hw⟩ := h25fiveS
    have hmul : 5 * S = 5 * (5 * w) := by
      calc
        5 * S = 25 * w := hw
        _ = 5 * (5 * w) := by ring
    exact ⟨w, Nat.mul_left_cancel (by norm_num : 0 < 5) hmul⟩
  have hfiveGcd : 5 ∣ Nat.gcd Q S := Nat.dvd_gcd h5Qsaved h5S
  rw [hcopQS.gcd_eq_one] at hfiveGcd
  norm_num at hfiveGcd

/-- The exceptional alternative is exact: its common `Q`--`K` part is five,
and `K` has no second factor of five. -/
theorem k5_G12_characteristic_five_exact_gcd_and_valuation
    {n d t : ℕ}
    (data : CanonicalOwnerData 5 n d t)
    (hfour : 4 ∣ n + d + t)
    (heq : blockProduct 5 (n + d) = 4 * blockProduct 5 n)
    (hprofile : K5G12ZeroResidualProfile data) :
    let P := canonicalOwnerCell data 4 1
    let Q := canonicalOwnerCell data 2 3
    let R := (n + 4) / P
    let C := (n + d + 1) / P
    let K := (R + C) / (P * Q)
    5 ∣ Q → 5 ∣ K → Nat.gcd Q K = 5 ∧ ¬25 ∣ K := by
  dsimp only
  let P := canonicalOwnerCell data 4 1
  let Q := canonicalOwnerCell data 2 3
  let R := (n + 4) / P
  let C := (n + d + 1) / P
  let K := (R + C) / (P * Q)
  intro h5Q h5K
  have hprimitive :=
    k5_G12_exceptional_complement_quotient_gcd_Q_dvd_five
      data hfour heq hprofile
  have hgcdDvd : Nat.gcd Q K ∣ 5 := hprimitive.2.2.2.2.2.2.1
  have hfiveDvdGcd : 5 ∣ Nat.gcd Q K := Nat.dvd_gcd h5Q h5K
  have hgcd : Nat.gcd Q K = 5 := Nat.dvd_antisymm hgcdDvd hfiveDvdGcd
  have hnot25 :=
    k5_G12_characteristic_five_K_not_dvd_twenty_five
      data hfour heq hprofile h5Q h5K
  exact ⟨hgcd, hnot25⟩

#print axioms k5_G12_characteristic_five_K_not_dvd_twenty_five
#print axioms k5_G12_characteristic_five_exact_gcd_and_valuation

end Erdos686Variant
end Erdos686
