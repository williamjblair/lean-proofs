/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import ErdosProblems.Erdos686ReflectedAlignmentSquareLift
import Mathlib.Data.Nat.Choose.Bounds

/-!
# Erdős 686: normalized matching arithmetic

This module banks the cancellation step needed to pass from a factorial
owner-square congruence to its reduced normalized form.  The cancellation is
made explicit: the owner modulus must have only prime support above the block
length, while the removed prefactor divides `(k-1)!`.
-/

namespace Erdos686
namespace Erdos686Variant

/-- Row-binomial coefficient `C_h = binom(k-1,h-1)`. -/
def matchingBinomial (k h : ℕ) : ℕ :=
  (k - 1).choose (h - 1)

/-- Reduced numerator `a_ij = C_i / gcd(C_i,C_j)`. -/
def reducedMatchingLeft (k i j : ℕ) : ℕ :=
  matchingBinomial k i /
    Nat.gcd (matchingBinomial k i) (matchingBinomial k j)

/-- Reduced denominator `b_ij = C_j / gcd(C_i,C_j)`. -/
def reducedMatchingRight (k i j : ℕ) : ℕ :=
  matchingBinomial k j /
    Nat.gcd (matchingBinomial k i) (matchingBinomial k j)

/-- Factorial-free normalized linear form at an owner cell. -/
def normalizedMatchingForm
    (a b sign delta x : ℤ) : ℤ :=
  b * delta - (4 * sign * a - b) * x

/-- The corresponding factorial-weighted form after writing the two local
coefficients as `q*b` and `q*a`. -/
def factorialMatchingForm
    (q a b sign delta x : ℤ) : ℤ :=
  (q * b) * delta - (4 * sign * (q * a) - q * b) * x

/-- Exact algebraic normalization identity. -/
theorem factorialMatchingForm_eq_prefactor_mul_normalized
    (q a b sign delta x : ℤ) :
    factorialMatchingForm q a b sign delta x =
      q * normalizedMatchingForm a b sign delta x := by
  simp only [factorialMatchingForm, normalizedMatchingForm]
  ring

/-- Equivalent upper-term presentation of the normalized form. -/
theorem normalizedMatchingForm_eq_upper_form
    (a b sign delta x : ℤ) :
    normalizedMatchingForm a b sign delta x =
      b * (x + delta) - 4 * sign * a * x := by
  simp only [normalizedMatchingForm]
  ring

/-- A natural number supported only on primes above `k` is coprime to
`(k-1)!`. -/
theorem largePrimeSupport_coprime_factorial
    {P k : ℕ}
    (hsupport : ∀ p, p.Prime → p ∣ P → k < p) :
    P.Coprime (k - 1).factorial := by
  by_contra hnot
  obtain ⟨p, hp, hpP, hpFact⟩ :=
    Nat.Prime.not_coprime_iff_dvd.mp hnot
  have hple : p ≤ k - 1 := hp.dvd_factorial.mp hpFact
  have hklt := hsupport p hp hpP
  omega

/-- Consequently the composite owner square is coprime, over the integers,
to every prefactor dividing `(k-1)!`. -/
theorem largePrimeSupport_square_isCoprime_of_dvd_factorial
    {P q k : ℕ}
    (hsupport : ∀ p, p.Prime → p ∣ P → k < p)
    (hq : q ∣ (k - 1).factorial) :
    IsCoprime ((P : ℤ) ^ 2) (q : ℤ) := by
  have hPq : P.Coprime q :=
    (largePrimeSupport_coprime_factorial hsupport).coprime_dvd_right hq
  exact (hPq.pow_left 2).isCoprime

/-- Cancellation modulo a possibly composite square, with the unit
hypothesis stated explicitly. -/
theorem owner_square_normalized_iff_of_isCoprime
    {P q a b sign delta x : ℤ}
    (hcop : IsCoprime (P ^ 2) q) :
    P ^ 2 ∣ factorialMatchingForm q a b sign delta x ↔
      P ^ 2 ∣ normalizedMatchingForm a b sign delta x := by
  rw [factorialMatchingForm_eq_prefactor_mul_normalized]
  constructor
  · exact hcop.dvd_of_dvd_mul_left
  · exact fun h => dvd_mul_of_dvd_right h q

/-- High-prime owner specialization of the normalized square equivalence.
This is the precise composite-modulus repair required by the imported
normalized-matching argument. -/
theorem owner_square_normalized_iff_of_largePrimeSupport
    {P q k : ℕ} {a b sign delta x : ℤ}
    (hsupport : ∀ p, p.Prime → p ∣ P → k < p)
    (hq : q ∣ (k - 1).factorial) :
    ((P : ℤ) ^ 2 ∣
        factorialMatchingForm (q : ℤ) a b sign delta x) ↔
      ((P : ℤ) ^ 2 ∣ normalizedMatchingForm a b sign delta x) := by
  exact owner_square_normalized_iff_of_isCoprime
    (largePrimeSupport_square_isCoprime_of_dvd_factorial hsupport hq)

/-- Exact identity `C_h F_h = (k-1)!` between the row binomial and the
unsigned local derivative coefficient. -/
theorem matchingBinomial_mul_localCoefficientNat
    {k h : ℕ} (hh : h ∈ Finset.Icc 1 k) :
    matchingBinomial k h * localBlockCoefficientNat k h =
      (k - 1).factorial := by
  have hh1 : 1 ≤ h := (Finset.mem_Icc.mp hh).1
  have hhk : h ≤ k := (Finset.mem_Icc.mp hh).2
  have hle : h - 1 ≤ k - 1 := by omega
  have hsub : (k - 1) - (h - 1) = k - h := by omega
  simpa [matchingBinomial, localBlockCoefficientNat, hsub, mul_assoc] using
    (Nat.choose_mul_factorial_mul_factorial hle)

/-- The two local factorial coefficients have the common prefactor required
by normalization. The prefactor divides `(k-1)!`, and the remaining factors
are exactly the two reduced row-binomial ratios. -/
theorem exists_matchingCommonPrefactor
    {k i j : ℕ}
    (hi : i ∈ Finset.Icc 1 k)
    (hj : j ∈ Finset.Icc 1 k) :
    ∃ q : ℕ,
      q ∣ (k - 1).factorial ∧
      localBlockCoefficientNat k i = q * reducedMatchingRight k i j ∧
      localBlockCoefficientNat k j = q * reducedMatchingLeft k i j := by
  let Ci := matchingBinomial k i
  let Cj := matchingBinomial k j
  let Fi := localBlockCoefficientNat k i
  let Fj := localBlockCoefficientNat k j
  let g := Nat.gcd Ci Cj
  let a := Ci / g
  let b := Cj / g
  have hCiPos : 0 < Ci := by
    dsimp [Ci, matchingBinomial]
    exact Nat.choose_pos (by
      have hi1 := (Finset.mem_Icc.mp hi).1
      have hik := (Finset.mem_Icc.mp hi).2
      omega)
  have hCjPos : 0 < Cj := by
    dsimp [Cj, matchingBinomial]
    exact Nat.choose_pos (by
      have hj1 := (Finset.mem_Icc.mp hj).1
      have hjk := (Finset.mem_Icc.mp hj).2
      omega)
  have hgPos : 0 < g := Nat.gcd_pos_of_pos_left Cj hCiPos
  have haPos : 0 < a := Nat.div_pos
    (Nat.le_of_dvd hCiPos (Nat.gcd_dvd_left Ci Cj)) hgPos
  have hbPos : 0 < b := Nat.div_pos
    (Nat.le_of_dvd hCjPos (Nat.gcd_dvd_right Ci Cj)) hgPos
  have hcop : a.Coprime b := Nat.coprime_div_gcd_div_gcd hgPos
  have hCi : g * a = Ci := Nat.mul_div_cancel' (Nat.gcd_dvd_left Ci Cj)
  have hCj : g * b = Cj := Nat.mul_div_cancel' (Nat.gcd_dvd_right Ci Cj)
  have hLi : Ci * Fi = (k - 1).factorial :=
    matchingBinomial_mul_localCoefficientNat hi
  have hLj : Cj * Fj = (k - 1).factorial :=
    matchingBinomial_mul_localCoefficientNat hj
  have hab : a * Fi = b * Fj := by
    apply Nat.mul_left_cancel hgPos
    calc
      g * (a * Fi) = (g * a) * Fi := by ring
      _ = Ci * Fi := by rw [hCi]
      _ = (k - 1).factorial := hLi
      _ = Cj * Fj := hLj.symm
      _ = (g * b) * Fj := by rw [hCj]
      _ = g * (b * Fj) := by ring
  have hbFi : b ∣ Fi := by
    apply hcop.symm.dvd_of_dvd_mul_left
    rw [hab]
    exact dvd_mul_right b Fj
  let q := Fi / b
  have hqFi : q * b = Fi := by
    dsimp [q]
    rw [Nat.mul_comm]
    exact Nat.mul_div_cancel' hbFi
  have hqFj : q * a = Fj := by
    apply Nat.mul_left_cancel hbPos
    calc
      b * (q * a) = a * (q * b) := by ring
      _ = a * Fi := by rw [hqFi]
      _ = b * Fj := hab
  have hqDvdFi : q ∣ Fi := ⟨b, hqFi.symm⟩
  have hFiDvdL : Fi ∣ (k - 1).factorial := by
    rw [← hLi]
    exact dvd_mul_left Fi Ci
  refine ⟨q, dvd_trans hqDvdFi hFiDvdL, ?_, ?_⟩
  · simpa [Fi, b, reducedMatchingRight, Ci, Cj, g] using hqFi.symm
  · simpa [Fj, a, reducedMatchingLeft, Ci, Cj, g] using hqFj.symm

private theorem neg_one_pow_add_eq_pred_mul_pred
    {i j : ℕ} (hi : 1 ≤ i) (hj : 1 ≤ j) :
    (-1 : ℤ) ^ (i + j) =
      (-1 : ℤ) ^ (i - 1) * (-1 : ℤ) ^ (j - 1) := by
  have hexp : i + j = (i - 1) + (j - 1) + 2 := by omega
  rw [hexp, pow_add, pow_add]
  norm_num

/-- Exact binomial-specialized normalized owner-square congruence. This
closes the normalization audit for a possibly composite high-prime owner
modulus, starting from the banked factorial square lift. -/
theorem matched_owner_normalized_square_dvd
    {k n d i j P : ℕ}
    (hd : k ≤ d)
    (hi : i ∈ Finset.Icc 1 k)
    (hj : j ∈ Finset.Icc 1 k)
    (hsupport : ∀ p, p.Prime → p ∣ P → k < p)
    (hlower : P ∣ n + j)
    (hupper : P ∣ n + d + i)
    (heq : blockProduct k (n + d) = 4 * blockProduct k n) :
    ((P : ℤ) ^ 2) ∣
      normalizedMatchingForm
        (reducedMatchingLeft k i j : ℤ)
        (reducedMatchingRight k i j : ℤ)
        ((-1 : ℤ) ^ (i + j))
        ((d + i - j : ℕ) : ℤ)
        ((n + j : ℕ) : ℤ) := by
  obtain ⟨q, hq, hFi, hFj⟩ :=
    exists_matchingCommonPrefactor hi hj
  have hraw := matched_owner_local_coefficients_dvd_sq
    hj hi hlower hupper heq
  rw [localBlockCoefficient_eq_sign_mul_nat hi,
    localBlockCoefficient_eq_sign_mul_nat hj] at hraw
  have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
  have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
  have hsign := neg_one_pow_add_eq_pred_mul_pred hi1 hj1
  have hweighted :
      ((P : ℤ) ^ 2) ∣
        (localBlockCoefficientNat k i : ℤ) *
            ((n + d + i : ℕ) : ℤ) -
          4 * ((-1 : ℤ) ^ (i + j)) *
            (localBlockCoefficientNat k j : ℤ) *
              ((n + j : ℕ) : ℤ) := by
    rcases neg_one_pow_eq_or ℤ (i - 1) with hisign | hisign
    · simpa [hisign, hsign, mul_assoc, mul_comm, mul_left_comm] using hraw
    · have hneg := dvd_neg.mpr hraw
      rw [hisign] at hneg
      convert hneg using 1
      rw [hsign, hisign]
      ring
  have hdiff :
      ((n + j : ℕ) : ℤ) + ((d + i - j : ℕ) : ℤ) =
        ((n + d + i : ℕ) : ℤ) := by
    have hjle : j ≤ d + i := by
      have hjk := (Finset.mem_Icc.mp hj).2
      have hi1 := (Finset.mem_Icc.mp hi).1
      omega
    exact_mod_cast (by omega :
      n + j + (d + i - j) = n + d + i)
  have hfactorial :
      ((P : ℤ) ^ 2) ∣
        factorialMatchingForm
          (q : ℤ)
          (reducedMatchingLeft k i j : ℤ)
          (reducedMatchingRight k i j : ℤ)
          ((-1 : ℤ) ^ (i + j))
          ((d + i - j : ℕ) : ℤ)
          ((n + j : ℕ) : ℤ) := by
    have hFiZ :
        (localBlockCoefficientNat k i : ℤ) =
          (q : ℤ) * (reducedMatchingRight k i j : ℤ) := by
      exact_mod_cast hFi
    have hFjZ :
        (localBlockCoefficientNat k j : ℤ) =
          (q : ℤ) * (reducedMatchingLeft k i j : ℤ) := by
      exact_mod_cast hFj
    unfold factorialMatchingForm
    rw [← hFiZ, ← hFjZ]
    convert hweighted using 1
    rw [← hdiff]
    ring
  exact (owner_square_normalized_iff_of_largePrimeSupport hsupport hq).mp
    hfactorial

private theorem reducedMatchingLeft_le_of_le
    {k i j : ℕ}
    (hi : i ∈ Finset.Icc 1 k)
    (hj : j ∈ Finset.Icc 1 k)
    (hji : j ≤ i) :
    reducedMatchingLeft k i j ≤ (k - 1).choose (i - j) := by
  let Ci := matchingBinomial k i
  let Cj := matchingBinomial k j
  let g := Nat.gcd Ci Cj
  let a := Ci / g
  let b := Cj / g
  let D := (i - 1).choose (j - 1)
  let U := (k - 1 - (j - 1)).choose ((i - 1) - (j - 1))
  have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
  have hik : i ≤ k := (Finset.mem_Icc.mp hi).2
  have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
  have hjk : j ≤ k := (Finset.mem_Icc.mp hj).2
  have hsub : j - 1 ≤ i - 1 := by omega
  have hCiPos : 0 < Ci := by
    dsimp [Ci, matchingBinomial]
    exact Nat.choose_pos (by omega)
  have hgPos : 0 < g := Nat.gcd_pos_of_pos_left Cj hCiPos
  have hcop : a.Coprime b := Nat.coprime_div_gcd_div_gcd hgPos
  have hraw : Ci * D = Cj * U := by
    dsimp [Ci, Cj, D, U, matchingBinomial]
    exact Nat.choose_mul hsub
  have hCi : g * a = Ci := Nat.mul_div_cancel' (Nat.gcd_dvd_left Ci Cj)
  have hCj : g * b = Cj := Nat.mul_div_cancel' (Nat.gcd_dvd_right Ci Cj)
  have hred : a * D = b * U := by
    apply Nat.mul_left_cancel hgPos
    calc
      g * (a * D) = (g * a) * D := by ring
      _ = Ci * D := by rw [hCi]
      _ = Cj * U := hraw
      _ = (g * b) * U := by rw [hCj]
      _ = g * (b * U) := by ring
  have haDvd : a ∣ b * U := by
    rw [← hred]
    exact dvd_mul_right a D
  have haU : a ∣ U := hcop.dvd_of_dvd_mul_left haDvd
  have hUPos : 0 < U := by
    dsimp [U]
    exact Nat.choose_pos (by omega)
  have haLeU : a ≤ U := Nat.le_of_dvd hUPos haU
  have hUle : U ≤ (k - 1).choose (i - j) := by
    dsimp [U]
    have heq : (i - 1) - (j - 1) = i - j := by omega
    rw [heq]
    apply Nat.choose_le_choose
    omega
  exact haLeU.trans hUle

private theorem reducedMatchingRight_le_of_le
    {k i j : ℕ}
    (hi : i ∈ Finset.Icc 1 k)
    (hj : j ∈ Finset.Icc 1 k)
    (hji : j ≤ i) :
    reducedMatchingRight k i j ≤ (k - 1).choose (i - j) := by
  let Ci := matchingBinomial k i
  let Cj := matchingBinomial k j
  let g := Nat.gcd Ci Cj
  let a := Ci / g
  let b := Cj / g
  let D := (i - 1).choose (j - 1)
  let U := (k - 1 - (j - 1)).choose ((i - 1) - (j - 1))
  have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
  have hik : i ≤ k := (Finset.mem_Icc.mp hi).2
  have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
  have hjk : j ≤ k := (Finset.mem_Icc.mp hj).2
  have hsub : j - 1 ≤ i - 1 := by omega
  have hCiPos : 0 < Ci := by
    dsimp [Ci, matchingBinomial]
    exact Nat.choose_pos (by omega)
  have hgPos : 0 < g := Nat.gcd_pos_of_pos_left Cj hCiPos
  have hcop : a.Coprime b := Nat.coprime_div_gcd_div_gcd hgPos
  have hraw : Ci * D = Cj * U := by
    dsimp [Ci, Cj, D, U, matchingBinomial]
    exact Nat.choose_mul hsub
  have hCi : g * a = Ci := Nat.mul_div_cancel' (Nat.gcd_dvd_left Ci Cj)
  have hCj : g * b = Cj := Nat.mul_div_cancel' (Nat.gcd_dvd_right Ci Cj)
  have hred : a * D = b * U := by
    apply Nat.mul_left_cancel hgPos
    calc
      g * (a * D) = (g * a) * D := by ring
      _ = Ci * D := by rw [hCi]
      _ = Cj * U := hraw
      _ = (g * b) * U := by rw [hCj]
      _ = g * (b * U) := by ring
  have hbDvd : b ∣ a * D := by
    rw [hred]
    exact dvd_mul_right b U
  have hbD : b ∣ D := hcop.symm.dvd_of_dvd_mul_left hbDvd
  have hDPos : 0 < D := by
    dsimp [D]
    exact Nat.choose_pos hsub
  have hbLeD : b ≤ D := Nat.le_of_dvd hDPos hbD
  have hDle : D ≤ (k - 1).choose (i - j) := by
    dsimp [D]
    have heq : (i - 1) - (j - 1) = i - j := by omega
    rw [← Nat.choose_symm hsub, heq]
    apply Nat.choose_le_choose
    omega
  exact hbLeD.trans hDle

/-- Exact reduced-binomial numerator bound
`a_ij <= binom(k-1,|i-j|)`. -/
theorem reducedMatchingLeft_le
    {k i j : ℕ}
    (hi : i ∈ Finset.Icc 1 k)
    (hj : j ∈ Finset.Icc 1 k) :
    reducedMatchingLeft k i j ≤ (k - 1).choose (Nat.dist i j) := by
  rcases le_total j i with hji | hij
  · simpa [Nat.dist_comm i j, Nat.dist_eq_sub_of_le hji] using
      reducedMatchingLeft_le_of_le hi hj hji
  · have hswap :
        reducedMatchingLeft k i j = reducedMatchingRight k j i := by
      simp [reducedMatchingLeft, reducedMatchingRight, Nat.gcd_comm]
    rw [hswap, Nat.dist_eq_sub_of_le hij]
    exact reducedMatchingRight_le_of_le hj hi hij

/-- Exact reduced-binomial denominator bound
`b_ij <= binom(k-1,|i-j|)`. -/
theorem reducedMatchingRight_le
    {k i j : ℕ}
    (hi : i ∈ Finset.Icc 1 k)
    (hj : j ∈ Finset.Icc 1 k) :
    reducedMatchingRight k i j ≤ (k - 1).choose (Nat.dist i j) := by
  rcases le_total j i with hji | hij
  · simpa [Nat.dist_comm i j, Nat.dist_eq_sub_of_le hji] using
      reducedMatchingRight_le_of_le hi hj hji
  · have hswap :
        reducedMatchingRight k i j = reducedMatchingLeft k j i := by
      simp [reducedMatchingLeft, reducedMatchingRight, Nat.gcd_comm]
    rw [hswap, Nat.dist_eq_sub_of_le hij]
    exact reducedMatchingLeft_le_of_le hj hi hij

#print axioms factorialMatchingForm_eq_prefactor_mul_normalized
#print axioms normalizedMatchingForm_eq_upper_form
#print axioms largePrimeSupport_coprime_factorial
#print axioms largePrimeSupport_square_isCoprime_of_dvd_factorial
#print axioms owner_square_normalized_iff_of_isCoprime
#print axioms owner_square_normalized_iff_of_largePrimeSupport
#print axioms matchingBinomial_mul_localCoefficientNat
#print axioms exists_matchingCommonPrefactor
#print axioms matched_owner_normalized_square_dvd
#print axioms reducedMatchingLeft_le
#print axioms reducedMatchingRight_le

end Erdos686Variant
end Erdos686
