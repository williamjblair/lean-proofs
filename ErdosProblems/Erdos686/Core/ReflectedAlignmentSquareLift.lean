/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import ErdosProblems.Erdos686.Core.ReflectionOwnerCorrelationAudit

/-!
# Erdős 686: a quadratic lift at matched and reflected owners

The first-order owner correlation only puts a prime power into one lower and
one upper factor.  Keeping the linear term of the two local block expansions
gains a second copy of that prime power.  This module proves the generic
matched-owner statement without primality or uniqueness assumptions.
-/

namespace Erdos686
namespace Erdos686Variant

private lemma int_modEq_neg_index_of_dvd_add_agent
    {h n i : ℕ} (hdiv : h ∣ n + i) :
    (n : ℤ) ≡ -(i : ℤ) [ZMOD (h : ℤ)] := by
  rw [Int.modEq_iff_dvd]
  have hcast : (h : ℤ) ∣ ((n + i : ℕ) : ℤ) := by
    exact_mod_cast hdiv
  have hneg := dvd_neg.mpr hcast
  convert hneg using 1
  push_cast
  ring

/-- If the same natural modulus lands on a lower factor and an arbitrary
upper factor, the exact multiplier-four equation forces its square into the
corresponding linear combination of the two signed local coefficients.

This is a genuine second-order consequence of the full equation.  Neither a
row prefix nor the first-order reflection congruence supplies `heq`. -/
theorem matched_owner_local_coefficients_dvd_sq
    {k n d i j h : ℕ}
    (hi : i ∈ Finset.Icc 1 k)
    (hj : j ∈ Finset.Icc 1 k)
    (hlower : h ∣ n + i)
    (hupper : h ∣ n + d + j)
    (heq : blockProduct k (n + d) = 4 * blockProduct k n) :
    (h : ℤ) ^ 2 ∣
      localBlockCoefficient k j * ((n + d + j : ℕ) : ℤ) -
        4 * localBlockCoefficient k i * ((n + i : ℕ) : ℤ) := by
  let Ci : ℤ := localBlockCoefficient k i
  let Cj : ℤ := localBlockCoefficient k j
  let L : ℤ := ((n + i : ℕ) : ℤ)
  let U : ℤ := ((n + d + j : ℕ) : ℤ)
  let QL : ℤ := localBlockCofactor k i (n : ℤ)
  let QU : ℤ := localBlockCofactor k j ((n + d : ℕ) : ℤ)
  have hnmod : (n : ℤ) ≡ -(i : ℤ) [ZMOD (h : ℤ)] :=
    int_modEq_neg_index_of_dvd_add_agent hlower
  have hnumod : ((n + d : ℕ) : ℤ) ≡ -(j : ℤ) [ZMOD (h : ℤ)] := by
    have hraw := int_modEq_neg_index_of_dvd_add_agent
      (n := n + d) (i := j) (h := h) (by
        simpa [Nat.add_assoc] using hupper)
    simpa [Nat.add_assoc] using hraw
  have hQLmod : QL ≡ Ci [ZMOD (h : ℤ)] := by
    exact localBlockCofactor_modEq hnmod
  have hQUmod : QU ≡ Cj [ZMOD (h : ℤ)] := by
    exact localBlockCofactor_modEq hnumod
  have hL : (h : ℤ) ∣ L := by
    dsimp [L]
    exact_mod_cast hlower
  have hU : (h : ℤ) ∣ U := by
    dsimp [U]
    exact_mod_cast hupper
  have hQLerr : (h : ℤ) ∣ QL - Ci := by
    have hraw := hQLmod.dvd
    simpa [sub_eq_add_neg, add_comm] using (dvd_neg.mpr hraw)
  have hQUerr : (h : ℤ) ∣ QU - Cj := by
    have hraw := hQUmod.dvd
    simpa [sub_eq_add_neg, add_comm] using (dvd_neg.mpr hraw)
  have hLowerSq : (h : ℤ) ^ 2 ∣ L * (QL - Ci) := by
    simpa [pow_two] using mul_dvd_mul hL hQLerr
  have hUpperSq : (h : ℤ) ^ 2 ∣ U * (QU - Cj) := by
    simpa [pow_two] using mul_dvd_mul hU hQUerr
  have heqInt :
      intBlockProduct k ((n + d : ℕ) : ℤ) =
        4 * intBlockProduct k (n : ℤ) := by
    rw [intBlockProduct_natCast, intBlockProduct_natCast]
    exact_mod_cast heq
  have heqLocal : U * QU = 4 * L * QL := by
    rw [intBlockProduct_eq_factor_mul_localBlockCofactor
        ((n + d : ℕ) : ℤ) hj,
      intBlockProduct_eq_factor_mul_localBlockCofactor (n : ℤ) hi] at heqInt
    simpa [U, L, QU, QL, Nat.cast_add, mul_assoc] using heqInt
  have hidentity :
      Cj * U - 4 * Ci * L =
        -(U * (QU - Cj)) + 4 * (L * (QL - Ci)) := by
    linear_combination heqLocal
  change (h : ℤ) ^ 2 ∣ Cj * U - 4 * Ci * L
  rw [hidentity]
  exact dvd_add (dvd_neg.mpr hUpperSq)
    (dvd_mul_of_dvd_right hLowerSq 4)

/-- Reflection of the signed local derivative coefficient. -/
lemma localBlockCoefficient_reflected_agent
    {k i : ℕ} (hi : i ∈ Finset.Icc 1 k) :
    localBlockCoefficient k (k + 1 - i) =
      (-1 : ℤ) ^ (k - 1) * localBlockCoefficient k i := by
  have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
  have hik : i ≤ k := (Finset.mem_Icc.mp hi).2
  have hj : k + 1 - i ∈ Finset.Icc 1 k := by
    rw [Finset.mem_Icc]
    constructor <;> omega
  rw [localBlockCoefficient_eq_sign_mul_nat hj,
    localBlockCoefficient_eq_sign_mul_nat hi]
  have hleft : k + 1 - i - 1 = k - i := by omega
  have hright : k - (k + 1 - i) = i - 1 := by omega
  have heven : Even (2 * (i - 1)) := by
    exact ⟨i - 1, by omega⟩
  have htwo : (-1 : ℤ) ^ (2 * (i - 1)) = 1 :=
    Even.neg_one_pow heven
  have hexp : k - i + 2 * (i - 1) = (k - 1) + (i - 1) := by omega
  have hsign : (-1 : ℤ) ^ (k - i) =
      (-1 : ℤ) ^ (k - 1) * (-1 : ℤ) ^ (i - 1) := by
    calc
      (-1 : ℤ) ^ (k - i) = (-1 : ℤ) ^ (k - i) * 1 := by ring
      _ = (-1 : ℤ) ^ (k - i) * (-1 : ℤ) ^ (2 * (i - 1)) := by rw [htwo]
      _ = (-1 : ℤ) ^ (k - i + 2 * (i - 1)) := by rw [pow_add]
      _ = (-1 : ℤ) ^ ((k - 1) + (i - 1)) := by rw [hexp]
      _ = (-1 : ℤ) ^ (k - 1) * (-1 : ℤ) ^ (i - 1) := by rw [pow_add]
  unfold localBlockCoefficientNat
  rw [hleft, hright, hsign]
  push_cast
  ring

/-- Reflected specialization.  The two local weights agree up to the global
parity sign, so a common owner modulus gains a full quadratic lift. -/
theorem reflected_owner_local_coefficient_dvd_sq
    {k n d i h : ℕ}
    (hi : i ∈ Finset.Icc 1 k)
    (hlower : h ∣ n + i)
    (hupper : h ∣ n + d + (k + 1 - i))
    (heq : blockProduct k (n + d) = 4 * blockProduct k n) :
    (h : ℤ) ^ 2 ∣
      localBlockCoefficient k i *
        (((-1 : ℤ) ^ (k - 1)) * ((n + d + (k + 1 - i) : ℕ) : ℤ) -
          4 * ((n + i : ℕ) : ℤ)) := by
  have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
  have hik : i ≤ k := (Finset.mem_Icc.mp hi).2
  have hj : k + 1 - i ∈ Finset.Icc 1 k := by
    rw [Finset.mem_Icc]
    constructor <;> omega
  have hraw := matched_owner_local_coefficients_dvd_sq
    hi hj hlower hupper heq
  rw [localBlockCoefficient_reflected_agent hi] at hraw
  convert hraw using 1 <;> ring

/-- Absolute local-weight form of the reflected quadratic lift. -/
theorem reflected_owner_local_coefficientNat_dvd_sq
    {k n d i h : ℕ}
    (hi : i ∈ Finset.Icc 1 k)
    (hlower : h ∣ n + i)
    (hupper : h ∣ n + d + (k + 1 - i))
    (heq : blockProduct k (n + d) = 4 * blockProduct k n) :
    (h : ℤ) ^ 2 ∣
      (localBlockCoefficientNat k i : ℤ) *
        (((-1 : ℤ) ^ (k - 1)) * ((n + d + (k + 1 - i) : ℕ) : ℤ) -
          4 * ((n + i : ℕ) : ℤ)) := by
  have hsigned := reflected_owner_local_coefficient_dvd_sq
    hi hlower hupper heq
  rw [localBlockCoefficient_eq_sign_mul_nat hi] at hsigned
  rcases neg_one_pow_eq_or ℤ (i - 1) with hsign | hsign
  · simpa [hsign, mul_assoc, mul_comm, mul_left_comm] using hsigned
  · have hneg := dvd_neg.mpr hsigned
    simpa [hsign, mul_assoc, mul_comm, mul_left_comm] using hneg

/-- When the prime base is at least the block length, it is absent from the
local derivative coefficient, so the reflected quadratic lift loses no
factorial valuation. -/
theorem primePower_reflected_owner_dvd_sq
    {p e k n d i : ℕ}
    (hp : p.Prime)
    (hkp : k ≤ p)
    (hi : i ∈ Finset.Icc 1 k)
    (hlower : p ^ e ∣ n + i)
    (hupper : p ^ e ∣ n + d + (k + 1 - i))
    (heq : blockProduct k (n + d) = 4 * blockProduct k n) :
    (((p ^ e : ℕ) : ℤ) ^ 2) ∣
      ((-1 : ℤ) ^ (k - 1)) * ((n + d + (k + 1 - i) : ℕ) : ℤ) -
        4 * ((n + i : ℕ) : ℤ) := by
  have hraw := reflected_owner_local_coefficientNat_dvd_sq
    hi hlower hupper heq
  have hpInt : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hpCoeff : ¬ (p : ℤ) ∣ (localBlockCoefficientNat k i : ℤ) := by
    intro hdiv
    apply prime_not_dvd_localBlockCoefficientNat hp hkp hi
    exact Int.natCast_dvd_natCast.mp hdiv
  have hraw' :
      (p : ℤ) ^ (e * 2) ∣
        (localBlockCoefficientNat k i : ℤ) *
          (((-1 : ℤ) ^ (k - 1)) * ((n + d + (k + 1 - i) : ℕ) : ℤ) -
            4 * ((n + i : ℕ) : ℤ)) := by
    simpa [Nat.cast_pow, ← pow_mul] using hraw
  have hcancel := hpInt.pow_dvd_of_dvd_mul_left (e * 2) hpCoeff hraw'
  simpa [Nat.cast_pow, ← pow_mul] using hcancel

lemma reflectionResidualExponent_eq_center_factorization_of_large_prime
    {p k n d : ℕ}
    (hp : p.Prime) (hk : 16 ≤ k) (hkp : k < p) :
    reflectionResidualExponent p k n d =
      (2 * n + d + k + 1).factorization p := by
  have hcLt : reflectionCoeff k < p := by
    unfold reflectionCoeff
    split <;> omega
  have hcVal : (reflectionCoeff k).factorization p = 0 :=
    Nat.factorization_eq_zero_of_lt hcLt
  have hfactLt : k - 1 < p := by omega
  have hfactVal : (k - 1).factorial.factorization p = 0 :=
    Nat.factorization_factorial_eq_zero_of_lt hfactLt
  simp [reflectionResidualExponent, hcVal, hfactVal]

/-- Every large prime divisor of the reflection center in a target-range
equation has a reflected owner on which the *square* of its complete center
prime power divides the parity linear form.  For even `k` that form is the
negative of `B+4A`; for odd `k` it is `B-4A`.

This eliminates the first-order reflected alternative whenever the center
prime power is too large for the explicit linear form. -/
theorem exists_large_prime_reflection_center_square_lift_four
    {p k n d : ℕ}
    (hp : p.Prime) (hk : 16 ≤ k) (hd : k ≤ d) (hkp : k < p)
    (hpS : p ∣ 2 * n + d + k + 1)
    (heq : blockProduct k (n + d) = 4 * blockProduct k n) :
    ∃ i, i ∈ Finset.Icc 1 k ∧
      ((((p ^ (2 * n + d + k + 1).factorization p : ℕ) : ℤ) ^ 2) ∣
        ((-1 : ℤ) ^ (k - 1)) *
            ((n + d + (k + 1 - i) : ℕ) : ℤ) -
          4 * ((n + i : ℕ) : ℤ)) := by
  let E := (2 * n + d + k + 1).factorization p
  have hS0 : 2 * n + d + k + 1 ≠ 0 := by omega
  have hEpos : 0 < E := by
    exact hp.factorization_pos_of_dvd hS0 hpS
  obtain ⟨i, hi, j, hj, hlower, hupper, hreflection, hcentered⟩ :=
    exists_reflection_owner_correlation_four hp (by omega : 1 ≤ k) hd heq
  have hresidual : reflectionResidualExponent p k n d = E := by
    simpa [E] using
      reflectionResidualExponent_eq_center_factorization_of_large_prime
        (n := n) (d := d) hp hk hkp
  rw [hresidual] at hlower hupper
  have hcorr := reflection_owner_correlation_offset_and_lcm
    (p := p) (n := n) (by omega : 1 ≤ k) hd hi hj hreflection hcentered
  rw [hresidual] at hcorr
  have hpPow : p ∣ p ^ E := by
    simpa using (pow_dvd_pow p (by omega : 1 ≤ E))
  have hpOffset : p ∣ Nat.dist (i + j) (k + 1) :=
    dvd_trans hpPow hcorr.1
  have hsum : i + j = k + 1 := by
    by_contra hne
    have hpos : 0 < Nat.dist (i + j) (k + 1) :=
      Nat.dist_pos_of_ne hne
    have hpLe : p ≤ Nat.dist (i + j) (k + 1) :=
      Nat.le_of_dvd hpos hpOffset
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
    omega
  have hjEq : j = k + 1 - i := by
    have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
    have hik : i ≤ k := (Finset.mem_Icc.mp hi).2
    omega
  have hupperReflected : p ^ E ∣ n + d + (k + 1 - i) := by
    simpa [hjEq] using hupper
  have hlift := primePower_reflected_owner_dvd_sq
    hp (by omega : k ≤ p) hi hlower hupperReflected heq
  exact ⟨i, hi, by simpa [E] using hlift⟩

/-- Quantitative elimination of a dominant reflected center power.  Every
prime power with base above the block length that occurs in the reflection
center of a target-range equation has square at most `7*n`.

The constant is deliberately loose and uniform in both parities. -/
theorem exists_large_prime_reflection_center_power_sq_le
    {p k n d : ℕ}
    (hp : p.Prime) (hk : 16 ≤ k) (hd : k ≤ d) (hkp : k < p)
    (hpS : p ∣ 2 * n + d + k + 1)
    (heq : blockProduct k (n + d) = 4 * blockProduct k n) :
    ∃ i, i ∈ Finset.Icc 1 k ∧
      (p ^ (2 * n + d + k + 1).factorization p) ^ 2 ≤ 7 * n := by
  obtain ⟨i, hi, hlift⟩ :=
    exists_large_prime_reflection_center_square_lift_four
      hp hk hd hkp hpS heq
  let q : ℕ := p ^ (2 * n + d + k + 1).factorization p
  let A : ℕ := n + i
  let B : ℕ := n + d + (k + 1 - i)
  let Z : ℤ := ((-1 : ℤ) ^ (k - 1)) * (B : ℤ) - 4 * (A : ℤ)
  have hliftZ : (q : ℤ) ^ 2 ∣ Z := by
    simpa [q, A, B, Z] using hlift
  have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
  have hik : i ≤ k := (Finset.mem_Icc.mp hi).2
  have hn9 : 9 * d < n :=
    nine_mul_gap_lt_n_of_four_solution hk hd heq
  have hZne : Z ≠ 0 := by
    by_cases hkeven : Even k
    · have hkoddPred : Odd (k - 1) :=
        Nat.Even.sub_odd (by omega : 1 ≤ k) hkeven (by norm_num)
      have hsign : (-1 : ℤ) ^ (k - 1) = -1 :=
        Odd.neg_one_pow hkoddPred
      dsimp [Z]
      rw [hsign]
      push_cast
      omega
    · have hkodd : Odd k := Nat.not_even_iff_odd.mp hkeven
      have hkevenPred : Even (k - 1) :=
        Nat.Odd.sub_odd hkodd (by norm_num)
      have hsign : (-1 : ℤ) ^ (k - 1) = 1 :=
        Even.neg_one_pow hkevenPred
      dsimp [Z, A, B]
      rw [hsign]
      push_cast
      omega
  have hqLe : q ^ 2 ≤ Int.natAbs Z := by
    simpa [Int.natAbs_pow] using
      Int.natAbs_le_of_dvd_ne_zero hliftZ hZne
  have hZBound : Int.natAbs Z ≤ 7 * n := by
    by_cases hkeven : Even k
    · have hkoddPred : Odd (k - 1) :=
        Nat.Even.sub_odd (by omega : 1 ≤ k) hkeven (by norm_num)
      have hsign : (-1 : ℤ) ^ (k - 1) = -1 :=
        Odd.neg_one_pow hkoddPred
      have hformula : Z = -((B + 4 * A : ℕ) : ℤ) := by
        dsimp [Z]
        rw [hsign]
        push_cast
        ring
      rw [hformula]
      simp only [Int.natAbs_neg, Int.natAbs_natCast]
      dsimp [A, B]
      omega
    · have hkodd : Odd k := Nat.not_even_iff_odd.mp hkeven
      have hkevenPred : Even (k - 1) :=
        Nat.Odd.sub_odd hkodd (by norm_num)
      have hsign : (-1 : ℤ) ^ (k - 1) = 1 :=
        Even.neg_one_pow hkevenPred
      have hBA : B ≤ 4 * A := by
        dsimp [A, B]
        omega
      have hformula : Z = -(((4 * A - B : ℕ) : ℤ)) := by
        dsimp [Z]
        rw [hsign]
        rw [Nat.cast_sub hBA]
        push_cast
        ring
      rw [hformula]
      simp only [Int.natAbs_neg, Int.natAbs_natCast]
      dsimp [A, B]
      omega
  exact ⟨i, hi, by simpa [q] using le_trans hqLe hZBound⟩

#print axioms matched_owner_local_coefficients_dvd_sq
#print axioms localBlockCoefficient_reflected_agent
#print axioms reflected_owner_local_coefficient_dvd_sq
#print axioms reflected_owner_local_coefficientNat_dvd_sq
#print axioms primePower_reflected_owner_dvd_sq
#print axioms reflectionResidualExponent_eq_center_factorization_of_large_prime
#print axioms exists_large_prime_reflection_center_square_lift_four
#print axioms exists_large_prime_reflection_center_power_sq_le

end Erdos686Variant
end Erdos686
