/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import ErdosProblems.Erdos686

/-!
# Erdős 686: arithmetic composition of the consecutive-property theorem

This isolated module kernel-banks the elementary arithmetic step after the
Erdős--Lacampagne--Selfridge bounded-part classification has supplied a
missing value `r`.

Write `A` and `B` for the products of the parts of the lower and upper blocks
supported on prime bases at most `k`.  The elementary valuation argument gives
`k! ∣ A`; an exact `N=4` equation gives `B=4A`.  If all upper parts are at most
`k+1`, ELS Theorem 4 says `r*B=(k+1)!` for the unique deleted value `r`.
The theorem below composes precisely those three facts.  It does **not** add
ELS Theorem 4 as an axiom and does not claim to formalize that published
classification.
-/

namespace Erdos686
namespace Erdos686Variant

/-- The factor of `x` supported on prime bases at most `k`. -/
def kSmallPart (k x : ℕ) : ℕ :=
  (Finsupp.filter (fun p : ℕ => p ≤ k) x.factorization).prod (· ^ ·)

private lemma filtered_factorization_le (k x : ℕ) :
    Finsupp.filter (fun p : ℕ => p ≤ k) x.factorization ≤ x.factorization := by
  intro p
  simp only [Finsupp.filter_apply]
  split <;> simp

lemma kSmallPart_dvd (k x : ℕ) : kSmallPart k x ∣ x := by
  exact Nat.prod_pow_dvd_of_le_factorization (filtered_factorization_le k x)

lemma kSmallPart_ne_zero {k x : ℕ} (hx : x ≠ 0) : kSmallPart k x ≠ 0 := by
  intro hz
  have hd := kSmallPart_dvd k x
  rw [hz] at hd
  simp at hd
  exact hx hd

lemma kSmallPart_factorization {k x p : ℕ} :
    (kSmallPart k x).factorization p =
      if p ≤ k then x.factorization p else 0 := by
  unfold kSmallPart
  rw [Nat.factorization_prod_pow_eq_self_of_le_factorization
    (filtered_factorization_le k x)]
  exact Finsupp.filter_apply _ _ _

/-- Product of the `k`-small parts of `x+1,...,x+k`. -/
def kSmallBlockProduct (k x : ℕ) : ℕ :=
  ∏ i ∈ Finset.Icc 1 k, kSmallPart k (x + i)

lemma kSmallBlockProduct_ne_zero (k x : ℕ) :
    kSmallBlockProduct k x ≠ 0 := by
  unfold kSmallBlockProduct
  apply Finset.prod_ne_zero_iff.mpr
  intro i hi
  have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
  exact kSmallPart_ne_zero (by omega)

private lemma blockProduct_eq_ascFactorial (k x : ℕ) :
    blockProduct k x = (x + 1).ascFactorial k := by
  have hs : Finset.Icc 1 k = Finset.Ico 1 (k + 1) := by
    ext i
    simp
  rw [Nat.ascFactorial_eq_prod_range]
  unfold blockProduct
  rw [hs, Finset.prod_Ico_eq_prod_range]
  simp only [Nat.add_sub_cancel]
  apply Finset.prod_congr rfl
  intro i hi
  omega

private lemma factorial_dvd_blockProduct (k x : ℕ) :
    k.factorial ∣ blockProduct k x := by
  rw [blockProduct_eq_ascFactorial]
  exact Nat.factorial_dvd_ascFactorial (x + 1) k

lemma kSmallBlockProduct_factorization (k x p : ℕ) :
    (kSmallBlockProduct k x).factorization p =
      if p ≤ k then (blockProduct k x).factorization p else 0 := by
  unfold kSmallBlockProduct
  rw [Nat.factorization_prod_apply]
  · unfold blockProduct
    rw [Nat.factorization_prod_apply]
    · simp only [kSmallPart_factorization]
      by_cases hp : p ≤ k
      · simp [hp]
      · simp [hp]
    · intro i hi
      have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
      omega
  · intro i hi
    have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
    exact kSmallPart_ne_zero (by omega)

/-- Every consecutive block carries at least one complete factorial in its
`k`-small part. -/
theorem factorial_dvd_kSmallBlockProduct (k x : ℕ) :
    k.factorial ∣ kSmallBlockProduct k x := by
  have hf0 : k.factorial ≠ 0 := Nat.factorial_ne_zero k
  have hs0 : kSmallBlockProduct k x ≠ 0 := kSmallBlockProduct_ne_zero k x
  apply (Nat.factorization_le_iff_dvd hf0 hs0).mp
  intro p
  by_cases hp : p.Prime
  · rcases le_or_gt p k with hpk | hpk
    · rw [kSmallBlockProduct_factorization, if_pos hpk]
      have hd := factorial_dvd_blockProduct k x
      exact ((Nat.factorization_le_iff_dvd hf0
        (ne_of_gt (blockProduct_pos k x))).mpr hd) p
    · have hnotdvd : ¬p ∣ k.factorial := by
        rw [hp.dvd_factorial]
        omega
      rw [Nat.factorization_eq_zero_of_not_dvd hnotdvd]
      exact Nat.zero_le _
  · simp [Nat.factorization_eq_zero_of_not_prime _ hp]

/-- An exact quotient-four equation preserves all prime valuations above
`k`, so after stripping those primes its two block products still have exact
ratio four. -/
theorem kSmallBlockProduct_eq_four_of_block_eq
    {k n d : ℕ} (hk : 2 ≤ k)
    (heq : blockProduct k (n + d) = 4 * blockProduct k n) :
    kSmallBlockProduct k (n + d) = 4 * kSmallBlockProduct k n := by
  have hU0 := kSmallBlockProduct_ne_zero k (n + d)
  have hL0 := kSmallBlockProduct_ne_zero k n
  have hR0 : 4 * kSmallBlockProduct k n ≠ 0 :=
    mul_ne_zero (by norm_num) hL0
  apply Nat.factorization_inj hU0 hR0
  ext p
  rw [Nat.factorization_mul (by norm_num : 4 ≠ 0) hL0, Finsupp.add_apply]
  rw [kSmallBlockProduct_factorization, kSmallBlockProduct_factorization]
  by_cases hpk : p ≤ k
  · rw [if_pos hpk, if_pos hpk]
    have hfull : (blockProduct k (n + d)).factorization =
        (4 * blockProduct k n).factorization := congrArg Nat.factorization heq
    rw [Nat.factorization_mul (by norm_num : 4 ≠ 0)
      (ne_of_gt (blockProduct_pos k n))] at hfull
    exact DFunLike.congr_fun hfull p
  · rw [if_neg hpk, if_neg hpk]
    by_cases hpprime : p.Prime
    · have hnotdvd : ¬p ∣ 4 := by
        intro hdvd
        have ple : p ≤ 4 := Nat.le_of_dvd (by norm_num) hdvd
        have pge : 3 ≤ p := by omega
        interval_cases p
        · norm_num at hdvd
        · norm_num at hpprime
      rw [Nat.factorization_eq_zero_of_not_dvd hnotdvd]
    · rw [Nat.factorization_eq_zero_of_not_prime 4 hpprime]

/-- The exact missing-value factorization forced by the factor-four mass
identity and the universal factorial divisor. -/
theorem missing_value_factorization_of_four_small_mass
    {k lower upper r : ℕ}
    (hfactorial : k.factorial ∣ lower)
    (hratio : upper = 4 * lower)
    (hmissing : r * upper = (k + 1).factorial) :
    ∃ t : ℕ,
      lower = k.factorial * t ∧
      k + 1 = 4 * r * t := by
  obtain ⟨t, ht⟩ := hfactorial
  refine ⟨t, ht, ?_⟩
  rw [hratio, ht, Nat.factorial_succ] at hmissing
  have hcancel : r * (4 * t) = k + 1 := by
    exact Nat.eq_of_mul_eq_mul_right (Nat.factorial_pos k)
      (by simpa [mul_assoc, mul_comm, mul_left_comm] using hmissing)
  simpa [mul_assoc, mul_comm, mul_left_comm] using hcancel.symm

/-- Divisibility form of the same conclusion: the deleted upper value consumes
an exact factor `4r` of `k+1`. -/
theorem four_mul_missing_value_dvd_k_add_one
    {k lower upper r : ℕ}
    (hfactorial : k.factorial ∣ lower)
    (hratio : upper = 4 * lower)
    (hmissing : r * upper = (k + 1).factorial) :
    4 * r ∣ k + 1 := by
  obtain ⟨t, _hlower, hk⟩ :=
    missing_value_factorization_of_four_small_mass
      hfactorial hratio hmissing
  refine ⟨t, ?_⟩
  simpa [mul_assoc] using hk

/-- Abstract equation-facing dichotomy.  `classify` is exactly the output
interface of ELS Theorem 4 in the bounded branch: either a part exceeds
`k+1`, or the bounded upper product has one deleted value `r`. -/
theorem upper_small_part_dichotomy_after_els
    {ι : Type} [Fintype ι]
    {k lower upper : ℕ} (part : ι → ℕ)
    (hfactorial : k.factorial ∣ lower)
    (hratio : upper = 4 * lower)
    (hproduct : ∏ i, part i = upper)
    (classify :
      (∃ i, k + 1 < part i) ∨
      ∃ r, r * upper = (k + 1).factorial) :
    (∃ i, k + 1 < part i) ∨
      ∃ r t,
        lower = k.factorial * t ∧
        k + 1 = 4 * r * t ∧
        r * (∏ i, part i) = (k + 1).factorial := by
  rcases classify with hlarge | ⟨r, hmissing⟩
  · exact Or.inl hlarge
  · right
    obtain ⟨t, hlower, hk⟩ :=
      missing_value_factorization_of_four_small_mass
        hfactorial hratio hmissing
    exact ⟨r, t, hlower, hk, by simpa [hproduct] using hmissing⟩

/-- A strict perfect matching cannot exist when both core multisets contain
the minimum value one.  This is the `r>1` endpoint obstruction used by the
owner-graph argument. -/
theorem no_strict_matching_of_common_one
    {ι κ : Type} [Nonempty ι]
    (lower : ι → ℕ) (upper : κ → ℕ) (pairing : ι ≃ κ)
    (hlowerPos : ∀ i, 1 ≤ lower i)
    (hupperOne : ∃ j, upper j = 1)
    (hstrict : ∀ i, lower i < upper (pairing i)) : False := by
  obtain ⟨j, hj⟩ := hupperOne
  have hs := hstrict (pairing.symm j)
  have hm : pairing (pairing.symm j) = j := pairing.apply_symm_apply j
  rw [hm, hj] at hs
  have hp := hlowerPos (pairing.symm j)
  omega

/-- A strict perfect matching cannot exist when the lower multiset contains
the common upper bound `K`.  This is the `r=1`, `K>=20` endpoint
obstruction. -/
theorem no_strict_matching_of_common_max
    {ι κ : Type} [Nonempty κ]
    (K : ℕ) (lower : ι → ℕ) (upper : κ → ℕ) (pairing : ι ≃ κ)
    (hlowerK : ∃ i, lower i = K)
    (hupperLe : ∀ j, upper j ≤ K)
    (hstrict : ∀ i, lower i < upper (pairing i)) : False := by
  obtain ⟨i, hi⟩ := hlowerK
  have hs := hstrict i
  have hu := hupperLe (pairing i)
  rw [hi] at hs
  omega

#print axioms missing_value_factorization_of_four_small_mass
#print axioms four_mul_missing_value_dvd_k_add_one
#print axioms upper_small_part_dichotomy_after_els
#print axioms factorial_dvd_kSmallBlockProduct
#print axioms kSmallBlockProduct_eq_four_of_block_eq
#print axioms no_strict_matching_of_common_one
#print axioms no_strict_matching_of_common_max

end Erdos686Variant
end Erdos686
