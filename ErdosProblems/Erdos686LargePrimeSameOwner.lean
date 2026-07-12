/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import ErdosProblems.Erdos686LargePrimeGapComponent
import ErdosProblems.Erdos686TwoOwnerGrouping

/-!
# Large-prime same-owner dominance for Erdős 686

The generic same-owner product-square theorem already exists as
`globalResidualGroupedLeft_square_dvd_residual`.  This file does not duplicate
it.  Instead it supplies the missing large-row archimedean consequence:
every square divisor `h^2` of one positive residual satisfies

`6*h^2 < (13*k-6)*d + 18*(k-1)`.

Thus a grouped owner bucket whose square reaches the opposite non-strict
bound rules out the equation.  A direct two-component wrapper gives a mixed
gap subclass, and a whole gap `d=p^e*q^f` with both bases at least `k>=16`
forces the two full components to have distinct localization owners.
-/

namespace Erdos686
namespace Erdos686Variant

/-- Any square divisor of a positive local residual obeys the exact large-row
ceiling.  This is the arithmetic interface needed by every same-owner
aggregate; it has no prime-power premise. -/
theorem localResidual_square_strict_upper_of_four_solution
    {h k n d i : ℕ}
    (hk : 16 ≤ k) (hd : k ≤ d)
    (hi : i ∈ Finset.Icc 1 k)
    (hsquare : h ^ 2 ∣ localResidual n d i)
    (heq : blockProduct k (n + d) = 4 * blockProduct k n) :
    6 * h ^ 2 < (13 * k - 6) * d + 18 * (k - 1) := by
  have h9d : 9 * d < n := nine_mul_gap_lt_n_of_four_solution hk hd heq
  have hresPos : 0 < localResidual n d i := by
    unfold localResidual
    omega
  have hsqLe : h ^ 2 ≤ localResidual n d i :=
    Nat.le_of_dvd hresPos hsquare
  have hresAdd : localResidual n d i + d = 3 * (n + i) := by
    unfold localResidual
    omega
  have hliftCeil : 6 * h ^ 2 + 6 * d ≤ 18 * (n + i) := by
    nlinarith
  have hik : i ≤ k := (Finset.mem_Icc.mp hi).2
  have hindexCeil : 18 * (n + i) ≤
      18 * (n + 1) + 18 * (k - 1) := by
    omega
  have hratio : 18 * (n + 1) < 13 * k * d :=
    eighteen_mul_n_add_one_lt_thirteen_mul_k_mul_gap_of_four_solution hk heq
  have hstrict :
      6 * h ^ 2 + 6 * d < 13 * k * d + 18 * (k - 1) :=
    lt_of_le_of_lt (hliftCeil.trans hindexCeil)
      (Nat.add_lt_add_right hratio _)
  by_contra hnot
  have hdominant :
      (13 * k - 6) * d + 18 * (k - 1) ≤ 6 * h ^ 2 :=
    Nat.le_of_not_gt hnot
  have hadd := Nat.add_le_add_right hdominant (6 * d)
  let A := 13 * k - 6
  have hA : A + 6 = 13 * k := by
    dsimp [A]
    omega
  have hreverse :
      13 * k * d + 18 * (k - 1) ≤ 6 * h ^ 2 + 6 * d := by
    calc
      13 * k * d + 18 * (k - 1) =
          (A * d + 18 * (k - 1)) + 6 * d := by
            rw [← hA]
            ring
      _ = ((13 * k - 6) * d + 18 * (k - 1)) + 6 * d := by rfl
      _ ≤ 6 * h ^ 2 + 6 * d := hadd
  exact (Nat.not_lt_of_ge hreverse) hstrict

/-- Existing pairwise-coprime owner aggregation, now equipped with the exact
large-row residual ceiling. -/
theorem grouped_owner_square_strict_upper_of_four_solution
    {k n d i : ℕ} {owner : ℕ → ℕ}
    (hk : 16 ≤ k) (hd : k ≤ d)
    (hi : i ∈ Finset.Icc 1 k)
    (hassign : GlobalResidualOwnerAssignment k n d owner)
    (heq : blockProduct k (n + d) = 4 * blockProduct k n) :
    6 * (globalResidualGroupedLeft k d owner i) ^ 2 <
      (13 * k - 6) * d + 18 * (k - 1) := by
  exact localResidual_square_strict_upper_of_four_solution hk hd hi
    (globalResidualGroupedLeft_square_dvd_residual hassign) heq

/-- A certified owner bucket whose product square reaches the explicit
residual ceiling rules out the quotient-four equation. -/
theorem no_four_solution_of_grouped_owner_dominance
    {k n d i : ℕ} {owner : ℕ → ℕ}
    (hk : 16 ≤ k) (hd : k ≤ d)
    (hi : i ∈ Finset.Icc 1 k)
    (hassign : GlobalResidualOwnerAssignment k n d owner)
    (hdominant :
      (13 * k - 6) * d + 18 * (k - 1) ≤
        6 * (globalResidualGroupedLeft k d owner i) ^ 2) :
    blockProduct k (n + d) ≠ 4 * blockProduct k n := by
  intro heq
  have hstrict := grouped_owner_square_strict_upper_of_four_solution
    hk hd hi hassign heq
  exact (Nat.not_lt_of_ge hdominant) hstrict

/-- Direct mixed-gap specialization: two coprime large-prime components at
one lower factor cannot coexist once their product square reaches the exact
large-row ceiling.  Extra factors of `d` are allowed. -/
theorem no_four_solution_of_two_large_prime_components_same_owner_dominance
    {p q e f k n d i : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (he : 0 < e) (hf : 0 < f)
    (hk : 16 ≤ k) (hd : k ≤ d)
    (hkp : k ≤ p) (hkq : k ≤ q)
    (hpDvd : p ^ e ∣ d) (hqDvd : q ^ f ∣ d)
    (hi : i ∈ Finset.Icc 1 k)
    (hpOwner : p ^ e ∣ n + i) (hqOwner : q ^ f ∣ n + i)
    (hdominant :
      (13 * k - 6) * d + 18 * (k - 1) ≤
        6 * (p ^ e * q ^ f) ^ 2) :
    blockProduct k (n + d) ≠ 4 * blockProduct k n := by
  intro heq
  have h9d : 9 * d < n := nine_mul_gap_lt_n_of_four_solution hk hd heq
  have hresPos : 0 < localResidual n d i := by
    unfold localResidual
    omega
  have hpLift := primePower_sq_dvd_three_factor_sub_gap
    hp hkp hi hpDvd hpOwner heq
  have hqLift := primePower_sq_dvd_three_factor_sub_gap
    hq hkq hi hqDvd hqOwner heq
  have hpSquare : (p ^ e) ^ 2 ∣ localResidual n d i :=
    nat_pow_dvd_localResidual_of_int_lift hresPos hpLift
  have hqSquare : (q ^ f) ^ 2 ∣ localResidual n d i :=
    nat_pow_dvd_localResidual_of_int_lift hresPos hqLift
  have hcop : Nat.Coprime (p ^ e) (q ^ f) :=
    Nat.coprime_pow_primes e f hp hq hpq
  have hproductSquare : (p ^ e * q ^ f) ^ 2 ∣ localResidual n d i := by
    have hmul := (hcop.pow 2 2).mul_dvd_of_dvd_of_dvd hpSquare hqSquare
    convert hmul using 1 <;> ring
  have hstrict := localResidual_square_strict_upper_of_four_solution
    hk hd hi hproductSquare heq
  exact (Nat.not_lt_of_ge hdominant) hstrict

/-- The dominance premise is automatic when the two full large-prime
components comprise the whole gap.  Primality and distinctness are not
needed for this arithmetic inequality. -/
lemma two_large_component_whole_gap_dominance
    {p q e f k d : ℕ}
    (he : 0 < e) (hf : 0 < f)
    (hk : 16 ≤ k) (hkp : k ≤ p) (hkq : k ≤ q)
    (hgap : d = p ^ e * q ^ f) :
    (13 * k - 6) * d + 18 * (k - 1) ≤ 6 * d ^ 2 := by
  have hpPos : 0 < p := by omega
  have hqPos : 0 < q := by omega
  have hpBaseLe : p ≤ p ^ e := by
    simpa using Nat.pow_le_pow_right hpPos (by omega : 1 ≤ e)
  have hqBaseLe : q ≤ q ^ f := by
    simpa using Nat.pow_le_pow_right hqPos (by omega : 1 ≤ f)
  have hkSqD : k ^ 2 ≤ d := by
    calc
      k ^ 2 = k * k := by ring
      _ ≤ p * q := Nat.mul_le_mul hkp hkq
      _ ≤ p ^ e * q ^ f := Nat.mul_le_mul hpBaseLe hqBaseLe
      _ = d := hgap.symm
  have hkd : k ≤ d := by
    have hkSq : k ≤ k ^ 2 := by nlinarith
    exact hkSq.trans hkSqD
  have htail : 18 * (k - 1) ≤ 18 * d :=
    Nat.mul_le_mul_left 18 (by omega)
  have hcoefficient : 13 * k + 12 ≤ 6 * d := by
    calc
      13 * k + 12 ≤ 6 * k ^ 2 := by nlinarith
      _ ≤ 6 * d := Nat.mul_le_mul_left 6 hkSqD
  let A := 13 * k - 6
  have hA : A + 18 = 13 * k + 12 := by
    dsimp [A]
    omega
  calc
    (13 * k - 6) * d + 18 * (k - 1) ≤
        (13 * k - 6) * d + 18 * d :=
      Nat.add_le_add_left htail _
    _ = (13 * k + 12) * d := by
      change A * d + 18 * d = (13 * k + 12) * d
      rw [← add_mul, hA]
    _ ≤ (6 * d) * d := Nat.mul_le_mul_right d hcoefficient
    _ = 6 * d ^ 2 := by ring

/-- All-parity large-row consequence for a whole two-large-prime gap: the
two full primary components have distinct unique lower localization owners.
This does not claim that the distinct-owner Pell branch is impossible. -/
theorem two_large_prime_whole_gap_has_distinct_local_owners
    {p q e f k n d : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (he : 0 < e) (hf : 0 < f)
    (hk : 16 ≤ k) (hkp : k ≤ p) (hkq : k ≤ q)
    (hgap : d = p ^ e * q ^ f)
    (heq : blockProduct k (n + d) = 4 * blockProduct k n) :
    ∃ i j,
      i ∈ Finset.Icc 1 k ∧ j ∈ Finset.Icc 1 k ∧ i ≠ j ∧
      p ^ e ∣ n + i ∧ q ^ f ∣ n + j ∧
      (((p ^ e : ℕ) : ℤ) ^ 2) ∣
        3 * ((n + i : ℕ) : ℤ) - (d : ℤ) ∧
      (((q ^ f : ℕ) : ℤ) ^ 2) ∣
        3 * ((n + j : ℕ) : ℤ) - (d : ℤ) := by
  have hqPowPos : 0 < q ^ f := pow_pos hq.pos _
  have hpDvd : p ^ e ∣ d := by
    rw [hgap]
    exact dvd_mul_right _ _
  have hqDvd : q ^ f ∣ d := by
    rw [hgap]
    exact dvd_mul_left _ _
  have hkd : k ≤ d := by
    have hpLePow : p ≤ p ^ e := by
      simpa using Nat.pow_le_pow_right hp.pos (by omega : 1 ≤ e)
    have hpartLe : p ^ e ≤ p ^ e * q ^ f :=
      Nat.le_mul_of_pos_right _ hqPowPos
    rw [hgap]
    exact hkp.trans (hpLePow.trans hpartLe)
  obtain ⟨i, hip, _huniqP⟩ := gap_primePower_existsUnique_local_sq_lift
    hp he (by omega : 4 ≤ k) hkp hpDvd heq
  obtain ⟨j, hiq, _huniqQ⟩ := gap_primePower_existsUnique_local_sq_lift
    hq hf (by omega : 4 ≤ k) hkq hqDvd heq
  have hdominant :
      (13 * k - 6) * d + 18 * (k - 1) ≤
        6 * (p ^ e * q ^ f) ^ 2 := by
    simpa [hgap] using
      two_large_component_whole_gap_dominance he hf hk hkp hkq hgap
  have hneq : i ≠ j := by
    intro hij
    have hqOwnerAtI : q ^ f ∣ n + i := by simpa [hij] using hiq.2.1
    have hno := no_four_solution_of_two_large_prime_components_same_owner_dominance
      hp hq hpq he hf hk hkd hkp hkq hpDvd hqDvd hip.1
      hip.2.1 hqOwnerAtI hdominant
    exact hno heq
  exact ⟨i, j, hip.1, hiq.1, hneq, hip.2.1, hiq.2.1, hip.2.2, hiq.2.2⟩

#print axioms localResidual_square_strict_upper_of_four_solution
#print axioms grouped_owner_square_strict_upper_of_four_solution
#print axioms no_four_solution_of_grouped_owner_dominance
#print axioms no_four_solution_of_two_large_prime_components_same_owner_dominance
#print axioms two_large_component_whole_gap_dominance
#print axioms two_large_prime_whole_gap_has_distinct_local_owners

end Erdos686Variant
end Erdos686
