/- leanprover/lean4:v4.29.1 mathlib v4.29.1 -/
import ErdosProblems.Erdos686CanonicalAlternatingComponents
import ErdosProblems.Erdos686RowDiagonalFourCycleTangent

/-!
# Erdős 686: canonical large-owner four-cycle tangents

This module instantiates the abstract row/diagonal four-cycle tangent theorem
on an actual four-cycle of the canonical above-`k` owner support.  In
particular, all four reduced-binomial coprimality conditions and all four
upper-quotient witnesses are discharged from the canonical data.

The conclusion is still the exact tangent-product versus repeated-owner
crowding dichotomy.  It is not a large-`k` exclusion: a separate global bound
on the four tangent defects, or an exclusion of the crowding alternatives,
is still required.
-/

namespace Erdos686
namespace Erdos686Variant

/-- Every prime divisor of a canonical above-`k` cell is strictly larger
than `k`.  The statement does not require that the cell be nontrivial. -/
theorem canonicalLargeOwnerCell_primeSupport
    {k n d t j i p : ℕ} (data : CanonicalOwnerData k n d t)
    (hp : p.Prime)
    (hpdvd : p ∣ canonicalLargeOwnerCell data j i) :
    k < p := by
  unfold canonicalLargeOwnerCell at hpdvd
  obtain ⟨q, hq, hpq⟩ := (hp.prime.dvd_finset_prod_iff _).mp hpdvd
  by_cases hcell : data.row q = j ∧ data.column q = i
  · simp only [if_pos hcell] at hpq
    have hqPrime := prime_of_mem_factorization_support
      (Finset.mem_filter.mp hq).1
    have hpEq : p = q :=
      (Nat.prime_dvd_prime_iff_eq hp hqPrime).mp
        (hp.dvd_of_dvd_pow hpq)
    simpa [hpEq] using (Finset.mem_filter.mp hq).2
  · simp [hcell] at hpq
    exact (hp.ne_one hpq).elim

/-- A canonical above-`k` cell is coprime to `(k-1)!`. -/
theorem canonicalLargeOwnerCell_coprime_factorial
    {k n d t j i : ℕ} (data : CanonicalOwnerData k n d t) :
    (canonicalLargeOwnerCell data j i).Coprime (k - 1).factorial := by
  exact largePrimeSupport_coprime_factorial
    (fun p hp hpdvd => canonicalLargeOwnerCell_primeSupport data hp hpdvd)

/-- Each reduced right matching coefficient divides `(k-1)!`. -/
theorem reducedMatchingRight_dvd_factorial
    {k i j : ℕ}
    (hi : i ∈ Finset.Icc 1 k) (hj : j ∈ Finset.Icc 1 k) :
    reducedMatchingRight k i j ∣ (k - 1).factorial := by
  obtain ⟨q, _hq, hFi, _hFj⟩ := exists_matchingCommonPrefactor hi hj
  have hFiDvd : localBlockCoefficientNat k i ∣ (k - 1).factorial := by
    rw [← matchingBinomial_mul_localCoefficientNat hi]
    exact dvd_mul_left _ _
  exact dvd_trans ⟨q, by simpa [Nat.mul_comm] using hFi⟩ hFiDvd

/-- Hence an above-`k` owner is coprime to every reduced right matching
coefficient occurring inside the owner square. -/
theorem canonicalLargeOwnerCell_coprime_reducedMatchingRight
    {k n d t j i i' j' : ℕ} (data : CanonicalOwnerData k n d t)
    (hi' : i' ∈ Finset.Icc 1 k) (hj' : j' ∈ Finset.Icc 1 k) :
    (canonicalLargeOwnerCell data j i).Coprime
      (reducedMatchingRight k i' j') := by
  exact (canonicalLargeOwnerCell_coprime_factorial data).coprime_dvd_right
    (reducedMatchingRight_dvd_factorial hi' hj')

/-- Quotient of the original upper term by one canonical large owner. -/
def canonicalLargeOwnerUpperQuotient
    {k n d t : ℕ} (data : CanonicalOwnerData k n d t)
    (e : ℕ × ℕ) : ℕ :=
  (n + d + e.2) / canonicalLargeOwnerCell data e.1 e.2

/-- Every support cell gives an exact upper-quotient factorization. -/
theorem canonicalLargeOwner_upper_quotient_factorization
    {k n d t : ℕ} (data : CanonicalOwnerData k n d t)
    (hfour : 4 ∣ n + d + t) (e : ℕ × ℕ) :
    n + d + e.2 = canonicalLargeOwnerCell data e.1 e.2 *
      canonicalLargeOwnerUpperQuotient data e := by
  have hdvd : canonicalLargeOwnerCell data e.1 e.2 ∣ n + d + e.2 :=
    dvd_trans (canonicalLargeOwnerCell_dvd_upper data)
      (upperTermAfterFour_dvd_original hfour)
  unfold canonicalLargeOwnerUpperQuotient
  exact (Nat.mul_div_cancel' hdvd).symm

/-- Exact two-owner row factorization exposed for the canonical four-cycle
specialization. -/
theorem canonicalLargeOwner_row_pair_factorization
    {k n d t : ℕ} (data : CanonicalOwnerData k n d t)
    {a b : ℕ × ℕ} (hab : a ≠ b)
    (hfibre : canonicalLargeOwnerRowSupport data b.1 = {a, b}) :
    n + b.1 =
      canonicalLargeOwnerCell data a.1 a.2 *
        canonicalLargeOwnerCell data b.1 b.2 *
          canonicalLargeOwnerRowCofactor data b.1 := by
  have hfactor := canonicalLargeOwner_lower_term_factorization data (j := b.1)
  unfold canonicalLargeOwnerRowAggregate at hfactor
  rw [hfibre] at hfactor
  simp only [Finset.prod_insert, Finset.mem_singleton, hab,
    not_false_eq_true, Finset.prod_singleton] at hfactor
  calc
    n + b.1 = canonicalLargeOwnerRowCofactor data b.1 *
        (canonicalLargeOwnerCell data a.1 a.2 *
          canonicalLargeOwnerCell data b.1 b.2) := hfactor
    _ = canonicalLargeOwnerCell data a.1 a.2 *
        canonicalLargeOwnerCell data b.1 b.2 *
          canonicalLargeOwnerRowCofactor data b.1 := by ring

/-- Exact two-owner signed-diagonal factorization exposed for the canonical
four-cycle specialization. -/
theorem canonicalLargeOwner_diagonal_pair_factorization
    {k n d t : ℕ} (data : CanonicalOwnerData k n d t)
    {a b : ℕ × ℕ} (hab : a ≠ b)
    (hk : 1 ≤ k) (hd : k ≤ d) (hfour : 4 ∣ n + d + t)
    (hb : b ∈ canonicalLargeOwnerSupport data)
    (hfibre : canonicalLargeOwnerDiagonalSupport data
      (canonicalOwnerDiagonalIndex k b) = {b, a}) :
    d + b.2 - b.1 =
      canonicalLargeOwnerCell data b.1 b.2 *
        canonicalLargeOwnerCell data a.1 a.2 *
          canonicalLargeOwnerDiagonalCofactor data
            (canonicalOwnerDiagonalIndex k b) := by
  have hbSquare := (canonicalLargeOwnerSupport_spec data hfour).1 b hb
  have hfactor := canonicalLargeOwner_diagonal_term_factorization
    data (h := canonicalOwnerDiagonalIndex k b) hk hd hfour
  unfold canonicalLargeOwnerDiagonalAggregate at hfactor
  rw [hfibre] at hfactor
  simp only [Finset.prod_insert, Finset.mem_singleton, hab.symm,
    not_false_eq_true, Finset.prod_singleton] at hfactor
  rw [centeredDiffTerm_eq_shiftedDifference hk hd hbSquare] at hfactor
  calc
    d + b.2 - b.1 =
        canonicalLargeOwnerDiagonalCofactor data
            (canonicalOwnerDiagonalIndex k b) *
          (canonicalLargeOwnerCell data b.1 b.2 *
            canonicalLargeOwnerCell data a.1 a.2) := hfactor
    _ = canonicalLargeOwnerCell data b.1 b.2 *
        canonicalLargeOwnerCell data a.1 a.2 *
          canonicalLargeOwnerDiagonalCofactor data
            (canonicalOwnerDiagonalIndex k b) := by ring

/-- The normalized owner-square congruence at an actual canonical large-owner
support cell. -/
theorem canonicalLargeOwner_normalized_square_dvd
    {k n d t : ℕ} (data : CanonicalOwnerData k n d t)
    (hd : k ≤ d) (hfour : 4 ∣ n + d + t)
    (heq : blockProduct k (n + d) = 4 * blockProduct k n)
    {e : ℕ × ℕ} (he : e ∈ canonicalLargeOwnerSupport data) :
    ((canonicalLargeOwnerCell data e.1 e.2 : ℤ) ^ 2) ∣
      normalizedMatchingForm
        (reducedMatchingLeft k e.2 e.1 : ℤ)
        (reducedMatchingRight k e.2 e.1 : ℤ)
        ((-1 : ℤ) ^ (e.2 + e.1))
        ((d + e.2 - e.1 : ℕ) : ℤ)
        ((n + e.1 : ℕ) : ℤ) := by
  have hsquare := (canonicalLargeOwnerSupport_spec data hfour).1 e he
  apply matched_owner_normalized_square_dvd hd hsquare.2 hsquare.1
  · exact fun p hp hpdvd =>
      canonicalLargeOwnerCell_primeSupport data hp hpdvd
  · exact canonicalLargeOwnerCell_dvd_lower data
  · exact dvd_trans (canonicalLargeOwnerCell_dvd_upper data)
      (upperTermAfterFour_dvd_original hfour)
  · exact heq

/-- At a support cell, the original upper term is exactly the lower term plus
the nonnegative shifted-diagonal term. -/
theorem canonicalLargeOwner_upper_eq_lower_add_diagonal
    {k n d t : ℕ} (data : CanonicalOwnerData k n d t)
    (hd : k ≤ d) (hfour : 4 ∣ n + d + t)
    {e : ℕ × ℕ} (he : e ∈ canonicalLargeOwnerSupport data) :
    n + d + e.2 = (n + e.1) + (d + e.2 - e.1) := by
  have heSquare := (canonicalLargeOwnerSupport_spec data hfour).1 e he
  have hle : e.1 ≤ d + e.2 := by
    have hej := (Finset.mem_Icc.mp heSquare.1).2
    omega
  omega

/-- The actual first-tangent defect at one canonical support cell, relative
to its other owner in the same two-owner row. -/
def canonicalLargeOwnerFourCycleTangent
    {k n d t : ℕ} (data : CanonicalOwnerData k n d t)
    (e rowPartner : ℕ × ℕ) : ℤ :=
  fourCycleTangentDefect
    (reducedMatchingRight k e.2 e.1 : ℤ)
    (4 * ((-1 : ℤ) ^ (e.2 + e.1)) *
      (reducedMatchingLeft k e.2 e.1 : ℤ))
    (canonicalLargeOwnerUpperQuotient data e : ℤ)
    (canonicalLargeOwnerCell data rowPartner.1 rowPartner.2 : ℤ)
    (canonicalLargeOwnerRowCofactor data e.1 : ℤ)

/-- Canonical instantiation of the additive/tangent four-cycle theorem.

The owner labeling is `A=b₁`, `B=a₁`, `C=a₂`, `D=b₂`.  Thus the
two exact rows are `A*B` and `C*D`, while the two exact signed diagonals are
`A*C` and `B*D`.  The theorem discharges all four normalized-square,
coefficient-coprimality, and upper-quotient hypotheses from the canonical
data itself. -/
theorem canonicalLargeOwnerFourCycle_normalizedSquares_tangentProduct_or_crowding
    {k n d t : ℕ} (data : CanonicalOwnerData k n d t)
    (hd : k ≤ d) (hfour : 4 ∣ n + d + t)
    (heq : blockProduct k (n + d) = 4 * blockProduct k n)
    (C : CanonicalLargeOwnerFourCycleWitness data) :
    let A := canonicalLargeOwnerCell data C.b₁.1 C.b₁.2
    let B := canonicalLargeOwnerCell data C.a₁.1 C.a₁.2
    let C₀ := canonicalLargeOwnerCell data C.a₂.1 C.a₂.2
    let D := canonicalLargeOwnerCell data C.b₂.1 C.b₂.2
    A * B * C₀ * D ≤
        (canonicalLargeOwnerFourCycleTangent data C.b₁ C.a₁ *
          canonicalLargeOwnerFourCycleTangent data C.a₁ C.b₁ *
          canonicalLargeOwnerFourCycleTangent data C.a₂ C.b₂ *
          canonicalLargeOwnerFourCycleTangent data C.b₂ C.a₂).natAbs ∨
      (((A * B * C₀ * D * B : ℕ) : ℤ) ∣
          ((d + C.b₁.2 - C.b₁.1 : ℕ) : ℤ) *
            ((d + C.b₂.2 - C.b₂.1 : ℕ) : ℤ)) ∨
       (((A * B * C₀ * D * A : ℕ) : ℤ) ∣
          ((d + C.b₁.2 - C.b₁.1 : ℕ) : ℤ) *
            ((d + C.b₂.2 - C.b₂.1 : ℕ) : ℤ)) ∨
       (((A * B * C₀ * D * D : ℕ) : ℤ) ∣
          ((d + C.b₁.2 - C.b₁.1 : ℕ) : ℤ) *
            ((d + C.b₂.2 - C.b₂.1 : ℕ) : ℤ)) ∨
       (((A * B * C₀ * D * C₀ : ℕ) : ℤ) ∣
          ((d + C.b₁.2 - C.b₁.1 : ℕ) : ℤ) *
            ((d + C.b₂.2 - C.b₂.1 : ℕ) : ℤ)) := by
  dsimp only
  have hspec := canonicalLargeOwnerSupport_spec data hfour
  have ha₁Square := hspec.1 C.a₁ C.mem_a₁
  have hb₁Square := hspec.1 C.b₁ C.mem_b₁
  have ha₂Square := hspec.1 C.a₂ C.mem_a₂
  have hb₂Square := hspec.1 C.b₂ C.mem_b₂
  have hk : 1 ≤ k := (Finset.mem_Icc.mp hb₁Square.1).1.trans
    (Finset.mem_Icc.mp hb₁Square.1).2
  have hrow₁ := canonicalLargeOwner_row_pair_factorization data
    C.a₁_ne_b₁ C.row₁
  have hrow₂ := canonicalLargeOwner_row_pair_factorization data
    C.a₂_ne_b₂ C.row₂
  have hdiag₁ := canonicalLargeOwner_diagonal_pair_factorization data
    C.b₁_ne_a₂.symm hk hd hfour C.mem_b₁ C.diagonal₁
  have hdiag₂ := canonicalLargeOwner_diagonal_pair_factorization data
    C.b₂_ne_a₁.symm hk hd hfour C.mem_b₂ C.diagonal₂
  have ha₁RowMem : C.a₁ ∈ canonicalLargeOwnerRowSupport data C.b₁.1 := by
    rw [C.row₁]
    simp
  have ha₂RowMem : C.a₂ ∈ canonicalLargeOwnerRowSupport data C.b₂.1 := by
    rw [C.row₂]
    simp
  have ha₁Row : C.a₁.1 = C.b₁.1 :=
    (Finset.mem_filter.mp ha₁RowMem).2
  have ha₂Row : C.a₂.1 = C.b₂.1 :=
    (Finset.mem_filter.mp ha₂RowMem).2
  have ha₂DiagMem : C.a₂ ∈ canonicalLargeOwnerDiagonalSupport data
      (canonicalOwnerDiagonalIndex k C.b₁) := by
    rw [C.diagonal₁]
    simp
  have ha₁DiagMem : C.a₁ ∈ canonicalLargeOwnerDiagonalSupport data
      (canonicalOwnerDiagonalIndex k C.b₂) := by
    rw [C.diagonal₂]
    simp
  have ha₂DiagIndex : canonicalOwnerDiagonalIndex k C.a₂ =
      canonicalOwnerDiagonalIndex k C.b₁ :=
    (Finset.mem_filter.mp ha₂DiagMem).2
  have ha₁DiagIndex : canonicalOwnerDiagonalIndex k C.a₁ =
      canonicalOwnerDiagonalIndex k C.b₂ :=
    (Finset.mem_filter.mp ha₁DiagMem).2
  have ha₂Diag : d + C.a₂.2 - C.a₂.1 =
      d + C.b₁.2 - C.b₁.1 := by
    rw [← centeredDiffTerm_eq_shiftedDifference hk hd ha₂Square,
      ← centeredDiffTerm_eq_shiftedDifference hk hd hb₁Square,
      ha₂DiagIndex]
  have ha₁Diag : d + C.a₁.2 - C.a₁.1 =
      d + C.b₂.2 - C.b₂.1 := by
    rw [← centeredDiffTerm_eq_shiftedDifference hk hd ha₁Square,
      ← centeredDiffTerm_eq_shiftedDifference hk hd hb₂Square,
      ha₁DiagIndex]
  have hu_a₁ := canonicalLargeOwner_upper_quotient_factorization
    data hfour C.a₁
  have hu_b₁ := canonicalLargeOwner_upper_quotient_factorization
    data hfour C.b₁
  have hu_a₂ := canonicalLargeOwner_upper_quotient_factorization
    data hfour C.a₂
  have hu_b₂ := canonicalLargeOwner_upper_quotient_factorization
    data hfour C.b₂
  have hadd_a₁ := canonicalLargeOwner_upper_eq_lower_add_diagonal
    data hd hfour C.mem_a₁
  have hadd_b₁ := canonicalLargeOwner_upper_eq_lower_add_diagonal
    data hd hfour C.mem_b₁
  have hadd_a₂ := canonicalLargeOwner_upper_eq_lower_add_diagonal
    data hd hfour C.mem_a₂
  have hadd_b₂ := canonicalLargeOwner_upper_eq_lower_add_diagonal
    data hd hfour C.mem_b₂
  have hsquare_a₁ := canonicalLargeOwner_normalized_square_dvd
    data hd hfour heq C.mem_a₁
  have hsquare_b₁ := canonicalLargeOwner_normalized_square_dvd
    data hd hfour heq C.mem_b₁
  have hsquare_a₂ := canonicalLargeOwner_normalized_square_dvd
    data hd hfour heq C.mem_a₂
  have hsquare_b₂ := canonicalLargeOwner_normalized_square_dvd
    data hd hfour heq C.mem_b₂
  have hA : (canonicalLargeOwnerCell data C.b₁.1 C.b₁.2 : ℤ) ≠ 0 := by
    have hnat : canonicalLargeOwnerCell data C.b₁.1 C.b₁.2 ≠ 0 := by
      have := hspec.2.1 C.b₁ C.mem_b₁
      omega
    exact_mod_cast hnat
  have hB : (canonicalLargeOwnerCell data C.a₁.1 C.a₁.2 : ℤ) ≠ 0 := by
    have hnat : canonicalLargeOwnerCell data C.a₁.1 C.a₁.2 ≠ 0 := by
      have := hspec.2.1 C.a₁ C.mem_a₁
      omega
    exact_mod_cast hnat
  have hC : (canonicalLargeOwnerCell data C.a₂.1 C.a₂.2 : ℤ) ≠ 0 := by
    have hnat : canonicalLargeOwnerCell data C.a₂.1 C.a₂.2 ≠ 0 := by
      have := hspec.2.1 C.a₂ C.mem_a₂
      omega
    exact_mod_cast hnat
  have hD : (canonicalLargeOwnerCell data C.b₂.1 C.b₂.2 : ℤ) ≠ 0 := by
    have hnat : canonicalLargeOwnerCell data C.b₂.1 C.b₂.2 ≠ 0 := by
      have := hspec.2.1 C.b₂ C.mem_b₂
      omega
    exact_mod_cast hnat
  have hcop₁₁ : IsCoprime
      (canonicalLargeOwnerCell data C.a₁.1 C.a₁.2 : ℤ)
      ((reducedMatchingRight k C.b₁.2 C.b₁.1 : ℤ) *
        canonicalLargeOwnerCell data C.a₂.1 C.a₂.2) := by
    exact ((canonicalLargeOwnerCell_coprime_reducedMatchingRight data
      hb₁Square.2 hb₁Square.1).mul_right
        (canonicalLargeOwnerCells_pairwise_coprime data C.a₁_ne_a₂)).isCoprime
  have hcop₁₂ : IsCoprime
      (canonicalLargeOwnerCell data C.b₁.1 C.b₁.2 : ℤ)
      ((reducedMatchingRight k C.a₁.2 C.a₁.1 : ℤ) *
        canonicalLargeOwnerCell data C.b₂.1 C.b₂.2) := by
    exact ((canonicalLargeOwnerCell_coprime_reducedMatchingRight data
      ha₁Square.2 ha₁Square.1).mul_right
        (canonicalLargeOwnerCells_pairwise_coprime data C.b₁_ne_b₂)).isCoprime
  have hcop₂₁ : IsCoprime
      (canonicalLargeOwnerCell data C.b₂.1 C.b₂.2 : ℤ)
      ((reducedMatchingRight k C.a₂.2 C.a₂.1 : ℤ) *
        canonicalLargeOwnerCell data C.b₁.1 C.b₁.2) := by
    exact ((canonicalLargeOwnerCell_coprime_reducedMatchingRight data
      ha₂Square.2 ha₂Square.1).mul_right
        (canonicalLargeOwnerCells_pairwise_coprime data C.b₁_ne_b₂.symm)).isCoprime
  have hcop₂₂ : IsCoprime
      (canonicalLargeOwnerCell data C.a₂.1 C.a₂.2 : ℤ)
      ((reducedMatchingRight k C.b₂.2 C.b₂.1 : ℤ) *
        canonicalLargeOwnerCell data C.a₁.1 C.a₁.2) := by
    exact ((canonicalLargeOwnerCell_coprime_reducedMatchingRight data
      hb₂Square.2 hb₂Square.1).mul_right
        (canonicalLargeOwnerCells_pairwise_coprime data C.a₁_ne_a₂.symm)).isCoprime
  have hx₁ : ((n + C.b₁.1 : ℕ) : ℤ) =
      (canonicalLargeOwnerCell data C.b₁.1 C.b₁.2 : ℤ) *
        canonicalLargeOwnerCell data C.a₁.1 C.a₁.2 *
          canonicalLargeOwnerRowCofactor data C.b₁.1 := by
    exact_mod_cast (by
      simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hrow₁)
  have hx₂ : ((n + C.b₂.1 : ℕ) : ℤ) =
      (canonicalLargeOwnerCell data C.a₂.1 C.a₂.2 : ℤ) *
        canonicalLargeOwnerCell data C.b₂.1 C.b₂.2 *
          canonicalLargeOwnerRowCofactor data C.b₂.1 := by
    exact_mod_cast hrow₂
  have hy₁ : ((d + C.b₁.2 - C.b₁.1 : ℕ) : ℤ) =
      (canonicalLargeOwnerCell data C.b₁.1 C.b₁.2 : ℤ) *
        canonicalLargeOwnerCell data C.a₂.1 C.a₂.2 *
          canonicalLargeOwnerDiagonalCofactor data
            (canonicalOwnerDiagonalIndex k C.b₁) := by
    exact_mod_cast hdiag₁
  have hy₂ : ((d + C.b₂.2 - C.b₂.1 : ℕ) : ℤ) =
      (canonicalLargeOwnerCell data C.a₁.1 C.a₁.2 : ℤ) *
        canonicalLargeOwnerCell data C.b₂.1 C.b₂.2 *
          canonicalLargeOwnerDiagonalCofactor data
            (canonicalOwnerDiagonalIndex k C.b₂) := by
    exact_mod_cast (by
      simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hdiag₂)
  have castUpper : ∀ e : ℕ × ℕ,
      n + d + e.2 = canonicalLargeOwnerCell data e.1 e.2 *
          canonicalLargeOwnerUpperQuotient data e →
      ((n + d + e.2 : ℕ) : ℤ) =
        (canonicalLargeOwnerCell data e.1 e.2 : ℤ) *
          canonicalLargeOwnerUpperQuotient data e := by
    intro e h
    exact_mod_cast h
  have castAdd : ∀ e : ℕ × ℕ,
      n + d + e.2 = (n + e.1) + (d + e.2 - e.1) →
      ((n + d + e.2 : ℕ) : ℤ) =
        ((n + e.1 : ℕ) : ℤ) + ((d + e.2 - e.1 : ℕ) : ℤ) := by
    intro e h
    exact_mod_cast h
  have hadd_a₁' : ((n + d + C.a₁.2 : ℕ) : ℤ) =
      ((n + C.b₁.1 : ℕ) : ℤ) +
        ((d + C.b₂.2 - C.b₂.1 : ℕ) : ℤ) := by
    have h := castAdd C.a₁ hadd_a₁
    rw [ha₁Diag, ha₁Row] at h
    exact h
  have hadd_a₂' : ((n + d + C.a₂.2 : ℕ) : ℤ) =
      ((n + C.b₂.1 : ℕ) : ℤ) +
        ((d + C.b₁.2 - C.b₁.1 : ℕ) : ℤ) := by
    have h := castAdd C.a₂ hadd_a₂
    rw [ha₂Diag, ha₂Row] at h
    exact h
  have hsquare_a₁' :
      ((canonicalLargeOwnerCell data C.a₁.1 C.a₁.2 : ℤ) ^ 2) ∣
        normalizedMatchingForm
          (reducedMatchingLeft k C.a₁.2 C.a₁.1 : ℤ)
          (reducedMatchingRight k C.a₁.2 C.a₁.1 : ℤ)
          ((-1 : ℤ) ^ (C.a₁.2 + C.a₁.1))
          ((d + C.b₂.2 - C.b₂.1 : ℕ) : ℤ)
          ((n + C.b₁.1 : ℕ) : ℤ) := by
    have hyEq : ((d + C.a₁.2 - C.a₁.1 : ℕ) : ℤ) =
        ((d + C.b₂.2 - C.b₂.1 : ℕ) : ℤ) := by
      exact_mod_cast ha₁Diag
    have hxEq : ((n + C.a₁.1 : ℕ) : ℤ) =
        ((n + C.b₁.1 : ℕ) : ℤ) := by
      exact_mod_cast congrArg (fun x => n + x) ha₁Row
    rw [← hyEq, ← hxEq]
    exact hsquare_a₁
  have hsquare_a₂' :
      ((canonicalLargeOwnerCell data C.a₂.1 C.a₂.2 : ℤ) ^ 2) ∣
        normalizedMatchingForm
          (reducedMatchingLeft k C.a₂.2 C.a₂.1 : ℤ)
          (reducedMatchingRight k C.a₂.2 C.a₂.1 : ℤ)
          ((-1 : ℤ) ^ (C.a₂.2 + C.a₂.1))
          ((d + C.b₁.2 - C.b₁.1 : ℕ) : ℤ)
          ((n + C.b₂.1 : ℕ) : ℤ) := by
    have hyEq : ((d + C.a₂.2 - C.a₂.1 : ℕ) : ℤ) =
        ((d + C.b₁.2 - C.b₁.1 : ℕ) : ℤ) := by
      exact_mod_cast ha₂Diag
    have hxEq : ((n + C.a₂.1 : ℕ) : ℤ) =
        ((n + C.b₂.1 : ℕ) : ℤ) := by
      exact_mod_cast congrArg (fun x => n + x) ha₂Row
    rw [← hyEq, ← hxEq]
    exact hsquare_a₂
  have hresult :=
    fourCycle_normalizedSquares_tangentProduct_or_diagonalProduct_ownerCrowding
      hA hB hC hD hx₁ hx₂ hy₁ hy₂
      (castUpper C.b₁ hu_b₁) (castUpper C.a₁ hu_a₁)
      (castUpper C.a₂ hu_a₂) (castUpper C.b₂ hu_b₂)
      (castAdd C.b₁ hadd_b₁) hadd_a₁'
      hadd_a₂' (castAdd C.b₂ hadd_b₂)
      hcop₁₁ hcop₁₂ hcop₂₁ hcop₂₂
      hsquare_b₁ hsquare_a₁' hsquare_a₂' hsquare_b₂
  simpa [canonicalLargeOwnerFourCycleTangent, ha₁Row, ha₂Row] using hresult

#print axioms canonicalLargeOwnerCell_primeSupport
#print axioms canonicalLargeOwnerCell_coprime_factorial
#print axioms reducedMatchingRight_dvd_factorial
#print axioms canonicalLargeOwnerCell_coprime_reducedMatchingRight
#print axioms canonicalLargeOwner_upper_quotient_factorization
#print axioms canonicalLargeOwner_row_pair_factorization
#print axioms canonicalLargeOwner_diagonal_pair_factorization
#print axioms canonicalLargeOwner_normalized_square_dvd
#print axioms canonicalLargeOwner_upper_eq_lower_add_diagonal
#print axioms canonicalLargeOwnerFourCycle_normalizedSquares_tangentProduct_or_crowding

end Erdos686Variant
end Erdos686
