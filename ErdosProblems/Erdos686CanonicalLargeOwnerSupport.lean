/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import ErdosProblems.Erdos686CanonicalOwnerMass
import ErdosProblems.Erdos686CanonicalOwnerMatrix
import ErdosProblems.Erdos686CollinearSupport

/-!
# Erdős 686: exact canonical large-prime owner support

This module projects the canonical owner matrix to prime bases strictly above
`k`.  Unlike the cleaned all-prime cells, the projected cells carry the full
lower-block exponent, so their total product is exactly `kLargePart`.

No graph connectivity or minimum-degree property is used.  The final theorem
extracts a fixed-column row-diagonal matching from the exact support.  The `k`
columns partition all owner mass, giving the sharp universal multiplicative
cover inequality `M ≤ X^k` for one extracted matching.
-/

namespace Erdos686
namespace Erdos686Variant

open scoped BigOperators

/-- Prime bases above `k` occurring in `x`, represented directly as a filter
of the factorization support. -/
def canonicalLargePrimeIndices (k x : ℕ) : Finset ℕ :=
  x.factorization.support.filter (fun p => k < p)

theorem kLargePart_eq_prod_canonicalLargePrimeIndices (k x : ℕ) :
    kLargePart k x =
      ∏ p ∈ canonicalLargePrimeIndices k x, p ^ x.factorization p := by
  unfold kLargePart canonicalLargePrimeIndices
  rw [Finsupp.prod]
  apply Finset.prod_congr
  · ext p
    simp
  · intro p hp
    simp only [Finsupp.filter_apply]
    rw [if_pos (Finset.mem_filter.mp hp).2]

/-- Above `k`, canonical cleaning omits no exponent: the residual is supported
entirely on primes dividing `(k-1)!`. -/
theorem canonicalOwnerExponent_eq_block_factorization_of_large
    {k n d t p : ℕ} (data : CanonicalOwnerData k n d t)
    (hp : p.Prime) (hkp : k < p) :
    data.exponent p = (blockProduct k n).factorization p := by
  have hfactorial : (k - 1).factorial.factorization p = 0 :=
    Nat.factorization_factorial_eq_zero_of_lt (by omega)
  have hres := data.residual_le p hp
  rw [hfactorial] at hres
  have hle := canonicalOwnerExponent_le_block_factorization data hp
  omega

/-- Full large-prime mass assigned to one canonical owner cell. -/
def canonicalLargeOwnerCell
    {k n d t : ℕ} (data : CanonicalOwnerData k n d t)
    (j i : ℕ) : ℕ :=
  ∏ p ∈ canonicalLargePrimeIndices k (blockProduct k n),
    if data.row p = j ∧ data.column p = i
    then p ^ (blockProduct k n).factorization p
    else 1

/-- The finite nontrivial large-prime support inside the owner square. -/
def canonicalLargeOwnerSupport
    {k n d t : ℕ} (data : CanonicalOwnerData k n d t) :
    Finset (ℕ × ℕ) :=
  ((Finset.Icc 1 k).product (Finset.Icc 1 k)).filter
    (fun e => canonicalLargeOwnerCell data e.1 e.2 ≠ 1)

private theorem large_prime_power_pairwise_coprime
    {x p q : ℕ}
    (hp : p ∈ x.factorization.support)
    (hq : q ∈ x.factorization.support)
    (hpq : p ≠ q) :
    Nat.Coprime (p ^ x.factorization p) (q ^ x.factorization q) := by
  have hpPrime := prime_of_mem_factorization_support hp
  have hqPrime := prime_of_mem_factorization_support hq
  exact Nat.Coprime.pow (x.factorization p) (x.factorization q)
    (hpPrime.coprime_iff_not_dvd.mpr (by
      intro hpdq
      exact hpq ((Nat.dvd_prime hqPrime).mp hpdq |>.resolve_left hpPrime.ne_one)))

private theorem finset_prod_dvd_of_pairwise_coprime_nat
    {ι : Type*}
    (s : Finset ι) (f : ι → ℕ) (z : ℕ)
    (hpair : (s : Set ι).Pairwise (Function.onFun Nat.Coprime f))
    (hdvd : ∀ x ∈ s, f x ∣ z) :
    (∏ x ∈ s, f x) ∣ z := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.prod_insert ha]
      apply Nat.Coprime.mul_dvd_of_dvd_of_dvd
      · apply Nat.Coprime.prod_right
        intro b hb
        exact hpair (by simp) (by simp [hb])
          (Ne.symm (ne_of_mem_of_not_mem hb ha))
      · exact hdvd a (by simp)
      · apply ih
        · intro x hx y hy hxy
          exact hpair (by simp [hx]) (by simp [hy]) hxy
        · intro x hx
          exact hdvd x (by simp [hx])

private theorem large_prime_product_dvd
    {k x z : ℕ} (f : ℕ → ℕ)
    (hfactor : ∀ p ∈ canonicalLargePrimeIndices k x,
      f p = 1 ∨ f p = p ^ x.factorization p)
    (hdvd : ∀ p ∈ canonicalLargePrimeIndices k x, f p ∣ z) :
    (∏ p ∈ canonicalLargePrimeIndices k x, f p) ∣ z := by
  classical
  let s := canonicalLargePrimeIndices k x
  have hpair : (s : Set ℕ).Pairwise (Function.onFun Nat.Coprime f) := by
    intro p hp q hq hpq
    change Nat.Coprime (f p) (f q)
    rcases hfactor p hp with hpOne | hpPow <;>
      rcases hfactor q hq with hqOne | hqPow
    · simp [hpOne]
    · simp [hpOne]
    · simp [hqOne]
    · rw [hpPow, hqPow]
      exact large_prime_power_pairwise_coprime
        (Finset.mem_filter.mp hp).1 (Finset.mem_filter.mp hq).1 hpq
  exact finset_prod_dvd_of_pairwise_coprime_nat s f z hpair
    (by intro p hp; exact hdvd p hp)

theorem canonicalLargeOwnerCell_dvd_lower
    {k n d t j i : ℕ} (data : CanonicalOwnerData k n d t) :
    canonicalLargeOwnerCell data j i ∣ n + j := by
  classical
  unfold canonicalLargeOwnerCell
  apply large_prime_product_dvd
  · intro p hp
    by_cases hcell : data.row p = j ∧ data.column p = i
    · exact Or.inr (by simp [hcell])
    · exact Or.inl (by simp [hcell])
  · intro p hp
    have hpSupport := (Finset.mem_filter.mp hp).1
    have hpPrime := prime_of_mem_factorization_support hpSupport
    have hkp := (Finset.mem_filter.mp hp).2
    by_cases hcell : data.row p = j ∧ data.column p = i
    · simp only [if_pos hcell]
      rw [← canonicalOwnerExponent_eq_block_factorization_of_large
        data hpPrime hkp]
      simpa [hcell.1] using data.lower_dvd p hpPrime
    · simp [hcell]

theorem canonicalLargeOwnerCell_dvd_upper
    {k n d t j i : ℕ} (data : CanonicalOwnerData k n d t) :
    canonicalLargeOwnerCell data j i ∣ upperTermAfterFour n d t i := by
  classical
  unfold canonicalLargeOwnerCell
  apply large_prime_product_dvd
  · intro p hp
    by_cases hcell : data.row p = j ∧ data.column p = i
    · exact Or.inr (by simp [hcell])
    · exact Or.inl (by simp [hcell])
  · intro p hp
    have hpSupport := (Finset.mem_filter.mp hp).1
    have hpPrime := prime_of_mem_factorization_support hpSupport
    have hkp := (Finset.mem_filter.mp hp).2
    by_cases hcell : data.row p = j ∧ data.column p = i
    · simp only [if_pos hcell]
      rw [← canonicalOwnerExponent_eq_block_factorization_of_large
        data hpPrime hkp]
      simpa [hcell.2] using data.upper_dvd p hpPrime
    · simp [hcell]

theorem canonicalLargeOwnerCell_dvd_shiftedDifference
    {k n d t j i : ℕ} (data : CanonicalOwnerData k n d t)
    (hfour : 4 ∣ n + d + t) :
    canonicalLargeOwnerCell data j i ∣ d + i - j := by
  have hlower := canonicalLargeOwnerCell_dvd_lower data (j := j) (i := i)
  have hupper := dvd_trans
    (canonicalLargeOwnerCell_dvd_upper data (j := j) (i := i))
    (upperTermAfterFour_dvd_original hfour)
  have hsub := Nat.dvd_sub hupper hlower
  have hdiff : (n + d + i) - (n + j) = d + i - j := by omega
  rwa [hdiff] at hsub

theorem canonicalLargeOwnerCells_pairwise_coprime
    {k n d t j i j' i' : ℕ}
    (data : CanonicalOwnerData k n d t)
    (hne : (j, i) ≠ (j', i')) :
    Nat.Coprime (canonicalLargeOwnerCell data j i)
      (canonicalLargeOwnerCell data j' i') := by
  classical
  unfold canonicalLargeOwnerCell
  apply Nat.Coprime.prod_left
  intro p hp
  apply Nat.Coprime.prod_right
  intro q hq
  by_cases hpCell : data.row p = j ∧ data.column p = i
  · by_cases hqCell : data.row q = j' ∧ data.column q = i'
    · rw [if_pos hpCell, if_pos hqCell]
      have hpPrime := prime_of_mem_factorization_support
        (Finset.mem_filter.mp hp).1
      have hqPrime := prime_of_mem_factorization_support
        (Finset.mem_filter.mp hq).1
      have hpq : p ≠ q := by
        intro hpq
        subst q
        apply hne
        exact Prod.ext (hpCell.1.symm.trans hqCell.1)
          (hpCell.2.symm.trans hqCell.2)
      exact Nat.Coprime.pow _ _
        (hpPrime.coprime_iff_not_dvd.mpr (by
          intro hpdq
          exact hpq
            ((Nat.dvd_prime hqPrime).mp hpdq |>.resolve_left hpPrime.ne_one)))
    · simp [hqCell]
  · simp [hpCell]

theorem canonicalLargeOwner_allCells_eq_kLargePart
    {k n d t : ℕ} (data : CanonicalOwnerData k n d t) :
    (∏ j ∈ Finset.Icc 1 k,
      ∏ i ∈ Finset.Icc 1 k, canonicalLargeOwnerCell data j i) =
        kLargePart k (blockProduct k n) := by
  classical
  rw [kLargePart_eq_prod_canonicalLargePrimeIndices]
  unfold canonicalLargeOwnerCell
  calc
    (∏ j ∈ Finset.Icc 1 k,
        ∏ i ∈ Finset.Icc 1 k,
          ∏ p ∈ canonicalLargePrimeIndices k (blockProduct k n),
            if data.row p = j ∧ data.column p = i
            then p ^ (blockProduct k n).factorization p else 1) =
      ∏ j ∈ Finset.Icc 1 k,
        ∏ p ∈ canonicalLargePrimeIndices k (blockProduct k n),
          ∏ i ∈ Finset.Icc 1 k,
            if data.row p = j ∧ data.column p = i
            then p ^ (blockProduct k n).factorization p else 1 := by
              apply Finset.prod_congr rfl
              intro j hj
              rw [Finset.prod_comm]
    _ = ∏ p ∈ canonicalLargePrimeIndices k (blockProduct k n),
        ∏ j ∈ Finset.Icc 1 k,
          ∏ i ∈ Finset.Icc 1 k,
            if data.row p = j ∧ data.column p = i
            then p ^ (blockProduct k n).factorization p else 1 := by
              rw [Finset.prod_comm]
    _ = ∏ p ∈ canonicalLargePrimeIndices k (blockProduct k n),
        p ^ (blockProduct k n).factorization p := by
      apply Finset.prod_congr rfl
      intro p hp
      have hpPrime := prime_of_mem_factorization_support
        (Finset.mem_filter.mp hp).1
      rw [Finset.prod_eq_single (data.row p)]
      · rw [Finset.prod_eq_single (data.column p)]
        · simp
        · intro i hi hine
          simp [Ne.symm hine]
        · exact fun hnot => (hnot (data.column_mem p hpPrime)).elim
      · intro j hj hjne
        simp [Ne.symm hjne]
      · exact fun hnot => (hnot (data.row_mem p hpPrime)).elim

theorem canonicalLargeOwnerSupport_product_eq_kLargePart
    {k n d t : ℕ} (data : CanonicalOwnerData k n d t) :
    (∏ e ∈ canonicalLargeOwnerSupport data,
      canonicalLargeOwnerCell data e.1 e.2) =
        kLargePart k (blockProduct k n) := by
  classical
  rw [canonicalLargeOwnerSupport, Finset.prod_filter]
  calc
    (∏ e ∈ (Finset.Icc 1 k).product (Finset.Icc 1 k),
        if canonicalLargeOwnerCell data e.1 e.2 ≠ 1
        then canonicalLargeOwnerCell data e.1 e.2 else 1) =
      ∏ e ∈ (Finset.Icc 1 k).product (Finset.Icc 1 k),
        canonicalLargeOwnerCell data e.1 e.2 := by
          apply Finset.prod_congr rfl
          intro e he
          split <;> simp_all
    _ = ∏ j ∈ Finset.Icc 1 k,
        ∏ i ∈ Finset.Icc 1 k, canonicalLargeOwnerCell data j i := by
          exact Finset.prod_product _ _ _
    _ = kLargePart k (blockProduct k n) :=
      canonicalLargeOwner_allCells_eq_kLargePart data

/-- Exact support package: square containment, nontriviality, lower and
diagonal divisibility, pairwise coprimality, and total mass equality. -/
theorem canonicalLargeOwnerSupport_spec
    {k n d t : ℕ} (data : CanonicalOwnerData k n d t)
    (hfour : 4 ∣ n + d + t) :
    (∀ e ∈ canonicalLargeOwnerSupport data,
      e.1 ∈ Finset.Icc 1 k ∧ e.2 ∈ Finset.Icc 1 k) ∧
    (∀ e ∈ canonicalLargeOwnerSupport data,
      1 < canonicalLargeOwnerCell data e.1 e.2) ∧
    (∀ e ∈ canonicalLargeOwnerSupport data,
      canonicalLargeOwnerCell data e.1 e.2 ∣ n + e.1) ∧
    (∀ e ∈ canonicalLargeOwnerSupport data,
      canonicalLargeOwnerCell data e.1 e.2 ∣ d + e.2 - e.1) ∧
    ((canonicalLargeOwnerSupport data : Set (ℕ × ℕ)).Pairwise
      (Function.onFun Nat.Coprime
        (fun e => canonicalLargeOwnerCell data e.1 e.2))) ∧
    (∏ e ∈ canonicalLargeOwnerSupport data,
      canonicalLargeOwnerCell data e.1 e.2) =
        kLargePart k (blockProduct k n) := by
  classical
  refine ⟨?_, ?_, ?_, ?_, ?_,
    canonicalLargeOwnerSupport_product_eq_kLargePart data⟩
  · intro e he
    exact Finset.mem_product.mp (Finset.mem_filter.mp he).1
  · intro e he
    have hne := (Finset.mem_filter.mp he).2
    have hpos : 0 < canonicalLargeOwnerCell data e.1 e.2 := by
      unfold canonicalLargeOwnerCell
      apply Finset.prod_pos
      intro p hp
      split
      · exact pow_pos (prime_of_mem_factorization_support
          (Finset.mem_filter.mp hp).1).pos _
      · norm_num
    omega
  · intro e he
    exact canonicalLargeOwnerCell_dvd_lower data
  · intro e he
    exact canonicalLargeOwnerCell_dvd_shiftedDifference data hfour
  · intro e he f hf hef
    exact canonicalLargeOwnerCells_pairwise_coprime data hef

/-- Every row and every signed diagonal contains at most `k` nontrivial
large-owner cells.  These are pure square-capacity bounds, with no graph
regularity assumption. -/
theorem canonicalLargeOwnerSupport_row_diagonal_capacity
    {k n d t : ℕ} (data : CanonicalOwnerData k n d t) :
    (∀ j,
      ((canonicalLargeOwnerSupport data).filter (fun e => e.1 = j)).card ≤ k) ∧
    (∀ rho : ℤ,
      ((canonicalLargeOwnerSupport data).filter
        (fun e => ownerCellOffset e = rho)).card ≤ k) := by
  classical
  constructor
  · intro j
    have hle := Finset.card_le_card_of_injOn
      (fun e : ℕ × ℕ => e.2)
      (s := (canonicalLargeOwnerSupport data).filter (fun e => e.1 = j))
      (t := Finset.Icc 1 k) ?_ ?_
    · simpa [Nat.card_Icc] using hle
    · intro e he
      have heSupport := (Finset.mem_filter.mp he).1
      exact (Finset.mem_product.mp
        (Finset.mem_filter.mp heSupport).1).2
    · intro a ha b hb hcol
      have harow := (Finset.mem_filter.mp ha).2
      have hbrow := (Finset.mem_filter.mp hb).2
      exact Prod.ext (harow.trans hbrow.symm) hcol
  · intro rho
    have hle := Finset.card_le_card_of_injOn
      (fun e : ℕ × ℕ => e.1)
      (s := (canonicalLargeOwnerSupport data).filter
        (fun e => ownerCellOffset e = rho))
      (t := Finset.Icc 1 k) ?_ ?_
    · simpa [Nat.card_Icc] using hle
    · intro e he
      have heSupport := (Finset.mem_filter.mp he).1
      exact (Finset.mem_product.mp
        (Finset.mem_filter.mp heSupport).1).1
    · intro a ha b hb hrow
      have haoff := (Finset.mem_filter.mp ha).2
      have hboff := (Finset.mem_filter.mp hb).2
      change a.1 = b.1 at hrow
      apply Prod.ext hrow
      simp only [ownerCellOffset, ownerDiagonalOffset, ownerCellColumn,
        ownerCellRow] at haoff hboff
      omega

/-- Signed row and diagonal divisor interface consumed by the secant and
affine-line matching theorems. -/
theorem canonicalLargeOwnerSupport_signed_divisibility
    {k n d t : ℕ} (data : CanonicalOwnerData k n d t)
    (hd : k ≤ d) (hfour : 4 ∣ n + d + t) :
    (∀ e ∈ canonicalLargeOwnerSupport data,
      (canonicalLargeOwnerCell data e.1 e.2 : ℤ) ∣
        (n : ℤ) + (ownerCellRow e : ℤ)) ∧
    (∀ e ∈ canonicalLargeOwnerSupport data,
      (canonicalLargeOwnerCell data e.1 e.2 : ℤ) ∣
        (d : ℤ) + ownerCellOffset e) := by
  constructor
  · intro e he
    have hnat := canonicalLargeOwnerCell_dvd_lower data
      (j := e.1) (i := e.2)
    simp only [ownerCellRow]
    exact_mod_cast hnat
  · intro e he
    have heSquare := Finset.mem_product.mp
      (Finset.mem_filter.mp he).1
    have hnat := canonicalLargeOwnerCell_dvd_shiftedDifference data
      (j := e.1) (i := e.2) hfour
    have hle : e.1 ≤ d + e.2 := by
      have hjk := (Finset.mem_Icc.mp heSquare.1).2
      omega
    have heq :
        (((d + e.2 - e.1 : ℕ) : ℤ)) =
          (d : ℤ) + ownerCellOffset e := by
      rw [Nat.cast_sub hle]
      simp only [Nat.cast_add, ownerCellOffset, ownerDiagonalOffset,
        ownerCellColumn, ownerCellRow]
      ring
    have hcast :
        (canonicalLargeOwnerCell data e.1 e.2 : ℤ) ∣
          ((d + e.2 - e.1 : ℕ) : ℤ) := by
      exact_mod_cast hnat
    rwa [heq] at hcast

/-- Fixed-column slice of the nontrivial large-owner support. -/
def canonicalLargeOwnerColumnSupport
    {k n d t : ℕ} (data : CanonicalOwnerData k n d t) (i : ℕ) :
    Finset (ℕ × ℕ) :=
  (canonicalLargeOwnerSupport data).filter (fun e => e.2 = i)

def canonicalLargeOwnerColumnProduct
    {k n d t : ℕ} (data : CanonicalOwnerData k n d t) (i : ℕ) : ℕ :=
  ∏ j ∈ Finset.Icc 1 k, canonicalLargeOwnerCell data j i

theorem canonicalLargeOwnerColumnSupport_product_eq
    {k n d t i : ℕ} (data : CanonicalOwnerData k n d t)
    (hi : i ∈ Finset.Icc 1 k) :
    (∏ e ∈ canonicalLargeOwnerColumnSupport data i,
      canonicalLargeOwnerCell data e.1 e.2) =
        canonicalLargeOwnerColumnProduct data i := by
  classical
  let rows := (Finset.Icc 1 k).filter
    (fun j => canonicalLargeOwnerCell data j i ≠ 1)
  calc
    (∏ e ∈ canonicalLargeOwnerColumnSupport data i,
        canonicalLargeOwnerCell data e.1 e.2) =
      ∏ j ∈ rows, canonicalLargeOwnerCell data j i := by
        apply Finset.prod_bij (fun e _ => e.1)
        · intro e he
          have heCol := (Finset.mem_filter.mp he).2
          have heSupport := (Finset.mem_filter.mp he).1
          have heSquare := Finset.mem_product.mp
            (Finset.mem_filter.mp heSupport).1
          have heNontrivial := (Finset.mem_filter.mp heSupport).2
          simp only [rows, Finset.mem_filter]
          exact ⟨heSquare.1, by simpa [heCol] using heNontrivial⟩
        · intro a ha b hb hab
          have haCol := (Finset.mem_filter.mp ha).2
          have hbCol := (Finset.mem_filter.mp hb).2
          apply Prod.ext hab
          simpa using haCol.trans hbCol.symm
        · intro j hj
          refine ⟨(j, i), ?_, rfl⟩
          have hj' := Finset.mem_filter.mp hj
          have hSquare :
              (j, i) ∈ (Finset.Icc 1 k).product (Finset.Icc 1 k) :=
            Finset.mem_product.mpr ⟨hj'.1, hi⟩
          have hSupport : (j, i) ∈ canonicalLargeOwnerSupport data :=
            Finset.mem_filter.mpr ⟨hSquare, hj'.2⟩
          exact Finset.mem_filter.mpr ⟨hSupport, rfl⟩
        · intro e he
          have heCol := (Finset.mem_filter.mp he).2
          simp [heCol]
    _ = ∏ j ∈ Finset.Icc 1 k,
        canonicalLargeOwnerCell data j i := by
          simp only [rows, Finset.prod_filter]
          apply Finset.prod_congr rfl
          intro j hj
          split <;> simp_all
    _ = canonicalLargeOwnerColumnProduct data i := rfl

theorem canonicalLargeOwnerSupport_product_eq_columnProducts
    {k n d t : ℕ} (data : CanonicalOwnerData k n d t) :
    (∏ e ∈ canonicalLargeOwnerSupport data,
      canonicalLargeOwnerCell data e.1 e.2) =
      ∏ i ∈ Finset.Icc 1 k, canonicalLargeOwnerColumnProduct data i := by
  classical
  rw [canonicalLargeOwnerSupport_product_eq_kLargePart data,
    ← canonicalLargeOwner_allCells_eq_kLargePart data]
  unfold canonicalLargeOwnerColumnProduct
  rw [Finset.prod_comm]

/-- One fixed column carries at least the sharp universal `k`-cover share of
the total multiplicative large-prime mass. -/
theorem exists_fixedColumn_matching_product_pow_ge_kLargePart
    {k n d t : ℕ} (data : CanonicalOwnerData k n d t)
    (hk : 1 ≤ k) :
    ∃ i ∈ Finset.Icc 1 k,
      kLargePart k (blockProduct k n) ≤
        (canonicalLargeOwnerColumnProduct data i) ^ k := by
  classical
  let I := Finset.Icc 1 k
  have hI : I.Nonempty := ⟨1, Finset.mem_Icc.mpr ⟨le_rfl, hk⟩⟩
  obtain ⟨i, hi, hmax⟩ := Finset.exists_max_image I
    (canonicalLargeOwnerColumnProduct data) hI
  refine ⟨i, by simpa [I] using hi, ?_⟩
  rw [← canonicalLargeOwnerSupport_product_eq_kLargePart data,
    canonicalLargeOwnerSupport_product_eq_columnProducts data]
  calc
    (∏ r ∈ Finset.Icc 1 k, canonicalLargeOwnerColumnProduct data r) ≤
        ∏ _r ∈ Finset.Icc 1 k, canonicalLargeOwnerColumnProduct data i := by
          apply Finset.prod_le_prod
          · intro r hr
            exact Nat.zero_le _
          · intro r hr
            exact hmax r (by simpa [I] using hr)
    _ = (canonicalLargeOwnerColumnProduct data i) ^ k := by
      rw [Finset.prod_const]
      congr 1
      rw [Nat.card_Icc]
      omega

/-- A fixed-column slice is a row-diagonal matching: rows and signed offsets
are both injective, without any connectivity assumption. -/
theorem canonicalLargeOwnerColumnSupport_row_offset_injective
    {k n d t i : ℕ} (data : CanonicalOwnerData k n d t) :
    (∀ a ∈ canonicalLargeOwnerColumnSupport data i,
      ∀ b ∈ canonicalLargeOwnerColumnSupport data i,
        ownerCellRow a = ownerCellRow b → a = b) ∧
    (∀ a ∈ canonicalLargeOwnerColumnSupport data i,
      ∀ b ∈ canonicalLargeOwnerColumnSupport data i,
        ownerCellOffset a = ownerCellOffset b → a = b) := by
  classical
  constructor
  · intro a ha b hb hrow
    have hacol := (Finset.mem_filter.mp ha).2
    have hbcol := (Finset.mem_filter.mp hb).2
    apply Prod.ext
    · exact hrow
    · simpa using hacol.trans hbcol.symm
  · intro a ha b hb hoff
    have hacol := (Finset.mem_filter.mp ha).2
    have hbcol := (Finset.mem_filter.mp hb).2
    apply Prod.ext
    · simp only [ownerCellOffset, ownerDiagonalOffset, ownerCellColumn,
        ownerCellRow] at hoff
      omega
    · simpa using hacol.trans hbcol.symm

/-- Strongest unconditional matching extraction supplied by square capacity:
one fixed-column slice is an actual row-diagonal matching, inherits all owner
divisibility and coprimality, and its product has `k`-th power at least the
entire high-prime mass.  The exponent `k` is sharp for a universal partition
argument because the `k` fixed columns partition the square. -/
theorem exists_fixedColumn_canonicalLarge_matching
    {k n d t : ℕ} (data : CanonicalOwnerData k n d t)
    (hk : 1 ≤ k) (hd : k ≤ d) (hfour : 4 ∣ n + d + t) :
    ∃ i, i ∈ Finset.Icc 1 k ∧
      let S := canonicalLargeOwnerColumnSupport data i
      (∀ a ∈ S, ∀ b ∈ S,
        ownerCellRow a = ownerCellRow b → a = b) ∧
      (∀ a ∈ S, ∀ b ∈ S,
        ownerCellOffset a = ownerCellOffset b → a = b) ∧
      (∀ e ∈ S,
        e.1 ∈ Finset.Icc 1 k ∧ e.2 ∈ Finset.Icc 1 k) ∧
      ((S : Set (ℕ × ℕ)).Pairwise
        (Function.onFun Nat.Coprime
          (fun e => canonicalLargeOwnerCell data e.1 e.2))) ∧
      (∀ e ∈ S,
        (canonicalLargeOwnerCell data e.1 e.2 : ℤ) ∣
          (n : ℤ) + (ownerCellRow e : ℤ)) ∧
      (∀ e ∈ S,
        (canonicalLargeOwnerCell data e.1 e.2 : ℤ) ∣
          (d : ℤ) + ownerCellOffset e) ∧
      kLargePart k (blockProduct k n) ≤
        (∏ e ∈ S, canonicalLargeOwnerCell data e.1 e.2) ^ k := by
  classical
  obtain ⟨i, hi, hmass⟩ :=
    exists_fixedColumn_matching_product_pow_ge_kLargePart data hk
  refine ⟨i, hi, ?_⟩
  dsimp
  have hinj := canonicalLargeOwnerColumnSupport_row_offset_injective
    data (i := i)
  have hspec := canonicalLargeOwnerSupport_spec data hfour
  have hsigned := canonicalLargeOwnerSupport_signed_divisibility
    data hd hfour
  refine ⟨hinj.1, hinj.2, ?_, ?_, ?_, ?_, ?_⟩
  · intro e he
    exact hspec.1 e (Finset.mem_filter.mp he).1
  · intro e he f hf hef
    exact hspec.2.2.2.2.1
      (Finset.mem_filter.mp he).1 (Finset.mem_filter.mp hf).1 hef
  · intro e he
    exact hsigned.1 e (Finset.mem_filter.mp he).1
  · intro e he
    exact hsigned.2 e (Finset.mem_filter.mp he).1
  · rw [canonicalLargeOwnerColumnSupport_product_eq data hi]
    exact hmass

#print axioms kLargePart_eq_prod_canonicalLargePrimeIndices
#print axioms canonicalOwnerExponent_eq_block_factorization_of_large
#print axioms canonicalLargeOwnerCell_dvd_lower
#print axioms canonicalLargeOwnerCell_dvd_upper
#print axioms canonicalLargeOwnerCell_dvd_shiftedDifference
#print axioms canonicalLargeOwnerCells_pairwise_coprime
#print axioms canonicalLargeOwner_allCells_eq_kLargePart
#print axioms canonicalLargeOwnerSupport_product_eq_kLargePart
#print axioms canonicalLargeOwnerSupport_spec
#print axioms canonicalLargeOwnerSupport_row_diagonal_capacity
#print axioms canonicalLargeOwnerSupport_signed_divisibility
#print axioms canonicalLargeOwnerSupport_product_eq_columnProducts
#print axioms canonicalLargeOwnerColumnSupport_product_eq
#print axioms exists_fixedColumn_matching_product_pow_ge_kLargePart
#print axioms canonicalLargeOwnerColumnSupport_row_offset_injective
#print axioms exists_fixedColumn_canonicalLarge_matching

end Erdos686Variant
end Erdos686
