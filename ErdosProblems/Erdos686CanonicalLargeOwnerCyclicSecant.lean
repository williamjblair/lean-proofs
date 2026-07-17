/- leanprover/lean4:v4.29.1 mathlib v4.29.1 -/
import ErdosProblems.Erdos686RowDiagonalCyclicSecant
import ErdosProblems.Erdos686CanonicalAlternatingComponents
import Mathlib.Logic.Equiv.Fin.Rotate

/-!
# Erdős 686: canonical long-component cyclic secant dichotomy

This file specializes the arbitrary cyclic secant invariant to every
canonical alternating component of length at least four.  In particular it
closes the symbolic C8 case without enumerating supports.  The same theorem
applies unchanged to every longer degree-two component.
-/

namespace Erdos686
namespace Erdos686Variant

open scoped BigOperators

private theorem finRotate_eq_alternatingCycleNext
    {m : ℕ} (hm : 0 < m) (i : Fin m) :
    finRotate m i = alternatingCycleNext hm i := by
  obtain ⟨u, hu⟩ : ∃ u, m = u + 1 :=
    Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hm)
  subst m
  apply Fin.ext
  simp [finRotate_succ_apply, alternatingCycleNext, Fin.add_def]

private theorem finRotate_ne_self
    {m : ℕ} (hm : 2 ≤ m) (i : Fin m) : finRotate m i ≠ i := by
  obtain ⟨u, hu⟩ : ∃ u, m = u + 1 :=
    Nat.exists_eq_succ_of_ne_zero (by omega)
  subst m
  by_cases hi : i = Fin.last u
  · subst i
    rw [finRotate_last]
    intro h
    have hv := congrArg Fin.val h
    simp only [Fin.val_zero, Fin.val_last] at hv
    omega
  · exact ne_of_gt ((lt_finRotate_iff_ne_last i).2 hi)

theorem canonical_cyclic_row_pair_factorization
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

theorem canonical_cyclic_diagonal_pair_factorization
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

theorem canonical_cyclic_ownerSquare_coprime_twoOwners_mul_rowCofactor
    {k n d t : ℕ} (data : CanonicalOwnerData k n d t)
    {e left right : ℕ × ℕ} {j : ℕ}
    (he : e ∈ canonicalLargeOwnerSupport data)
    (hel : e ≠ left) (her : e ≠ right)
    (hj : j ∈ Finset.Icc 1 k) :
    (canonicalLargeOwnerCell data e.1 e.2 ^ 2).Coprime
      (canonicalLargeOwnerCell data left.1 left.2 *
        canonicalLargeOwnerCell data right.1 right.2 *
          canonicalLargeOwnerRowCofactor data j) := by
  have hEL := canonicalLargeOwnerCells_pairwise_coprime data hel
  have hER := canonicalLargeOwnerCells_pairwise_coprime data her
  have hEC := canonicalLargeOwnerCell_coprime_rowCofactor data he hj
  exact ((hEL.mul_right hER).mul_right hEC).pow_left 2

theorem canonical_cyclic_twoOwners_coprime_ownerSquare_mul_rowCofactor
    {k n d t : ℕ} (data : CanonicalOwnerData k n d t)
    {left right e : ℕ × ℕ} {j : ℕ}
    (hleft : left ∈ canonicalLargeOwnerSupport data)
    (hright : right ∈ canonicalLargeOwnerSupport data)
    (hle : left ≠ e) (hre : right ≠ e)
    (hj : j ∈ Finset.Icc 1 k) :
    (canonicalLargeOwnerCell data left.1 left.2 *
      canonicalLargeOwnerCell data right.1 right.2).Coprime
        (canonicalLargeOwnerCell data e.1 e.2 ^ 2 *
          canonicalLargeOwnerRowCofactor data j) := by
  have hLE := canonicalLargeOwnerCells_pairwise_coprime data hle
  have hRE := canonicalLargeOwnerCells_pairwise_coprime data hre
  have hLC := canonicalLargeOwnerCell_coprime_rowCofactor data hleft hj
  have hRC := canonicalLargeOwnerCell_coprime_rowCofactor data hright hj
  have howners :
      (canonicalLargeOwnerCell data left.1 left.2 *
        canonicalLargeOwnerCell data right.1 right.2).Coprime
          (canonicalLargeOwnerCell data e.1 e.2 ^ 2) :=
    ((hLE.pow_right 2).symm.mul_right (hRE.pow_right 2).symm).symm
  have hcofactor :
      (canonicalLargeOwnerCell data left.1 left.2 *
        canonicalLargeOwnerCell data right.1 right.2).Coprime
          (canonicalLargeOwnerRowCofactor data j) :=
    (hLC.symm.mul_right hRC.symm).symm
  exact howners.mul_right hcofactor

/-- Equation-facing cyclic secant-or-crowding theorem for every canonical
alternating component of length at least four.  The case `m=4` is exactly
the first unresolved eight-edge component. -/
theorem canonicalLargeOwnerAlternatingComponent_cyclic_secant_or_crowding
    {k n d t m : ℕ} (data : CanonicalOwnerData k n d t)
    (C : CanonicalLargeOwnerAlternatingComponent data m)
    (hm : 4 ≤ m) (hd : k ≤ d) (hfour : 4 ∣ n + d + t) :
    let A : Fin m → ℕ := fun i =>
      canonicalLargeOwnerCell data (C.a i).1 (C.a i).2
    let B : Fin m → ℕ := fun i =>
      canonicalLargeOwnerCell data (C.b i).1 (C.b i).2
    let Q : Fin m → ℕ := fun i =>
      canonicalLargeOwnerDiagonalCofactor data
        (canonicalOwnerDiagonalIndex k (C.b i))
    let X : Fin m → ℤ := fun i => (n + (C.b i).1 : ℕ)
    let Y : Fin m → ℤ := fun i => ((d + (C.b i).2 - (C.b i).1 : ℕ) : ℤ)
    (∏ i, B i) ^ 2 ≤
        (cyclicSecantProduct (finRotate m) X Y).natAbs ∨
      ∃ i, (A i * A (finRotate m (finRotate m i))) *
          A (finRotate m i) ^ 2 ∣ Q i * Q (finRotate m i) := by
  dsimp
  have hmpos : 0 < m := by omega
  have hrotate (i : Fin m) :
      finRotate m i = alternatingCycleNext hmpos i :=
    finRotate_eq_alternatingCycleNext hmpos i
  have hbSquare (i : Fin m) :=
    (canonicalLargeOwnerSupport_spec data hfour).1 (C.b i) (C.mem_b i)
  have hk : 1 ≤ k := by
    have hi := (Finset.mem_Icc.mp (hbSquare (⟨0, hmpos⟩ : Fin m)).1)
    omega
  let A : Fin m → ℕ := fun i =>
    canonicalLargeOwnerCell data (C.a i).1 (C.a i).2
  let B : Fin m → ℕ := fun i =>
    canonicalLargeOwnerCell data (C.b i).1 (C.b i).2
  let R : Fin m → ℕ := fun i => canonicalLargeOwnerRowCofactor data (C.b i).1
  let Q : Fin m → ℕ := fun i =>
    canonicalLargeOwnerDiagonalCofactor data
      (canonicalOwnerDiagonalIndex k (C.b i))
  let X : Fin m → ℤ := fun i => (n + (C.b i).1 : ℕ)
  let Y : Fin m → ℤ := fun i => ((d + (C.b i).2 - (C.b i).1 : ℕ) : ℤ)
  change (∏ i, B i) ^ 2 ≤
      (cyclicSecantProduct (finRotate m) X Y).natAbs ∨
    ∃ i, (A i * A (finRotate m (finRotate m i))) *
      A (finRotate m i) ^ 2 ∣ Q i * Q (finRotate m i)
  apply cyclic_secant_or_ownerSquare_crowding
    (finRotate m) A B R Q X Y
  · intro i
    have hgt := (canonicalLargeOwnerSupport_spec data hfour).2.1
      (C.b i) (C.mem_b i)
    exact Nat.zero_lt_one.trans hgt
  · intro i
    apply canonical_cyclic_ownerSquare_coprime_twoOwners_mul_rowCofactor
      data (C.mem_a (finRotate m i))
    · apply C.a_injective.ne
      exact finRotate_ne_self (by omega) i
    · apply C.a_injective.ne
      exact (finRotate_ne_self (by omega) (finRotate m i)).symm
    · exact (hbSquare i).1
  · intro i
    apply canonical_cyclic_twoOwners_coprime_ownerSquare_mul_rowCofactor data
      (C.mem_a i) (C.mem_a (finRotate m (finRotate m i)))
    · apply C.a_injective.ne
      exact (finRotate_ne_self (by omega) i).symm
    · apply C.a_injective.ne
      exact finRotate_ne_self (by omega) (finRotate m i)
    · exact (hbSquare (finRotate m i)).1
  · intro i
    have hrowNat := canonical_cyclic_row_pair_factorization
      data (C.a_ne_b_same i) (C.row_fibre i)
    dsimp [X, A, B, R]
    exact_mod_cast hrowNat
  · intro i
    have hdiagFibre : canonicalLargeOwnerDiagonalSupport data
        (canonicalOwnerDiagonalIndex k (C.b i)) =
          {C.b i, C.a (finRotate m i)} := by
      simpa [hrotate i] using C.diagonal_fibre i
    have hdiagNe : C.b i ≠ C.a (finRotate m i) := by
      simpa [hrotate i] using C.b_ne_a_next i
    have hdiagNat := canonical_cyclic_diagonal_pair_factorization
      (a := C.a (finRotate m i)) (b := C.b i) data
      hdiagNe.symm hk hd hfour (C.mem_b i) hdiagFibre
    dsimp [Y, B, A, Q]
    exact_mod_cast hdiagNat

/-- Explicit C8 interface: four alternating rows, hence eight owner edges.
This is the first long-component case left by the C4/C6 trichotomy. -/
theorem canonicalLargeOwnerEightCycle_secant_or_crowding
    {k n d t : ℕ} (data : CanonicalOwnerData k n d t)
    (C : CanonicalLargeOwnerAlternatingComponent data 4)
    (hd : k ≤ d) (hfour : 4 ∣ n + d + t) :
    let A : Fin 4 → ℕ := fun i =>
      canonicalLargeOwnerCell data (C.a i).1 (C.a i).2
    let B : Fin 4 → ℕ := fun i =>
      canonicalLargeOwnerCell data (C.b i).1 (C.b i).2
    let Q : Fin 4 → ℕ := fun i =>
      canonicalLargeOwnerDiagonalCofactor data
        (canonicalOwnerDiagonalIndex k (C.b i))
    let X : Fin 4 → ℤ := fun i => (n + (C.b i).1 : ℕ)
    let Y : Fin 4 → ℤ := fun i => ((d + (C.b i).2 - (C.b i).1 : ℕ) : ℤ)
    (∏ i, B i) ^ 2 ≤
        (cyclicSecantProduct (finRotate 4) X Y).natAbs ∨
      ∃ i, (A i * A (finRotate 4 (finRotate 4 i))) *
          A (finRotate 4 i) ^ 2 ∣ Q i * Q (finRotate 4 i) := by
  exact canonicalLargeOwnerAlternatingComponent_cyclic_secant_or_crowding
    data C (by omega) hd hfour

#print axioms canonicalLargeOwnerAlternatingComponent_cyclic_secant_or_crowding
#print axioms canonicalLargeOwnerEightCycle_secant_or_crowding

end Erdos686Variant
end Erdos686
