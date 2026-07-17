/- leanprover/lean4:v4.29.1 mathlib v4.29.1 -/
import ErdosProblems.Erdos686CanonicalLargeOwnerCyclicSecant

/-!
# Erdős 686: global cyclic secant dichotomy for degree-two support

Exact row-degree two and used-diagonal-degree two turn the entire canonical
large-owner support into a permutation: move to the other cell on the signed
diagonal, then to the other cell in its row.  Its orbits are precisely the
alternating components, so applying the arbitrary-permutation cyclic theorem
once globalizes over every component without choosing or enumerating them.

The alternating `b`-mass over the support subtype is the complete
`kLargePart`.  Thus the nonzero branch bounds its square by the global secant
product.  The zero branch gives one exact owner-square crowding divisor and,
using the two diagonal factorizations, an enlarged divisor of two actual
shifted-diagonal terms.
-/

namespace Erdos686
namespace Erdos686Variant

open scoped BigOperators

/-- The global alternating-step permutation on an exact degree-two canonical
large-owner support. -/
noncomputable def canonicalLargeOwnerAlternatingPerm
    {k n d t : ℕ} (data : CanonicalOwnerData k n d t)
    (hrow : ∀ e ∈ canonicalLargeOwnerSupport data,
      (canonicalLargeOwnerRowSupport data e.1).card = 2)
    (hdiag : ∀ e ∈ canonicalLargeOwnerSupport data,
      (canonicalLargeOwnerDiagonalSupport data
        (canonicalOwnerDiagonalIndex k e)).card = 2) :
    Equiv.Perm ↥(canonicalLargeOwnerSupport data) where
  toFun e := canonicalLargeOwnerRowPartner data hrow
    (canonicalLargeOwnerDiagonalPartner data hdiag e)
  invFun e := canonicalLargeOwnerDiagonalPartner data hdiag
    (canonicalLargeOwnerRowPartner data hrow e)
  left_inv e := by
    change canonicalLargeOwnerDiagonalPartner data hdiag
      (canonicalLargeOwnerRowPartner data hrow
        (canonicalLargeOwnerRowPartner data hrow
          (canonicalLargeOwnerDiagonalPartner data hdiag e))) = e
    rw [canonicalLargeOwnerRowPartner_involutive,
      canonicalLargeOwnerDiagonalPartner_involutive]
  right_inv e := by
    change canonicalLargeOwnerRowPartner data hrow
      (canonicalLargeOwnerDiagonalPartner data hdiag
        (canonicalLargeOwnerDiagonalPartner data hdiag
          (canonicalLargeOwnerRowPartner data hrow e))) = e
    rw [canonicalLargeOwnerDiagonalPartner_involutive,
      canonicalLargeOwnerRowPartner_involutive]

@[simp]
theorem canonicalLargeOwnerAlternatingPerm_apply
    {k n d t : ℕ} (data : CanonicalOwnerData k n d t)
    (hrow : ∀ e ∈ canonicalLargeOwnerSupport data,
      (canonicalLargeOwnerRowSupport data e.1).card = 2)
    (hdiag : ∀ e ∈ canonicalLargeOwnerSupport data,
      (canonicalLargeOwnerDiagonalSupport data
        (canonicalOwnerDiagonalIndex k e)).card = 2)
    (e : ↥(canonicalLargeOwnerSupport data)) :
    canonicalLargeOwnerAlternatingPerm data hrow hdiag e =
      canonicalLargeOwnerRowPartner data hrow
        (canonicalLargeOwnerDiagonalPartner data hdiag e) := rfl

/-- A global alternating step cannot fix a support cell: its row partner and
diagonal partner would then have both the same row and the same signed
diagonal, hence would be the same cell, contradicting partner distinctness. -/
theorem canonicalLargeOwnerAlternatingPerm_ne_self
    {k n d t : ℕ} (data : CanonicalOwnerData k n d t)
    (hrow : ∀ e ∈ canonicalLargeOwnerSupport data,
      (canonicalLargeOwnerRowSupport data e.1).card = 2)
    (hdiag : ∀ e ∈ canonicalLargeOwnerSupport data,
      (canonicalLargeOwnerDiagonalSupport data
        (canonicalOwnerDiagonalIndex k e)).card = 2)
    (e : ↥(canonicalLargeOwnerSupport data)) :
    canonicalLargeOwnerAlternatingPerm data hrow hdiag e ≠ e := by
  let rowP := canonicalLargeOwnerRowPartner data hrow
  let diagP := canonicalLargeOwnerDiagonalPartner data hdiag
  intro he
  have hdiagEqRow : diagP e = rowP e := by
    calc
      diagP e = rowP (rowP (diagP e)) :=
        (canonicalLargeOwnerRowPartner_involutive data hrow (diagP e)).symm
      _ = rowP (canonicalLargeOwnerAlternatingPerm data hrow hdiag e) := rfl
      _ = rowP e := congrArg rowP he
  have hsameRow : (rowP e).1.1 = e.1.1 := by
    simpa [rowP] using (Finset.mem_filter.mp
      (canonicalLargeOwnerRowPartner_mem_fibre data hrow e)).2
  have hsameDiag : canonicalOwnerDiagonalIndex k (rowP e).1 =
      canonicalOwnerDiagonalIndex k e.1 := by
    rw [← hdiagEqRow]
    simpa [diagP] using (Finset.mem_filter.mp
      (canonicalLargeOwnerDiagonalPartner_mem_fibre data hdiag e)).2
  apply canonicalLargeOwnerRowPartner_ne data hrow e
  simpa [rowP] using
    (canonicalLargeOwnerSupport_eq_of_row_diagonalIndex_eq
      (rowP e) e hsameRow hsameDiag)

/-- The row partner at the next alternating position is the current diagonal
partner. -/
theorem canonicalLargeOwnerRowPartner_perm_eq_diagonalPartner
    {k n d t : ℕ} (data : CanonicalOwnerData k n d t)
    (hrow : ∀ e ∈ canonicalLargeOwnerSupport data,
      (canonicalLargeOwnerRowSupport data e.1).card = 2)
    (hdiag : ∀ e ∈ canonicalLargeOwnerSupport data,
      (canonicalLargeOwnerDiagonalSupport data
        (canonicalOwnerDiagonalIndex k e)).card = 2)
    (e : ↥(canonicalLargeOwnerSupport data)) :
    canonicalLargeOwnerRowPartner data hrow
        (canonicalLargeOwnerAlternatingPerm data hrow hdiag e) =
      canonicalLargeOwnerDiagonalPartner data hdiag e := by
  change canonicalLargeOwnerRowPartner data hrow
      (canonicalLargeOwnerRowPartner data hrow
        (canonicalLargeOwnerDiagonalPartner data hdiag e)) = _
  exact canonicalLargeOwnerRowPartner_involutive data hrow _

/-- Global equation-facing dichotomy over every alternating component of an
exact degree-two canonical support. -/
theorem canonicalLargeOwner_degreeTwo_global_secant_or_diagonal_crowding
    {k n d t : ℕ} (data : CanonicalOwnerData k n d t)
    (hne : (canonicalLargeOwnerSupport data).Nonempty)
    (hrow : ∀ e ∈ canonicalLargeOwnerSupport data,
      (canonicalLargeOwnerRowSupport data e.1).card = 2)
    (hdiag : ∀ e ∈ canonicalLargeOwnerSupport data,
      (canonicalLargeOwnerDiagonalSupport data
        (canonicalOwnerDiagonalIndex k e)).card = 2)
    (hd : k ≤ d) (hfour : 4 ∣ n + d + t) :
    let S := ↥(canonicalLargeOwnerSupport data)
    let σ : Equiv.Perm S := canonicalLargeOwnerAlternatingPerm data hrow hdiag
    let rowP : S → S := canonicalLargeOwnerRowPartner data hrow
    let A : S → ℕ := fun e =>
      canonicalLargeOwnerCell data (rowP e).1.1 (rowP e).1.2
    let B : S → ℕ := fun e =>
      canonicalLargeOwnerCell data e.1.1 e.1.2
    let Q : S → ℕ := fun e =>
      canonicalLargeOwnerDiagonalCofactor data
        (canonicalOwnerDiagonalIndex k e.1)
    let X : S → ℤ := fun e => (n + e.1.1 : ℕ)
    let Y : S → ℤ := fun e => ((d + e.1.2 - e.1.1 : ℕ) : ℤ)
    kLargePart k (blockProduct k n) ^ 2 ≤
        (cyclicSecantProduct σ X Y).natAbs ∨
      ∃ e, let D := (A e * A (σ (σ e))) * A (σ e) ^ 2
        D ∣ Q e * Q (σ e) ∧
        ((B e * A (σ e)) * (B (σ e) * A (σ (σ e)))) * D ∣
          (d + e.1.2 - e.1.1) *
            (d + (σ e).1.2 - (σ e).1.1) := by
  classical
  dsimp
  let S := ↥(canonicalLargeOwnerSupport data)
  let σ : Equiv.Perm S := canonicalLargeOwnerAlternatingPerm data hrow hdiag
  let rowP : S → S := canonicalLargeOwnerRowPartner data hrow
  let diagP : S → S := canonicalLargeOwnerDiagonalPartner data hdiag
  let A : S → ℕ := fun e =>
    canonicalLargeOwnerCell data (rowP e).1.1 (rowP e).1.2
  let B : S → ℕ := fun e =>
    canonicalLargeOwnerCell data e.1.1 e.1.2
  let R : S → ℕ := fun e => canonicalLargeOwnerRowCofactor data e.1.1
  let Q : S → ℕ := fun e =>
    canonicalLargeOwnerDiagonalCofactor data
      (canonicalOwnerDiagonalIndex k e.1)
  let X : S → ℤ := fun e => (n + e.1.1 : ℕ)
  let Y : S → ℤ := fun e => ((d + e.1.2 - e.1.1 : ℕ) : ℤ)
  change kLargePart k (blockProduct k n) ^ 2 ≤
      (cyclicSecantProduct σ X Y).natAbs ∨
    ∃ e, let D := (A e * A (σ (σ e))) * A (σ e) ^ 2
      D ∣ Q e * Q (σ e) ∧
      ((B e * A (σ e)) * (B (σ e) * A (σ (σ e)))) * D ∣
        (d + e.1.2 - e.1.1) *
          (d + (σ e).1.2 - (σ e).1.1)
  have hrowInv : Function.Involutive rowP := by
    intro e
    simpa [rowP] using canonicalLargeOwnerRowPartner_involutive data hrow e
  have hrowInj : Function.Injective rowP := hrowInv.injective
  have hσne : ∀ e, σ e ≠ e := by
    intro e
    simpa [σ] using canonicalLargeOwnerAlternatingPerm_ne_self data hrow hdiag e
  have hASigma (e : S) : rowP (σ e) = diagP e := by
    simpa [rowP, diagP, σ] using
      canonicalLargeOwnerRowPartner_perm_eq_diagonalPartner data hrow hdiag e
  obtain ⟨e₀, he₀⟩ := hne
  let z₀ : S := ⟨e₀, he₀⟩
  have hzSquare := (canonicalLargeOwnerSupport_spec data hfour).1 z₀.1 z₀.2
  have hk : 1 ≤ k := by
    have hj := Finset.mem_Icc.mp hzSquare.1
    omega
  have hcyc := cyclic_secant_or_ownerSquare_crowding
    σ A B R Q X Y
    (fun e => by
      have hgt := (canonicalLargeOwnerSupport_spec data hfour).2.1 e.1 e.2
      exact Nat.zero_lt_one.trans hgt)
    (fun e => by
      apply canonical_cyclic_ownerSquare_coprime_twoOwners_mul_rowCofactor
        data (rowP (σ e)).2
      · intro h
        exact hσne e (hrowInj (Subtype.ext h))
      · intro h
        exact hσne (σ e) (hrowInj (Subtype.ext h.symm))
      · exact (canonicalLargeOwnerSupport_spec data hfour).1 e.1 e.2 |>.1)
    (fun e => by
      apply canonical_cyclic_twoOwners_coprime_ownerSquare_mul_rowCofactor
        data (rowP e).2 (rowP (σ (σ e))).2
      · intro h
        exact hσne e (hrowInj (Subtype.ext h.symm))
      · intro h
        exact hσne (σ e) (hrowInj (Subtype.ext h))
      · exact (canonicalLargeOwnerSupport_spec data hfour).1 (σ e).1 (σ e).2 |>.1)
    (fun e => by
      have hrowNe : (rowP e).1 ≠ e.1 := by
        intro h
        exact canonicalLargeOwnerRowPartner_ne data hrow e (Subtype.ext h)
      have hrowNat := canonical_cyclic_row_pair_factorization data
        hrowNe
        (canonicalLargeOwnerRowPartner_fibre data hrow e)
      dsimp [X, A, B, R, rowP]
      exact_mod_cast hrowNat)
    (fun e => by
      have hdiagFibre : canonicalLargeOwnerDiagonalSupport data
          (canonicalOwnerDiagonalIndex k e.1) =
            {e.1, (rowP (σ e)).1} := by
        rw [hASigma e]
        exact canonicalLargeOwnerDiagonalPartner_fibre data hdiag e
      have hdiagNe : e.1 ≠ (rowP (σ e)).1 := by
        rw [hASigma e]
        exact fun h => canonicalLargeOwnerDiagonalPartner_ne data hdiag e
          (Subtype.ext h.symm)
      have hdiagNat := canonical_cyclic_diagonal_pair_factorization
        (a := (rowP (σ e)).1) (b := e.1) data hdiagNe.symm
        hk hd hfour e.2 hdiagFibre
      dsimp [Y, B, A, Q]
      exact_mod_cast hdiagNat)
  have hBprod : (∏ e, B e) = kLargePart k (blockProduct k n) := by
    rw [← canonicalLargeOwnerSupport_product_eq_kLargePart data]
    simpa [B, S] using
      (Finset.prod_coe_sort (canonicalLargeOwnerSupport data)
        (fun e => canonicalLargeOwnerCell data e.1 e.2))
  rcases hcyc with hmass | ⟨e, hdvd⟩
  · left
    simpa [hBprod] using hmass
  · right
    refine ⟨e, hdvd, ?_⟩
    have hdiagFibre (z : S) : canonicalLargeOwnerDiagonalSupport data
        (canonicalOwnerDiagonalIndex k z.1) =
          {z.1, (rowP (σ z)).1} := by
      rw [hASigma z]
      exact canonicalLargeOwnerDiagonalPartner_fibre data hdiag z
    have hdiagNe (z : S) : z.1 ≠ (rowP (σ z)).1 := by
      rw [hASigma z]
      exact fun h => canonicalLargeOwnerDiagonalPartner_ne data hdiag z
        (Subtype.ext h.symm)
    have hy₁ := canonical_cyclic_diagonal_pair_factorization
      (a := (rowP (σ e)).1) (b := e.1) data (hdiagNe e).symm
      hk hd hfour e.2 (hdiagFibre e)
    have hy₂ := canonical_cyclic_diagonal_pair_factorization
      (a := (rowP (σ (σ e))).1) (b := (σ e).1) data
      (hdiagNe (σ e)).symm hk hd hfour (σ e).2 (hdiagFibre (σ e))
    obtain ⟨u, hu⟩ := hdvd
    refine ⟨u, ?_⟩
    rw [hy₁, hy₂]
    change (B e * A (σ e) * Q e) *
        (B (σ e) * A (σ (σ e)) * Q (σ e)) =
      (((B e * A (σ e)) * (B (σ e) * A (σ (σ e)))) *
        ((A e * A (σ (σ e))) * A (σ e) ^ 2)) * u
    calc
      (B e * A (σ e) * Q e) *
          (B (σ e) * A (σ (σ e)) * Q (σ e)) =
        ((B e * A (σ e)) * (B (σ e) * A (σ (σ e)))) *
          (Q e * Q (σ e)) := by ring
      _ = ((B e * A (σ e)) * (B (σ e) * A (σ (σ e)))) *
          (((A e * A (σ (σ e))) * A (σ e) ^ 2) * u) := by rw [hu]
      _ = (((B e * A (σ e)) * (B (σ e) * A (σ (σ e)))) *
          ((A e * A (σ (σ e))) * A (σ e) ^ 2)) * u := by ring

#print axioms canonicalLargeOwnerAlternatingPerm
#print axioms canonicalLargeOwnerAlternatingPerm_ne_self
#print axioms canonicalLargeOwner_degreeTwo_global_secant_or_diagonal_crowding

end Erdos686Variant
end Erdos686
