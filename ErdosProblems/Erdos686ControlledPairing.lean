/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import ErdosProblems.Erdos686SecantPairing

/-!
# Erdős 686: explicit controlled pairing

The algorithm consumes four sorted entries at a time, cross-pairing
`(a,c)` and `(b,d)`.  Its terminal blocks have lengths four through seven;
the length-six terminal block uses `(a,c)`, `(b,e)`, `(d,f)`, and length
seven uses the same block while leaving the last entry unmatched.
-/

namespace Erdos686
namespace Erdos686Variant

/-- The pairs and (zero or one) unmatched entries returned by the explicit
four-block / six-block construction. -/
def controlledPairing {α : Type*} : List α → List (α × α) × List α
  | a :: b :: c :: d :: rest =>
      match rest with
      | [] => ([(a, c), (b, d)], [])
      | [e] => ([(a, c), (b, d)], [e])
      | [e, f] => ([(a, c), (b, e), (d, f)], [])
      | [e, f, g] => ([(a, c), (b, e), (d, f)], [g])
      | e :: f :: g :: h :: tail =>
          let next := controlledPairing (e :: f :: g :: h :: tail)
          ((a, c) :: (b, d) :: next.1, next.2)
  | xs => ([], xs)
termination_by xs => xs.length

def pairedEntries {α : Type*} (r : List (α × α) × List α) : List α :=
  r.1.flatMap (fun p => [p.1, p.2]) ++ r.2

def pairingCost {α : Type*} (rho : α → ℤ)
    (r : List (α × α) × List α) : ℤ :=
  (r.1.map (fun p => rho p.2 - rho p.1)).sum

def orderedSpan {α : Type*} (rho : α → ℤ) : List α → ℤ
  | [] => 0
  | a :: tail => rho (tail.getLastD a) - rho a

theorem perm_cross_four {α : Type*} (a b c d : α) (tail : List α) :
    (a :: c :: b :: d :: tail).Perm (a :: b :: c :: d :: tail) := by
  exact (List.Perm.swap b c (d :: tail)).cons a

theorem perm_cross_six {α : Type*} (a b c d e f : α) (tail : List α) :
    (a :: c :: b :: e :: d :: f :: tail).Perm
      (a :: b :: c :: d :: e :: f :: tail) := by
  exact ((List.Perm.swap b c (e :: d :: f :: tail)).cons a).trans
    (((List.Perm.swap d e (f :: tail)).cons c).cons b |>.cons a)

theorem pairedEntries_perm {α : Type*} (xs : List α) :
    (pairedEntries (controlledPairing xs)).Perm xs := by
  match xs with
  | [] => simp [controlledPairing, pairedEntries]
  | [a] => simp [controlledPairing, pairedEntries]
  | [a, b] => simp [controlledPairing, pairedEntries]
  | [a, b, c] => simp [controlledPairing, pairedEntries]
  | [a, b, c, d] =>
      simpa [controlledPairing, pairedEntries] using
        perm_cross_four a b c d []
  | [a, b, c, d, e] =>
      simpa [controlledPairing, pairedEntries] using
        perm_cross_four a b c d [e]
  | [a, b, c, d, e, f] =>
      simpa [controlledPairing, pairedEntries] using
        perm_cross_six a b c d e f []
  | [a, b, c, d, e, f, g] =>
      simpa [controlledPairing, pairedEntries] using
        perm_cross_six a b c d e f [g]
  | a :: b :: c :: d :: e :: f :: g :: h :: tail =>
      let suffix := e :: f :: g :: h :: tail
      let entries := pairedEntries (controlledPairing suffix)
      have ih := pairedEntries_perm suffix
      have hprefix :
          (a :: c :: b :: d :: entries).Perm
            (a :: b :: c :: d :: entries) :=
        perm_cross_four a b c d entries
      have hsuffix :
          (a :: b :: c :: d :: entries).Perm
            (a :: b :: c :: d :: suffix) :=
        (((ih.cons d).cons c).cons b).cons a
      simpa [controlledPairing, pairedEntries, suffix, entries] using
        hprefix.trans hsuffix
termination_by xs.length

theorem pair_count_and_unmatched {α : Type*} (xs : List α) :
    2 * (controlledPairing xs).1.length +
        (controlledPairing xs).2.length = xs.length := by
  have hp := pairedEntries_perm xs
  have hl := List.Perm.length_eq hp
  simpa [pairedEntries, Nat.mul_comm] using hl

theorem controlledPairing_core_spec
    {α : Type*} (rho : α → ℤ)
    (xs : List α) (hsorted : xs.Pairwise (fun a b => rho a < rho b))
    (hlen : 4 ≤ xs.length) :
    (controlledPairing xs).2.length ≤ 1 ∧
    (∀ p ∈ (controlledPairing xs).1, rho p.1 + 2 ≤ rho p.2) ∧
    pairingCost rho (controlledPairing xs) ≤ 2 * orderedSpan rho xs := by
  match xs with
  | [] => simp at hlen
  | [_] => simp at hlen
  | [_, _] => simp at hlen
  | [_, _, _] => simp at hlen
  | [a, b, c, d] =>
      simp [controlledPairing, pairingCost, orderedSpan,
        List.pairwise_cons] at hsorted ⊢
      omega
  | [a, b, c, d, e] =>
      simp [controlledPairing, pairingCost, orderedSpan,
        List.pairwise_cons] at hsorted ⊢
      omega
  | [a, b, c, d, e, f] =>
      simp [controlledPairing, pairingCost, orderedSpan,
        List.pairwise_cons] at hsorted ⊢
      omega
  | [a, b, c, d, e, f, g] =>
      simp [controlledPairing, pairingCost, orderedSpan,
        List.pairwise_cons] at hsorted ⊢
      omega
  | a :: b :: c :: d :: e :: f :: g :: h :: tail =>
      let suffix := e :: f :: g :: h :: tail
      have hsuffix : suffix.Pairwise (fun a b => rho a < rho b) := by
        simpa [suffix] using hsorted.drop (i := 4)
      have ih := controlledPairing_core_spec rho suffix hsuffix (by simp [suffix])
      have ihcost := ih.2.2
      dsimp [suffix, orderedSpan] at ihcost
      change pairingCost rho (controlledPairing (e :: f :: g :: h :: tail)) ≤
        2 * (rho ((h :: tail).getLastD e) - rho e) at ihcost
      rw [List.getLastD_cons] at ihcost
      have ihcost' :
          (List.map (fun p : α × α => rho p.2 - rho p.1)
              (controlledPairing (e :: f :: g :: h :: tail)).1).sum ≤
            2 * (rho (tail.getLastD h) - rho e) := by
        simpa [pairingCost] using ihcost
      simp only [controlledPairing, pairingCost, List.map_cons, List.sum_cons]
      refine ⟨ih.1, ?_, ?_⟩
      · intro p hp
        simp only [List.mem_cons] at hp
        rcases hp with rfl | rfl | hp
        · change rho a + 2 ≤ rho c
          simp [List.pairwise_cons] at hsorted
          omega
        · change rho b + 2 ≤ rho d
          simp [List.pairwise_cons] at hsorted
          omega
        · exact ih.2.1 p hp
      · have horder := hsorted
        simp [List.pairwise_cons] at horder
        simp only [orderedSpan, List.getLastD_cons]
        omega
termination_by xs.length

theorem unmatched_length_le_one
    {α : Type*} (rho : α → ℤ)
    (xs : List α) (hsorted : xs.Pairwise (fun a b => rho a < rho b))
    (hlen : 4 ≤ xs.length) :
    (controlledPairing xs).2.length ≤ 1 := by
  exact (controlledPairing_core_spec rho xs hsorted hlen).1

theorem every_pair_gap_at_least_two
    {α : Type*} (rho : α → ℤ)
    (xs : List α) (hsorted : xs.Pairwise (fun a b => rho a < rho b))
    (hlen : 4 ≤ xs.length)
    (p : α × α) (hp : p ∈ (controlledPairing xs).1) :
    rho p.1 + 2 ≤ rho p.2 :=
  (controlledPairing_core_spec rho xs hsorted hlen).2.1 p hp

theorem unmatched_length_eq_mod_two
    {α : Type*} (rho : α → ℤ)
    (xs : List α) (hsorted : xs.Pairwise (fun a b => rho a < rho b))
    (hlen : 4 ≤ xs.length) :
    (controlledPairing xs).2.length = xs.length % 2 := by
  have hcount := pair_count_and_unmatched xs
  have hle := unmatched_length_le_one rho xs hsorted hlen
  have hdiv := Nat.mod_add_div xs.length 2
  omega

theorem pair_count_eq_div_two
    {α : Type*} (rho : α → ℤ)
    (xs : List α) (hsorted : xs.Pairwise (fun a b => rho a < rho b))
    (hlen : 4 ≤ xs.length) :
    (controlledPairing xs).1.length = xs.length / 2 := by
  have hcount := pair_count_and_unmatched xs
  have hmod := unmatched_length_eq_mod_two rho xs hsorted hlen
  have hdiv := Nat.mod_add_div xs.length 2
  omega

/-- Any forbidden relation whose zero case can only occur across a unit
offset gap is avoided by every pair selected by the construction. -/
theorem every_pair_avoids_unit_gap_relation
    {α : Type*} (rho : α → ℤ)
    (forbidden : (α × α) → Prop)
    (hunit : ∀ p, forbidden p → |rho p.2 - rho p.1| = 1)
    (xs : List α) (hsorted : xs.Pairwise (fun a b => rho a < rho b))
    (hlen : 4 ≤ xs.length) :
    ∀ p ∈ (controlledPairing xs).1, ¬ forbidden p := by
  intro p hp hforbidden
  have hgap := every_pair_gap_at_least_two rho xs hsorted hlen p hp
  have hnonneg : 0 ≤ rho p.2 - rho p.1 := by omega
  have hone := hunit p hforbidden
  rw [abs_of_nonneg hnonneg] at hone
  omega

/-- The combined controlled-pairing interface.  For a strictly increasing
list of at least seven integer offsets, the explicit algorithm covers every
entry exactly once, leaves precisely the parity bit unmatched, selects
`floor(m/2)` pairs, gives every selected gap at least two, and has total gap
at most twice the full ordered span. -/
theorem explicit_controlled_pairing
    {α : Type*} (rho : α → ℤ)
    (xs : List α) (hsorted : xs.Pairwise (fun a b => rho a < rho b))
    (hlen : 7 ≤ xs.length) :
    (pairedEntries (controlledPairing xs)).Perm xs ∧
    (pairedEntries (controlledPairing xs)).Nodup ∧
    (controlledPairing xs).2.length = xs.length % 2 ∧
    (controlledPairing xs).1.length = xs.length / 2 ∧
    (∀ p ∈ (controlledPairing xs).1, rho p.1 + 2 ≤ rho p.2) ∧
    pairingCost rho (controlledPairing xs) ≤ 2 * orderedSpan rho xs := by
  have hfour : 4 ≤ xs.length := by omega
  have hperm := pairedEntries_perm xs
  have hne : xs.Pairwise (· ≠ ·) := by
    exact hsorted.imp (by intro a b hab heq; subst b; omega)
  have hnodup : xs.Nodup := List.nodup_iff_pairwise_ne.mpr hne
  exact ⟨hperm, hperm.symm.nodup hnodup,
    unmatched_length_eq_mod_two rho xs hsorted hfour,
    pair_count_eq_div_two rho xs hsorted hfour,
    (controlledPairing_core_spec rho xs hsorted hfour).2.1,
    (controlledPairing_core_spec rho xs hsorted hfour).2.2⟩

/-- Equation-facing specialization: every pair selected from a sorted list
of owner cells has a nonzero secant.  The explicit construction forces an
offset gap at least two, while the banked zero-secant classification forces
every zero secant to have offset gap one. -/
theorem controlled_pairing_secants_nonzero
    {k n d : ℕ} {xs : List (ℕ × ℕ)}
    (hk : 16 ≤ k)
    (hd : k ≤ d)
    (hgap : 708827 * k ^ 2 < 5000000 * d)
    (heq : blockProduct k (n + d) = 4 * blockProduct k n)
    (hcells : ∀ z ∈ xs,
      ownerCellRow z ∈ Finset.Icc 1 k ∧
        ownerCellColumn z ∈ Finset.Icc 1 k)
    (hsorted : xs.Pairwise (fun a b =>
      ownerCellOffset a < ownerCellOffset b))
    (hlen : 7 ≤ xs.length) :
    ∀ p ∈ (controlledPairing xs).1,
      ownerCellSecant n d p.1 p.2 ≠ 0 := by
  intro p hp hzero
  have hfour : 4 ≤ xs.length := by omega
  have hpairGap :=
    every_pair_gap_at_least_two ownerCellOffset xs hsorted hfour p hp
  have hp1Paired :
      p.1 ∈ pairedEntries (controlledPairing xs) := by
    simp only [pairedEntries, List.mem_append, List.mem_flatMap]
    exact Or.inl ⟨p, hp, by simp⟩
  have hp2Paired :
      p.2 ∈ pairedEntries (controlledPairing xs) := by
    simp only [pairedEntries, List.mem_append, List.mem_flatMap]
    exact Or.inl ⟨p, hp, by simp⟩
  have hp1Xs : p.1 ∈ xs :=
    (pairedEntries_perm xs).mem_iff.mp hp1Paired
  have hp2Xs : p.2 ∈ xs :=
    (pairedEntries_perm xs).mem_iff.mp hp2Paired
  have hp1Cell := hcells p.1 hp1Xs
  have hp2Cell := hcells p.2 hp2Xs
  have hoffsets :
      ownerCellOffset p.2 - ownerCellOffset p.1 ≠ 0 := by omega
  have hclass := large_k_zero_secant_classification
    hk hd hp1Cell.2 hp1Cell.1 hp2Cell.1 hgap heq hoffsets
    (by simpa [ownerCellSecant, ownerCellOffset, ownerCellRow,
      ownerCellColumn] using hzero)
  have hnonneg :
      0 ≤ ownerCellOffset p.2 - ownerCellOffset p.1 := by omega
  have hunit :
      |ownerCellOffset p.2 - ownerCellOffset p.1| = 1 := by
    simpa [ownerCellOffset] using hclass.1
  rw [abs_of_nonneg hnonneg] at hunit
  omega

/-- The total paired offset gap in the owner square is at most
`4*(k-1)`, exactly as required by the product estimate. -/
theorem controlled_pairing_total_gap_le_four_k_sub_one
    {k : ℕ} {xs : List (ℕ × ℕ)}
    (hcells : ∀ z ∈ xs,
      ownerCellRow z ∈ Finset.Icc 1 k ∧
        ownerCellColumn z ∈ Finset.Icc 1 k)
    (hsorted : xs.Pairwise (fun a b =>
      ownerCellOffset a < ownerCellOffset b))
    (hlen : 7 ≤ xs.length) :
    pairingCost ownerCellOffset (controlledPairing xs) ≤
      4 * ((k - 1 : ℕ) : ℤ) := by
  have hfour : 4 ≤ xs.length := by omega
  have hcost :=
    (controlledPairing_core_spec ownerCellOffset xs hsorted hfour).2.2
  match xs with
  | [] => simp at hlen
  | a :: tail =>
      have haCell := hcells a (by simp)
      simp only [ownerCellRow, ownerCellColumn] at haCell
      have hkOne : 1 ≤ k := by
        exact le_trans (Finset.mem_Icc.mp haCell.1).1
          (Finset.mem_Icc.mp haCell.1).2
      have hkCast :
          ((k - 1 : ℕ) : ℤ) = (k : ℤ) - 1 := by
        rw [Nat.cast_sub (by omega : 1 ≤ k)]
        norm_num
      have hlastMem : tail.getLastD a ∈ a :: tail :=
        List.getLastD_mem_cons
      have hlastCell := hcells (tail.getLastD a) hlastMem
      simp only [ownerCellRow, ownerCellColumn] at hlastCell
      have haBounds :
          -((k - 1 : ℕ) : ℤ) ≤ ownerCellOffset a ∧
            ownerCellOffset a ≤ ((k - 1 : ℕ) : ℤ) := by
        rw [hkCast]
        simp only [ownerCellOffset, ownerCellColumn, ownerCellRow,
          ownerDiagonalOffset]
        have harow := Finset.mem_Icc.mp haCell.1
        have hacol := Finset.mem_Icc.mp haCell.2
        omega
      have hlastBounds :
          -((k - 1 : ℕ) : ℤ) ≤ ownerCellOffset (tail.getLastD a) ∧
            ownerCellOffset (tail.getLastD a) ≤
              ((k - 1 : ℕ) : ℤ) := by
        rw [hkCast]
        simp only [ownerCellOffset, ownerCellColumn, ownerCellRow,
          ownerDiagonalOffset]
        have hlrow := Finset.mem_Icc.mp hlastCell.1
        have hlcol := Finset.mem_Icc.mp hlastCell.2
        omega
      simp only [orderedSpan] at hcost
      omega

#print axioms pairedEntries_perm
#print axioms pair_count_and_unmatched
#print axioms controlledPairing_core_spec
#print axioms unmatched_length_eq_mod_two
#print axioms pair_count_eq_div_two
#print axioms every_pair_avoids_unit_gap_relation
#print axioms explicit_controlled_pairing
#print axioms controlled_pairing_secants_nonzero
#print axioms controlled_pairing_total_gap_le_four_k_sub_one

end Erdos686Variant
end Erdos686
