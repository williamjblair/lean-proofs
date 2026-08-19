import Mathlib

/-!
# Erdős 94: total distance multiplicity

This file proves the elementary counting variant attached to Erdős problem 94 in
Formal Conjectures.  The two definitions below match the frozen source target:
`distanceSet` is formed from ordered distinct pairs, while
`distanceMultiplicity` divides each ordered distance fiber by two.

The proof makes that division explicit.  Each non-diagonal unordered pair has
exactly the two ordered representatives `(a, b)` and `(b, a)`.
-/

open scoped BigOperators Finset

local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

/-- The set of distances determined by a finite set of points in a metric space. -/
noncomputable def distanceSet {X : Type*} [MetricSpace X] (points : Finset X) : Finset ℝ :=
  points.offDiag.image fun pair : X × X => dist pair.1 pair.2

/-- The number of unordered pairs of distinct points at a specified distance. -/
noncomputable def distanceMultiplicity (points : Finset ℝ²) (d : ℝ) : ℕ :=
  #(points.offDiag.filter fun pair : ℝ² × ℝ² => dist pair.1 pair.2 = d) / 2

namespace Erdos94

noncomputable section

private def distanceSym2 : Sym2 ℝ² → ℝ :=
  Sym2.lift ⟨fun a b => dist a b, fun a b => dist_comm a b⟩

@[simp]
private lemma distanceSym2_mk (a b : ℝ²) :
    distanceSym2 s(a, b) = dist a b := by
  simp [distanceSym2]

private def unorderedDistancePairs (P : Finset ℝ²) (u : ℝ) : Finset (Sym2 ℝ²) :=
  (P.offDiag.image Sym2.mk.uncurry).filter fun z => distanceSym2 z = u

/-- Every unordered, non-diagonal distance pair has exactly its two swapped
ordered representatives. -/
private lemma ordered_distance_fiber_card (P : Finset ℝ²) (u : ℝ) :
    #(P.offDiag.filter fun pq : ℝ² × ℝ² => dist pq.1 pq.2 = u) =
      2 * #(unorderedDistancePairs P u) := by
  classical
  let s : Finset (ℝ² × ℝ²) :=
    P.offDiag.filter fun pq => dist pq.1 pq.2 = u
  let t : Finset (Sym2 ℝ²) := unorderedDistancePairs P u
  have hmap : (s : Set (ℝ² × ℝ²)).MapsTo (fun pq => s(pq.1, pq.2)) t := by
    intro pq hpq
    have hpq' : pq ∈ P.offDiag := (Finset.mem_filter.mp hpq).1
    have hdist : dist pq.1 pq.2 = u := (Finset.mem_filter.mp hpq).2
    have hmem : s(pq.1, pq.2) ∈ P.offDiag.image Sym2.mk.uncurry := by
      exact Finset.mem_image.mpr ⟨pq, hpq', rfl⟩
    exact Finset.mem_filter.mpr ⟨hmem, by simpa using hdist⟩
  have hfiber := Finset.card_eq_sum_card_fiberwise
    (s := s) (t := t) (f := fun pq => s(pq.1, pq.2)) hmap
  have hfiber_card : ∀ z ∈ t, #{pq ∈ s | s(pq.1, pq.2) = z} = 2 := by
    intro z hz
    have hz' := Finset.mem_filter.mp hz
    rcases Finset.mem_image.mp hz'.1 with ⟨⟨a, b⟩, habP, rfl⟩
    have habP' := Finset.mem_offDiag.mp habP
    have ha : a ∈ P := habP'.1
    have hb : b ∈ P := habP'.2.1
    have hab : a ≠ b := habP'.2.2
    have hdist : dist a b = u := by simpa using hz'.2
    have hab_mem : (a, b) ∈ s := by
      simp [s, Finset.mem_offDiag, ha, hb, hab, hdist]
    have hba_mem : (b, a) ∈ s := by
      have hba : b ≠ a := Ne.symm hab
      have hdist' : dist b a = u := by simpa [dist_comm] using hdist
      simp [s, Finset.mem_offDiag, hb, ha, hba, hdist']
    have hfiber_eq :
        {pq ∈ s | s(pq.1, pq.2) = s(a, b)} = {(a, b), (b, a)} := by
      ext pq
      constructor
      · intro hpq
        have hpqeq := (Finset.mem_filter.mp hpq).2
        rcases (Sym2.mk_eq_mk_iff (p := pq) (q := (a, b))).mp hpqeq with hpqeq | hpqeq
        · simp [hpqeq]
        · simp [hpqeq]
      · intro hpq
        have hpqeq : pq = (a, b) ∨ pq = (b, a) := by simpa using hpq
        rcases hpqeq with rfl | rfl
        · exact Finset.mem_filter.mpr
            ⟨hab_mem, (Sym2.mk_eq_mk_iff (p := (a, b)) (q := (a, b))).mpr (Or.inl rfl)⟩
        · exact Finset.mem_filter.mpr
            ⟨hba_mem, (Sym2.mk_eq_mk_iff (p := (b, a)) (q := (a, b))).mpr (Or.inr rfl)⟩
    change #({pq ∈ s | s(pq.1, pq.2) = s(a, b)}) = 2
    rw [hfiber_eq]
    simp [hab]
  calc
    #(P.offDiag.filter fun pq : ℝ² × ℝ² => dist pq.1 pq.2 = u) = s.card := rfl
    _ = ∑ z ∈ t, #{pq ∈ s | s(pq.1, pq.2) = z} := hfiber
    _ = ∑ _z ∈ t, 2 := Finset.sum_congr rfl hfiber_card
    _ = 2 * t.card := by simp [Nat.mul_comm]
    _ = 2 * #(unorderedDistancePairs P u) := rfl

private lemma distanceMultiplicity_eq_unordered (P : Finset ℝ²) (u : ℝ) :
    distanceMultiplicity P u = #(unorderedDistancePairs P u) := by
  rw [distanceMultiplicity, ordered_distance_fiber_card]
  omega

namespace variants

/-- The sum of the multiplicities of all distances is the number of unordered
pairs of distinct points. -/
theorem sum_multiplicity (P : Finset ℝ²) :
    ∑ u ∈ distanceSet P, distanceMultiplicity P u = P.card.choose 2 := by
  classical
  let s : Finset (Sym2 ℝ²) := P.offDiag.image Sym2.mk.uncurry
  have hmap : (s : Set (Sym2 ℝ²)).MapsTo distanceSym2 (distanceSet P) := by
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨⟨a, b⟩, habP, rfl⟩
    exact Finset.mem_image.mpr ⟨(a, b), habP, by simp⟩
  have hfiber := Finset.card_eq_sum_card_fiberwise
    (s := s) (t := distanceSet P) (f := distanceSym2) hmap
  calc
    ∑ u ∈ distanceSet P, distanceMultiplicity P u =
        ∑ u ∈ distanceSet P, #(unorderedDistancePairs P u) := by
          exact Finset.sum_congr rfl fun u _ => distanceMultiplicity_eq_unordered P u
    _ = s.card := by
      rw [hfiber]
      rfl
    _ = P.card.choose 2 := Sym2.card_image_offDiag P

end variants
end
end Erdos94
