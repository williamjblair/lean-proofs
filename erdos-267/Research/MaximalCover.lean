import Research.ShiftedPowers

/-!
# Canonical divisibility-maximal covers
-/

namespace Research

open Filter Topology
open scoped BigOperators

/-- Positions in a finite prefix whose selected index divides no selected index
at a strictly later position of that prefix. -/
def divisibilityMaxima (n : ℕ → ℕ) (N : ℕ) : Finset ℕ :=
  (Finset.range N).filter fun j =>
    ∀ l < N, n j ∣ n l → l ≤ j

/-- Every finite-prefix position is index-divisibility-covered by a maximal
position. -/
theorem divisibilityMaxima_cover (n : ℕ → ℕ) (N k : ℕ) (hk : k < N) :
    ∃ j ∈ divisibilityMaxima n N, n k ∣ n j := by
  let S := (Finset.range N).filter fun l => n k ∣ n l
  have hSne : S.Nonempty := by
    refine ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hk, dvd_refl _⟩⟩
  obtain ⟨j, hjS, hjmax⟩ := Finset.exists_max_image S id hSne
  have hjS' := Finset.mem_filter.mp hjS
  refine ⟨j, ?_, hjS'.2⟩
  rw [divisibilityMaxima, Finset.mem_filter]
  refine ⟨hjS'.1, ?_⟩
  intro l hl hdiv
  apply hjmax l
  rw [Finset.mem_filter]
  exact ⟨Finset.mem_range.mpr hl, hjS'.2.trans hdiv⟩

/-- The canonical maximal positions give a concrete version of F-011.  Thus
only the total weight of divisibility-maximal indices in each prefix needs to
be estimated. -/
theorem irrational_reciprocal_fib_of_maximal_cover_budget
    (n s : ℕ → ℕ) (hpos : ∀ k, 0 < n k) (hmono : StrictMono n)
    (hs : Tendsto s atTop atTop)
    (hbudget : ∀ t,
      (∑ j ∈ divisibilityMaxima n (s t), n j) + s t ≤
        n (s t) + (divisibilityMaxima n (s t)).card) :
    Irrational (∑' k : ℕ, (Nat.fib (n k) : ℝ)⁻¹) := by
  exact irrational_reciprocal_fib_of_divisibility_covers n s
    (fun t => divisibilityMaxima n (s t)) hpos hmono hs
    (fun t k hk => divisibilityMaxima_cover n (s t) k hk) hbudget

end Research
