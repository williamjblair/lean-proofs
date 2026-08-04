import Mathlib

/-!
# Distinct reciprocal subset sums

This file pins down the exact finite object in Erdős Problem 320.  The original
question says “estimate”, so a proposed quantitative theorem must state its own
bounds explicitly; `EventuallySandwiched` is the common schema used below.

We index `Finset.range N` by `0, …, N-1` and use the reciprocal of `n+1`, so
there is no division by zero and the denominators are exactly `1, …, N`.
-/

namespace Research

/-- The reciprocal sum attached to a finite set of zero-based denominator
indices.  Index `n` represents denominator `n+1`. -/
def reciprocalSubsetSum (A : Finset ℕ) : ℚ :=
  ∑ n ∈ A, (1 : ℚ) / (n + 1)

/-- All distinct sums of reciprocals of a subset of `{1, …, N}`. -/
def reciprocalSubsetSums (N : ℕ) : Finset ℚ :=
  (Finset.range N).powerset.image reciprocalSubsetSum

/-- The counting function `S(N)` in Erdős Problem 320. -/
def S (N : ℕ) : ℕ :=
  (reciprocalSubsetSums N).card

/-- Natural logarithm of `S(N)`, viewed as a real number. -/
noncomputable def logS (N : ℕ) : ℝ :=
  Real.log (S N : ℝ)

/-- A precise schema for an eventual two-sided estimate for `log S(N)`.
A substantive proposed answer supplies explicit `lower` and `upper` functions. -/
def EventuallySandwiched (lower upper : ℕ → ℝ) : Prop :=
  ∃ N₀ : ℕ, ∀ N ≥ N₀, lower N ≤ logS N ∧ logS N ≤ upper N

/-- The translate of the old value set produced by adjoining denominator `N+1`. -/
def nextLayer (N : ℕ) : Finset ℚ :=
  (reciprocalSubsetSums N).image
    (fun x => x + (1 : ℚ) / (N + 1))

/-- Adjoining denominator `N+1` expresses the new value set as the old set
union one translate of the old set. -/
theorem reciprocalSubsetSums_succ (N : ℕ) :
    reciprocalSubsetSums (N + 1) =
      reciprocalSubsetSums N ∪ nextLayer N := by
  rw [reciprocalSubsetSums, Finset.range_add_one, Finset.powerset_insert,
    Finset.image_union]
  congr 1
  rw [nextLayer, reciprocalSubsetSums, Finset.image_image, Finset.image_image]
  apply Finset.image_congr
  intro A hA
  change A ∈ (Finset.range N).powerset at hA
  rw [Finset.mem_powerset] at hA
  have hNA : N ∉ A := by
    intro hN
    have hlt : N < N := Finset.mem_range.mp (hA hN)
    exact (Nat.lt_irrefl N) hlt
  simp [reciprocalSubsetSum, hNA, add_comm]

/-- Translation by the new reciprocal is injective, so the next layer has
exactly as many values as the old value set. -/
theorem card_nextLayer (N : ℕ) :
    (nextLayer N).card = (reciprocalSubsetSums N).card := by
  apply Finset.card_image_of_injective
  intro x y hxy
  exact add_right_cancel hxy

/-- There is no signed representation of `1/(N+1)` using the first `N`
reciprocals.  Writing a signed sum as a difference of two subset sums also
allows overlap, which simply cancels and hence is equivalent to coefficients
in `{-1,0,1}`. -/
def NoSignedReciprocalRepresentation (N : ℕ) : Prop :=
  ∀ A ∈ (Finset.range N).powerset,
    ∀ B ∈ (Finset.range N).powerset,
      reciprocalSubsetSum A - reciprocalSubsetSum B ≠
        (1 : ℚ) / (N + 1)

/-- The old value set and its translate by the new reciprocal are disjoint. -/
def IsExactDoublingIndex (N : ℕ) : Prop :=
  Disjoint (reciprocalSubsetSums N) (nextLayer N)

/-- Disjointness of the two layers is exactly absence of a signed reciprocal
representation of the new term. -/
theorem exactDoubling_iff_noSignedRepresentation (N : ℕ) :
    IsExactDoublingIndex N ↔ NoSignedReciprocalRepresentation N := by
  constructor
  · intro hdis A hA B hB hEq
    have hsumA : reciprocalSubsetSum A ∈ reciprocalSubsetSums N := by
      exact Finset.mem_image.mpr ⟨A, hA, rfl⟩
    have hsumB : reciprocalSubsetSum B ∈ reciprocalSubsetSums N := by
      exact Finset.mem_image.mpr ⟨B, hB, rfl⟩
    have htranslated :
        reciprocalSubsetSum B + (1 : ℚ) / (N + 1) ∈ nextLayer N := by
      exact Finset.mem_image.mpr ⟨reciprocalSubsetSum B, hsumB, rfl⟩
    have heq' :
        reciprocalSubsetSum A =
          reciprocalSubsetSum B + (1 : ℚ) / (N + 1) := by
      linarith
    have hnot := Finset.disjoint_left.mp hdis hsumA
    exact hnot (heq' ▸ htranslated)
  · intro hno
    rw [IsExactDoublingIndex, Finset.disjoint_left]
    intro x hx hnext
    rw [nextLayer, Finset.mem_image] at hnext
    obtain ⟨y, hy, rfl⟩ := hnext
    rw [reciprocalSubsetSums, Finset.mem_image] at hx hy
    obtain ⟨A, hA, hAx⟩ := hx
    obtain ⟨B, hB, hBy⟩ := hy
    apply hno A hA B hB
    rw [hAx, hBy]
    ring

/-- The exact-doubling criterion: adjoining `1/(N+1)` doubles the number of
values if and only if it has no signed representation using earlier terms. -/
theorem S_succ_eq_two_mul_iff (N : ℕ) :
    S (N + 1) = 2 * S N ↔ NoSignedReciprocalRepresentation N := by
  rw [← exactDoubling_iff_noSignedRepresentation N]
  simp only [S, IsExactDoublingIndex]
  rw [reciprocalSubsetSums_succ]
  have hcard := card_nextLayer N
  constructor
  · intro h
    apply Finset.card_union_eq_card_add_card.mp
    rw [hcard]
    simpa [two_mul] using h
  · intro h
    have hu := Finset.card_union_eq_card_add_card.mpr h
    rw [hu, hcard, two_mul]

/-- Sanity check at the empty initial segment. -/
theorem S_zero : S 0 = 1 := by
  simp [S, reciprocalSubsetSums, reciprocalSubsetSum]

/-- Every subset gives at most one value, hence the elementary universal upper
bound.  This is a verifier sanity theorem, not the requested research estimate. -/
theorem S_le_two_pow (N : ℕ) : S N ≤ 2 ^ N := by
  rw [S, reciprocalSubsetSums]
  calc
    ((Finset.range N).powerset.image reciprocalSubsetSum).card ≤
        (Finset.range N).powerset.card := Finset.card_image_le
    _ = 2 ^ N := by simp

end Research
