import Research.RayHyperbola

namespace Erdos796

section CanonicalIncidence

variable {T Q P : Type*}
  [Fintype T] [Fintype Q] [Fintype P]
  [DecidableEq T] [DecidableEq Q] [DecidableEq P]

/-- Canonical factor encodings in pairwise cross-compatible fibers yield a
cube-free incidence hypergraph without any size separation between the two
factor coordinates. -/
theorem canonicalIncidence_cubeFree
    (D : Q → Finset ℕ) (coeffValue : T → ℕ) (primeValue : P → ℕ)
    (H : Finset (T × (Q × P)))
    (hcompat : ∀ ⦃q r : Q⦄, q ≠ r → CrossCompatible (D q) (D r))
    (hmem : ∀ ⦃t q p⦄, (t, (q, p)) ∈ H →
      coeffValue t * primeValue p ∈ D q)
    (hcanonical : ∀ ⦃q : Q⦄ ⦃t u : T⦄ ⦃p v : P⦄,
      (t, (q, p)) ∈ H → (u, (q, v)) ∈ H →
      coeffValue t * primeValue p = coeffValue u * primeValue v →
      (t, p) = (u, v)) :
    CubeFree H := by
  intro t u q r p v htu hqr hpv
    htqp htqv htrp htrv huqp huqv hurp hurv
  have h00_ne_01 : coeffValue t * primeValue p ≠
      coeffValue t * primeValue v := by
    intro h
    exact hpv (Prod.mk.inj (hcanonical htqp htqv h)).2
  have h00_ne_11 : coeffValue t * primeValue p ≠
      coeffValue u * primeValue v := by
    intro h
    exact htu (Prod.mk.inj (hcanonical htqp huqv h)).1
  have h01_ne_11 : coeffValue t * primeValue v ≠
      coeffValue u * primeValue v := by
    intro h
    exact htu (Prod.mk.inj (hcanonical htqv huqv h)).1
  have hnot := factor_rectangle_not_compatible
    (S := D q) (T := D r)
    (a₀ := coeffValue t) (a₁ := coeffValue u)
    (b₀ := primeValue p) (b₁ := primeValue v)
    (hmem htqp) (hmem htqv) (hmem huqp) (hmem huqv)
    (hmem htrp) (hmem htrv) (hmem hurp) (hmem hurv)
    h00_ne_01 h00_ne_11 h01_ne_11
  exact hnot (hcompat hqr)

/-- Every ordered coefficient-pair common-cell graph is rectangle-free for a
canonical factor encoding. -/
theorem canonicalCoefficientPairCells_rectangleFree
    (D : Q → Finset ℕ) (coeffValue : T → ℕ) (primeValue : P → ℕ)
    (H : Finset (T × (Q × P)))
    (hcompat : ∀ ⦃q r : Q⦄, q ≠ r → CrossCompatible (D q) (D r))
    (hmem : ∀ ⦃t q p⦄, (t, (q, p)) ∈ H →
      coeffValue t * primeValue p ∈ D q)
    (hcanonical : ∀ ⦃q : Q⦄ ⦃t u : T⦄ ⦃p v : P⦄,
      (t, (q, p)) ∈ H → (u, (q, v)) ∈ H →
      coeffValue t * primeValue p = coeffValue u * primeValue v →
      (t, p) = (u, v))
    {tu : T × T} (htu : tu ∈ (Finset.univ : Finset T).offDiag) :
    RectangleFree (coefficientPairCells H tu) := by
  have hfree := canonicalIncidence_cubeFree D coeffValue primeValue H
    hcompat hmem hcanonical
  exact commonSlice_rectangleFree H hfree
    (Finset.mem_offDiag.mp htu).2.2

/-- Projection-sensitive canonical-incidence estimate: one edge per occupied
label-factor cell plus a cube-root multiplicity error. -/
theorem canonicalIncidence_card_le_active_sqrt
    (D : Q → Finset ℕ) (coeffValue : T → ℕ) (primeValue : P → ℕ)
    (H : Finset (T × (Q × P)))
    (hcompat : ∀ ⦃q r : Q⦄, q ≠ r → CrossCompatible (D q) (D r))
    (hmem : ∀ ⦃t q p⦄, (t, (q, p)) ∈ H →
      coeffValue t * primeValue p ∈ D q)
    (hcanonical : ∀ ⦃q : Q⦄ ⦃t u : T⦄ ⦃p v : P⦄,
      (t, (q, p)) ∈ H → (u, (q, v)) ∈ H →
      coeffValue t * primeValue p = coeffValue u * primeValue v →
      (t, p) = (u, v)) :
    (H.card : ℝ) ≤ (activeCells H).card +
      (Fintype.card T : ℝ) *
        Real.sqrt (((activeCells H).card : ℝ) *
          (Fintype.card Q +
            Fintype.card P * Real.sqrt (Fintype.card Q))) := by
  have hfree := canonicalIncidence_cubeFree D coeffValue primeValue H
    hcompat hmem hcanonical
  simpa [activeCells, activeBetaGamma, coefficientFiber, alphaFiber] using
    cubeFree_card_le_active H hfree

/-- Pair-excess version of canonical incidence accounting. -/
theorem canonicalIncidence_card_le_active_add_pairCells
    (D : Q → Finset ℕ) (coeffValue : T → ℕ) (primeValue : P → ℕ)
    (H : Finset (T × (Q × P)))
    (hcompat : ∀ ⦃q r : Q⦄, q ≠ r → CrossCompatible (D q) (D r))
    (hmem : ∀ ⦃t q p⦄, (t, (q, p)) ∈ H →
      coeffValue t * primeValue p ∈ D q)
    (hcanonical : ∀ ⦃q : Q⦄ ⦃t u : T⦄ ⦃p v : P⦄,
      (t, (q, p)) ∈ H → (u, (q, v)) ∈ H →
      coeffValue t * primeValue p = coeffValue u * primeValue v →
      (t, p) = (u, v)) :
    H.card ≤ (activeCells H).card +
      ∑ tu ∈ (Finset.univ : Finset T).offDiag,
        (coefficientPairCells H tu).card := by
  exact incidence_card_le_active_add_pairExcess H

end CanonicalIncidence

end Erdos796
