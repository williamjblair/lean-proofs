import Research.IncidenceExcess
import Research.UpperFiberHypergraphs

namespace Erdos796

section RayProjection

variable {T Q P : Type*}
  [Fintype T] [Fintype Q] [Fintype P]
  [DecidableEq T] [DecidableEq Q] [DecidableEq P]

/-- A coefficient/label/prime incidence hypergraph is cube-free whenever its
cores lie in pairwise cross-compatible fibers. -/
theorem rayIncidence_cubeFree
    (D : Q → Finset ℕ) (coeffValue : T → ℕ) (primeValue : P → ℕ)
    (H : Finset (T × (Q × P))) {W : ℕ}
    (hcoeff : ∀ t : T, 0 < coeffValue t ∧ coeffValue t ≤ W)
    (hcoeff_inj : Function.Injective coeffValue)
    (hprime : ∀ p : P, W < primeValue p ∧ (primeValue p).Prime)
    (hprime_inj : Function.Injective primeValue)
    (hcompat : ∀ ⦃q r : Q⦄, q ≠ r → CrossCompatible (D q) (D r))
    (hmem : ∀ ⦃t : T⦄ ⦃q : Q⦄ ⦃p : P⦄,
      (t, (q, p)) ∈ H → coeffValue t * primeValue p ∈ D q) :
    CubeFree H := by
  intro t u q r p v htu hqr hpv
    htqp htqv htrp htrv huqp huqv hurp hurv
  have hcoeffne : coeffValue t ≠ coeffValue u := fun h => htu (hcoeff_inj h)
  have hprimene : primeValue p ≠ primeValue v := fun h => hpv (hprime_inj h)
  have hnot := prime_ray_rectangle_not_compatible
    (S := D q) (T := D r) (W := W)
    (t := coeffValue t) (u := coeffValue u)
    (p := primeValue p) (s := primeValue v)
    (hcoeff t).1 (hcoeff u).1 (hcoeff t).2 (hcoeff u).2 hcoeffne
    (hprime p).1 (hprime v).1 (hprime p).2 (hprime v).2 hprimene
    (hmem htqp) (hmem huqp) (hmem htqv) (hmem huqv)
    (hmem htrp) (hmem hurp) (hmem htrv) (hmem hurv)
  exact hnot (hcompat hqr)

/-- Every ordered coefficient-pair codegree graph is rectangle-free. -/
theorem rayCoefficientPairCells_rectangleFree
    (D : Q → Finset ℕ) (coeffValue : T → ℕ) (primeValue : P → ℕ)
    (H : Finset (T × (Q × P))) {W : ℕ}
    (hcoeff : ∀ t : T, 0 < coeffValue t ∧ coeffValue t ≤ W)
    (hcoeff_inj : Function.Injective coeffValue)
    (hprime : ∀ p : P, W < primeValue p ∧ (primeValue p).Prime)
    (hprime_inj : Function.Injective primeValue)
    (hcompat : ∀ ⦃q r : Q⦄, q ≠ r → CrossCompatible (D q) (D r))
    (hmem : ∀ ⦃t : T⦄ ⦃q : Q⦄ ⦃p : P⦄,
      (t, (q, p)) ∈ H → coeffValue t * primeValue p ∈ D q)
    {tu : T × T} (htu : tu ∈ (Finset.univ : Finset T).offDiag) :
    RectangleFree (coefficientPairCells H tu) := by
  have htune : tu.1 ≠ tu.2 := (Finset.mem_offDiag.mp htu).2.2
  apply primeRayIncidence_rectangleFree
    (D := D) (primeValue := primeValue)
    (E := coefficientPairCells H tu)
    (W := W) (t := coeffValue tu.1) (u := coeffValue tu.2)
    (hcoeff tu.1).1 (hcoeff tu.2).1
    (hcoeff tu.1).2 (hcoeff tu.2).2
    (fun h => htune (hcoeff_inj h)) hprime hprime_inj hcompat
  intro q p hqp
  have hqp' := Finset.mem_filter.mp hqp
  exact ⟨hmem hqp'.2.1, hmem hqp'.2.2⟩

/-- Exact bounded-ray estimate: one edge per occupied `(label,prime)` cell,
plus a C4-free excess for every ordered coefficient pair. -/
theorem rayIncidence_card_le_active_add_c4
    (D : Q → Finset ℕ) (coeffValue : T → ℕ) (primeValue : P → ℕ)
    (H : Finset (T × (Q × P))) {W : ℕ}
    (hcoeff : ∀ t : T, 0 < coeffValue t ∧ coeffValue t ≤ W)
    (hcoeff_inj : Function.Injective coeffValue)
    (hprime : ∀ p : P, W < primeValue p ∧ (primeValue p).Prime)
    (hprime_inj : Function.Injective primeValue)
    (hcompat : ∀ ⦃q r : Q⦄, q ≠ r → CrossCompatible (D q) (D r))
    (hmem : ∀ ⦃t : T⦄ ⦃q : Q⦄ ⦃p : P⦄,
      (t, (q, p)) ∈ H → coeffValue t * primeValue p ∈ D q) :
    (H.card : ℝ) ≤ (activeCells H).card +
      (((Finset.univ : Finset T).offDiag).card : ℝ) *
        ((Fintype.card Q : ℝ) +
          Fintype.card P * Real.sqrt (Fintype.card Q)) := by
  have hbase := incidence_card_le_active_add_pairExcess H
  have hbaseR : (H.card : ℝ) ≤ (activeCells H).card +
      ∑ tu ∈ (Finset.univ : Finset T).offDiag,
        ((coefficientPairCells H tu).card : ℝ) := by
    exact_mod_cast hbase
  have hone : ∀ tu ∈ (Finset.univ : Finset T).offDiag,
      ((coefficientPairCells H tu).card : ℝ) ≤
        (Fintype.card Q : ℝ) +
          Fintype.card P * Real.sqrt (Fintype.card Q) := by
    intro tu htu
    exact rectangleFree_card_le _
      (rayCoefficientPairCells_rectangleFree D coeffValue primeValue H
        hcoeff hcoeff_inj hprime hprime_inj hcompat hmem htu)
  apply hbaseR.trans
  gcongr
  calc
    (∑ tu ∈ (Finset.univ : Finset T).offDiag,
        ((coefficientPairCells H tu).card : ℝ))
      ≤ ∑ _tu ∈ (Finset.univ : Finset T).offDiag,
          ((Fintype.card Q : ℝ) +
            Fintype.card P * Real.sqrt (Fintype.card Q)) :=
        Finset.sum_le_sum hone
    _ = (((Finset.univ : Finset T).offDiag).card : ℝ) *
        ((Fintype.card Q : ℝ) +
          Fintype.card P * Real.sqrt (Fintype.card Q)) := by
      rw [Finset.sum_const, nsmul_eq_mul]

/-- Projection-sensitive alternative, useful when the occupied cell set is
much smaller than the full label-prime rectangle. -/
theorem rayIncidence_card_le_active_sqrt
    (D : Q → Finset ℕ) (coeffValue : T → ℕ) (primeValue : P → ℕ)
    (H : Finset (T × (Q × P))) {W : ℕ}
    (hcoeff : ∀ t : T, 0 < coeffValue t ∧ coeffValue t ≤ W)
    (hcoeff_inj : Function.Injective coeffValue)
    (hprime : ∀ p : P, W < primeValue p ∧ (primeValue p).Prime)
    (hprime_inj : Function.Injective primeValue)
    (hcompat : ∀ ⦃q r : Q⦄, q ≠ r → CrossCompatible (D q) (D r))
    (hmem : ∀ ⦃t : T⦄ ⦃q : Q⦄ ⦃p : P⦄,
      (t, (q, p)) ∈ H → coeffValue t * primeValue p ∈ D q) :
    (H.card : ℝ) ≤ (activeCells H).card +
      (Fintype.card T : ℝ) *
        Real.sqrt (((activeCells H).card : ℝ) *
          (Fintype.card Q +
            Fintype.card P * Real.sqrt (Fintype.card Q))) := by
  have hfree := rayIncidence_cubeFree D coeffValue primeValue H
    hcoeff hcoeff_inj hprime hprime_inj hcompat hmem
  simpa [activeCells, activeBetaGamma, coefficientFiber, alphaFiber] using
    cubeFree_card_le_active H hfree

end RayProjection

end Erdos796
