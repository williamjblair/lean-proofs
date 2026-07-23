import Research.HyperbolaC4
import Research.RayProjection
import Research.GenericProfileAsymptotic

namespace Erdos796

open Filter Topology

section TypedHyperbola

variable {Q P : Type*} [Fintype Q] [Fintype P]
  [DecidableEq Q] [DecidableEq P]

/-- Value-map version of the hyperbolic C4 estimate.  This is the form needed
when vertices are labels and primes carrying injective natural-number values. -/
theorem rectangleFree_hyperbola_card_le_values
    (E : Finset (Q × P)) (qValue : Q → ℕ) (pValue : P → ℕ)
    {u P₀ n : ℕ} (hu : 0 < u)
    (hqinj : Function.Injective qValue)
    (hpinj : Function.Injective pValue)
    (hfree : RectangleFree E)
    (hedge : ∀ z ∈ E,
      (qValue z.1).Prime ∧ n.sqrt < qValue z.1 ∧
      P₀ < pValue z.2 ∧ pValue z.2 ≤ n.sqrt ∧
      u * qValue z.1 * pValue z.2 ≤ n) :
    (E.card : ℝ) ≤ hyperbolaC4Majorant u P₀ n := by
  let y := hyperbolaSplit n
  let Elo := E.filter fun z => pValue z.2 ≤ y
  let Ehi := E.filter fun z => y < pValue z.2
  have hcard : E.card = Elo.card + Ehi.card := by
    have h := Finset.card_filter_add_card_filter_not
      (s := E) (fun z => pValue z.2 ≤ y)
    simpa [Elo, Ehi, not_le] using h.symm
  let Xlo := (Finset.univ : Finset Q).filter fun q =>
    qValue q ≤ n / (u * (P₀ + 1)) ∧ ∃ p, (q, p) ∈ Elo
  let Ylo := (Finset.univ : Finset P).filter fun p =>
    1 ≤ pValue p ∧ pValue p ≤ y
  let Xhi := (Finset.univ : Finset Q).filter fun q =>
    qValue q ≤ n / (u * (y + 1)) ∧ ∃ p, (q, p) ∈ Ehi
  let Yhi := (Finset.univ : Finset P).filter fun p =>
    1 ≤ pValue p ∧ pValue p ≤ n.sqrt
  have hloSub : Elo ⊆ Xlo.product Ylo := by
    intro z hz
    have hz' := Finset.mem_filter.mp hz
    have he := hedge z hz'.1
    apply Finset.mem_product.mpr
    constructor
    · simp only [Xlo, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · apply (Nat.le_div_iff_mul_le (mul_pos hu (by omega))).2
        calc
          qValue z.1 * (u * (P₀ + 1)) =
              u * qValue z.1 * (P₀ + 1) := by ring
          _ ≤ u * qValue z.1 * pValue z.2 := by gcongr; omega
          _ ≤ n := he.2.2.2.2
      · exact ⟨z.2, hz⟩
    · simp only [Ylo, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨by omega, hz'.2⟩
  have hhiSub : Ehi ⊆ Xhi.product Yhi := by
    intro z hz
    have hz' := Finset.mem_filter.mp hz
    have he := hedge z hz'.1
    apply Finset.mem_product.mpr
    constructor
    · simp only [Xhi, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · apply (Nat.le_div_iff_mul_le (mul_pos hu (by omega))).2
        calc
          qValue z.1 * (u * (y + 1)) =
              u * qValue z.1 * (y + 1) := by ring
          _ ≤ u * qValue z.1 * pValue z.2 := by gcongr; omega
          _ ≤ n := he.2.2.2.2
      · exact ⟨z.2, hz⟩
    · simp only [Yhi, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨by omega, he.2.2.2.1⟩
  have hloFree : RectangleFree Elo := hfree.mono (Finset.filter_subset _ _)
  have hhiFree : RectangleFree Ehi := hfree.mono (Finset.filter_subset _ _)
  have hlo := rectangleFree_card_le_ambient Elo Xlo Ylo hloFree hloSub
  have hhi := rectangleFree_card_le_ambient Ehi Xhi Yhi hhiFree hhiSub
  have hXlo : Xlo.card ≤ Nat.primeCounting (n / (u * (P₀ + 1))) := by
    rw [← Nat.primesLE_card_eq_primeCounting]
    apply Finset.card_le_card_of_injOn qValue
    · intro q hq
      have hq' := (Finset.mem_filter.mp hq).2
      rcases hq'.2 with ⟨p, hp⟩
      exact Nat.mem_primesLE.mpr
        ⟨hq'.1, (hedge (q, p) (Finset.filter_subset _ _ hp)).1⟩
    · exact hqinj.injOn
  have hXhi : Xhi.card ≤ Nat.primeCounting (n / (u * (y + 1))) := by
    rw [← Nat.primesLE_card_eq_primeCounting]
    apply Finset.card_le_card_of_injOn qValue
    · intro q hq
      have hq' := (Finset.mem_filter.mp hq).2
      rcases hq'.2 with ⟨p, hp⟩
      exact Nat.mem_primesLE.mpr
        ⟨hq'.1, (hedge (q, p) (Finset.filter_subset _ _ hp)).1⟩
    · exact hqinj.injOn
  have hYlo : Ylo.card ≤ y := by
    have h := Finset.card_le_card_of_injOn pValue
      (s := Ylo) (t := Finset.Icc 1 y)
      (by intro p hp; exact Finset.mem_Icc.mpr (Finset.mem_filter.mp hp).2)
      hpinj.injOn
    simpa using h
  have hYhi : Yhi.card ≤ n.sqrt := by
    have h := Finset.card_le_card_of_injOn pValue
      (s := Yhi) (t := Finset.Icc 1 n.sqrt)
      (by intro p hp; exact Finset.mem_Icc.mpr (Finset.mem_filter.mp hp).2)
      hpinj.injOn
    simpa using h
  have hlo' : (Elo.card : ℝ) ≤
      (Nat.primeCounting (n / (u * (P₀ + 1))) : ℝ) +
        (y : ℝ) * Real.sqrt (Nat.primeCounting (n / (u * (P₀ + 1))) : ℝ) := by
    calc
      (Elo.card : ℝ) ≤ Xlo.card + Ylo.card * Real.sqrt Xlo.card := hlo
      _ ≤ _ := by
        gcongr <;> exact_mod_cast hXlo <;> exact_mod_cast hYlo
  have hhi' : (Ehi.card : ℝ) ≤
      (Nat.primeCounting (n / (u * (y + 1))) : ℝ) +
        (n.sqrt : ℝ) * Real.sqrt (Nat.primeCounting (n / (u * (y + 1))) : ℝ) := by
    calc
      (Ehi.card : ℝ) ≤ Xhi.card + Yhi.card * Real.sqrt Xhi.card := hhi
      _ ≤ _ := by
        gcongr <;> exact_mod_cast hXhi <;> exact_mod_cast hYhi
  have hsum := add_le_add hlo' hhi'
  rw [hcard]
  push_cast
  simpa only [hyperbolaC4Majorant, y, add_assoc] using hsum

end TypedHyperbola

section RayTail

variable {T Q P : Type*} [Fintype T] [Fintype Q] [Fintype P]
  [DecidableEq T] [DecidableEq Q] [DecidableEq P]

/-- Every occupied label-prime cell is a literal semiprime-tail pair. -/
theorem activeRayCells_card_le_profileTail
    (H : Finset (T × (Q × P)))
    (coeffValue : T → ℕ) (labelValue : Q → ℕ) (primeValue : P → ℕ)
    {P₀ n : ℕ}
    (hcoeff : ∀ t, 0 < coeffValue t)
    (hlabelinj : Function.Injective labelValue)
    (hprimeinj : Function.Injective primeValue)
    (hlabel : ∀ q, (labelValue q).Prime ∧ n.sqrt < labelValue q)
    (hprime : ∀ p, (primeValue p).Prime ∧ P₀ < primeValue p ∧
      primeValue p ≤ n.sqrt)
    (hproduct : ∀ ⦃t q p⦄, (t, (q, p)) ∈ H →
      coeffValue t * labelValue q * primeValue p ≤ n) :
    (activeCells H).card ≤ profileTailCount P₀ n := by
  rw [← profilePrimePairs_card_eq_tail]
  apply Finset.card_le_card_of_injOn
    (fun c : Q × P => (primeValue c.2, labelValue c.1))
  · intro c hc
    have hc' := (Finset.mem_filter.mp hc).2
    rcases hc' with ⟨t, ht⟩
    have hinc : (t, c) ∈ H := (Finset.mem_filter.mp ht).2
    have hq := hlabel c.1
    have hp := hprime c.2
    have ht1 : 1 ≤ coeffValue t := hcoeff t
    have hp1 : 1 ≤ primeValue c.2 := hp.1.one_le
    have hpq : primeValue c.2 * labelValue c.1 ≤ n := by
      calc
        primeValue c.2 * labelValue c.1 =
            1 * (labelValue c.1 * primeValue c.2) := by ring
        _ ≤ coeffValue t * (labelValue c.1 * primeValue c.2) := by
          gcongr
        _ = coeffValue t * labelValue c.1 * primeValue c.2 := by ring
        _ ≤ n := hproduct hinc
    have hqn : labelValue c.1 ≤ n := by
      calc
        labelValue c.1 = 1 * labelValue c.1 := by simp
        _ ≤ primeValue c.2 * labelValue c.1 := by gcongr
        _ ≤ n := hpq
    unfold profilePrimePairs
    apply Finset.mem_filter.mpr
    constructor
    · apply Finset.mem_product.mpr
      constructor
      · apply Finset.mem_filter.mpr
        exact ⟨Finset.mem_Icc.mpr ⟨by
          change P₀ + 1 ≤ primeValue c.2
          omega, hp.2.2⟩, hp.1⟩
      · unfold sqrtPrimeLabels
        apply Finset.mem_filter.mpr
        exact ⟨Finset.mem_Icc.mpr ⟨by
          change n.sqrt + 1 ≤ labelValue c.1
          omega, hqn⟩, hq.1⟩
    · exact hpq
  · intro a ha b hb hab
    apply Prod.ext
    · exact hlabelinj (congrArg Prod.snd hab)
    · exact hprimeinj (congrArg Prod.fst hab)

/-- Exact prime-ray accounting: one semiprime-tail charge per active cell and
one hyperbolic C4 majorant for each ordered coefficient pair. -/
theorem rayIncidence_card_le_tail_add_hyperbola
    (D : Q → Finset ℕ)
    (coeffValue : T → ℕ) (labelValue : Q → ℕ) (primeValue : P → ℕ)
    (H : Finset (T × (Q × P))) {W P₀ n : ℕ}
    (hcoeff : ∀ t : T, 0 < coeffValue t ∧ coeffValue t ≤ W)
    (hcoeffinj : Function.Injective coeffValue)
    (hlabelinj : Function.Injective labelValue)
    (hprimeinj : Function.Injective primeValue)
    (hWP : W ≤ P₀)
    (hlabel : ∀ q, (labelValue q).Prime ∧ n.sqrt < labelValue q)
    (hprime : ∀ p, (primeValue p).Prime ∧ P₀ < primeValue p ∧
      primeValue p ≤ n.sqrt)
    (hcompat : ∀ ⦃q r : Q⦄, q ≠ r → CrossCompatible (D q) (D r))
    (hmem : ∀ ⦃t q p⦄, (t, (q, p)) ∈ H →
      coeffValue t * primeValue p ∈ D q)
    (hproduct : ∀ ⦃t q p⦄, (t, (q, p)) ∈ H →
      coeffValue t * labelValue q * primeValue p ≤ n) :
    (H.card : ℝ) ≤ (profileTailCount P₀ n : ℝ) +
      ∑ tu ∈ (Finset.univ : Finset T).offDiag,
        hyperbolaC4Majorant (coeffValue tu.1) P₀ n := by
  have hprimeRay : ∀ p : P, W < primeValue p ∧ (primeValue p).Prime := by
    intro p
    exact ⟨lt_of_le_of_lt hWP (hprime p).2.1, (hprime p).1⟩
  have hbase := incidence_card_le_active_add_pairExcess H
  have hbaseR : (H.card : ℝ) ≤ (activeCells H).card +
      ∑ tu ∈ (Finset.univ : Finset T).offDiag,
        ((coefficientPairCells H tu).card : ℝ) := by
    exact_mod_cast hbase
  have hactive := activeRayCells_card_le_profileTail H coeffValue labelValue
    primeValue (fun t => (hcoeff t).1) hlabelinj hprimeinj hlabel hprime hproduct
  have hpairs : ∀ tu ∈ (Finset.univ : Finset T).offDiag,
      ((coefficientPairCells H tu).card : ℝ) ≤
        hyperbolaC4Majorant (coeffValue tu.1) P₀ n := by
    intro tu htu
    apply rectangleFree_hyperbola_card_le_values
      (coefficientPairCells H tu) labelValue primeValue
      (hcoeff tu.1).1 hlabelinj hprimeinj
    · exact rayCoefficientPairCells_rectangleFree D coeffValue primeValue H
        hcoeff hcoeffinj hprimeRay hprimeinj hcompat hmem htu
    · intro z hz
      have hz' := (Finset.mem_filter.mp hz).2
      exact ⟨(hlabel z.1).1, (hlabel z.1).2,
        (hprime z.2).2.1, (hprime z.2).2.2, hproduct hz'.1⟩
  calc
    (H.card : ℝ) ≤ (activeCells H).card +
        ∑ tu ∈ (Finset.univ : Finset T).offDiag,
          ((coefficientPairCells H tu).card : ℝ) := hbaseR
    _ ≤ (profileTailCount P₀ n : ℝ) +
        ∑ tu ∈ (Finset.univ : Finset T).offDiag,
          hyperbolaC4Majorant (coeffValue tu.1) P₀ n := by
      exact add_le_add (by exact_mod_cast hactive)
        (Finset.sum_le_sum hpairs)

/-- Fixed-coefficient normalized limit of all pair-multiplicity errors. -/
noncomputable def rayPairLimit (coeffValue : T → ℕ) (P₀ : ℕ) : ℝ :=
  ∑ tu ∈ ((Finset.univ : Finset T).offDiag),
    (1 : ℝ) / (coeffValue tu.1 * (P₀ + 1))

/-- The finite sum of hyperbolic majorants has its expected exact limit. -/
theorem tendsto_rayPairMajorants_normalized
    (coeffValue : T → ℕ) (P₀ : ℕ)
    (hcoeff : ∀ t, 0 < coeffValue t) :
    Tendsto (fun n : ℕ =>
      (∑ tu ∈ ((Finset.univ : Finset T).offDiag),
        hyperbolaC4Majorant (coeffValue tu.1) P₀ n) /
          ((n : ℝ) / Real.log (n : ℝ))) atTop
      (nhds (rayPairLimit coeffValue P₀)) := by
  have htu : ∀ tu ∈ (Finset.univ : Finset T).offDiag,
      Tendsto (fun n : ℕ =>
        hyperbolaC4Majorant (coeffValue tu.1) P₀ n /
          ((n : ℝ) / Real.log (n : ℝ))) atTop
        (nhds ((1 : ℝ) / (coeffValue tu.1 * (P₀ + 1)))) := by
    intro tu htu
    exact tendsto_hyperbolaC4Majorant_normalized _ _ (hcoeff tu.1)
  have hsum := tendsto_finsetSum (Finset.univ : Finset T).offDiag htu
  simpa only [Finset.sum_div, rayPairLimit] using hsum

/-- Injective coefficients in `[1,W]` have total pair error at most
`W²/(P₀+1)`. -/
theorem rayPairLimit_le_square
    (coeffValue : T → ℕ) {W P₀ : ℕ}
    (hcoeff : ∀ t, 0 < coeffValue t ∧ coeffValue t ≤ W)
    (hinj : Function.Injective coeffValue) :
    rayPairLimit coeffValue P₀ ≤
      ((W : ℝ) * W) / (P₀ + 1) := by
  have hcard : Fintype.card T ≤ W := by
    have h := Finset.card_le_card_of_injOn coeffValue
      (s := (Finset.univ : Finset T)) (t := Finset.Icc 1 W)
      (by intro t ht; exact Finset.mem_Icc.mpr ⟨(hcoeff t).1, (hcoeff t).2⟩)
      hinj.injOn
    simpa using h
  have hoff : ((Finset.univ : Finset T).offDiag).card ≤ W * W := by
    rw [Finset.offDiag_card]
    exact (Nat.sub_le _ _).trans (Nat.mul_le_mul hcard hcard)
  have hterm : ∀ tu ∈ (Finset.univ : Finset T).offDiag,
      (1 : ℝ) / (coeffValue tu.1 * (P₀ + 1)) ≤
        (1 : ℝ) / (P₀ + 1) := by
    intro tu htu
    apply one_div_le_one_div_of_le (by positivity)
    exact_mod_cast Nat.le_mul_of_pos_left (P₀ + 1) (hcoeff tu.1).1
  unfold rayPairLimit
  calc
    (∑ tu ∈ ((Finset.univ : Finset T).offDiag),
        (1 : ℝ) / (coeffValue tu.1 * (P₀ + 1)))
      ≤ ∑ _tu ∈ ((Finset.univ : Finset T).offDiag),
          (1 : ℝ) / (P₀ + 1) := Finset.sum_le_sum hterm
    _ = (((Finset.univ : Finset T).offDiag).card : ℝ) /
        (P₀ + 1) := by
      rw [Finset.sum_const, nsmul_eq_mul]
      ring
    _ ≤ ((W : ℝ) * W) / (P₀ + 1) := by
      gcongr
      exact_mod_cast hoff

end RayTail

end Erdos796
