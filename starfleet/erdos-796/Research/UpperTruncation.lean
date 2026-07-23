import Research.EnvelopeProfile

namespace Erdos796

open Filter Topology

/-- Cross-compatibility is inherited by subsets. -/
theorem CrossCompatible.mono {S T S' T' : Finset ℕ}
    (h : CrossCompatible S T) (hS : S' ⊆ S) (hT : T' ⊆ T) :
    CrossCompatible S' T' := by
  apply Finset.sup_le
  intro m hm
  have hsub : ((S' ×ˢ T').filter fun z => z.1 * z.2 = m) ⊆
      ((S ×ˢ T).filter fun z => z.1 * z.2 = m) := by
    intro z hz
    have hz' := Finset.mem_filter.mp hz
    have hzprod := Finset.mem_product.mp hz'.1
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr ⟨hS hzprod.1, hT hzprod.2⟩, hz'.2⟩
  unfold crossRepCount
  exact (Finset.card_le_card hsub).trans
    (crossRepCount_le_two_of_compatible h m)

/-- Truncate one extracted fiber at a fixed finite core cutoff. -/
def truncatedExtractedFiber (A : Finset ℕ) (n R q : ℕ) : Finset ℕ :=
  (extractedFiber A n.sqrt q).filter fun d => d ≤ R

/-- Capped capacity class of a label. -/
def cutoffCapacityIndex (R : ℕ) (hR : 0 < R) (J : ℕ) : Fin R :=
  ⟨min (J - 1) (R - 1), by omega⟩

/-- Truncated fibers from an admissible set are enveloped by one compatible
finite profile, apart from at most `2^R` singleton-occurrence types. -/
theorem exists_truncatedFiberEnvelope
    {A : Finset ℕ} {n R : ℕ} (hR : 0 < R)
    (hAint : A ⊆ Finset.Icc 1 n) (hA : HasRepBound 3 A) :
    ∃ P : FiberProfile R,
      (∀ q ∈ sqrtPrimeLabels n,
        q ∉ exceptionalTypeIndices (sqrtPrimeLabels n)
          (fun r => truncatedExtractedFiber A n R r) →
        (truncatedExtractedFiber A n R q).card ≤
          (P.fiber (cutoffCapacityIndex R hR (n / q))).card) ∧
      (exceptionalTypeIndices (sqrtPrimeLabels n)
        (fun r => truncatedExtractedFiber A n R r)).card ≤ 2 ^ R := by
  classical
  let I := sqrtPrimeLabels n
  let D : ℕ → Finset ℕ := fun q => truncatedExtractedFiber A n R q
  let cap : ℕ → Fin R := fun q => cutoffCapacityIndex R hR (n / q)
  have hpos : ∀ q ∈ I, ∀ d ∈ D q, 0 < d := by
    intro q hq d hd
    exact (Finset.mem_Icc.mp
      (Finset.mem_filter.mp (Finset.mem_filter.mp hd).1).1).1
  have hbound : ∀ q ∈ I, ∀ d ∈ D q, d ≤ (cap q).val + 1 := by
    intro q hq d hd
    have hd' := Finset.mem_filter.mp hd
    have hdExtract := Finset.mem_filter.mp hd'.1
    have hdR := hd'.2
    have hqdA := hdExtract.2
    have hqdle : q * d ≤ n := (Finset.mem_Icc.mp (hAint hqdA)).2
    have hqprime := (Finset.mem_filter.mp hq).2
    have hdJ : d ≤ n / q := (Nat.le_div_iff_mul_le hqprime.pos).2 (by
      simpa [Nat.mul_comm] using hqdle)
    dsimp [cap, cutoffCapacityIndex]
    omega
  have hcompat : ∀ q ∈ I, ∀ r ∈ I, q ≠ r →
      CrossCompatible (D q) (D r) := by
    intro q hq r hr hqr
    have hq' := Finset.mem_filter.mp hq
    have hr' := Finset.mem_filter.mp hr
    have hbase := extractedFiber_crossCompatible
      (K := n.sqrt) (q := q) (r := r) hA
      (by have := (Finset.mem_Icc.mp hq'.1).1; omega)
      (by have := (Finset.mem_Icc.mp hr'.1).1; omega)
      hq'.2 hr'.2 hqr
    apply hbase.mono
    · intro d hd
      exact (Finset.mem_filter.mp hd).1
    · intro d hd
      exact (Finset.mem_filter.mp hd).1
  rcases exists_envelopeProfile hR I D cap hpos hbound hcompat with ⟨P, hP⟩
  refine ⟨P, ?_, ?_⟩
  · intro q hq hqne
    exact hP q hq hqne
  · have hDU : ∀ q ∈ I, D q ⊆ Finset.Icc 1 R := by
      intro q hq d hd
      have hd' := Finset.mem_filter.mp hd
      exact Finset.mem_Icc.mpr
        ⟨(Finset.mem_Icc.mp (Finset.mem_filter.mp hd'.1).1).1, hd'.2⟩
    have he := exceptionalTypeIndices_card_le_powerset I D
      (Finset.Icc 1 R) hDU
    simpa using he

/-- Canonical capacity classes independent of the chosen profile. -/
def canonicalCapacityClassLabels (R : ℕ) (hR : 0 < R)
    (n : ℕ) (i : Fin R) : Finset ℕ :=
  (emptyFiberProfile R hR).capacityClassLabels n i

lemma capacityClassLabels_eq_canonical {R : ℕ} (hR : 0 < R)
    (P : FiberProfile R) (n : ℕ) (i : Fin R) :
    P.capacityClassLabels n i = canonicalCapacityClassLabels R hR n i := by
  ext q
  simp only [FiberProfile.capacityClassLabels,
    canonicalCapacityClassLabels, Finset.mem_filter]
  constructor <;> rintro ⟨hq, heq⟩ <;> refine ⟨hq, ?_⟩
  · apply Fin.ext
    have hv := congrArg Fin.val heq
    exact hv
  · apply Fin.ext
    have hv := congrArg Fin.val heq
    exact hv

/-- Uniform finite-cutoff PNT discrepancy for all capacity profiles. -/
noncomputable def profileApproxError (R : ℕ) (hR : 0 < R) (n : ℕ) : ℝ :=
  ∑ i : Fin R, (R : ℝ) *
    |((canonicalCapacityClassLabels R hR n i).card : ℝ) /
        ((n : ℝ) / Real.log (n : ℝ)) - profileLayerWeight i|

/-- At every fixed cutoff, the uniform profile discrepancy tends to zero. -/
theorem tendsto_profileApproxError_zero (R : ℕ) (hR : 0 < R) :
    Tendsto (profileApproxError R hR) atTop (nhds 0) := by
  have hi : ∀ i : Fin R, Tendsto (fun n : ℕ => (R : ℝ) *
      |((canonicalCapacityClassLabels R hR n i).card : ℝ) /
          ((n : ℝ) / Real.log (n : ℝ)) - profileLayerWeight i|) atTop
      (nhds 0) := by
    intro i
    have hclass :=
      (emptyFiberProfile R hR).tendsto_capacityClassLabels_card_div_normalization i
    have hsub := hclass.sub
      (tendsto_const_nhds (x := profileLayerWeight i))
    have habs := hsub.abs
    have hmul := habs.const_mul (R : ℝ)
    simpa [canonicalCapacityClassLabels] using hmul
  change Tendsto (fun n : ℕ => ∑ i : Fin R, (R : ℝ) *
      |((canonicalCapacityClassLabels R hR n i).card : ℝ) /
          ((n : ℝ) / Real.log (n : ℝ)) - profileLayerWeight i|) atTop (nhds 0)
  simpa using tendsto_finsetSum Finset.univ (fun i _ => hi i)

/-- The profile selected at a given `n` may vary arbitrarily: fixed-cutoff
capacity weights still approximate its `beta` uniformly. -/
theorem FiberProfile.baseCount_div_le_beta_add_error {R : ℕ}
    (hR : 0 < R) (P : FiberProfile R) {n : ℕ} (hn : 1 < n) :
    (P.baseCount n : ℝ) / ((n : ℝ) / Real.log (n : ℝ)) ≤
      P.beta + profileApproxError R hR n := by
  have hnR : (0 : ℝ) < n := by positivity
  have hlog : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn)
  have hden : 0 < (n : ℝ) / Real.log (n : ℝ) := div_pos hnR hlog
  rw [P.baseCount_eq_capacityClasses, Nat.cast_sum, Finset.sum_div,
    P.beta_eq_weighted]
  unfold profileApproxError
  push_cast
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i hi
  have hclass := capacityClassLabels_eq_canonical hR P n i
  rw [hclass]
  have hcardNat : (P.fiber i).card ≤ R := by
    have hc := Finset.card_le_card (show P.fiber i ⊆ Finset.Icc 1 R by
      intro d hd
      exact Finset.mem_Icc.mpr
        ⟨P.positive i d hd, (P.bounded i d hd).trans (by omega)⟩)
    simpa using hc
  have hcard : ((P.fiber i).card : ℝ) ≤ R := by exact_mod_cast hcardNat
  have hcard0 : (0 : ℝ) ≤ (P.fiber i).card := by positivity
  let x : ℝ := ((canonicalCapacityClassLabels R hR n i).card : ℝ) /
    ((n : ℝ) / Real.log (n : ℝ))
  let w : ℝ := profileLayerWeight i
  have habs : x - w ≤ |x - w| := le_abs_self _
  have hmul1 := mul_le_mul_of_nonneg_left habs hcard0
  have hmul2 := mul_le_mul_of_nonneg_right hcard (abs_nonneg (x - w))
  calc
    ((P.fiber i).card : ℝ) *
          ((canonicalCapacityClassLabels R hR n i).card : ℝ) /
          ((n : ℝ) / Real.log (n : ℝ)) =
        profileLayerWeight i * (P.fiber i).card +
          ((P.fiber i).card : ℝ) * (x - w) := by
      dsimp [x, w]
      ring
    _ ≤ profileLayerWeight i * (P.fiber i).card +
          (R : ℝ) * |x - w| :=
      by simpa [add_comm] using
        add_le_add_left (hmul1.trans hmul2)
          (profileLayerWeight i * (P.fiber i).card)
    _ = _ := by rfl

lemma profile_sum_eq_baseCount {R : ℕ} (hR : 0 < R)
    (P : FiberProfile R) (n : ℕ) :
    (∑ q ∈ sqrtPrimeLabels n,
      (P.fiber (cutoffCapacityIndex R hR (n / q))).card) =
      P.baseCount n := by
  unfold FiberProfile.baseCount
  apply Finset.sum_congr rfl
  intro q hq
  rw [P.base_eq_fiber_capacityIndex]
  congr 2

/-- Aggregate truncated-fiber incidence count is bounded by one finite profile
plus the explicit singleton-type error `R*2^R`. -/
theorem exists_profile_sum_bound_truncatedFibers
    {A : Finset ℕ} {n R : ℕ} (hR : 0 < R)
    (hAint : A ⊆ Finset.Icc 1 n) (hA : HasRepBound 3 A) :
    ∃ P : FiberProfile R,
      (∑ q ∈ sqrtPrimeLabels n,
        (truncatedExtractedFiber A n R q).card) ≤
      (∑ q ∈ sqrtPrimeLabels n,
        (P.fiber (cutoffCapacityIndex R hR (n / q))).card) +
      R * 2 ^ R := by
  classical
  rcases exists_truncatedFiberEnvelope hR hAint hA with ⟨P, henv, hexc⟩
  let I := sqrtPrimeLabels n
  let D : ℕ → Finset ℕ := fun q => truncatedExtractedFiber A n R q
  let cap : ℕ → Fin R := fun q => cutoffCapacityIndex R hR (n / q)
  let E := exceptionalTypeIndices I D
  have hDcard : ∀ q ∈ I, (D q).card ≤ R := by
    intro q hq
    have hsub : D q ⊆ Finset.Icc 1 R := by
      intro d hd
      have hd' := Finset.mem_filter.mp hd
      exact Finset.mem_Icc.mpr
        ⟨(Finset.mem_Icc.mp (Finset.mem_filter.mp hd'.1).1).1, hd'.2⟩
    calc
      (D q).card ≤ (Finset.Icc 1 R).card := Finset.card_le_card hsub
      _ = R := by simp [hR]
  have hpoint : ∀ q ∈ I,
      (D q).card ≤ (P.fiber (cap q)).card + if q ∈ E then R else 0 := by
    intro q hq
    by_cases hqE : q ∈ E
    · rw [if_pos hqE]
      exact (hDcard q hq).trans (Nat.le_add_left _ _)
    · rw [if_neg hqE, Nat.add_zero]
      exact henv q hq hqE
  refine ⟨P, ?_⟩
  change (∑ q ∈ I, (D q).card) ≤
    (∑ q ∈ I, (P.fiber (cap q)).card) + R * 2 ^ R
  calc
    (∑ q ∈ I, (D q).card) ≤
        ∑ q ∈ I, ((P.fiber (cap q)).card + if q ∈ E then R else 0) :=
      Finset.sum_le_sum hpoint
    _ = (∑ q ∈ I, (P.fiber (cap q)).card) + R * E.card := by
      rw [Finset.sum_add_distrib]
      congr 1
      rw [← Finset.sum_filter]
      have hfilter : I.filter (fun q => q ∈ E) = E := by
        ext q
        simp [E, exceptionalTypeIndices]
      rw [hfilter, Finset.sum_const, nsmul_eq_mul]
      simp [Nat.mul_comm]
    _ ≤ (∑ q ∈ I, (P.fiber (cap q)).card) + R * 2 ^ R := by
      exact Nat.add_le_add_left (Nat.mul_le_mul_left R hexc) _

/-- Uniform finite-cutoff upper bound for the truncated part of every
admissible fiber family. -/
theorem truncatedFiberSum_div_le_variational
    {A : Finset ℕ} {n R : ℕ} (hR : 0 < R) (hn : 1 < n)
    (hAint : A ⊆ Finset.Icc 1 n) (hA : HasRepBound 3 A) :
    ((∑ q ∈ sqrtPrimeLabels n,
      (truncatedExtractedFiber A n R q).card : ℕ) : ℝ) /
        ((n : ℝ) / Real.log (n : ℝ)) ≤
      primeMass R + variationalLimit + profileApproxError R hR n +
        (R * 2 ^ R : ℕ) / ((n : ℝ) / Real.log (n : ℝ)) := by
  rcases exists_profile_sum_bound_truncatedFibers hR hAint hA with ⟨P, hP⟩
  have hnR : (0 : ℝ) < n := by positivity
  have hlog : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn)
  have hden : 0 < (n : ℝ) / Real.log (n : ℝ) := div_pos hnR hlog
  have hPR : ((∑ q ∈ sqrtPrimeLabels n,
      (truncatedExtractedFiber A n R q).card : ℕ) : ℝ) ≤
      (P.baseCount n : ℝ) + (R * 2 ^ R : ℕ) := by
    rw [← profile_sum_eq_baseCount hR P n]
    exact_mod_cast hP
  have hbase := P.baseCount_div_le_beta_add_error hR hn
  have hbeta : P.beta ≤ primeMass R + variationalLimit := by
    have hg := P.gamma_le_variationalLimit
    unfold FiberProfile.gamma at hg
    linarith
  calc
    ((∑ q ∈ sqrtPrimeLabels n,
        (truncatedExtractedFiber A n R q).card : ℕ) : ℝ) /
          ((n : ℝ) / Real.log (n : ℝ)) ≤
      ((P.baseCount n : ℝ) + (R * 2 ^ R : ℕ)) /
          ((n : ℝ) / Real.log (n : ℝ)) :=
        div_le_div_of_nonneg_right hPR hden.le
    _ = (P.baseCount n : ℝ) / ((n : ℝ) / Real.log (n : ℝ)) +
        (R * 2 ^ R : ℕ) / ((n : ℝ) / Real.log (n : ℝ)) := by ring
    _ ≤ primeMass R + variationalLimit + profileApproxError R hR n +
        (R * 2 ^ R : ℕ) / ((n : ℝ) / Real.log (n : ℝ)) := by
      linarith

end Erdos796
