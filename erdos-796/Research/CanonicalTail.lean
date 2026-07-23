import Research.CanonicalDyadicAsymptotic

namespace Erdos796

open Filter Topology

/-- Relative density of primes in the `k`-th dyadic interval. -/
noncomputable def canonicalPrimeDensity (k : ℕ) : ℝ :=
  ((dyadicPrimes k).card : ℝ) / (((2 ^ k : ℕ) : ℝ))

lemma canonicalPrimeDensity_nonneg (k : ℕ) :
    0 ≤ canonicalPrimeDensity k := by
  unfold canonicalPrimeDensity
  positivity

lemma canonicalPrimeDensity_le_one (k : ℕ) :
    canonicalPrimeDensity k ≤ 1 := by
  unfold canonicalPrimeDensity
  apply (div_le_one (by positivity)).2
  exact_mod_cast (show (dyadicPrimes k).card ≤ 2 ^ k by
    exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq
      (dyadicInterval_card k))

/-- The relative prime density of dyadic intervals tends to zero. -/
theorem tendsto_canonicalPrimeDensity_zero :
    Tendsto canonicalPrimeDensity atTop (nhds 0) := by
  have hmodel : Tendsto (fun k : ℕ =>
      dyadicPrimeConstant / (((k + 1 : ℕ) : ℝ))) atTop (nhds 0) := by
    have hInv : Tendsto (fun k : ℕ =>
        (((k + 1 : ℕ) : ℝ))⁻¹) atTop (nhds 0) := by
      have hcast : Tendsto (fun k : ℕ => (((k + 1 : ℕ) : ℝ))) atTop atTop :=
        tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
      simpa [Function.comp_def] using tendsto_inv_atTop_zero.comp hcast
    simpa [div_eq_mul_inv] using hInv.const_mul dyadicPrimeConstant
  apply squeeze_zero' (g := fun k : ℕ =>
      dyadicPrimeConstant / (((k + 1 : ℕ) : ℝ)))
  · exact Filter.Eventually.of_forall canonicalPrimeDensity_nonneg
  · filter_upwards [eventually_dyadicPrimes_card_le] with k hk
    unfold canonicalPrimeDensity
    have hpow : (0 : ℝ) < (((2 ^ k : ℕ) : ℝ)) := by positivity
    apply (div_le_iff₀ hpow).2
    simpa [div_mul_eq_mul_div] using hk
  · exact hmodel

/-- The summable majorant used after reversing the low-prime dyadic index. -/
noncomputable def canonicalRootDominant (z : ℕ × ℕ) : ℝ :=
  if z.2 < z.1 + 1 then 2 * rootGeometricWeight z.1 else 0

lemma rootGeometricWeight_pos (j : ℕ) : 0 < rootGeometricWeight j := by
  unfold rootGeometricWeight
  positivity

lemma canonicalRootDominant_nonneg (z : ℕ × ℕ) :
    0 ≤ canonicalRootDominant z := by
  unfold canonicalRootDominant
  split_ifs
  · exact mul_nonneg (by norm_num) (rootGeometricWeight_pos z.1).le
  · rfl

lemma summable_nat_succ_mul_rootGeometric :
    Summable (fun j : ℕ => (((j + 1 : ℕ) : ℝ)) *
      rootGeometricWeight j) := by
  let r : ℝ := (Real.sqrt 2)⁻¹
  have hr : ‖r‖ < 1 := by
    dsimp [r]
    rw [abs_of_pos (by positivity : 0 < (Real.sqrt 2)⁻¹)]
    exact (inv_lt_one₀ (show 0 < Real.sqrt 2 by positivity)).2
      (by
        have hs0 := Real.sqrt_nonneg 2
        have hs2 := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
        nlinarith)
  have hlin : Summable (fun j : ℕ => (j : ℝ) * r ^ j) := by
    simpa using summable_pow_mul_geometric_of_norm_lt_one 1 hr
  have hgeom : Summable (fun j : ℕ => r ^ j) :=
    summable_geometric_of_norm_lt_one hr
  have hadd := hlin.add hgeom
  apply hadd.congr
  intro j
  rw [rootGeometricWeight_eq_pow]
  dsimp [r]
  push_cast
  ring

/-- The reversed-index root kernel is summable on `ℕ × ℕ`. -/
theorem summable_canonicalRootDominant :
    Summable canonicalRootDominant := by
  rw [summable_prod_of_nonneg canonicalRootDominant_nonneg]
  constructor
  · intro j
    apply summable_of_ne_finset_zero (s := Finset.range (j + 1))
    intro r hr
    have hnot : ¬r < j + 1 := by simpa using hr
    simp [canonicalRootDominant, hnot]
  · have heq : (fun j : ℕ => ∑' r : ℕ,
        canonicalRootDominant (j, r)) =
        fun j : ℕ => 2 * (((j + 1 : ℕ) : ℝ)) *
          rootGeometricWeight j := by
      funext j
      rw [tsum_eq_sum (s := Finset.range (j + 1))]
      · calc
          (∑ r ∈ Finset.range (j + 1), canonicalRootDominant (j, r)) =
              ∑ _r ∈ Finset.range (j + 1),
                2 * rootGeometricWeight j := by
            apply Finset.sum_congr rfl
            intro r hr
            rw [canonicalRootDominant, if_pos (Finset.mem_range.mp hr)]
          _ = 2 * (((j + 1 : ℕ) : ℝ)) * rootGeometricWeight j := by
            rw [Finset.sum_const, nsmul_eq_mul, Finset.card_range]
            push_cast
            ring
      · intro r hr
        have hnot : ¬r < j + 1 := by simpa using hr
        simp [canonicalRootDominant, hnot]
    rw [heq]
    simpa [mul_assoc] using
      Summable.mul_left 2 summable_nat_succ_mul_rootGeometric

/-- Reversed low-prime kernel.  The second coordinate records distance from
`K+1`, so the moving diagonal becomes the fixed condition `r<j+1`. -/
noncomputable def canonicalRootKernel (K : ℕ) (z : ℕ × ℕ) : ℝ :=
  if z.2 < K + 2 ∧ z.2 < z.1 + 1 then
    2 * rootGeometricWeight z.1 * canonicalPrimeDensity (K + 1 - z.2)
  else 0

lemma canonicalRootKernel_nonneg (K : ℕ) (z : ℕ × ℕ) :
    0 ≤ canonicalRootKernel K z := by
  unfold canonicalRootKernel
  split_ifs
  · exact mul_nonneg
      (mul_nonneg (by norm_num) (rootGeometricWeight_pos z.1).le)
      (canonicalPrimeDensity_nonneg _)
  · rfl

lemma canonicalRootKernel_le_dominant (K : ℕ) (z : ℕ × ℕ) :
    canonicalRootKernel K z ≤ canonicalRootDominant z := by
  unfold canonicalRootKernel canonicalRootDominant
  by_cases h : z.2 < K + 2 ∧ z.2 < z.1 + 1
  · rw [if_pos h, if_pos h.2]
    have ha : 0 ≤ 2 * rootGeometricWeight z.1 :=
      mul_nonneg (by norm_num) (rootGeometricWeight_pos z.1).le
    exact mul_le_of_le_one_right ha (canonicalPrimeDensity_le_one _)
  · rw [if_neg h]
    split_ifs
    · exact mul_nonneg (by norm_num) (rootGeometricWeight_pos z.1).le
    · rfl

lemma tendsto_add_one_sub_atTop (r : ℕ) :
    Tendsto (fun K : ℕ => K + 1 - r) atTop atTop := by
  rw [tendsto_atTop]
  intro B
  filter_upwards [eventually_ge_atTop (B + r)] with K hK
  omega

lemma tendsto_canonicalRootKernel_pointwise (z : ℕ × ℕ) :
    Tendsto (fun K : ℕ => canonicalRootKernel K z) atTop (nhds 0) := by
  by_cases hz : z.2 < z.1 + 1
  · have hdensity := tendsto_canonicalPrimeDensity_zero.comp
        (tendsto_add_one_sub_atTop z.2)
    have hmul := hdensity.const_mul (2 * rootGeometricWeight z.1)
    have hmul0 : Tendsto (fun K : ℕ =>
        2 * rootGeometricWeight z.1 *
          canonicalPrimeDensity (K + 1 - z.2)) atTop (nhds 0) := by
      simpa [Function.comp_def] using hmul
    apply hmul0.congr'
    filter_upwards [eventually_ge_atTop z.2] with K hK
    unfold canonicalRootKernel
    rw [if_pos ⟨by omega, hz⟩]
  · apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop 0] with K hK
    simp [canonicalRootKernel, hz]

/-- The total reversed low-prime kernel tends to zero by dominated
convergence. -/
theorem tendsto_canonicalRootKernel_tsum_zero :
    Tendsto (fun K : ℕ => ∑' z : ℕ × ℕ, canonicalRootKernel K z)
      atTop (nhds 0) := by
  have h := tendsto_tsum_of_dominated_convergence
    (𝓕 := atTop)
    (f := canonicalRootKernel)
    (g := fun _z : ℕ × ℕ => (0 : ℝ))
    summable_canonicalRootDominant
    tendsto_canonicalRootKernel_pointwise
    (by
      filter_upwards [eventually_ge_atTop 0] with K hK
      intro z
      rw [Real.norm_eq_abs,
        abs_of_nonneg (canonicalRootKernel_nonneg K z)]
      exact canonicalRootKernel_le_dominant K z)
  simpa using h

lemma canonicalCoefficientRootRatio_le (j k : ℕ) :
    Real.sqrt ((canonicalCoefficientRange j k).card : ℝ) /
        (((2 ^ j : ℕ) : ℝ)) ≤
      2 * rootGeometricWeight j := by
  have hT : ((canonicalCoefficientRange j k).card : ℝ) ≤
      ((2 ^ (j + 2) : ℕ) : ℝ) := by
    exact_mod_cast canonicalCoefficientRange_card_le_pow j k
  have hsqrtT := Real.sqrt_le_sqrt hT
  have hsqrtEq : Real.sqrt (((2 ^ (j + 2) : ℕ) : ℝ)) =
      2 * Real.sqrt (((2 ^ j : ℕ) : ℝ)) := by
    rw [sqrt_two_pow_eq, sqrt_two_pow_eq]
    rw [pow_add]
    norm_num
    ring
  have hjpow : (0 : ℝ) < ((2 ^ j : ℕ) : ℝ) := by positivity
  have hsqrtj : (0 : ℝ) < Real.sqrt (((2 ^ j : ℕ) : ℝ)) := by positivity
  apply (div_le_iff₀ hjpow).2
  unfold rootGeometricWeight
  rw [show (2 * (1 / Real.sqrt (((2 ^ j : ℕ) : ℝ)))) *
      (((2 ^ j : ℕ) : ℝ)) =
      2 * Real.sqrt (((2 ^ j : ℕ) : ℝ)) by
    have hs := Real.sq_sqrt
      (show (0 : ℝ) ≤ ((2 ^ j : ℕ) : ℝ) by positivity)
    field_simp [ne_of_gt hsqrtj]
    nlinarith]
  rw [← hsqrtEq]
  exact hsqrtT

lemma canonicalActualRootWeight_le_density_geometric (j k : ℕ) :
    canonicalActualRootWeight j k ≤
      2 * rootGeometricWeight j * canonicalPrimeDensity k := by
  unfold canonicalActualRootWeight canonicalPrimeDensity
  have hdensity : (0 : ℝ) ≤
      ((dyadicPrimes k).card : ℝ) / (((2 ^ k : ℕ) : ℝ)) := by positivity
  have h := mul_le_mul_of_nonneg_left
    (canonicalCoefficientRootRatio_le j k) hdensity
  simpa [mul_assoc, mul_left_comm, mul_comm] using h

/-- The low-prime root majorant after reflecting `k` across `K+1`. -/
noncomputable def canonicalRootReversedMajorant (K : ℕ) : ℝ :=
  ∑ r ∈ Finset.range (K + 2), ∑' j : ℕ,
    if r < j + 1 then
      2 * rootGeometricWeight j * canonicalPrimeDensity (K + 1 - r)
    else 0

lemma summable_canonicalRootKernel (K : ℕ) :
    Summable (canonicalRootKernel K) :=
  Summable.of_nonneg_of_le (canonicalRootKernel_nonneg K)
    (canonicalRootKernel_le_dominant K)
    summable_canonicalRootDominant

lemma canonicalRootReversedMajorant_eq_kernel (K : ℕ) :
    canonicalRootReversedMajorant K =
      ∑' z : ℕ × ℕ, canonicalRootKernel K z := by
  let hswap : ℕ × ℕ → ℝ := fun z => canonicalRootKernel K z.swap
  have hswapSummable : Summable hswap := by
    dsimp [hswap]
    simpa [Function.comp_def] using
      (summable_canonicalRootKernel K).comp_injective
        (i := Prod.swap) Prod.swap_injective
  have hprod := hswapSummable.tsum_prod
  have hfinite : (∑' r : ℕ, ∑' j : ℕ,
      canonicalRootKernel K (j, r)) =
      canonicalRootReversedMajorant K := by
    rw [tsum_eq_sum (s := Finset.range (K + 2))]
    · unfold canonicalRootReversedMajorant
      apply Finset.sum_congr rfl
      intro r hr
      apply tsum_congr
      intro j
      have hrange : r < K + 2 := Finset.mem_range.mp hr
      unfold canonicalRootKernel
      simp only [Prod.fst, Prod.snd]
      rw [if_congr (by
        constructor
        · intro h
          exact h.2
        · intro h
          exact ⟨hrange, h⟩)] <;> rfl
    · intro r hr
      have hnot : ¬r < K + 2 := by simpa using hr
      simp [canonicalRootKernel, hnot]
  calc
    canonicalRootReversedMajorant K =
        ∑' r : ℕ, ∑' j : ℕ, canonicalRootKernel K (j, r) := hfinite.symm
    _ = ∑' z : ℕ × ℕ, hswap z := hprod.symm
    _ = ∑' z : ℕ × ℕ, canonicalRootKernel K z :=
      (Equiv.prodComm ℕ ℕ).tsum_eq (canonicalRootKernel K)

lemma canonicalRootTriangle_nonneg (K : ℕ) :
    0 ≤ canonicalRootTriangle K := by
  unfold canonicalRootTriangle
  apply Finset.sum_nonneg
  intro k hk
  exact tsum_nonneg fun j => by
    split_ifs
    · exact canonicalActualRootWeight_nonneg j k
    · rfl

/-- The low-prime rotated root error is bounded by the reversed kernel. -/
theorem canonicalRootTriangle_le_kernel (K : ℕ) :
    canonicalRootTriangle K ≤
      ∑' z : ℕ × ℕ, canonicalRootKernel K z := by
  have hmajor : canonicalRootTriangle K ≤
      ∑ k ∈ Finset.range (K + 2), ∑' j : ℕ,
        if K < j + k then
          2 * rootGeometricWeight j * canonicalPrimeDensity k else 0 := by
    unfold canonicalRootTriangle
    apply Finset.sum_le_sum
    intro k hk
    have hleft : Summable (fun j : ℕ =>
        if K < j + k then canonicalActualRootWeight j k else 0) := by
      apply Summable.of_nonneg_of_le
        (fun j => by
          split_ifs
          · exact canonicalActualRootWeight_nonneg j k
          · rfl)
        (fun j => by
          by_cases h : K < j + k
          · simp [h, canonicalActualRootWeight_nonneg]
          · simp [h, canonicalActualRootWeight_nonneg])
        (summable_canonicalActualRootWeight k)
    have hrightBase : Summable (fun j : ℕ =>
        2 * rootGeometricWeight j * canonicalPrimeDensity k) := by
      exact Summable.mul_right (canonicalPrimeDensity k)
        (Summable.mul_left 2 summable_rootGeometricWeight)
    have hright : Summable (fun j : ℕ =>
        if K < j + k then
          2 * rootGeometricWeight j * canonicalPrimeDensity k else 0) := by
      apply Summable.of_nonneg_of_le
        (fun j => by
          split_ifs
          · exact mul_nonneg
              (mul_nonneg (by norm_num) (rootGeometricWeight_pos j).le)
              (canonicalPrimeDensity_nonneg k)
          · rfl)
        (fun j => by
          by_cases h : K < j + k
          · simp [h]
          · simp [h]
            exact mul_nonneg
              (mul_nonneg (by norm_num) (rootGeometricWeight_pos j).le)
              (canonicalPrimeDensity_nonneg k))
        hrightBase
    exact Summable.tsum_le_tsum
      (fun j => by
        by_cases h : K < j + k
        · simp only [if_pos h]
          exact canonicalActualRootWeight_le_density_geometric j k
        · simp [h])
      hleft hright
  apply hmajor.trans
  rw [← canonicalRootReversedMajorant_eq_kernel]
  unfold canonicalRootReversedMajorant
  rw [← Finset.sum_range_reflect
    (fun k => ∑' j : ℕ, if K < j + k then
      2 * rootGeometricWeight j * canonicalPrimeDensity k else 0)
    (K + 2)]
  apply le_of_eq
  apply Finset.sum_congr rfl
  intro r hr
  apply tsum_congr
  intro j
  have hrange : r < K + 2 := Finset.mem_range.mp hr
  have hsub : K + 2 - 1 - r = K + 1 - r := by omega
  rw [hsub]
  have hiff : K < j + (K + 1 - r) ↔ r < j + 1 := by omega
  rw [if_congr hiff] <;> rfl

/-- The triangular low-prime root error vanishes as the core cutoff grows. -/
theorem tendsto_canonicalRootTriangle_zero :
    Tendsto canonicalRootTriangle atTop (nhds 0) := by
  apply squeeze_zero'
    (g := fun K : ℕ => ∑' z : ℕ × ℕ, canonicalRootKernel K z)
  · exact Filter.Eventually.of_forall canonicalRootTriangle_nonneg
  · exact Filter.Eventually.of_forall canonicalRootTriangle_le_kernel
  · exact tendsto_canonicalRootKernel_tsum_zero

/-- Natural-valued image of the occupied cells in one canonical block. -/
noncomputable def canonicalDyadicActiveNatCells
    (A : Finset ℕ) (n R i j k : ℕ) : Finset (ℕ × ℕ) := by
  classical
  exact (canonicalDyadicActiveCells A n R i j k).image fun c =>
    ((c.2 : ℕ), (c.1 : ℕ))

lemma canonicalDyadicActiveNatCells_card
    (A : Finset ℕ) (n R i j k : ℕ) :
    (canonicalDyadicActiveNatCells A n R i j k).card =
      (canonicalDyadicActiveCells A n R i j k).card := by
  classical
  unfold canonicalDyadicActiveNatCells
  rw [Finset.card_image_iff]
  intro a ha b hb hab
  apply Prod.ext
  · apply Subtype.ext
    exact congrArg Prod.snd hab
  · apply Subtype.ext
    exact congrArg Prod.fst hab

lemma activeNatCell_indices_unique
    {A : Finset ℕ} {n R i j k i' j' k' : ℕ}
    {z : ℕ × ℕ}
    (hz : z ∈ canonicalDyadicActiveNatCells A n R i j k)
    (hz' : z ∈ canonicalDyadicActiveNatCells A n R i' j' k') :
    (i, (j, k)) = (i', (j', k')) := by
  classical
  rcases Finset.mem_image.mp hz with ⟨c, hc, hcz⟩
  rcases Finset.mem_image.mp hz' with ⟨c', hc', hcz'⟩
  have hmaps : ((c.2 : ℕ), (c.1 : ℕ)) =
      ((c'.2 : ℕ), (c'.1 : ℕ)) := hcz.trans hcz'.symm
  have hpval : (c.2 : ℕ) = (c'.2 : ℕ) := congrArg Prod.fst hmaps
  have hqval : (c.1 : ℕ) = (c'.1 : ℕ) := congrArg Prod.snd hmaps
  have hqmem := Finset.mem_inter.mp c.1.2
  have hqmem' := Finset.mem_inter.mp c'.1.2
  have hpmem := Finset.mem_filter.mp c.2.2
  have hpmem' := Finset.mem_filter.mp c'.2.2
  have hi : Nat.log2 (c.1 : ℕ) = i :=
    (Nat.log2_eq_iff (Finset.mem_filter.mp hqmem.1).2.ne_zero).2
      (Finset.mem_Ico.mp (Finset.mem_filter.mp hqmem.1).1)
  have hi' : Nat.log2 (c'.1 : ℕ) = i' :=
    (Nat.log2_eq_iff (Finset.mem_filter.mp hqmem'.1).2.ne_zero).2
      (Finset.mem_Ico.mp (Finset.mem_filter.mp hqmem'.1).1)
  have hk : Nat.log2 (c.2 : ℕ) = k :=
    (Nat.log2_eq_iff hpmem.2.ne_zero).2
      (Finset.mem_Ico.mp hpmem.1)
  have hk' : Nat.log2 (c'.2 : ℕ) = k' :=
    (Nat.log2_eq_iff hpmem'.2.ne_zero).2
      (Finset.mem_Ico.mp hpmem'.1)
  have hij : i = i' := by rw [← hi, ← hi', hqval]
  have hkj : k = k' := by rw [← hk, ← hk', hpval]
  have hcell := (Finset.mem_filter.mp hc).2
  have hcell' := (Finset.mem_filter.mp hc').2
  rcases hcell with ⟨t, ht⟩
  rcases hcell' with ⟨t', ht'⟩
  have hedgeMem := (Finset.mem_filter.mp ht).2
  have hedgeMem' := (Finset.mem_filter.mp ht').2
  have hedge := (Finset.mem_filter.mp hedgeMem).2
  have hedge' := (Finset.mem_filter.mp hedgeMem').2
  have hjEq : Nat.log2 (canonicalCellMax A n R (c.1 : ℕ) (c.2 : ℕ)) = j :=
    hedge.2.2
  have hjEq' : Nat.log2 (canonicalCellMax A n R (c'.1 : ℕ) (c'.2 : ℕ)) = j' :=
    hedge'.2.2
  have hjj : j = j' := by
    rw [← hjEq, ← hjEq', hqval, hpval]
  simp [hij, hjj, hkj]

/-- High-prime active cells attached to a dyadic block. -/
noncomputable def canonicalHighActiveFamily
    (A : Finset ℕ) (n R K : ℕ) (e : ℕ × (ℕ × ℕ)) :
    Finset (ℕ × ℕ) :=
  if K + 2 ≤ e.2.2 then
    canonicalDyadicActiveNatCells A n R e.1 e.2.1 e.2.2
  else ∅

lemma canonicalHighActiveFamily_pairwiseDisjoint
    (A : Finset ℕ) (n R K : ℕ) :
    (↑(dyadicIndexCube n) : Set (ℕ × (ℕ × ℕ))).PairwiseDisjoint
      (canonicalHighActiveFamily A n R K) := by
  intro e he f hf hef
  change Disjoint (canonicalHighActiveFamily A n R K e)
    (canonicalHighActiveFamily A n R K f)
  rw [Finset.disjoint_left]
  intro z hz hz'
  have heHigh : K + 2 ≤ e.2.2 := by
    by_contra h
    have hnot : ¬K + 2 ≤ e.2.2 := h
    simp [canonicalHighActiveFamily, hnot] at hz
  have hfHigh : K + 2 ≤ f.2.2 := by
    by_contra h
    have hnot : ¬K + 2 ≤ f.2.2 := h
    simp [canonicalHighActiveFamily, hnot] at hz'
  have hze : z ∈ canonicalDyadicActiveNatCells A n R e.1 e.2.1 e.2.2 := by
    simpa [canonicalHighActiveFamily, heHigh] using hz
  have hzf : z ∈ canonicalDyadicActiveNatCells A n R f.1 f.2.1 f.2.2 := by
    simpa [canonicalHighActiveFamily, hfHigh] using hz'
  exact hef (activeNatCell_indices_unique hze hzf)

/-- Union of all high-prime occupied cells. -/
noncomputable def canonicalHighActiveUnion
    (A : Finset ℕ) (n R K : ℕ) : Finset (ℕ × ℕ) :=
  (dyadicIndexCube n).biUnion (canonicalHighActiveFamily A n R K)

lemma canonicalHighActiveUnion_card_eq_sum
    (A : Finset ℕ) (n R K : ℕ) :
    (canonicalHighActiveUnion A n R K).card =
      ∑ e ∈ dyadicIndexCube n,
        if K + 2 ≤ e.2.2 then
          (canonicalDyadicActiveCells A n R e.1 e.2.1 e.2.2).card
        else 0 := by
  classical
  unfold canonicalHighActiveUnion
  rw [Finset.card_biUnion
    (canonicalHighActiveFamily_pairwiseDisjoint A n R K)]
  apply Finset.sum_congr rfl
  intro e he
  by_cases hhigh : K + 2 ≤ e.2.2
  · rw [if_pos hhigh]
    simp only [canonicalHighActiveFamily, if_pos hhigh]
    exact canonicalDyadicActiveNatCells_card A n R e.1 e.2.1 e.2.2
  · simp [canonicalHighActiveFamily, hhigh]

lemma two_pow_add_two_not_prime (K : ℕ) :
    ¬(2 ^ (K + 2)).Prime := by
  intro hp
  have hdvd : 2 ∣ 2 ^ (K + 2) := dvd_pow_self 2 (by omega)
  rcases hp.eq_one_or_self_of_dvd 2 hdvd with hbad | htwo
  · norm_num at hbad
  · have hfour : 4 ≤ 2 ^ (K + 2) := by
      calc
        4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (K + 2) := Nat.pow_le_pow_right (by omega) (by omega)
    omega

/-- Globally, high-prime active cells inject into the literal semiprime tail. -/
theorem canonicalHighActiveUnion_subset_profile
    {A : Finset ℕ} {n K : ℕ} (hAint : A ⊆ Finset.Icc 1 n) :
    canonicalHighActiveUnion A n (2 ^ (K + 2)) K ⊆
      profilePrimePairs (2 ^ (K + 2)) n := by
  classical
  intro z hz
  rcases Finset.mem_biUnion.mp hz with ⟨e, he, hzFamily⟩
  have hhigh : K + 2 ≤ e.2.2 := by
    by_contra h
    have hnot : ¬K + 2 ≤ e.2.2 := h
    simp [canonicalHighActiveFamily, hnot] at hzFamily
  have hzNat : z ∈ canonicalDyadicActiveNatCells A n (2 ^ (K + 2))
      e.1 e.2.1 e.2.2 := by
    simpa [canonicalHighActiveFamily, hhigh] using hzFamily
  rcases Finset.mem_image.mp hzNat with ⟨c, hc, hcz⟩
  rw [← hcz]
  have hqRange := Finset.mem_inter.mp c.1.2
  have hqLabel := Finset.mem_filter.mp hqRange.2
  have hpDy := Finset.mem_filter.mp c.2.2
  have hpPrime : (c.2 : ℕ).Prime := hpDy.2
  have hpLowerDy : 2 ^ e.2.2 ≤ (c.2 : ℕ) :=
    (Finset.mem_Ico.mp hpDy.1).1
  have hRleP : 2 ^ (K + 2) ≤ (c.2 : ℕ) :=
    (Nat.pow_le_pow_right (by omega) hhigh).trans hpLowerDy
  have hRp : 2 ^ (K + 2) < (c.2 : ℕ) := by
    by_contra hnot
    have heq : (c.2 : ℕ) = 2 ^ (K + 2) := by omega
    rw [heq] at hpPrime
    exact two_pow_add_two_not_prime K hpPrime
  have hcell := (Finset.mem_filter.mp hc).2
  rcases hcell with ⟨t, ht⟩
  have hedgeMem := (Finset.mem_filter.mp ht).2
  have hedge := (Finset.mem_filter.mp hedgeMem).2
  have htail := Finset.mem_filter.mp hedge.1
  have hfiber := Finset.mem_filter.mp htail.1
  have hdI := Finset.mem_Icc.mp hfiber.1
  have htpos : 0 < (t : ℕ) := by
    exact Nat.pos_of_ne_zero (Nat.mem_smoothNumbersUpTo.mp t.2).2.1
  have htOne : 1 ≤ (t : ℕ) := htpos
  have hpLeCore : (c.2 : ℕ) ≤ (t : ℕ) * (c.2 : ℕ) := by
    calc
      (c.2 : ℕ) = 1 * (c.2 : ℕ) := by simp
      _ ≤ (t : ℕ) * (c.2 : ℕ) := Nat.mul_le_mul_right _ htOne
  have hpSqrt : (c.2 : ℕ) ≤ n.sqrt := hpLeCore.trans hdI.2
  have hqdle : (c.1 : ℕ) * ((t : ℕ) * (c.2 : ℕ)) ≤ n :=
    (Finset.mem_Icc.mp (hAint hfiber.2)).2
  have hpq : (c.2 : ℕ) * (c.1 : ℕ) ≤ n := by
    calc
      (c.2 : ℕ) * (c.1 : ℕ) =
          (c.1 : ℕ) * (1 * (c.2 : ℕ)) := by ring
      _ ≤ (c.1 : ℕ) * ((t : ℕ) * (c.2 : ℕ)) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ htOne)
      _ ≤ n := hqdle
  unfold profilePrimePairs
  apply Finset.mem_filter.mpr
  constructor
  · apply Finset.mem_product.mpr
    constructor
    · apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_Icc.mpr ⟨by omega, hpSqrt⟩, hpPrime⟩
    · exact hqRange.2
  · exact hpq

/-- The sum of all high-prime active-cell charges is at most the literal
semiprime tail, with no repeated charge across coefficient scales. -/
theorem canonicalHighActiveSum_le_profile
    {A : Finset ℕ} {n K : ℕ} (hAint : A ⊆ Finset.Icc 1 n) :
    (∑ e ∈ dyadicIndexCube n,
        if K + 2 ≤ e.2.2 then
          (canonicalDyadicActiveCells A n (2 ^ (K + 2))
            e.1 e.2.1 e.2.2).card else 0) ≤
      profileTailCount (2 ^ (K + 2)) n := by
  rw [← canonicalHighActiveUnion_card_eq_sum]
  rw [← profilePrimePairs_card_eq_tail]
  exact Finset.card_le_card
    (canonicalHighActiveUnion_subset_profile hAint)

/-- Projection-sensitive high-prime block estimate with named persistent and
transient terms. -/
theorem canonicalDyadicBlock_card_le_projection_split
    {A : Finset ℕ} {n R i j k : ℕ} (hA : HasRepBound 3 A) :
    ((canonicalDyadicBlock A n R i j k).card : ℝ) ≤
      (canonicalDyadicActiveCells A n R i j k).card +
        canonicalPersistentTerm A n R i j k +
        canonicalTransientTerm A n R i j k := by
  classical
  by_cases hne : (canonicalDyadicBlock A n R i j k).Nonempty
  · have hbase := canonicalDyadicBlock_card_le_active_sqrt
      (A := A) (n := n) (R := R) (i := i) (j := j) (k := k) hA
    have herr := canonicalDyadicBlock_error_le_split A n R i j k
    unfold canonicalPersistentTerm canonicalTransientTerm
    rw [if_pos hne, if_pos hne]
    linarith
  · have hz : (canonicalDyadicBlock A n R i j k).card = 0 :=
      Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp hne)
    rw [hz]
    have hactive : (0 : ℝ) ≤
        ((canonicalDyadicActiveCells A n R i j k).card : ℝ) := by
      exact_mod_cast (Nat.zero_le _)
    simpa using add_nonneg
      (add_nonneg hactive (canonicalPersistentTerm_nonneg A n R i j k))
      (canonicalTransientTerm_nonneg A n R i j k)

/-- All canonical blocks are bounded by one global semiprime charge and four
error sums. -/
theorem canonicalDyadicSum_le_profile_add_errors
    {A : Finset ℕ} {n K : ℕ}
    (hAint : A ⊆ Finset.Icc 1 n) (hA : HasRepBound 3 A) :
    ((∑ e ∈ dyadicIndexCube n,
      (canonicalDyadicBlock A n (2 ^ (K + 2))
        e.1 e.2.1 e.2.2).card : ℕ) : ℝ) ≤
      (profileTailCount (2 ^ (K + 2)) n : ℝ) +
        canonicalPersistentSum A n (2 ^ (K + 2)) +
        canonicalLowLinearSum A n (2 ^ (K + 2)) +
        canonicalLowRootSum A n (2 ^ (K + 2)) K +
        canonicalTransientSum A n (2 ^ (K + 2)) := by
  let H : ℕ × (ℕ × ℕ) → ℝ := fun e =>
    ((canonicalDyadicBlock A n (2 ^ (K + 2))
      e.1 e.2.1 e.2.2).card : ℝ)
  let B : ℕ × (ℕ × ℕ) → ℝ := fun e =>
    (if K + 2 ≤ e.2.2 then
      ((canonicalDyadicActiveCells A n (2 ^ (K + 2))
        e.1 e.2.1 e.2.2).card : ℝ) else 0) +
    canonicalPersistentTerm A n (2 ^ (K + 2)) e.1 e.2.1 e.2.2 +
    canonicalLowLinearTerm A n (2 ^ (K + 2)) e.1 e.2.1 e.2.2 +
    (if e.2.2 < K + 2 then
      canonicalLowRootTerm A n (2 ^ (K + 2)) e.1 e.2.1 e.2.2 else 0) +
    canonicalTransientTerm A n (2 ^ (K + 2)) e.1 e.2.1 e.2.2
  have hpoint : ∀ e ∈ dyadicIndexCube n, H e ≤ B e := by
    intro e he
    by_cases hlow : e.2.2 < K + 2
    · have hbase := canonicalDyadicBlock_card_le_rotated_split
        (A := A) (n := n) (R := 2 ^ (K + 2))
        (i := e.1) (j := e.2.1) (k := e.2.2) hA
      have hnotHigh : ¬K + 2 ≤ e.2.2 := by omega
      dsimp [H, B]
      rw [if_neg hnotHigh, if_pos hlow]
      have hp := canonicalPersistentTerm_nonneg A n (2 ^ (K + 2))
        e.1 e.2.1 e.2.2
      linarith
    · have hhigh : K + 2 ≤ e.2.2 := by omega
      have hbase := canonicalDyadicBlock_card_le_projection_split
        (A := A) (n := n) (R := 2 ^ (K + 2))
        (i := e.1) (j := e.2.1) (k := e.2.2) hA
      dsimp [H, B]
      rw [if_pos hhigh, if_neg hlow]
      have hl := canonicalLowLinearTerm_nonneg A n (2 ^ (K + 2))
        e.1 e.2.1 e.2.2
      linarith
  have hsum : (∑ e ∈ dyadicIndexCube n, H e) ≤
      ∑ e ∈ dyadicIndexCube n, B e := Finset.sum_le_sum hpoint
  have hactiveNat := canonicalHighActiveSum_le_profile
    (A := A) (n := n) (K := K) hAint
  have hactive : (∑ e ∈ dyadicIndexCube n,
      if K + 2 ≤ e.2.2 then
        ((canonicalDyadicActiveCells A n (2 ^ (K + 2))
          e.1 e.2.1 e.2.2).card : ℝ) else 0) ≤
      (profileTailCount (2 ^ (K + 2)) n : ℝ) := by
    exact_mod_cast hactiveNat
  have hcast : ((∑ e ∈ dyadicIndexCube n,
      (canonicalDyadicBlock A n (2 ^ (K + 2))
        e.1 e.2.1 e.2.2).card : ℕ) : ℝ) =
      ∑ e ∈ dyadicIndexCube n, H e := by
    dsimp [H]
    push_cast
    rfl
  rw [hcast]
  apply hsum.trans
  change (∑ e ∈ dyadicIndexCube n, B e) ≤ _
  dsimp [B]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
    Finset.sum_add_distrib, Finset.sum_add_distrib]
  change _ ≤ (profileTailCount (2 ^ (K + 2)) n : ℝ) +
    canonicalPersistentSum A n (2 ^ (K + 2)) +
    canonicalLowLinearSum A n (2 ^ (K + 2)) +
    canonicalLowRootSum A n (2 ^ (K + 2)) K +
    canonicalTransientSum A n (2 ^ (K + 2))
  unfold canonicalPersistentSum canonicalLowLinearSum canonicalLowRootSum
    canonicalTransientSum
  linarith

/-- After normalization, the low-prime rotated root error is bounded by its
triangular arithmetic weight. -/
theorem eventually_canonicalLowRootSum_normalized_le (K : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ A : Finset ℕ, A ⊆ Finset.Icc 1 n →
      canonicalLowRootSum A n (2 ^ (K + 2)) K /
          ((n : ℝ) / Real.log (n : ℝ)) ≤
        (4 * dyadicPrimeConstant * Real.log 2) * canonicalRootTriangle K := by
  rcases (eventually_atTop.1 eventually_dyadicPrimes_card_le) with ⟨I₀, hI₀⟩
  have hlog2 := tendsto_nat_log2_atTop.eventually_ge_atTop (2 * I₀)
  filter_upwards [eventually_gt_atTop 1, hlog2] with n hn hL
  intro A hAint
  have hraw := canonicalLowRootSum_le (K := K) (I₀ := I₀)
    (by omega : 0 < n) hAint hI₀ hL
  exact normalized_le_of_dyadicProjection_bound hn
    (canonicalRootTriangle_nonneg K) hraw

/-- The global transient cube error is uniformly negligible for every fixed
core cutoff. -/
theorem eventually_canonicalTransientSum_normalized_lt
    (K : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ A : Finset ℕ, A ⊆ Finset.Icc 1 n →
      canonicalTransientSum A n (2 ^ (K + 2)) /
          ((n : ℝ) / Real.log (n : ℝ)) < ε := by
  have hmajor := tendsto_canonicalTransientMajorant_normalized_zero.eventually
    (gt_mem_nhds hε)
  filter_upwards [eventually_gt_atTop 1, hmajor] with n hn hmaj
  intro A hAint
  have hraw := canonicalTransientSum_le
    (A := A) (n := n) (R := 2 ^ (K + 2)) (by positivity) hAint
  have hden : 0 < (n : ℝ) / Real.log (n : ℝ) :=
    div_pos (by positivity) (Real.log_pos (by exact_mod_cast hn))
  have hdiv := div_le_div_of_nonneg_right hraw hden.le
  exact hdiv.trans_lt hmaj

/-- Total persistent arithmetic error at dyadic core cutoff `2^(K+2)`. -/
noncomputable def canonicalDyadicTailError (K : ℕ) : ℝ :=
  (4 * dyadicPrimeConstant * Real.log 2) *
    ((∑' z : ℕ × ℕ, if K < z.1 + z.2 then
        canonicalActualMainWeight z.1 z.2 else 0) +
      (∑' z : ℕ × ℕ, if K < z.1 + z.2 then
        canonicalActualLinearWeight z.1 z.2 else 0) +
      canonicalRootTriangle K)

lemma canonicalDyadicTailError_nonneg (K : ℕ) :
    0 ≤ canonicalDyadicTailError K := by
  unfold canonicalDyadicTailError
  have hC : 0 ≤ 4 * dyadicPrimeConstant * Real.log 2 :=
    mul_nonneg
      (mul_nonneg (by norm_num) dyadicPrimeConstant_pos.le)
      (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le
  have hmain : 0 ≤ ∑' z : ℕ × ℕ, if K < z.1 + z.2 then
      canonicalActualMainWeight z.1 z.2 else 0 :=
    tsum_nonneg fun z => by
      split_ifs
      · exact canonicalActualMainWeight_nonneg z.1 z.2
      · rfl
  have hlinear : 0 ≤ ∑' z : ℕ × ℕ, if K < z.1 + z.2 then
      canonicalActualLinearWeight z.1 z.2 else 0 :=
    tsum_nonneg fun z => by
      split_ifs
      · exact canonicalActualLinearWeight_nonneg z.1 z.2
      · rfl
  exact mul_nonneg hC
    (add_nonneg (add_nonneg hmain hlinear)
      (canonicalRootTriangle_nonneg K))

/-- All three persistent arithmetic tails vanish with the core cutoff. -/
theorem tendsto_canonicalDyadicTailError_zero :
    Tendsto canonicalDyadicTailError atTop (nhds 0) := by
  have hmain := tendsto_canonicalActualMainWeight_degreeTail_zero'
  have hlinear := tendsto_canonicalActualLinearWeight_degreeTail_zero
  have hroot := tendsto_canonicalRootTriangle_zero
  unfold canonicalDyadicTailError
  convert (hmain.add hlinear |>.add hroot).const_mul
    (4 * dyadicPrimeConstant * Real.log 2) using 1 <;> ring

/-- At a fixed dyadic cutoff, the extracted tail is bounded by the literal
semiprime tail plus the persistent arithmetic error and an arbitrary transient
error. -/
theorem eventually_extractedTail_normalized_le_profile_add
    (K : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ A : Finset ℕ,
      A ⊆ Finset.Icc 1 n → HasRepBound 3 A →
      (extractedTailSum A n (2 ^ (K + 2)) : ℝ) /
          ((n : ℝ) / Real.log (n : ℝ)) ≤
        (profileTailCount (2 ^ (K + 2)) n : ℝ) /
          ((n : ℝ) / Real.log (n : ℝ)) +
        canonicalDyadicTailError K + ε := by
  have hpersist := eventually_canonicalPersistentSum_normalized_le K
  have hlinear := eventually_canonicalLowLinearSum_normalized_le K
  have hroot := eventually_canonicalLowRootSum_normalized_le K
  have htrans := eventually_canonicalTransientSum_normalized_lt K hε
  filter_upwards [eventually_gt_atTop 1, hpersist, hlinear, hroot, htrans]
      with n hn hp hl hr ht
  intro A hAint hArep
  have hcoverNat := extractedTailSum_le_canonicalDyadicSum
    (A := A) (n := n) (R := 2 ^ (K + 2)) (by positivity)
  have hcover : (extractedTailSum A n (2 ^ (K + 2)) : ℝ) ≤
      ((∑ e ∈ dyadicIndexCube n,
        (canonicalDyadicBlock A n (2 ^ (K + 2))
          e.1 e.2.1 e.2.2).card : ℕ) : ℝ) := by
    exact_mod_cast hcoverNat
  have hblocks := canonicalDyadicSum_le_profile_add_errors
    (A := A) (n := n) (K := K) hAint hArep
  have hraw := hcover.trans hblocks
  have hden : 0 < (n : ℝ) / Real.log (n : ℝ) :=
    div_pos (by positivity) (Real.log_pos (by exact_mod_cast hn))
  have hdiv := div_le_div_of_nonneg_right hraw hden.le
  have hpA := hp A hAint
  have hlA := hl A hAint
  have hrA := hr A hAint
  have htA := ht A hAint
  have hsplit :
      ((profileTailCount (2 ^ (K + 2)) n : ℝ) +
          canonicalPersistentSum A n (2 ^ (K + 2)) +
          canonicalLowLinearSum A n (2 ^ (K + 2)) +
          canonicalLowRootSum A n (2 ^ (K + 2)) K +
          canonicalTransientSum A n (2 ^ (K + 2))) /
          ((n : ℝ) / Real.log (n : ℝ)) =
        (profileTailCount (2 ^ (K + 2)) n : ℝ) /
            ((n : ℝ) / Real.log (n : ℝ)) +
          canonicalPersistentSum A n (2 ^ (K + 2)) /
            ((n : ℝ) / Real.log (n : ℝ)) +
          canonicalLowLinearSum A n (2 ^ (K + 2)) /
            ((n : ℝ) / Real.log (n : ℝ)) +
          canonicalLowRootSum A n (2 ^ (K + 2)) K /
            ((n : ℝ) / Real.log (n : ℝ)) +
          canonicalTransientSum A n (2 ^ (K + 2)) /
            ((n : ℝ) / Real.log (n : ℝ)) := by ring
  rw [hsplit] at hdiv
  unfold canonicalDyadicTailError
  linarith

/-- The extracted-tail gate required by the final upper-bound reduction. -/
theorem extractedTailGate_proved : ExtractedTailGate := by
  intro ε hε
  let δ := ε / 2
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hsmall : ∀ᶠ K : ℕ in atTop, canonicalDyadicTailError K < δ :=
    tendsto_canonicalDyadicTailError_zero.eventually (gt_mem_nhds hδ)
  rcases (eventually_atTop.1 hsmall) with ⟨K, hK⟩
  refine ⟨2 ^ (K + 2), by positivity, ?_⟩
  have hfixed := eventually_extractedTail_normalized_le_profile_add K hδ
  filter_upwards [hfixed] with n hn
  intro A hAint hArep
  have hbound := hn A hAint hArep
  have herr : canonicalDyadicTailError K < δ := hK K le_rfl
  dsimp [δ] at hbound herr ⊢
  linarith

/-- Affirmative solution of Erdős Problem 796. -/
theorem erdos796_statement : Statement :=
  remainderGates_imply_statement smoothRemainderGate_proved
    extractedTailGate_proved

end Erdos796
