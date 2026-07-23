import Research.SmoothCoreCount
import Research.SmoothDyadic

namespace Erdos796

open Filter Topology

/-- Uniform Chebyshev majorant at all complementary divisors through
`sqrt n`. -/
theorem eventually_primeCounting_div_le_reciprocal :
    ∀ᶠ n : ℕ in atTop, ∀ d : ℕ, 0 < d → d ≤ n.sqrt →
      (Nat.primeCounting (n / d) : ℝ) /
          ((n : ℝ) / Real.log (n : ℝ)) ≤
        (2 * (Real.log 4 + 1)) / d := by
  have hcheb := Chebyshev.eventually_primeCounting_le
    (ε := (1 : ℝ)) one_pos
  rcases (eventually_atTop.1 hcheb) with ⟨X, hX⟩
  have hsqrt : Tendsto (fun n : ℕ => Real.sqrt (n : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have hevent := hsqrt.eventually (eventually_ge_atTop (max X 2))
  filter_upwards [hevent, eventually_gt_atTop 1] with n hnroot hn
  intro d hd hdroot
  have hnR : (0 : ℝ) < n := by positivity
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hsqd : (d : ℝ) ^ 2 ≤ (n : ℝ) := by
    have hnat : d ^ 2 ≤ n := by
      simpa [pow_two] using (Nat.le_sqrt.mp hdroot)
    exact_mod_cast hnat
  have hdsqrt : (d : ℝ) ≤ Real.sqrt (n : ℝ) := by
    rw [Real.le_sqrt (by positivity) hnR.le]
    exact hsqd
  have hx : Real.sqrt (n : ℝ) ≤ (n : ℝ) / d := by
    apply (le_div_iff₀ hdR).2
    calc
      Real.sqrt (n : ℝ) * d ≤
          Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) := by gcongr
      _ = (n : ℝ) := by rw [← pow_two, Real.sq_sqrt hnR.le]
  have hxX : X ≤ (n : ℝ) / d := le_trans (le_max_left _ _) (hnroot.trans hx)
  have hpi := hX ((n : ℝ) / d) hxX
  rw [Nat.floor_div_natCast, Nat.floor_natCast] at hpi
  have hlogn : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn)
  have hlogsqrt : Real.log (Real.sqrt (n : ℝ)) =
      Real.log (n : ℝ) / 2 := by
    rw [Real.log_sqrt hnR.le]
  have hlogx : Real.log (n : ℝ) / 2 ≤
      Real.log ((n : ℝ) / d) := by
    rw [← hlogsqrt]
    exact Real.log_le_log (Real.sqrt_pos.2 hnR) hx
  have hlogxpos : 0 < Real.log ((n : ℝ) / d) :=
    lt_of_lt_of_le (half_pos hlogn) hlogx
  have hratio : Real.log (n : ℝ) /
      Real.log ((n : ℝ) / d) ≤ 2 := by
    apply (div_le_iff₀ hlogxpos).2
    linarith
  calc
    (Nat.primeCounting (n / d) : ℝ) /
          ((n : ℝ) / Real.log (n : ℝ))
      ≤ ((Real.log 4 + 1) * ((n : ℝ) / d) /
          Real.log ((n : ℝ) / d)) /
          ((n : ℝ) / Real.log (n : ℝ)) := by
        gcongr
    _ = ((Real.log 4 + 1) / d) *
          (Real.log (n : ℝ) / Real.log ((n : ℝ) / d)) := by
      field_simp
    _ ≤ ((Real.log 4 + 1) / d) * 2 := by
      gcongr
    _ = (2 * (Real.log 4 + 1)) / d := by ring

/-- Incidences whose core is fixed-smooth and lies beyond `2^J`. -/
noncomputable def smoothTailIncidences
    (A : Finset ℕ) (n S J : ℕ) : Finset (ℕ × ℕ) :=
  ((sqrtPrimeLabels n).product (smoothCoresUpTo S n.sqrt)).filter fun z =>
    2 ^ J ≤ z.2 ∧ z.1 * z.2 ∈ A

/-- Swap the label/core sum and discard membership in `A`. -/
theorem smoothTailIncidences_card_le
    {A : Finset ℕ} {n S J : ℕ} (hAint : A ⊆ Finset.Icc 1 n) :
    (smoothTailIncidences A n S J).card ≤
      ∑ d ∈ (smoothCoresUpTo S n.sqrt).filter (fun d => 2 ^ J ≤ d),
        Nat.primeCounting (n / d) := by
  classical
  let D := (smoothCoresUpTo S n.sqrt).filter fun d => 2 ^ J ≤ d
  have hrewrite : smoothTailIncidences A n S J =
      ((sqrtPrimeLabels n).product D).filter fun z => z.1 * z.2 ∈ A := by
    ext z
    simp [smoothTailIncidences, D, and_assoc, and_left_comm, and_comm]
  rw [hrewrite, Finset.card_filter]
  change (∑ z ∈ (sqrtPrimeLabels n).product D,
      if z.1 * z.2 ∈ A then 1 else 0) ≤
        ∑ d ∈ D, Nat.primeCounting (n / d)
  rw [show (∑ z ∈ (sqrtPrimeLabels n).product D,
      if z.1 * z.2 ∈ A then 1 else 0) =
      ∑ q ∈ sqrtPrimeLabels n, ∑ d ∈ D,
        if q * d ∈ A then 1 else 0 from
      Finset.sum_product _ _ _]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro d hd
  rw [← Finset.card_filter]
  have hsub : (sqrtPrimeLabels n).filter (fun q => q * d ∈ A) ⊆
      Nat.primesLE (n / d) := by
    intro q hq
    have hq' := Finset.mem_filter.mp hq
    have hdpos : 0 < d := (mem_smoothCoresUpTo.mp
      (Finset.mem_filter.mp hd).1).1
    have hqd := (Finset.mem_Icc.mp (hAint hq'.2)).2
    apply Nat.mem_primesLE.mpr
    exact ⟨(Nat.le_div_iff_mul_le hdpos).2 hqd,
      (Finset.mem_filter.mp hq'.1).2⟩
  rw [← Nat.primesLE_card_eq_primeCounting]
  exact Finset.card_le_card hsub

/-- Half-open version of a smooth dyadic block. -/
noncomputable def smoothCoreProperBlock (S j : ℕ) : Finset ℕ :=
  (smoothCoreDyadicBlock S j).filter fun d => d < 2 ^ (j + 1)

lemma smoothCoreProperBlock_subset (S j : ℕ) :
    smoothCoreProperBlock S j ⊆ smoothCoreDyadicBlock S j :=
  Finset.filter_subset _ _

lemma smoothCoreProperBlocks_disjoint (S : ℕ) :
    Set.PairwiseDisjoint Set.univ (smoothCoreProperBlock S) := by
  intro i hi j hj hij
  change Disjoint (smoothCoreProperBlock S i) (smoothCoreProperBlock S j)
  rw [Finset.disjoint_left]
  intro d hdi hdj
  have hi' := Finset.mem_filter.mp hdi
  have hj' := Finset.mem_filter.mp hdj
  have hdi0 := (Finset.mem_filter.mp hi'.1).2
  have hdj0 := (Finset.mem_filter.mp hj'.1).2
  rcases lt_or_gt_of_ne hij with hij' | hji'
  · have hp : 2 ^ (i + 1) ≤ 2 ^ j :=
      Nat.pow_le_pow_right (by omega) (by omega)
    omega
  · have hp : 2 ^ (j + 1) ≤ 2 ^ i :=
      Nat.pow_le_pow_right (by omega) (by omega)
    omega

/-- The reciprocal sum over smooth cores beyond `2^J` and through `sqrt n`
is bounded by the infinite dyadic tail from F-049. -/
theorem smoothCoreTail_reciprocal_le_tsum (n S J : ℕ) :
    (∑ d ∈ (smoothCoresUpTo S n.sqrt).filter (fun d => 2 ^ J ≤ d),
      (1 : ℝ) / d) ≤
      ∑' k : ℕ, smoothCoreDyadicMass S (k + J) := by
  classical
  let K := Nat.log2 n.sqrt + 1
  let B : ℕ → Finset ℕ := fun k => smoothCoreProperBlock S (k + J)
  let U := (Finset.range K).biUnion B
  have hsub : (smoothCoresUpTo S n.sqrt).filter (fun d => 2 ^ J ≤ d) ⊆ U := by
    intro d hd
    have hd' := Finset.mem_filter.mp hd
    have hdpos : 0 < d := (mem_smoothCoresUpTo.mp hd'.1).1
    let k := Nat.log2 d - J
    have hJlog : J ≤ Nat.log2 d := by
      rw [Nat.log2_eq_log_two]
      apply Nat.le_log_of_pow_le Nat.one_lt_two
      exact hd'.2
    have hklog : k + J = Nat.log2 d := by dsimp [k]; omega
    have hkn : k < K := by
      dsimp [K, k]
      have hmono := log2_mono_of_le (Nat.ne_of_gt hdpos)
        (mem_smoothCoresUpTo.mp hd'.1).2.1
      omega
    apply Finset.mem_biUnion.mpr
    refine ⟨k, Finset.mem_range.mpr hkn, ?_⟩
    unfold B smoothCoreProperBlock
    apply Finset.mem_filter.mpr
    constructor
    · unfold smoothCoreDyadicBlock
      apply Finset.mem_filter.mpr
      constructor
      · apply mem_smoothCoresUpTo.mpr
        refine ⟨(mem_smoothCoresUpTo.mp hd'.1).1, ?_,
          (mem_smoothCoresUpTo.mp hd'.1).2.2⟩
        rw [hklog, Nat.log2_eq_log_two]
        exact Nat.le_of_lt (Nat.lt_pow_succ_log_self Nat.one_lt_two d)
      · rw [hklog, Nat.log2_eq_log_two]
        exact Nat.pow_log_le_self 2 (Nat.ne_of_gt hdpos)
    · rw [hklog, Nat.log2_eq_log_two]
      exact Nat.lt_pow_succ_log_self Nat.one_lt_two d
  have hsumU : (∑ d ∈ U, (1 : ℝ) / d) =
      ∑ k ∈ Finset.range K,
        ∑ d ∈ B k, (1 : ℝ) / d := by
    apply Finset.sum_biUnion
    intro i hi j hj hij
    exact smoothCoreProperBlocks_disjoint S (by simp) (by simp) (by
      intro h
      apply hij
      omega)
  calc
    (∑ d ∈ (smoothCoresUpTo S n.sqrt).filter (fun d => 2 ^ J ≤ d),
        (1 : ℝ) / d)
      ≤ ∑ d ∈ U, (1 : ℝ) / d :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (by intros; positivity)
    _ = ∑ k ∈ Finset.range K,
        ∑ d ∈ B k, (1 : ℝ) / d := hsumU
    _ ≤ ∑ k ∈ Finset.range K, smoothCoreDyadicMass S (k + J) := by
      apply Finset.sum_le_sum
      intro k hk
      unfold B smoothCoreDyadicMass
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (smoothCoreProperBlock_subset S (k + J)) (by intros; positivity)
    _ ≤ ∑' k : ℕ, smoothCoreDyadicMass S (k + J) := by
      exact ((summable_nat_add_iff J).mpr (summable_smoothCoreDyadicMass S)).sum_le_tsum
        (Finset.range K) (by intros; exact smoothCoreDyadicMass_nonneg _ _)

/-- Uniform normalized fixed-smooth tail bound. -/
theorem eventually_smoothTailIncidences_le_tsum (S J : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ A : Finset ℕ, A ⊆ Finset.Icc 1 n →
      (smoothTailIncidences A n S J).card /
          ((n : ℝ) / Real.log (n : ℝ)) ≤
        2 * (Real.log 4 + 1) *
          (∑' k : ℕ, smoothCoreDyadicMass S (k + J)) := by
  filter_upwards [eventually_primeCounting_div_le_reciprocal,
    eventually_gt_atTop 1] with n hprime hn
  intro A hA
  have hcard := smoothTailIncidences_card_le (S := S) (J := J) hA
  have hden : 0 < (n : ℝ) / Real.log (n : ℝ) :=
    div_pos (by positivity) (Real.log_pos (by exact_mod_cast hn))
  have hsum : (∑ d ∈ (smoothCoresUpTo S n.sqrt).filter
      (fun d => 2 ^ J ≤ d), (Nat.primeCounting (n / d) : ℝ)) /
      ((n : ℝ) / Real.log (n : ℝ)) ≤
      2 * (Real.log 4 + 1) *
        (∑ d ∈ (smoothCoresUpTo S n.sqrt).filter (fun d => 2 ^ J ≤ d),
          (1 : ℝ) / d) := by
    rw [Finset.sum_div]
    calc
      (∑ d ∈ (smoothCoresUpTo S n.sqrt).filter (fun d => 2 ^ J ≤ d),
          (Nat.primeCounting (n / d) : ℝ) /
            ((n : ℝ) / Real.log (n : ℝ)))
        ≤ ∑ d ∈ (smoothCoresUpTo S n.sqrt).filter (fun d => 2 ^ J ≤ d),
            (2 * (Real.log 4 + 1)) / d := by
          apply Finset.sum_le_sum
          intro d hd
          exact hprime d (mem_smoothCoresUpTo.mp
            (Finset.mem_filter.mp hd).1).1
            (mem_smoothCoresUpTo.mp (Finset.mem_filter.mp hd).1).2.1
      _ = _ := by rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intros; ring
  calc
    ((smoothTailIncidences A n S J).card : ℝ) /
        ((n : ℝ) / Real.log (n : ℝ))
      ≤ (∑ d ∈ (smoothCoresUpTo S n.sqrt).filter
          (fun d => 2 ^ J ≤ d), (Nat.primeCounting (n / d) : ℝ)) /
          ((n : ℝ) / Real.log (n : ℝ)) := by
        apply div_le_div_of_nonneg_right _ hden.le
        exact_mod_cast hcard
    _ ≤ 2 * (Real.log 4 + 1) *
        (∑ d ∈ (smoothCoresUpTo S n.sqrt).filter (fun d => 2 ^ J ≤ d),
          (1 : ℝ) / d) := hsum
    _ ≤ 2 * (Real.log 4 + 1) *
        (∑' k : ℕ, smoothCoreDyadicMass S (k + J)) := by
      gcongr
      exact smoothCoreTail_reciprocal_le_tsum n S J

end Erdos796
