import Research.AdaptiveParameter

noncomputable section
open Filter Asymptotics
namespace Erdos959

/-- The matching easy half of the PNT-in-AP consequence: eventually the
Chebyshev sum in the split progression is at most `x`. -/
theorem eventually_splitPrimeChebyshev_upper :
    ∀ᶠ x : ℝ in atTop,
      (∑ p ∈ (Finset.Iic ⌊x⌋₊).filter Nat.Prime,
        if p % 4 = 1 then Real.log p else 0) ≤ x := by
  let f : ℝ → ℝ := fun x =>
    ∑ p ∈ (Finset.Iic ⌊x⌋₊).filter Nat.Prime,
      if p % 4 = 1 then Real.log p else 0
  let g : ℝ → ℝ := fun x => x / (4 : ℕ).totient
  have hequiv : f ~[atTop] g := by
    simpa [f, g] using
      (chebyshev_asymptotic_pnt (q := 4) (a := 1) (by norm_num) (by norm_num) (by norm_num))
  have hgz : ∀ᶠ x : ℝ in atTop, g x ≠ 0 := by
    filter_upwards [eventually_gt_atTop 0] with x hx
    dsimp [g]
    positivity
  have htend : Tendsto (f / g) atTop (nhds 1) :=
    (isEquivalent_iff_tendsto_one hgz).mp hequiv
  have hclose : ∀ᶠ x : ℝ in atTop, dist ((f / g) x) 1 < 1 / 2 :=
    htend.eventually (Metric.ball_mem_nhds 1 (by norm_num))
  filter_upwards [hclose, eventually_gt_atTop 0] with x hxclose hx
  have htot : Nat.totient 4 = 2 := by decide
  have hg : g x = x / 2 := by simp [g, htot]
  have hgpos : 0 < g x := by rw [hg]; positivity
  have habs : |f x / g x - 1| < 1 / 2 := by
    simpa [Pi.div_apply, Real.dist_eq] using hxclose
  rw [abs_lt] at habs
  rw [hg] at hgpos habs
  have hxne : x / 2 ≠ 0 := ne_of_gt hgpos
  field_simp at habs
  nlinarith

/-- A usable upper bound complementary to F-036. Eventually the number of
split primes below `m²` is at most `2m²/log m`. -/
theorem eventually_parameterUniverse_card_log_upper :
    ∃ M : ℕ, ∀ m ≥ M,
      ((parameterUniverse m).card : ℝ) * Real.log m ≤ 2 * (m : ℝ) ^ 2 := by
  obtain ⟨X, hX⟩ := eventually_atTop.1 eventually_splitPrimeChebyshev_upper
  let M : ℕ := max 2 ⌈max X 0⌉₊
  refine ⟨M, fun m hm => ?_⟩
  have hm2 : 2 ≤ m := le_trans (le_max_left 2 ⌈max X 0⌉₊) hm
  have hmX : X ≤ ((m ^ 2 : ℕ) : ℝ) := by
    have hceil : max X 0 ≤ (⌈max X 0⌉₊ : ℝ) := Nat.le_ceil (max X 0)
    have hmceil : ⌈max X 0⌉₊ ≤ m := le_trans (le_max_right 2 ⌈max X 0⌉₊) hm
    have hmle : (m : ℝ) ≤ (m : ℝ) ^ 2 := by
      have : (1 : ℝ) ≤ m := by exact_mod_cast (by omega : 1 ≤ m)
      nlinarith
    have hmceilR : (⌈max X 0⌉₊ : ℝ) ≤ m := by exact_mod_cast hmceil
    have hmle' : (m : ℝ) ≤ ((m ^ 2 : ℕ) : ℝ) := by
      push_cast
      exact hmle
    exact (le_max_left X 0).trans (hceil.trans (hmceilR.trans hmle'))
  have htheta0 := hX ((m ^ 2 : ℕ) : ℝ) hmX
  rw [Nat.floor_natCast, splitPrimeChebyshev_eq] at htheta0
  have htheta : (∑ p ∈ parameterUniverse m, Real.log p) ≤ (m : ℝ) ^ 2 := by
    simpa [parameterUniverse, Nat.cast_pow] using htheta0
  let V := (parameterUniverse m).filter fun p => m < p
  let W := (parameterUniverse m).filter fun p => p ≤ m
  have hpartition : W ∪ V = parameterUniverse m := by
    ext p
    simp only [Finset.mem_union, Finset.mem_filter, W, V]
    constructor
    · rintro (⟨hp, _⟩ | ⟨hp, _⟩) <;> exact hp
    · intro hp
      rcases le_or_gt p m with hpm | hmp
      · exact Or.inl ⟨hp, hpm⟩
      · exact Or.inr ⟨hp, hmp⟩
  have hWcard : W.card ≤ m + 1 := by
    have hsub : W ⊆ Finset.Iic m := by
      intro p hp
      exact Finset.mem_Iic.mpr (Finset.mem_filter.mp hp).2
    simpa using Finset.card_le_card hsub
  have hcard : (parameterUniverse m).card ≤ (m + 1) + V.card := by
    rw [← hpartition]
    exact (Finset.card_union_le W V).trans (Nat.add_le_add_right hWcard V.card)
  have hmlog : 0 < Real.log (m : ℝ) := Real.log_pos (by exact_mod_cast hm2)
  have hVsum : (V.card : ℝ) * Real.log m ≤
      ∑ p ∈ parameterUniverse m, Real.log p := by
    calc
      (V.card : ℝ) * Real.log m = ∑ _p ∈ V, Real.log m := by
        rw [Finset.sum_const]
        simp
      _ ≤ ∑ p ∈ V, Real.log p := by
        apply Finset.sum_le_sum
        intro p hp
        have hpm : m < p := (Finset.mem_filter.mp hp).2
        exact Real.strictMonoOn_log.monotoneOn
          (show 0 < (m : ℝ) by positivity)
          (show 0 < (p : ℝ) by exact_mod_cast (by omega : 0 < p))
          (by exact_mod_cast (Nat.le_of_lt hpm))
      _ ≤ ∑ p ∈ parameterUniverse m, Real.log p := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro p hp
          exact (Finset.mem_filter.mp hp).1
        · intro p hpU hpV
          exact Real.log_nonneg (by
            have hp1 : 1 ≤ p := (parameter_prime hpU).one_le
            exact_mod_cast hp1)
  have hlogSub : Real.log (m : ℝ) ≤ m - 1 :=
    Real.log_le_sub_one_of_pos (by positivity)
  have hsmall : ((m + 1 : ℕ) : ℝ) * Real.log m ≤ (m : ℝ) ^ 2 := by
    calc
      ((m + 1 : ℕ) : ℝ) * Real.log m ≤ (m + 1 : ℝ) * (m - 1) := by
        norm_num only [Nat.cast_add, Nat.cast_one]
        exact mul_le_mul_of_nonneg_left hlogSub (by positivity)
      _ ≤ (m : ℝ) ^ 2 := by nlinarith
  have hcardCast : ((parameterUniverse m).card : ℝ) ≤ (m + 1 : ℕ) + V.card := by
    exact_mod_cast hcard
  calc
    ((parameterUniverse m).card : ℝ) * Real.log m ≤
        (((m + 1 : ℕ) : ℝ) + V.card) * Real.log m :=
      mul_le_mul_of_nonneg_right hcardCast hmlog.le
    _ = ((m + 1 : ℕ) : ℝ) * Real.log m + (V.card : ℝ) * Real.log m := by ring
    _ ≤ (m : ℝ) ^ 2 + (m : ℝ) ^ 2 :=
      add_le_add hsmall (hVsum.trans htheta)
    _ = 2 * (m : ℝ) ^ 2 := by ring

end Erdos959
