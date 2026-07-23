import Mathlib
import Research.Statement
import Research.Growth

namespace Erdos254.CountableConvergencePhases

open Filter
open scoped BigOperators
open Erdos254

noncomputable section

lemma nd_nonneg (x : ℝ) : 0 ≤ nearestIntegerDistance x := by
  apply le_min
  · exact Int.fract_nonneg x
  · exact sub_nonneg.mpr (Int.fract_lt_one x).le

lemma nd_eq_abs_sub_round (x : ℝ) :
    nearestIntegerDistance x = |x - (round x : ℝ)| :=
  (abs_sub_round_eq_min x).symm

lemma nd_le_abs_sub_int (x : ℝ) (z : ℤ) :
    nearestIntegerDistance x ≤ |x - (z : ℝ)| := by
  rw [nd_eq_abs_sub_round]
  exact round_le x z

lemma nd_add_le (x y : ℝ) :
    nearestIntegerDistance (x + y) ≤
      nearestIntegerDistance x + nearestIntegerDistance y := by
  calc
    nearestIntegerDistance (x + y) ≤
        |(x + y) - ((round x + round y : ℤ) : ℝ)| :=
      nd_le_abs_sub_int _ _
    _ = |(x - (round x : ℝ)) + (y - (round y : ℝ))| := by
      rw [Int.cast_add]
      ring_nf
    _ ≤ |x - (round x : ℝ)| + |y - (round y : ℝ)| := abs_add_le _ _
    _ = nearestIntegerDistance x + nearestIntegerDistance y := by
      rw [← nd_eq_abs_sub_round, ← nd_eq_abs_sub_round]

lemma nd_neg (x : ℝ) : nearestIntegerDistance (-x) = nearestIntegerDistance x := by
  apply le_antisymm
  · calc
      nearestIntegerDistance (-x) ≤ |-x - ((-round x : ℤ) : ℝ)| :=
        nd_le_abs_sub_int _ _
      _ = |x - (round x : ℝ)| := by
        rw [Int.cast_neg]
        rw [show -x - -(round x : ℝ) = -(x - (round x : ℝ)) by ring_nf,
          abs_neg]
      _ = nearestIntegerDistance x := (nd_eq_abs_sub_round x).symm
  · simpa only [neg_neg] using
      (show nearestIntegerDistance (-(-x)) ≤ nearestIntegerDistance (-x) by
        calc
          nearestIntegerDistance (-(-x)) ≤
              |-(-x) - ((-round (-x) : ℤ) : ℝ)| := nd_le_abs_sub_int _ _
          _ = |(-x) - (round (-x) : ℝ)| := by
            rw [Int.cast_neg]
            rw [show - -x - -(round (-x) : ℝ) = -((-x) - (round (-x) : ℝ)) by
              ring_nf, abs_neg]
          _ = nearestIntegerDistance (-x) := (nd_eq_abs_sub_round (-x)).symm)

lemma nd_sub_le (x y : ℝ) :
    nearestIntegerDistance (x - y) ≤
      nearestIntegerDistance x + nearestIntegerDistance y := by
  simpa only [sub_eq_add_neg, nd_neg] using nd_add_le x (-y)

lemma nd_eq_self_of_mem (z : ℝ) (hz0 : 0 ≤ z) (hzh : z ≤ 1 / 2) :
    nearestIntegerDistance z = z := by
  have hz1 : z < 1 := hzh.trans_lt (by norm_num)
  rw [nearestIntegerDistance, Int.fract_eq_self.mpr ⟨hz0, hz1⟩]
  exact min_eq_left (by linarith)

lemma shell_phase_lower
    (C : Set ℕ) (x : ℕ) (δ : ℝ)
    (hδ : 0 < δ)
    (hxlo : 1 / 8 ≤ (x : ℝ) * δ)
    (hxhi : (x : ℝ) * δ ≤ 1 / 4) :
    ((shellCount C x : ℝ) / 8) ≤ phasePartialSum C δ (2 * x) := by
  classical
  let S := (Finset.Ioc x (2 * x)).filter (fun n => n ∈ C)
  let P := (Finset.Icc 1 (2 * x)).filter (fun n => n ∈ C)
  have hterm : ∀ n ∈ S, (1 / 8 : ℝ) ≤
      nearestIntegerDistance (δ * (n : ℝ)) := by
    intro n hn
    have hn' := Finset.mem_Ioc.mp (Finset.mem_filter.mp hn).1
    have hlo : 1 / 8 ≤ δ * (n : ℝ) := by
      have hxn : (x : ℝ) ≤ n := by exact_mod_cast hn'.1.le
      nlinarith [hxlo]
    have hhi : δ * (n : ℝ) ≤ 1 / 2 := by
      have hn2 : (n : ℝ) ≤ 2 * x := by exact_mod_cast hn'.2
      nlinarith [hxhi]
    rw [nd_eq_self_of_mem _ (by positivity) hhi]
    exact hlo
  have hSP : S ⊆ P := by
    intro n hn
    simp only [S, P, Finset.mem_filter, Finset.mem_Ioc, Finset.mem_Icc] at hn ⊢
    exact ⟨⟨by omega, hn.1.2⟩, hn.2⟩
  calc
    (shellCount C x : ℝ) / 8 = ∑ _n ∈ S, (1 / 8 : ℝ) := by
      simp [shellCount, S]
      ring
    _ ≤ ∑ n ∈ S, nearestIntegerDistance (δ * (n : ℝ)) := by
      exact Finset.sum_le_sum fun n hn => hterm n hn
    _ ≤ ∑ n ∈ P, nearestIntegerDistance (δ * (n : ℝ)) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hSP
      intro n hnP hnS
      exact nd_nonneg _
    _ = phasePartialSum C δ (2 * x) := by
      simp only [phasePartialSum, P]

/-- Phases in `[0,1]` whose every partial sum is at most `k`. -/
def boundedPhases (C : Set ℕ) (k : ℕ) : Set ℝ :=
  {θ | θ ∈ Set.Icc (0 : ℝ) 1 ∧
    ∀ N, phasePartialSum C θ N ≤ (k : ℝ)}

lemma boundedPhases_separated
    {C : Set ℕ} (hdyadic : Tendsto (dyadicIncrement C) atTop atTop)
    (k : ℕ) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ θ ∈ boundedPhases C k, ∀ φ ∈ boundedPhases C k,
        θ ≠ φ → ε ≤ |θ - φ| := by
  let M : ℕ := 16 * k + 1
  obtain ⟨X, hX⟩ := (eventually_atTop.1
    (dyadic_tendsto_eventually_many C hdyadic M))
  let ε : ℝ := min (1 / 8) (1 / (8 * ((X : ℝ) + 1)))
  have hε : 0 < ε := by
    dsimp [ε]
    positivity
  refine ⟨ε, hε, ?_⟩
  intro θ hθ φ hφ hne
  by_contra hnot
  have hdist : |θ - φ| < ε := lt_of_not_ge hnot
  let δ : ℝ := |θ - φ|
  have hδ : 0 < δ := abs_pos.mpr (sub_ne_zero.mpr hne)
  have hδ8 : δ < 1 / 8 := hdist.trans_le (min_le_left _ _)
  have hδX : δ < 1 / (8 * ((X : ℝ) + 1)) :=
    hdist.trans_le (min_le_right _ _)
  let x : ℕ := ⌈1 / (8 * δ)⌉₊
  have hr0 : 0 ≤ 1 / (8 * δ) := by positivity
  have hxceil_lo : 1 / (8 * δ) ≤ (x : ℝ) := Nat.le_ceil _
  have hxceil_hi : (x : ℝ) < 1 / (8 * δ) + 1 := Nat.ceil_lt_add_one hr0
  have hxX : X ≤ x := by
    have hprod : δ * (8 * ((X : ℝ) + 1)) < 1 :=
      (lt_div_iff₀ (by positivity)).mp hδX
    have hlarge : (X : ℝ) + 1 < 1 / (8 * δ) := by
      rw [lt_div_iff₀ (by positivity)]
      nlinarith [hprod]
    have : (X : ℝ) ≤ (x : ℝ) := by linarith [hlarge, hxceil_lo]
    exact_mod_cast this
  have hxlo : 1 / 8 ≤ (x : ℝ) * δ := by
    calc
      1 / 8 = (1 / (8 * δ)) * δ := by field_simp
      _ ≤ (x : ℝ) * δ := mul_le_mul_of_nonneg_right hxceil_lo hδ.le
  have hxhi : (x : ℝ) * δ ≤ 1 / 4 := by
    have hlt : (x : ℝ) * δ < 1 / 8 + δ := by
      calc
        (x : ℝ) * δ < (1 / (8 * δ) + 1) * δ :=
          mul_lt_mul_of_pos_right hxceil_hi hδ
        _ = 1 / 8 + δ := by field_simp
    linarith
  have hlower := shell_phase_lower C x δ hδ hxlo hxhi
  have hcard : M ≤ shellCount C x := hX x hxX
  have hlower' : (2 * k : ℝ) < phasePartialSum C δ (2 * x) := by
    calc
      (2 * k : ℝ) < (M : ℝ) / 8 := by
        dsimp [M]
        push_cast
        linarith
      _ ≤ (shellCount C x : ℝ) / 8 := by
        apply div_le_div_of_nonneg_right
        · exact_mod_cast hcard
        · norm_num
      _ ≤ phasePartialSum C δ (2 * x) := hlower
  have htri : phasePartialSum C δ (2 * x) ≤
      phasePartialSum C θ (2 * x) + phasePartialSum C φ (2 * x) := by
    classical
    simp only [phasePartialSum]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro n hn
    have hpoint : nearestIntegerDistance (δ * (n : ℝ)) ≤
        nearestIntegerDistance (θ * (n : ℝ)) +
          nearestIntegerDistance (φ * (n : ℝ)) := by
      rcases le_total φ θ with hφθ | hθφ
      · have hδeq : δ * (n : ℝ) = θ * (n : ℝ) - φ * (n : ℝ) := by
          dsimp [δ]
          rw [abs_of_nonneg (sub_nonneg.mpr hφθ)]
          ring
        rw [hδeq]
        exact nd_sub_le _ _
      · have hδeq : δ * (n : ℝ) = -(θ * (n : ℝ) - φ * (n : ℝ)) := by
          dsimp [δ]
          rw [abs_of_nonpos (sub_nonpos.mpr hθφ)]
          ring
        rw [hδeq, nd_neg]
        exact nd_sub_le _ _
    exact hpoint
  have hupp : phasePartialSum C θ (2 * x) +
      phasePartialSum C φ (2 * x) ≤ 2 * k := by
    have hθb := hθ.2 (2 * x)
    have hφb := hφ.2 (2 * x)
    linarith
  linarith

lemma finite_of_totallyBounded_separated
    {s : Set ℝ} (htb : TotallyBounded s) {ε : ℝ} (hε : 0 < ε)
    (hsep : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → ε ≤ |x - y|) :
    s.Finite := by
  obtain ⟨t, htfin, hcover⟩ := Metric.totallyBounded_iff.mp htb (ε / 2) (by positivity)
  classical
  have hex : ∀ x : s, ∃ y ∈ t, dist x.1 y < ε / 2 := by
    intro x
    have hx := hcover x.2
    simp only [Set.mem_iUnion, Metric.mem_ball] at hx
    obtain ⟨y, hy, hd⟩ := hx
    exact ⟨y, hy, hd⟩
  choose center hcenter_mem hcenter using hex
  let f : s → ℝ := fun x => center x
  have hf_range : Set.range f ⊆ t := by
    rintro y ⟨x, rfl⟩
    exact hcenter_mem x
  have hfrange_fin : (Set.range f).Finite := htfin.subset hf_range
  have hfinj : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    by_contra hne
    have hsep' := hsep x.1 x.2 y.1 y.2 hne
    have hxd : dist x.1 (f x) < ε / 2 := hcenter x
    have hyd : dist y.1 (f y) < ε / 2 := hcenter y
    have : |x.1 - y.1| < ε := by
      rw [← Real.dist_eq]
      calc
        dist x.1 y.1 ≤ dist x.1 (f x) + dist (f x) y.1 := dist_triangle _ _ _
        _ = dist x.1 (f x) + dist (f y) y.1 := by rw [hxy]
        _ < ε := by
          have hyd' : dist (f y) y.1 < ε / 2 := by
            rwa [dist_comm]
          linarith
    linarith
  have : Set.Finite (Set.univ : Set s) := by
    apply Set.Finite.of_finite_image (f := f)
    · simpa only [Set.image_univ] using hfrange_fin
    · intro x hx y hy hxy
      exact hfinj hxy
  letI : Finite s := Set.finite_univ_iff.mp this
  exact Set.toFinite s

/-- Under dyadic shell multiplicity, the set of phases in `[0,1]` at which the
nearest-integer partial sums remain bounded is countable. -/
theorem countable_bounded_phase_set
    {C : Set ℕ} (hdyadic : Tendsto (dyadicIncrement C) atTop atTop) :
    {θ : ℝ | θ ∈ Set.Icc (0 : ℝ) 1 ∧
      ∃ B : ℝ, ∀ N, phasePartialSum C θ N ≤ B}.Countable := by
  have hfinite : ∀ k : ℕ, (boundedPhases C k).Finite := by
    intro k
    obtain ⟨ε, hε, hsep⟩ := boundedPhases_separated hdyadic k
    apply finite_of_totallyBounded_separated
      ((totallyBounded_Icc (0 : ℝ) 1).subset (fun θ hθ => hθ.1)) hε hsep
  refine (Set.countable_iUnion fun k => (hfinite k).countable).mono ?_
  rintro θ ⟨hθI, B, hB⟩
  obtain ⟨k, hk⟩ := exists_nat_ge B
  refine Set.mem_iUnion.mpr ⟨k, ?_⟩
  exact ⟨hθI, fun N => (hB N).trans (by exact_mod_cast hk)⟩

end

end Erdos254.CountableConvergencePhases
