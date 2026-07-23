import Research.CentralZeroFree
import Research.UpperReduction
import Research.FairPrefix
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Tactic

open Filter MeasureTheory Set
open scoped Topology

namespace Erdos521

local instance fairCoin_isProbabilityMeasure_oneSided : IsProbabilityMeasure fairCoin := by
  unfold fairCoin
  infer_instance

/-- Distinct roots on the positive endpoint-side half of `[-1,1]`. -/
noncomputable def rightRootCount (ω : ℕ → Bool) (n : ℕ) : ℕ :=
  Set.ncard ((littlewoodPolynomial ω n).rootSet ℝ ∩ Set.Ioc (1 / 2 : ℝ) 1)

/-- Distinct roots on the negative endpoint-side half of `[-1,1]`. -/
noncomputable def leftRootCount (ω : ℕ → Bool) (n : ℕ) : ℕ :=
  Set.ncard ((littlewoodPolynomial ω n).rootSet ℝ ∩ Set.Ico (-1 : ℝ) (-1 / 2))

lemma innerRootSet_eq_left_union_right (ω : ℕ → Bool) (n : ℕ) :
    (littlewoodPolynomial ω n).rootSet ℝ ∩ {x : ℝ | |x| ≤ 1} =
      ((littlewoodPolynomial ω n).rootSet ℝ ∩ Set.Ico (-1 : ℝ) (-1 / 2)) ∪
      ((littlewoodPolynomial ω n).rootSet ℝ ∩ Set.Ioc (1 / 2 : ℝ) 1) := by
  ext x
  constructor
  · rintro ⟨hroot, hx⟩
    have hxunit : -1 ≤ x ∧ x ≤ 1 := by simpa [abs_le] using hx
    have hncentral : ¬ |x| ≤ 1 / 2 :=
      fun h ↦ central_not_mem_littlewood_rootSet ω n x h hroot
    rcases lt_or_ge x (-1 / 2) with hleft | hnleft
    · exact Or.inl ⟨hroot, ⟨hxunit.1, hleft⟩⟩
    · have hright : 1 / 2 < x := by
        by_contra hnot
        have hxhalf : x ≤ 1 / 2 := le_of_not_gt hnot
        apply hncentral
        rw [abs_le]
        constructor
        · linarith
        · exact hxhalf
      exact Or.inr ⟨hroot, ⟨hright, hxunit.2⟩⟩
  · rintro (⟨hroot, hx⟩ | ⟨hroot, hx⟩)
    · change -1 ≤ x ∧ x < -1 / 2 at hx
      refine ⟨hroot, ?_⟩
      change |x| ≤ 1
      rw [abs_le]
      exact ⟨hx.1, by linarith⟩
    · change 1 / 2 < x ∧ x ≤ 1 at hx
      refine ⟨hroot, ?_⟩
      change |x| ≤ 1
      rw [abs_le]
      exact ⟨by linarith, hx.2⟩

lemma disjoint_left_right_rootSets (ω : ℕ → Bool) (n : ℕ) :
    Disjoint
      ((littlewoodPolynomial ω n).rootSet ℝ ∩ Set.Ico (-1 : ℝ) (-1 / 2))
      ((littlewoodPolynomial ω n).rootSet ℝ ∩ Set.Ioc (1 / 2 : ℝ) 1) := by
  rw [Set.disjoint_left]
  rintro x ⟨hxroot, hxleft⟩ ⟨_, hxright⟩
  change -1 ≤ x ∧ x < -1 / 2 at hxleft
  change 1 / 2 < x ∧ x ≤ 1 at hxright
  linarith

lemma innerRootCount_eq_left_add_right (ω : ℕ → Bool) (n : ℕ) :
    innerRootCount ω n = leftRootCount ω n + rightRootCount ω n := by
  rw [innerRootCount, leftRootCount, rightRootCount,
    innerRootSet_eq_left_union_right,
    Set.ncard_union_eq (disjoint_left_right_rootSets ω n)]

/-- Flip exactly the odd coefficient bits. -/
def oddTwist (ω : ℕ → Bool) : ℕ → Bool :=
  fun k ↦ if Even k then ω k else !(ω k)

lemma sign_not (b : Bool) : sign (!b) = -sign b := by
  cases b <;> norm_num [sign]

lemma sign_oddTwist (ω : ℕ → Bool) (k : ℕ) :
    sign (oddTwist ω k) = (-1 : ℝ) ^ k * sign (ω k) := by
  by_cases hk : Even k
  · obtain ⟨j, rfl⟩ := hk
    simp [oddTwist, pow_mul]
  · have hkodd : Odd k := Nat.not_even_iff_odd.mp hk
    obtain ⟨j, rfl⟩ := hkodd
    simp [oddTwist, sign_not, pow_succ, pow_mul]

lemma littlewoodPolynomial_oddTwist_eval (ω : ℕ → Bool) (n : ℕ) (x : ℝ) :
    (littlewoodPolynomial (oddTwist ω) n).eval x =
      (littlewoodPolynomial ω n).eval (-x) := by
  rw [littlewoodPolynomial_eval, littlewoodPolynomial_eval]
  apply Finset.sum_congr rfl
  intro k hk
  rw [sign_oddTwist, neg_pow]
  ring

lemma mem_littlewood_rootSet_iff_eval_eq_zero (ω : ℕ → Bool) (n : ℕ) (x : ℝ) :
    x ∈ (littlewoodPolynomial ω n).rootSet ℝ ↔
      (littlewoodPolynomial ω n).eval x = 0 := by
  rw [Polynomial.mem_rootSet]
  have hp : littlewoodPolynomial ω n ≠ 0 := by
    intro hzero
    have h := littlewoodPolynomial_ne_zero_of_abs_le_half ω n 0 (by norm_num)
    rw [hzero, Polynomial.eval_zero] at h
    exact h rfl
  constructor
  · rintro ⟨_, h⟩
    simpa [Polynomial.aeval_def] using h
  · intro h
    refine ⟨hp, ?_⟩
    simpa [Polynomial.aeval_def] using h

lemma mem_rootSet_oddTwist_iff (ω : ℕ → Bool) (n : ℕ) (x : ℝ) :
    x ∈ (littlewoodPolynomial (oddTwist ω) n).rootSet ℝ ↔
      -x ∈ (littlewoodPolynomial ω n).rootSet ℝ := by
  rw [mem_littlewood_rootSet_iff_eval_eq_zero,
    mem_littlewood_rootSet_iff_eval_eq_zero,
    littlewoodPolynomial_oddTwist_eval]

lemma rightRootCount_oddTwist (ω : ℕ → Bool) (n : ℕ) :
    rightRootCount (oddTwist ω) n = leftRootCount ω n := by
  rw [rightRootCount, leftRootCount]
  apply Set.ncard_congr (fun x _ ↦ -x)
  · intro x hx
    exact ⟨(mem_rootSet_oddTwist_iff ω n x).mp hx.1, by
      constructor <;> linarith [hx.2.1, hx.2.2]⟩
  · intro a b ha hb hab
    linarith
  · intro y hy
    refine ⟨-y, ?_, by ring⟩
    exact ⟨(mem_rootSet_oddTwist_iff ω n (-y)).mpr (by simpa using hy.1), by
      constructor <;> linarith [hy.2.1, hy.2.2]⟩

lemma fairCoin_map_not : Measure.map (fun b : Bool ↦ !b) fairCoin = fairCoin := by
  apply Measure.ext_of_singleton
  intro b
  rw [Measure.map_apply (by fun_prop) (MeasurableSet.singleton b)]
  have hpre : (fun c : Bool ↦ !c) ⁻¹' ({b} : Set Bool) = {!b} := by
    ext c
    cases b <;> cases c <;> simp
  rw [hpre, fairCoin_singleton, fairCoin_singleton]

lemma measurePreserving_oddTwist :
    MeasurePreserving oddTwist rademacherMeasure rademacherMeasure := by
  refine ⟨by unfold oddTwist; fun_prop, ?_⟩
  let f := fun i : ℕ ↦ fun b : Bool ↦ if Even i then b else !b
  change Measure.map (fun ω i ↦ f i (ω i))
      (Measure.infinitePi (fun _ : ℕ ↦ fairCoin)) =
    Measure.infinitePi (fun _ : ℕ ↦ fairCoin)
  rw [Measure.infinitePi_map_pi (fun _ : ℕ ↦ fairCoin) (by intro i; dsimp [f]; fun_prop)]
  congr 1
  funext i
  by_cases hi : Even i
  · simp [f, hi]
  · simp [f, hi, fairCoin_map_not]

/-- An eventual one-sided upper bound with half of the budget in F-019. -/
def RightUpperGap : Prop :=
  ∀ᵐ ω ∂rademacherMeasure,
    ∀ᶠ n : ℕ in atTop,
      (rightRootCount ω n : ℝ) / Real.log (n : ℝ) ≤ (3 : ℝ) / (4 * Real.pi)

lemma leftUpperGap_of_rightUpperGap (h : RightUpperGap) :
    ∀ᵐ ω ∂rademacherMeasure,
      ∀ᶠ n : ℕ in atTop,
        (leftRootCount ω n : ℝ) / Real.log (n : ℝ) ≤ (3 : ℝ) / (4 * Real.pi) := by
  have htend : Tendsto oddTwist (ae rademacherMeasure) (ae rademacherMeasure) := by
    simpa only [measurePreserving_oddTwist.map_eq] using
      Measure.tendsto_ae_map measurePreserving_oddTwist.aemeasurable
  filter_upwards [htend.eventually h] with ω hω
  filter_upwards [hω] with n hn
  simpa only [rightRootCount_oddTwist] using hn

/-- By sign-twist symmetry and the central zero-free interval, a one-sided bound on `(1/2,1]`
already supplies the two-sided local upper gap needed by F-019. -/
lemma localUpperGap_of_rightUpperGap (h : RightUpperGap) : LocalUpperGap := by
  have hleft := leftUpperGap_of_rightUpperGap h
  filter_upwards [h, hleft] with ω hright hleftω
  filter_upwards [hright, hleftω, eventually_ge_atTop (2 : ℕ)] with n hr hn hnlarge
  rw [innerRootCount_eq_left_add_right]
  push_cast
  rw [add_div]
  calc
    (leftRootCount ω n : ℝ) / Real.log (n : ℝ) +
        (rightRootCount ω n : ℝ) / Real.log (n : ℝ) ≤
      3 / (4 * Real.pi) + 3 / (4 * Real.pi) := add_le_add hn hr
    _ = 3 / (2 * Real.pi) := by
      field_simp [ne_of_gt Real.pi_pos]
      ring

end Erdos521
