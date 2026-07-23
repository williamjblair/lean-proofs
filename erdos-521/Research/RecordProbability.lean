import Research.RademacherRecords
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators

namespace Erdos521

local instance fairCoin_isProbabilityMeasure : IsProbabilityMeasure fairCoin := by
  unfold fairCoin
  infer_instance

local instance rademacherMeasure_isProbabilityMeasure :
    IsProbabilityMeasure rademacherMeasure := by
  unfold rademacherMeasure
  infer_instance

/-- The event that time `n` is a cone record for the paired Rademacher walk. -/
def coneRecordEvent (n : ℕ) : Set (ℕ → Bool) :=
  {ω | IsConeRecord (rademacherIncrement ω) n}

/-- Shifting the underlying Boolean sequence by an even number shifts the paired increments. -/
def pairShift (a : ℕ) (ω : ℕ → Bool) : ℕ → Bool := fun k ↦ ω (2 * a + k)

lemma rademacherIncrement_pairShift (a i : ℕ) (ω : ℕ → Bool) :
    rademacherIncrement (pairShift a ω) i = rademacherIncrement ω (a + i) := by
  ext <;> simp [rademacherIncrement, pairShift] <;> congr 2 <;> omega

lemma walk_shift (z : ℕ → ℝ × ℝ) (a n : ℕ) :
    walk (fun i ↦ z (a + i)) n = walk z (a + n) - walk z a := by
  rw [walk, walk, walk, ← Finset.sum_Ico_eq_sub z (by omega : a ≤ a + n)]
  rw [Finset.sum_Ico_eq_sum_range]
  simp

/-- Fresh record suffixes on `[a,a+n)` are the ordinary record event for the shifted walk. -/
lemma isConeRecordAfter_add_iff (z : ℕ → ℝ × ℝ) (a n : ℕ) :
    IsConeRecordAfter z a (a + n) ↔ IsConeRecord (fun i ↦ z (a + i)) n := by
  constructor
  · intro h k hk
    rw [walk_shift, walk_shift]
    have hh := h (a + k) (by omega) (by omega)
    have heq :
        (walk z (a + n) - walk z a) - (walk z (a + k) - walk z a) =
          walk z (a + n) - walk z (a + k) := by abel
    rw [heq]
    exact hh
  · intro h k hak hk
    have hkn : k - a < n := by omega
    have hh := h (k - a) hkn
    rw [walk_shift, walk_shift] at hh
    have hka : a + (k - a) = k := by omega
    rw [hka] at hh
    have heq :
        (walk z (a + n) - walk z a) - (walk z k - walk z a) =
          walk z (a + n) - walk z k := by abel
    rw [← heq]
    exact hh

lemma coneRecordAfter_pairShift_iff (ω : ℕ → Bool) (a n : ℕ) :
    IsConeRecordAfter (rademacherIncrement ω) a (a + n) ↔
      IsConeRecord (rademacherIncrement (pairShift a ω)) n := by
  rw [isConeRecordAfter_add_iff]
  have hfun : (fun i ↦ rademacherIncrement ω (a + i)) =
      rademacherIncrement (pairShift a ω) := by
    funext i
    exact (rademacherIncrement_pairShift a i ω).symm
  rw [hfun]

/-- Even-coordinate shifts preserve the iid Rademacher product law. -/
lemma measurePreserving_pairShift (a : ℕ) :
    MeasurePreserving (pairShift a) rademacherMeasure rademacherMeasure := by
  refine ⟨?_, ?_⟩
  · unfold pairShift
    fun_prop
  · unfold rademacherMeasure pairShift
    simpa only using
      (Measure.map_infinitePi_infinitePi_of_inj
        (P := fun _ : ℕ ↦ fairCoin) (f := fun k : ℕ ↦ 2 * a + k)
          (fun _ _ h ↦ Nat.add_left_cancel h))

/-- The fresh-suffix event between times `a` and `a+n`. -/
def freshConeRecordEvent (a n : ℕ) : Set (ℕ → Bool) :=
  {ω | IsConeRecordAfter (rademacherIncrement ω) a (a + n)}

lemma freshConeRecordEvent_eq_preimage (a n : ℕ) :
    freshConeRecordEvent a n = pairShift a ⁻¹' coneRecordEvent n := by
  ext ω
  exact coneRecordAfter_pairShift_iff ω a n

lemma rademacherIncrement_eq_of_prefix {ω η : ℕ → Bool} {n i : ℕ}
    (h : ∀ k < 2 * n, ω k = η k) (hi : i < n) :
    rademacherIncrement ω i = rademacherIncrement η i := by
  unfold rademacherIncrement
  congr 2
  · apply h
    omega
  · apply h
    omega

lemma walk_rademacher_eq_of_prefix {ω η : ℕ → Bool} {n t : ℕ}
    (h : ∀ k < 2 * n, ω k = η k) (ht : t ≤ n) :
    walk (rademacherIncrement ω) t = walk (rademacherIncrement η) t := by
  unfold walk
  apply Finset.sum_congr rfl
  intro i hi
  apply rademacherIncrement_eq_of_prefix h
  have := Finset.mem_range.mp hi
  omega

lemma isConeRecord_iff_of_prefix {ω η : ℕ → Bool} {n : ℕ}
    (h : ∀ k < 2 * n, ω k = η k) :
    IsConeRecord (rademacherIncrement ω) n ↔
      IsConeRecord (rademacherIncrement η) n := by
  have hn := walk_rademacher_eq_of_prefix h (t := n) le_rfl
  constructor <;> intro hr k hk
  · rw [← walk_rademacher_eq_of_prefix h (t := k) hk.le, ← hn]
    exact hr k hk
  · rw [walk_rademacher_eq_of_prefix h (t := k) hk.le, hn]
    exact hr k hk

/-- Cone-record events are finite-coordinate cylinder events and hence measurable. -/
lemma measurableSet_coneRecordEvent (n : ℕ) : MeasurableSet (coneRecordEvent n) := by
  let S := Finset.range (2 * n)
  let f : (ℕ → Bool) → (S → Bool) := fun ω i ↦ ω i
  let E : Set (S → Bool) := f '' coneRecordEvent n
  have hf : Measurable f := by fun_prop
  have hE : MeasurableSet E := Set.toFinite E |>.measurableSet
  suffices coneRecordEvent n = f ⁻¹' E by
    rw [this]
    exact hE.preimage hf
  ext ω
  constructor
  · intro hω
    exact ⟨ω, hω, rfl⟩
  · rintro ⟨η, hη, hηω⟩
    have hpref : ∀ k < 2 * n, η k = ω k := by
      intro k hk
      have hkS : k ∈ S := by simpa [S] using hk
      exact congrFun hηω ⟨k, hkS⟩
    exact (isConeRecord_iff_of_prefix hpref).mp hη

lemma measurableSet_freshConeRecordEvent (a n : ℕ) :
    MeasurableSet (freshConeRecordEvent a n) := by
  rw [freshConeRecordEvent_eq_preimage]
  exact (measurableSet_coneRecordEvent n).preimage (measurePreserving_pairShift a).measurable

lemma measure_freshConeRecordEvent (a n : ℕ) :
    rademacherMeasure (freshConeRecordEvent a n) =
      rademacherMeasure (coneRecordEvent n) := by
  rw [freshConeRecordEvent_eq_preimage]
  exact (measurePreserving_pairShift a).measure_preimage
    (measurableSet_coneRecordEvent n).nullMeasurableSet

lemma freshConeRecord_iff_of_block {ω η : ℕ → Bool} {a n : ℕ}
    (h : ∀ k, 2 * a ≤ k → k < 2 * (a + n) → ω k = η k) :
    ω ∈ freshConeRecordEvent a n ↔ η ∈ freshConeRecordEvent a n := by
  rw [freshConeRecordEvent_eq_preimage]
  change IsConeRecord (rademacherIncrement (pairShift a ω)) n ↔
    IsConeRecord (rademacherIncrement (pairShift a η)) n
  apply isConeRecord_iff_of_prefix
  intro k hk
  apply h (2 * a + k)
  · omega
  · omega

/-- A record event and the fresh record test on a disjoint later block are independent. -/
lemma indep_coneRecordEvent_fresh (a n : ℕ) :
    IndepSet (coneRecordEvent a) (freshConeRecordEvent a n) rademacherMeasure := by
  let S := Finset.range (2 * a)
  let T := Finset.Ico (2 * a) (2 * (a + n))
  let f : (ℕ → Bool) → (S → Bool) := fun ω i ↦ ω i
  let g : (ℕ → Bool) → (T → Bool) := fun ω i ↦ ω i
  have hST : Disjoint S T := by
    rw [Finset.disjoint_left]
    intro k hkS hkT
    have hlt : k < 2 * a := by simpa [S] using hkS
    have hle : 2 * a ≤ k := (Finset.mem_Ico.mp hkT).1
    omega
  have hcoord : iIndepFun (fun i (ω : ℕ → Bool) ↦ ω i) rademacherMeasure := by
    unfold rademacherMeasure
    exact iIndepFun_infinitePi (X := fun _ b ↦ b) (by fun_prop)
  have hfg : IndepFun f g rademacherMeasure := by
    exact iIndepFun.indepFun_finset S T hST hcoord (by fun_prop)
  let E : Set (S → Bool) := f '' coneRecordEvent a
  let F : Set (T → Bool) := g '' freshConeRecordEvent a n
  have hE : MeasurableSet E := Set.toFinite E |>.measurableSet
  have hF : MeasurableSet F := Set.toFinite F |>.measurableSet
  have hAeq : coneRecordEvent a = f ⁻¹' E := by
    ext ω
    constructor
    · intro hω
      exact ⟨ω, hω, rfl⟩
    · rintro ⟨η, hη, hηω⟩
      have hpref : ∀ k < 2 * a, η k = ω k := by
        intro k hk
        have hkS : k ∈ S := by simpa [S] using hk
        exact congrFun hηω ⟨k, hkS⟩
      exact (isConeRecord_iff_of_prefix hpref).mp hη
  have hBeq : freshConeRecordEvent a n = g ⁻¹' F := by
    ext ω
    constructor
    · intro hω
      exact ⟨ω, hω, rfl⟩
    · rintro ⟨η, hη, hηω⟩
      have hblock : ∀ k, 2 * a ≤ k → k < 2 * (a + n) → η k = ω k := by
        intro k hklo hkhi
        have hkT : k ∈ T := by simpa [T, Finset.mem_Ico] using And.intro hklo hkhi
        exact congrFun hηω ⟨k, hkT⟩
      exact (freshConeRecord_iff_of_block hblock).mp hη
  rw [hAeq, hBeq]
  exact (indepFun_iff_indepSet_preimage (μ := rademacherMeasure) (by fun_prop) (by fun_prop)).mp
    hfg E F hE hF

lemma measure_inter_coneRecord_fresh (a n : ℕ) :
    rademacherMeasure (coneRecordEvent a ∩ freshConeRecordEvent a n) =
      rademacherMeasure (coneRecordEvent a) * rademacherMeasure (coneRecordEvent n) := by
  rw [(indep_coneRecordEvent_fresh a n).measure_inter_eq_mul,
    measure_freshConeRecordEvent]

/-- The deterministic record decomposition, pulled back to the Rademacher sample space. -/
lemma coneRecordEvent_inter_add (a n : ℕ) (hn : 0 < n) :
    coneRecordEvent a ∩ coneRecordEvent (a + n) =
      coneRecordEvent a ∩ freshConeRecordEvent a n := by
  ext ω
  simp only [mem_inter_iff, coneRecordEvent, freshConeRecordEvent, mem_setOf_eq]
  exact (cone_record_decomposition (rademacherIncrement ω) (by omega : a < a + n)).symm

/-- Exact record-event correlation at two distinct times. -/
lemma measure_inter_coneRecordEvent (a n : ℕ) (hn : 0 < n) :
    rademacherMeasure (coneRecordEvent a ∩ coneRecordEvent (a + n)) =
      rademacherMeasure (coneRecordEvent a) * rademacherMeasure (coneRecordEvent n) := by
  rw [coneRecordEvent_inter_add a n hn, measure_inter_coneRecord_fresh]

end Erdos521
