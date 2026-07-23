import Mathlib
import Research.TorusCharacterSeparation
import Research.ScalarOrbit
import Research.CompactSemigroup
import Research.TailSemigroup

namespace Erdos254.TorusOrbit

open scoped BigOperators Topology
open Erdos254.TorusCharacterSeparation Erdos254.ScalarOrbit
open Erdos254.CompactSemigroup Erdos254.TailSemigroup

noncomputable section

variable {d : Type*} [Fintype d]

/-- The additive-circle character associated to an integer vector. -/
def torusChar (k : d → ℤ) : UnitAddTorus d →ₜ+ UnitAddCircle := by
  classical
  let f : UnitAddTorus d →+ UnitAddCircle :=
    { toFun := fun y => ∑ i, k i • y i
      map_zero' := by simp
      map_add' := by
        intro x y
        simp only [Pi.add_apply, zsmul_add, Finset.sum_add_distrib] }
  exact ContinuousAddMonoidHom.mk f <| continuous_finsetSum Finset.univ fun i hi =>
    (continuous_apply i).zsmul (k i)

lemma mFourier_eq_torusChar_toCircle (k : d → ℤ) (y : UnitAddTorus d) :
    UnitAddTorus.mFourier k y = ((torusChar k y).toCircle : ℂ) := by
  classical
  simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, fourier_apply, torusChar]
  have haux : ∀ s : Finset d,
      (∏ i ∈ s, ((k i • y i).toCircle : ℂ)) =
        (((∑ i ∈ s, k i • y i : UnitAddCircle).toCircle) : ℂ) := by
    intro s
    induction s using Finset.induction with
    | empty => simp
    | @insert i s hi ih =>
        rw [Finset.prod_insert hi, Finset.sum_insert hi, AddCircle.toCircle_add,
          Circle.coe_mul, ih]
  exact haux Finset.univ

lemma torusChar_phase (k : d → ℤ) (α : d → ℝ) :
    torusChar k (fun i => (α i : UnitAddCircle)) =
      ((∑ i, (k i : ℝ) * α i : ℝ) : UnitAddCircle) := by
  classical
  let Q : ℝ →+ UnitAddCircle :=
    QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℝ))
  change (∑ i, k i • Q (α i)) = Q (∑ i, (k i : ℝ) * α i)
  calc
    (∑ i, k i • Q (α i)) = ∑ i, Q (k i • α i) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact (map_zsmul Q (k i) (α i)).symm
    _ = Q (∑ i, k i • α i) := (map_sum Q (fun i => k i • α i) Finset.univ).symm
    _ = Q (∑ i, (k i : ℝ) * α i) := by
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      simp [zsmul_eq_mul]

/-- Under the canonical phase hypothesis, every point of a finite-dimensional
integer rotation orbit is approximable by distinct subset sums from every
tail. -/
theorem torus_orbit_tail_approximation (A : Set ℕ)
    (hphase : ∀ θ : ℝ, θ ∈ Set.Ioo 0 1 →
      Filter.Tendsto (phasePartialSum A θ)
        (Filter.atTop : Filter ℕ) Filter.atTop)
    (α : d → ℝ) (m N : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ s : Finset ℕ,
      (∀ n ∈ s, n ∈ A ∧ N ≤ n) ∧
      dist (∑ n ∈ s, n • (fun i => (α i : UnitAddCircle)))
        (m • (fun i => (α i : UnitAddCircle))) < ε := by
  classical
  let a : UnitAddTorus d := fun i => (α i : UnitAddCircle)
  let seq : ℕ → UnitAddTorus d := fun n => n • a
  let S := tailLimit A seq
  have hSclosed : IsClosed S := tailLimit_isClosed A seq
  have hSzero : (0 : UnitAddTorus d) ∈ S := zero_mem_tailLimit A seq
  have hSadd : ∀ u ∈ S, ∀ v ∈ S, u + v ∈ S := by
    intro u hu v hv
    exact tailLimit_add_mem A seq hu hv
  obtain ⟨H, hH⟩ := compact_add_subsemigroup_is_addSubgroup S
    ⟨0, hSzero⟩ hSclosed hSadd
  let target : UnitAddTorus d := m • a
  have htarget : target ∈ H := by
    by_contra htH
    obtain ⟨k, hkH, hkt⟩ := exists_character_separating_point H
      (by rw [hH]; exact hSclosed) htH
    let C := torusChar k
    let φ : ℝ := ∑ i, (k i : ℝ) * α i
    have hCa : C a = (φ : UnitAddCircle) := torusChar_phase k α
    have hCt : C target = m • (φ : UnitAddCircle) := by
      change C (m • a) = _
      rw [map_nsmul, hCa]
    have hCH : ∀ y ∈ H, C y = 0 := by
      intro y hy
      have hfour := hkH y hy
      rw [mFourier_eq_torusChar_toCircle] at hfour
      apply AddCircle.injective_toCircle one_ne_zero
      apply Subtype.ext
      simpa using hfour
    have hCt0 : C target ≠ 0 := by
      intro hzero
      apply hkt
      rw [mFourier_eq_torusChar_toCircle, hzero]
      simp
    have hImageClosure : ∀ K : ℕ,
        C target ∈ closure (C '' tailSubsetSums A seq K) := by
      intro K
      rw [Metric.mem_closure_iff]
      intro δ hδ
      obtain ⟨s, hs, hdist⟩ := scalar_orbit_tail_approximation
        A hphase φ m K δ hδ
      let g : UnitAddTorus d := ∑ n ∈ s, seq n
      have hg : g ∈ tailSubsetSums A seq K := ⟨s, hs, rfl⟩
      refine ⟨C g, ⟨g, hg, rfl⟩, ?_⟩
      have hCg : C g = ∑ n ∈ s, ((φ * (n : ℝ) : ℝ) : UnitAddCircle) := by
        change C (∑ n ∈ s, n • a) = _
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro n hn
        rw [map_nsmul, hCa]
        rw [← AddCircle.coe_nsmul]
        congr 1
        simp [nsmul_eq_mul, mul_comm]
      rw [hCg, hCt]
      simpa only [dist_comm] using hdist
    let E : Set (UnitAddTorus d) := {y | C y = C target}
    have hE : IsClosed E := isClosed_eq C.continuous_toFun continuous_const
    let Kset : ℕ → Set (UnitAddTorus d) := fun K =>
      closure (tailSubsetSums A seq K) ∩ E
    have hKn : ∀ K, (Kset K).Nonempty := by
      intro K
      have himg := hImageClosure K
      have hcompact : IsCompact (closure (tailSubsetSums A seq K)) :=
        isClosed_closure.isCompact
      have hclosedImage : IsClosed (C '' closure (tailSubsetSums A seq K)) :=
        (hcompact.image C.continuous_toFun).isClosed
      have hsub : closure (C '' tailSubsetSums A seq K) ⊆
          C '' closure (tailSubsetSums A seq K) := by
        apply closure_minimal
        · exact Set.image_mono subset_closure
        · exact hclosedImage
      obtain ⟨y, hy, hyC⟩ := hsub himg
      exact ⟨y, hy, hyC⟩
    have hKclosed : ∀ K, IsClosed (Kset K) := fun K => isClosed_closure.inter hE
    have hKcompact : ∀ K, IsCompact (Kset K) := fun K => (hKclosed K).isCompact
    have hKdir : Directed (fun X Y : Set (UnitAddTorus d) => X ⊇ Y) Kset := by
      intro K L
      refine ⟨max K L, ?_, ?_⟩
      · intro y hy
        exact ⟨closure_mono (tailSubsetSums_mono_cutoff A seq (le_max_left K L)) hy.1,
          hy.2⟩
      · intro y hy
        exact ⟨closure_mono (tailSubsetSums_mono_cutoff A seq (le_max_right K L)) hy.1,
          hy.2⟩
    obtain ⟨y, hy⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
      Kset hKdir hKn hKcompact hKclosed
    have hyS : y ∈ S := by
      change y ∈ tailLimit A seq
      rw [tailLimit, Set.mem_iInter]
      intro K
      exact (Set.mem_iInter.mp hy K).1
    have hyH : y ∈ H := by
      change y ∈ (H : Set (UnitAddTorus d))
      rw [hH]
      exact hyS
    have hyE : C y = C target := (Set.mem_iInter.mp hy 0).2
    exact hCt0 (hyE ▸ hCH y hyH)
  have htS : target ∈ S := by
    have ht : target ∈ (H : Set (UnitAddTorus d)) := htarget
    rw [hH] at ht
    exact ht
  have htN : target ∈ closure (tailSubsetSums A seq N) := by
    change target ∈ tailLimit A seq at htS
    rw [tailLimit, Set.mem_iInter] at htS
    exact htS N
  rw [Metric.mem_closure_iff] at htN
  obtain ⟨g, ⟨s, hs, hsg⟩, hdist⟩ := htN ε hε
  refine ⟨s, hs, ?_⟩
  change dist (∑ n ∈ s, seq n) target < ε
  rw [hsg]
  simpa only [dist_comm] using hdist

end

end Erdos254.TorusOrbit
