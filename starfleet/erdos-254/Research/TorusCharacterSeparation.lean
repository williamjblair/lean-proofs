import Mathlib.Analysis.Fourier.AddCircleMulti
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
import Mathlib.Topology.MetricSpace.HausdorffDistance

namespace Erdos254.TorusCharacterSeparation

open scoped Topology ComplexConjugate ENNReal
open Set MeasureTheory Algebra Submodule

noncomputable section

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

variable {d : Type*} [Fintype d]

lemma mFourier_add_point (k : d → ℤ) (x y : UnitAddTorus d) :
    UnitAddTorus.mFourier k (x + y) =
      UnitAddTorus.mFourier k x * UnitAddTorus.mFourier k y := by
  simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, Pi.add_apply]
  calc
    (∏ i, fourier (k i) (x i + y i)) =
        ∏ i, (fourier (k i) (x i) * fourier (k i) (y i)) := by
      apply Finset.prod_congr rfl
      intro i hi
      rw [fourier_apply, fourier_apply, fourier_apply, zsmul_add,
        AddCircle.toCircle_add]
      rfl
    _ = (∏ i, fourier (k i) (x i)) * ∏ i, fourier (k i) (y i) :=
      Finset.prod_mul_distrib

lemma integral_mFourier_subgroup_eq_zero (H : AddSubgroup (UnitAddTorus d))
    (μ : Measure H) [μ.IsAddLeftInvariant]
    (k : d → ℤ)
    (hk : ∃ a : H, UnitAddTorus.mFourier k a.1 ≠ 1) :
    ∫ h : H, UnitAddTorus.mFourier k h.1 ∂μ = 0 := by
  obtain ⟨a, ha⟩ := hk
  have htrans := integral_add_left_eq_self
    (μ := μ) (fun h : H => UnitAddTorus.mFourier k h.1) a
  have heq : UnitAddTorus.mFourier k a.1 *
      (∫ h : H, UnitAddTorus.mFourier k h.1 ∂μ) =
      ∫ h : H, UnitAddTorus.mFourier k h.1 ∂μ := by
    calc
      UnitAddTorus.mFourier k a.1 *
          (∫ h : H, UnitAddTorus.mFourier k h.1 ∂μ) =
          ∫ h : H, UnitAddTorus.mFourier k a.1 *
            UnitAddTorus.mFourier k h.1 ∂μ := by rw [integral_const_mul]
      _ = ∫ h : H, UnitAddTorus.mFourier k (a + h).1 ∂μ := by
        apply integral_congr_ae
        filter_upwards [] with h
        exact (mFourier_add_point k a.1 h.1).symm
      _ = ∫ h : H, UnitAddTorus.mFourier k h.1 ∂μ := htrans
  have hmul : (UnitAddTorus.mFourier k a.1 - 1) *
      (∫ h : H, UnitAddTorus.mFourier k h.1 ∂μ) = 0 := by
    calc
      _ = UnitAddTorus.mFourier k a.1 *
          (∫ h : H, UnitAddTorus.mFourier k h.1 ∂μ) -
          ∫ h : H, UnitAddTorus.mFourier k h.1 ∂μ := by ring
      _ = 0 := by rw [heq, sub_self]
  exact (mul_eq_zero.mp hmul).resolve_left (sub_ne_zero.mpr ha)

lemma integral_mFourier_univ_eq_zero (k : d → ℤ) (hk : k ≠ 0) :
    ∫ x : UnitAddTorus d, UnitAddTorus.mFourier k x = 0 := by
  have ho := (orthonormal_iff_ite.mp UnitAddTorus.orthonormal_mFourier)
    (0 : d → ℤ) k
  rw [if_neg hk.symm] at ho
  simpa only [ContinuousMap.inner_toLp, UnitAddTorus.mFourier_zero,
    ContinuousMap.one_apply, RCLike.star_def, map_one, one_mul, mul_one,
    UnitAddTorus.coeFn_mFourierLp] using ho

/-- Integer Fourier characters separate proper closed subgroups of a finite
unit additive torus. -/
theorem eq_top_of_no_nonzero_annihilator (H : AddSubgroup (UnitAddTorus d))
    (hHclosed : IsClosed (H : Set (UnitAddTorus d)))
    (hann : ∀ k : d → ℤ,
      (∀ h ∈ H, UnitAddTorus.mFourier k h = 1) → k = 0) :
    H = ⊤ := by
  classical
  by_contra hHtop
  letI : IsClosed (H : Set (UnitAddTorus d)) := hHclosed
  letI : CompactSpace H := isCompact_iff_compactSpace.mp hHclosed.isCompact
  let μ : Measure H := Measure.addHaar
  letI : μ.IsAddLeftInvariant := inferInstance
  letI : IsFiniteMeasure μ := inferInstance
  letI : NeZero μ := inferInstance
  let M : ℝ := μ.real Set.univ
  have hM : 0 < M := measureReal_univ_pos
  have hIntH (k : d → ℤ) :
      (∫ h : H, UnitAddTorus.mFourier k h.1 ∂μ) =
        if k = 0 then (M : ℂ) else 0 := by
    by_cases hk : k = 0
    · subst k
      simp only [UnitAddTorus.mFourier_zero, ContinuousMap.one_apply, if_pos]
      rw [integral_const]
      simp [M]
    · rw [if_neg hk]
      apply integral_mFourier_subgroup_eq_zero H μ k
      by_contra hnone
      have hall : ∀ h ∈ H, UnitAddTorus.mFourier k h = 1 := by
        intro h hh
        have : ¬ UnitAddTorus.mFourier k h ≠ 1 := by
          intro hne
          exact hnone ⟨⟨h, hh⟩, hne⟩
        exact not_ne_iff.mp this
      exact hk (hann k hall)
  have hIntT (k : d → ℤ) :
      (∫ x : UnitAddTorus d, UnitAddTorus.mFourier k x) =
        if k = 0 then 1 else 0 := by
    by_cases hk : k = 0
    · subst k
      simp [UnitAddTorus.mFourier_zero]
    · rw [if_neg hk]
      exact integral_mFourier_univ_eq_zero k hk
  have hIntegrableH (f : C(UnitAddTorus d, ℂ)) :
      Integrable (fun h : H => f h.1) μ := by
    refine Integrable.of_bound
      (f.continuous.comp continuous_subtype_val).aestronglyMeasurable ‖f‖ ?_
    filter_upwards [] with h
    exact f.norm_coe_le_norm h.1
  have hIntegrableT (f : C(UnitAddTorus d, ℂ)) :
      Integrable f := by
    refine Integrable.of_bound f.continuous.aestronglyMeasurable ‖f‖ ?_
    filter_upwards [] with x
    exact f.norm_coe_le_norm x
  let P : C(UnitAddTorus d, ℂ) → Prop := fun f =>
    (∫ h : H, f h.1 ∂μ) = (M : ℂ) * ∫ x : UnitAddTorus d, f x
  have hspan : ∀ f ∈ span ℂ (Set.range UnitAddTorus.mFourier), P f := by
    intro f hf
    induction hf using Submodule.span_induction with
    | mem f hf =>
        obtain ⟨k, rfl⟩ := hf
        dsimp [P]
        rw [hIntH, hIntT]
        split_ifs <;> simp
    | zero => simp [P]
    | add f g hf hg hPf hPg =>
        dsimp [P] at hPf hPg ⊢
        rw [integral_add (hIntegrableH f) (hIntegrableH g),
          integral_add (hIntegrableT f) (hIntegrableT g), hPf, hPg]
        ring
    | smul c f hf hPf =>
        dsimp [P] at hPf ⊢
        rw [integral_const_mul, integral_const_mul, hPf]
        ring
  have hHne : (H : Set (UnitAddTorus d)) ≠ Set.univ := by
    intro hset
    apply hHtop
    exact SetLike.coe_injective hset
  have hcomp : ((H : Set (UnitAddTorus d))ᶜ).Nonempty :=
    Set.nonempty_compl.mpr hHne
  let gr : C(UnitAddTorus d, ℝ) :=
    ⟨fun x => Metric.infDist x (H : Set (UnitAddTorus d)),
      Metric.continuous_infDist_pt _⟩
  have hgrInt : Integrable gr := by
    refine Integrable.of_bound gr.continuous.aestronglyMeasurable ‖gr‖ ?_
    filter_upwards [] with x
    exact gr.norm_coe_le_norm x
  have hsupp : Function.support gr = (H : Set (UnitAddTorus d))ᶜ := by
    ext x
    rw [Function.mem_support, Set.mem_compl_iff]
    change Metric.infDist x (H : Set (UnitAddTorus d)) ≠ 0 ↔ x ∉ H
    exact not_congr (hHclosed.mem_iff_infDist_zero ⟨0, H.zero_mem⟩).symm
  let c : ℝ := ∫ x : UnitAddTorus d, gr x
  have hc : 0 < c := by
    dsimp [c, gr]
    rw [integral_pos_iff_support_of_nonneg (fun x => Metric.infDist_nonneg)
      hgrInt]
    have hsupp' : Function.support (fun x : UnitAddTorus d =>
        Metric.infDist x (H : Set (UnitAddTorus d))) =
        (H : Set (UnitAddTorus d))ᶜ := by
      ext x
      rw [Function.mem_support, Set.mem_compl_iff]
      exact not_congr (hHclosed.mem_iff_infDist_zero ⟨0, H.zero_mem⟩).symm
    rw [hsupp']
    exact (hHclosed.isOpen_compl.measure_pos volume hcomp)
  let fc : C(UnitAddTorus d, ℂ) :=
    ⟨fun x => (gr x : ℂ), Complex.continuous_ofReal.comp gr.continuous⟩
  have hfcInt : Integrable fc := hIntegrableT fc
  have hfcIntegral : (∫ x : UnitAddTorus d, fc x) = (c : ℂ) := by
    have hmap := Complex.ofRealCLM.integral_comp_comm hgrInt
    exact hmap
  have hfcl : fc ∈ closure
      ((span ℂ (Set.range UnitAddTorus.mFourier) :
        Submodule ℂ C(UnitAddTorus d, ℂ)) : Set C(UnitAddTorus d, ℂ)) := by
    change fc ∈ (span ℂ (Set.range UnitAddTorus.mFourier)).topologicalClosure
    rw [UnitAddTorus.span_mFourier_closure_eq_top]
    exact Submodule.mem_top
  rw [Metric.mem_closure_iff] at hfcl
  obtain ⟨p, hpSpan, hdist⟩ := hfcl (c / 4) (by positivity)
  have hpEq := hspan p hpSpan
  have hpoint : ∀ x, ‖p x - fc x‖ < c / 4 := by
    intro x
    exact (ContinuousMap.norm_coe_le_norm (p - fc) x).trans_lt
      (by simpa [dist_eq_norm, norm_sub_rev] using hdist)
  have hfcH : ∀ h : H, fc h.1 = 0 := by
    intro h
    change (Metric.infDist h.1 (H : Set (UnitAddTorus d)) : ℂ) = 0
    rw [Metric.infDist_zero_of_mem h.2]
    norm_num
  have hboundH : ‖∫ h : H, p h.1 ∂μ‖ ≤ (c / 4) * M := by
    apply (norm_integral_le_of_norm_le_const (μ := μ))
    filter_upwards [] with h
    have := (hpoint h.1).le
    simpa [hfcH h] using this
  have hboundT : ‖(∫ x : UnitAddTorus d, p x) - (c : ℂ)‖ ≤ c / 4 := by
    rw [← hfcIntegral, ← integral_sub (hIntegrableT p) hfcInt]
    have hb := norm_integral_le_of_norm_le_const
      (μ := (volume : Measure (UnitAddTorus d)))
      (Filter.Eventually.of_forall fun x => (hpoint x).le)
    simpa using hb
  have hnormP : ‖∫ x : UnitAddTorus d, p x‖ ≤ c / 4 := by
    rw [hpEq, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hM] at hboundH
    have hm : M * ‖∫ x : UnitAddTorus d, p x‖ ≤ M * (c / 4) := by
      simpa [mul_comm] using hboundH
    exact (mul_le_mul_iff_right₀ hM).mp hm
  have hc_le : c ≤ c / 2 := by
    have htri := norm_le_norm_add_norm_sub
      (∫ x : UnitAddTorus d, p x) (c : ℂ)
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc] at htri
    linarith [hboundT, hnormP]
  linarith

/-- A point outside a closed torus subgroup is separated from it by an integer
Fourier character. -/
theorem exists_character_separating_point (H : AddSubgroup (UnitAddTorus d))
    (hHclosed : IsClosed (H : Set (UnitAddTorus d)))
    {x : UnitAddTorus d} (hx : x ∉ H) :
    ∃ k : d → ℤ,
      (∀ h ∈ H, UnitAddTorus.mFourier k h = 1) ∧
      UnitAddTorus.mFourier k x ≠ 1 := by
  classical
  by_contra hnone
  have hforce : ∀ k : d → ℤ,
      (∀ h ∈ H, UnitAddTorus.mFourier k h = 1) →
      UnitAddTorus.mFourier k x = 1 := by
    intro k hk
    by_contra hkx
    exact hnone ⟨k, hk, hkx⟩
  letI : IsClosed (H : Set (UnitAddTorus d)) := hHclosed
  letI : CompactSpace H := isCompact_iff_compactSpace.mp hHclosed.isCompact
  let μ : Measure H := Measure.addHaar
  letI : μ.IsAddLeftInvariant := inferInstance
  letI : IsFiniteMeasure μ := inferInstance
  letI : NeZero μ := inferInstance
  let M : ℝ := μ.real Set.univ
  have hM : 0 < M := measureReal_univ_pos
  have hcharShift (k : d → ℤ) :
      (∫ h : H, UnitAddTorus.mFourier k (x + h.1) ∂μ) =
      UnitAddTorus.mFourier k x *
        ∫ h : H, UnitAddTorus.mFourier k h.1 ∂μ := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with h
    exact mFourier_add_point k x h.1
  have hcharEq (k : d → ℤ) :
      (∫ h : H, UnitAddTorus.mFourier k h.1 ∂μ) =
      ∫ h : H, UnitAddTorus.mFourier k (x + h.1) ∂μ := by
    by_cases htriv : ∀ h ∈ H, UnitAddTorus.mFourier k h = 1
    · have hkx := hforce k htriv
      rw [hcharShift, hkx, one_mul]
    · have hex : ∃ a : H, UnitAddTorus.mFourier k a.1 ≠ 1 := by
        push Not at htriv
        obtain ⟨a, haH, ha⟩ := htriv
        exact ⟨⟨a, haH⟩, ha⟩
      have hz := integral_mFourier_subgroup_eq_zero H μ k hex
      rw [hcharShift, hz, mul_zero]
  have hIntegrable0 (f : C(UnitAddTorus d, ℂ)) :
      Integrable (fun h : H => f h.1) μ := by
    refine Integrable.of_bound
      (f.continuous.comp continuous_subtype_val).aestronglyMeasurable ‖f‖ ?_
    filter_upwards [] with h
    exact f.norm_coe_le_norm h.1
  have hIntegrableX (f : C(UnitAddTorus d, ℂ)) :
      Integrable (fun h : H => f (x + h.1)) μ := by
    refine Integrable.of_bound
      (f.continuous.comp (continuous_const.add continuous_subtype_val)).aestronglyMeasurable
      ‖f‖ ?_
    filter_upwards [] with h
    exact f.norm_coe_le_norm (x + h.1)
  let P : C(UnitAddTorus d, ℂ) → Prop := fun f =>
    (∫ h : H, f h.1 ∂μ) = ∫ h : H, f (x + h.1) ∂μ
  have hspan : ∀ f ∈ span ℂ (Set.range UnitAddTorus.mFourier), P f := by
    intro f hf
    induction hf using Submodule.span_induction with
    | mem f hf =>
        obtain ⟨k, rfl⟩ := hf
        exact hcharEq k
    | zero => simp [P]
    | add f g hf hg hPf hPg =>
        dsimp [P] at hPf hPg ⊢
        rw [integral_add (hIntegrable0 f) (hIntegrable0 g),
          integral_add (hIntegrableX f) (hIntegrableX g), hPf, hPg]
    | smul c f hf hPf =>
        dsimp [P] at hPf ⊢
        rw [integral_const_mul, integral_const_mul, hPf]
  let gr : C(UnitAddTorus d, ℝ) :=
    ⟨fun y => Metric.infDist y (H : Set (UnitAddTorus d)),
      Metric.continuous_infDist_pt _⟩
  have hgr0 : ∀ h : H, gr h.1 = 0 := fun h => Metric.infDist_zero_of_mem h.2
  have hnotmem : ∀ h : H, x + h.1 ∉ H := by
    intro h hxh
    apply hx
    have := H.sub_mem hxh h.2
    simpa using this
  have hgrXpos : ∀ h : H, 0 < gr (x + h.1) := by
    intro h
    change 0 < Metric.infDist (x + h.1) (H : Set (UnitAddTorus d))
    exact (hHclosed.notMem_iff_infDist_pos ⟨0, H.zero_mem⟩).mp (hnotmem h)
  have hgrXInt : Integrable (fun h : H => gr (x + h.1)) μ := by
    refine Integrable.of_bound
      (gr.continuous.comp (continuous_const.add continuous_subtype_val)).aestronglyMeasurable
      ‖gr‖ ?_
    filter_upwards [] with h
    exact gr.norm_coe_le_norm (x + h.1)
  let c : ℝ := ∫ h : H, gr (x + h.1) ∂μ
  have hc : 0 < c := by
    dsimp [c]
    rw [integral_pos_iff_support_of_nonneg (fun h => (hgrXpos h).le) hgrXInt]
    have hsupp : Function.support (fun h : H => gr (x + h.1)) = Set.univ := by
      ext h
      simp only [Function.mem_support, Set.mem_univ, iff_true]
      exact (hgrXpos h).ne'
    rw [hsupp]
    exact Measure.measure_univ_pos.mpr (NeZero.ne μ)
  let fc : C(UnitAddTorus d, ℂ) :=
    ⟨fun y => (gr y : ℂ), Complex.continuous_ofReal.comp gr.continuous⟩
  have hfcl : fc ∈ closure
      ((span ℂ (Set.range UnitAddTorus.mFourier) :
        Submodule ℂ C(UnitAddTorus d, ℂ)) : Set C(UnitAddTorus d, ℂ)) := by
    change fc ∈ (span ℂ (Set.range UnitAddTorus.mFourier)).topologicalClosure
    rw [UnitAddTorus.span_mFourier_closure_eq_top]
    exact Submodule.mem_top
  rw [Metric.mem_closure_iff] at hfcl
  obtain ⟨p, hpSpan, hdist⟩ := hfcl (c / (4 * M)) (by positivity)
  have hpEq := hspan p hpSpan
  have hpoint : ∀ y, ‖p y - fc y‖ < c / (4 * M) := by
    intro y
    exact (ContinuousMap.norm_coe_le_norm (p - fc) y).trans_lt
      (by simpa [dist_eq_norm, norm_sub_rev] using hdist)
  have hbound0 : ‖∫ h : H, p h.1 ∂μ‖ ≤ c / 4 := by
    have hb := norm_integral_le_of_norm_le_const (μ := μ)
      (Filter.Eventually.of_forall fun h : H => (hpoint h.1).le)
    have hzero : (∫ h : H, fc h.1 ∂μ) = 0 := by
      apply integral_eq_zero_of_ae
      filter_upwards [] with h
      change (gr h.1 : ℂ) = 0
      rw [hgr0 h]
      norm_num
    calc
      ‖∫ h : H, p h.1 ∂μ‖ =
          ‖(∫ h : H, p h.1 ∂μ) - ∫ h : H, fc h.1 ∂μ‖ := by rw [hzero, sub_zero]
      _ = ‖∫ h : H, p h.1 - fc h.1 ∂μ‖ := by
        rw [integral_sub (hIntegrable0 p) (hIntegrable0 fc)]
      _ ≤ (c / (4 * M)) * M := hb
      _ = c / 4 := by field_simp
  have hfcXIntegral : (∫ h : H, fc (x + h.1) ∂μ) = (c : ℂ) := by
    have hmap := Complex.ofRealCLM.integral_comp_comm hgrXInt
    exact hmap
  have hboundX : ‖(∫ h : H, p (x + h.1) ∂μ) - (c : ℂ)‖ ≤ c / 4 := by
    rw [← hfcXIntegral, ← integral_sub (hIntegrableX p) (hIntegrableX fc)]
    have hb := norm_integral_le_of_norm_le_const (μ := μ)
      (Filter.Eventually.of_forall fun h : H => (hpoint (x + h.1)).le)
    calc
      ‖∫ h : H, p (x + h.1) - fc (x + h.1) ∂μ‖ ≤
          (c / (4 * M)) * M := hb
      _ = c / 4 := by field_simp
  have hc_le : c ≤ c / 2 := by
    have htri := norm_le_norm_add_norm_sub
      (∫ h : H, p h.1 ∂μ) (c : ℂ)
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc, hpEq] at htri
    have hbound0' : ‖∫ h : H, p (x + h.1) ∂μ‖ ≤ c / 4 := by
      rw [← hpEq]
      exact hbound0
    linarith [hbound0', hboundX]
  linarith

end

end Erdos254.TorusCharacterSeparation
