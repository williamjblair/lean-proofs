import Research.GlobalShellSix
import Research.ShellCounterexample38

/-!
# Strict shell-threshold readings of the corrupted Erdős #662

This file treats the strict `d < t_n` wording left open by the source audit.
For the corrected cumulative triangular comparison, a rational oblique lattice
beats the closed triangular count at the genuine shell `t = sqrt 300`.  For
the printed value `f(3)=18`, the exact 38-point packing already beats the
corresponding global normalized strict bound, and its replicated centers beat
both 18 and the corrected local value 36.
-/

namespace Research

set_option maxRecDepth 200000

local instance strictProdLexLinearOrder {α β : Type*} [LinearOrder α]
    [LinearOrder β] : LinearOrder (α × β) :=
  Prod.Lex.instLinearOrder α β

/-- An executable integer window from `-24` through `24`. -/
def intWindow24 : Finset ℤ :=
  (Finset.range 49).image fun k : ℕ => (k : ℤ) - 24

lemma mem_intWindow24_iff (z : ℤ) :
    z ∈ intWindow24 ↔ -24 ≤ z ∧ z ≤ 24 := by
  constructor
  · intro hz
    rw [intWindow24, Finset.mem_image] at hz
    rcases hz with ⟨k, hk, rfl⟩
    have hk' := Finset.mem_range.mp hk
    constructor <;> omega
  · rintro ⟨hl, hu⟩
    let k : ℕ := (z + 24).toNat
    have hz0 : 0 ≤ z + 24 := by omega
    have hkcast : (k : ℤ) = z + 24 := by
      exact Int.toNat_of_nonneg hz0
    apply Finset.mem_image.mpr
    refine ⟨k, Finset.mem_range.mpr ?_, ?_⟩
    · have hkZ : (k : ℤ) < 49 := by omega
      exact_mod_cast hkZ
    · exact_mod_cast (show (k : ℤ) - 24 = z by omega)

/-- Numerator (denominator 565) for the strict-shell oblique lattice generated
by `(1,0)` and `(276/565,493/565)`. -/
def strictObliqueNormNum (d : ℤ × ℤ) : ℤ :=
  565 * d.1 ^ 2 + 565 * d.2 ^ 2 + 552 * d.1 * d.2

/-- Nonzero oblique offsets strictly below squared radius 300. -/
def strictThreeHundredOffsets : Finset (ℤ × ℤ) :=
  (intWindow24.product intWindow24).filter fun d =>
    d ≠ (0, 0) ∧ strictObliqueNormNum d < 300 * 565

/-- There are 1078 strict oblique offsets. -/
theorem strictThreeHundredOffsets_card :
    strictThreeHundredOffsets.card = 1078 := by
  decide

/-- Exact boundary count for the first winning square patch. -/
theorem strictThreeHundredOffsets_weighted_sum :
    ∑ d ∈ strictThreeHundredOffsets,
      (4535 - d.1.natAbs) * (4535 - d.2.natAbs) = 22088128946 := by
  decide

/-- Independent boundary statistics. -/
theorem strictThreeHundredOffsets_boundary_sums :
    (∑ d ∈ strictThreeHundredOffsets,
      (d.1.natAbs + d.2.natAbs)) = 18156 ∧
    (∑ d ∈ strictThreeHundredOffsets,
      d.1.natAbs * d.2.natAbs) = 75856 := by
  decide

lemma strictObliqueNormNum_decomposition (m n : ℤ) :
    strictObliqueNormNum (m, n) =
      276 * (m + n) ^ 2 + 289 * m ^ 2 + 289 * n ^ 2 := by
  simp only [strictObliqueNormNum]
  ring

private lemma strict_int_sq_ge_one {z : ℤ} (hz : z ≠ 0) : 1 ≤ z ^ 2 := by
  have hp : 0 < z ^ 2 := sq_pos_of_ne_zero hz
  omega

/-- The new oblique lattice is globally one-separated. -/
theorem strictObliqueNormNum_ge_denominator (m n : ℤ)
    (hne : (m, n) ≠ (0, 0)) :
    565 ≤ strictObliqueNormNum (m, n) := by
  rw [strictObliqueNormNum_decomposition]
  by_cases hs : m + n = 0
  · have hm : m ≠ 0 := by
      intro hm
      apply hne
      apply Prod.ext
      · exact hm
      · simpa [hm] using hs
    have hn : n ≠ 0 := by
      intro hn
      apply hne
      apply Prod.ext
      · simpa [hn] using hs
      · exact hn
    have hm2 := strict_int_sq_ge_one hm
    have hn2 := strict_int_sq_ge_one hn
    rw [hs]
    norm_num
    omega
  · have hs2 := strict_int_sq_ge_one hs
    have hmn : 1 ≤ m ^ 2 + n ^ 2 := by
      by_cases hm : m = 0
      · subst m
        simpa using strict_int_sq_ge_one (by
          intro hn
          exact hne (Prod.ext rfl hn))
      · have hm2 := strict_int_sq_ge_one hm
        nlinarith [sq_nonneg n]
    nlinarith [sq_nonneg m, sq_nonneg n]

/-- Every strict radius-`sqrt 300` offset lies in `[-24,24]²`. -/
theorem strictOblique_norm_lt_threeHundred_bounds (m n : ℤ)
    (h : strictObliqueNormNum (m, n) < 300 * 565) :
    -24 ≤ m ∧ m ≤ 24 ∧ -24 ≤ n ∧ n ≤ 24 := by
  have hd := strictObliqueNormNum_decomposition m n
  have hsum : 0 ≤ (m + n) ^ 2 := sq_nonneg (m + n)
  have hm0 : 0 ≤ m ^ 2 := sq_nonneg m
  have hn0 : 0 ≤ n ^ 2 := sq_nonneg n
  constructor
  · by_contra hm
    have : m ≤ -25 := by omega
    nlinarith [sq_nonneg (m + 25)]
  constructor
  · by_contra hm
    have : 25 ≤ m := by omega
    nlinarith [sq_nonneg (m - 25)]
  constructor
  · by_contra hn
    have : n ≤ -25 := by omega
    nlinarith [sq_nonneg (n + 25)]
  · by_contra hn
    have : 25 ≤ n := by omega
    nlinarith [sq_nonneg (n - 25)]

/-- Completeness of the executable strict-offset census. -/
theorem mem_strictThreeHundredOffsets_iff (d : ℤ × ℤ) :
    d ∈ strictThreeHundredOffsets ↔
      d ≠ (0, 0) ∧ strictObliqueNormNum d < 300 * 565 := by
  rcases d with ⟨m, n⟩
  constructor
  · exact fun h => (Finset.mem_filter.mp h).2
  · intro h
    have hb := strictOblique_norm_lt_threeHundred_bounds m n h.2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr ⟨?_, ?_⟩, h⟩
    · exact (mem_intWindow24_iff m).2 ⟨hb.1, hb.2.1⟩
    · exact (mem_intWindow24_iff n).2 ⟨hb.2.2.1, hb.2.2.2⟩

/-- Complete corrected triangular cumulative census at squared radius 300. -/
def triCoordsWithinThreeHundred : Finset (ℤ × ℤ) :=
  ((intWindow24.product intWindow24).filter
    (fun d => triNormSq d ≤ 300)).erase (0, 0)

/-- Squared norm 300 is a genuine triangular-lattice shell (`t=10√3`). -/
theorem threeHundred_is_triangular_shell : triNormSq (10, 10) = 300 := by
  norm_num [triNormSq]

/-- The corrected closed triangular comparison value is 1074. -/
theorem triCoordsWithinThreeHundred_card :
    triCoordsWithinThreeHundred.card = 1074 := by
  decide

/-- The triangular count strictly below the same shell is 1068. -/
def triCoordsStrictThreeHundred : Finset (ℤ × ℤ) :=
  ((intWindow24.product intWindow24).filter
    (fun d => triNormSq d < 300)).erase (0, 0)

theorem triCoordsStrictThreeHundred_card :
    triCoordsStrictThreeHundred.card = 1068 := by
  decide

/-- Completeness bound for the triangular radius-`sqrt 300` census. -/
theorem tri_norm_le_threeHundred_bounds (m n : ℤ)
    (h : triNormSq (m, n) ≤ 300) :
    -20 ≤ m ∧ m ≤ 20 ∧ -20 ≤ n ∧ n ≤ 20 := by
  have hm2 : 3 * m ^ 2 ≤ 1200 := by
    simp only [triNormSq] at h
    nlinarith [sq_nonneg (m + 2 * n)]
  have hn2 : 3 * n ^ 2 ≤ 1200 := by
    simp only [triNormSq] at h
    nlinarith [sq_nonneg (2 * m + n)]
  constructor
  · by_contra hm
    have : m ≤ -21 := by omega
    nlinarith [sq_nonneg (m + 21)]
  constructor
  · by_contra hm
    have : 21 ≤ m := by omega
    nlinarith [sq_nonneg (m - 21)]
  constructor
  · by_contra hn
    have : n ≤ -21 := by omega
    nlinarith [sq_nonneg (n + 21)]
  · by_contra hn
    have : 21 ≤ n := by omega
    nlinarith [sq_nonneg (n - 21)]

/-- The corrected 1074 count is a global census, not a window artifact. -/
theorem mem_triCoordsWithinThreeHundred_iff (d : ℤ × ℤ) :
    d ∈ triCoordsWithinThreeHundred ↔
      d ≠ (0, 0) ∧ triNormSq d ≤ 300 := by
  rcases d with ⟨m, n⟩
  constructor
  · intro h
    have he := Finset.mem_erase.mp h
    exact ⟨he.1, (Finset.mem_filter.mp he.2).2⟩
  · intro h
    have hb := tri_norm_le_threeHundred_bounds m n h.2
    apply Finset.mem_erase.mpr
    refine ⟨h.1, Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨?_, ?_⟩, h.2⟩⟩
    · exact (mem_intWindow24_iff m).2 ⟨by omega, by omega⟩
    · exact (mem_intWindow24_iff n).2 ⟨by omega, by omega⟩

/-- Rational realization of the strict-shell oblique patch. -/
noncomputable def strictObliquePoint (q : Fin 4535 × Fin 4535) : ℝ × ℝ :=
  ((q.1.val : ℝ) + (276 / 565 : ℝ) * (q.2.val : ℝ),
    (493 / 565 : ℝ) * (q.2.val : ℝ))

lemma strictObliquePoint_sqDist_eq (q s : Fin 4535 × Fin 4535) :
    sqDist (strictObliquePoint q) (strictObliquePoint s) =
      (strictObliqueNormNum
        (((s.1.val : ℤ) - (q.1.val : ℤ)),
         ((s.2.val : ℤ) - (q.2.val : ℤ))) : ℝ) / 565 := by
  simp only [sqDist, strictObliquePoint, strictObliqueNormNum,
    Int.cast_add, Int.cast_sub, Int.cast_mul, Int.cast_pow, Int.cast_ofNat]
  norm_num
  ring

/-- The finite strict-shell patch is one-separated. -/
theorem strictObliquePoint_oneSeparated :
    ∀ q s : Fin 4535 × Fin 4535, q ≠ s →
      1 ≤ sqDist (strictObliquePoint q) (strictObliquePoint s) := by
  intro q s hqs
  let d : ℤ × ℤ :=
    ((s.1.val : ℤ) - (q.1.val : ℤ),
      (s.2.val : ℤ) - (q.2.val : ℤ))
  have hdne : d ≠ (0, 0) := by
    intro hd
    have hx : s.1.val = q.1.val := by
      have hh := congrArg Prod.fst hd
      dsimp [d] at hh
      omega
    have hy : s.2.val = q.2.val := by
      have hh := congrArg Prod.snd hd
      dsimp [d] at hh
      omega
    exact hqs (Prod.ext (Fin.ext hx.symm) (Fin.ext hy.symm))
  have hz := strictObliqueNormNum_ge_denominator d.1 d.2 (by
    simpa [d] using hdne)
  have hzR : (565 : ℝ) ≤ (strictObliqueNormNum d : ℝ) := by exact_mod_cast hz
  rw [strictObliquePoint_sqDist_eq]
  change 1 ≤ (strictObliqueNormNum d : ℝ) / 565
  norm_num at hzR ⊢
  linarith

/-- Certified strict-shell offsets. -/
abbrev StrictThreeHundredOffset :=
  {d : ℤ × ℤ // d ∈ strictThreeHundredOffsets}

private lemma strict_natAbs_le_twentyFour_of_bounds
    (z : ℤ) (hl : -24 ≤ z) (hu : z ≤ 24) : z.natAbs ≤ 24 := by
  by_cases hz : 0 ≤ z
  · have hc : (z.natAbs : ℤ) = z := Int.natAbs_of_nonneg hz
    omega
  · have hn : 0 ≤ -z := by omega
    have hc : (z.natAbs : ℤ) = -z := by
      calc
        (z.natAbs : ℤ) = ((-z).natAbs : ℕ) := by rw [Int.natAbs_neg]
        _ = -z := Int.natAbs_of_nonneg hn
    omega

lemma strictThreeHundredOffset_natAbs_le (d : StrictThreeHundredOffset) :
    d.val.1.natAbs ≤ 24 ∧ d.val.2.natAbs ≤ 24 := by
  have hm := (mem_strictThreeHundredOffsets_iff d.val).mp d.property
  have hb := strictOblique_norm_lt_threeHundred_bounds d.val.1 d.val.2 hm.2
  exact ⟨strict_natAbs_le_twentyFour_of_bounds d.val.1 hb.1 hb.2.1,
    strict_natAbs_le_twentyFour_of_bounds d.val.2 hb.2.2.1 hb.2.2.2⟩

/-- Start coordinate for a signed offset in a 4535-point interval. -/
def strictSignedStart (d : ℤ) (hd : d.natAbs ≤ 24)
    (k : Fin (4535 - d.natAbs)) : Fin 4535 :=
  if h : d < 0 then ⟨k.val + d.natAbs, by omega⟩
  else ⟨k.val, by omega⟩

/-- End coordinate for a signed offset in a 4535-point interval. -/
def strictSignedEnd (d : ℤ) (hd : d.natAbs ≤ 24)
    (k : Fin (4535 - d.natAbs)) : Fin 4535 :=
  if h : d < 0 then ⟨k.val, by omega⟩
  else ⟨k.val + d.natAbs, by omega⟩

lemma strictSignedEnd_sub_start (d : ℤ) (hd : d.natAbs ≤ 24)
    (k : Fin (4535 - d.natAbs)) :
    ((strictSignedEnd d hd k).val : ℤ) -
      ((strictSignedStart d hd k).val : ℤ) = d := by
  by_cases h : d < 0
  · have hn : 0 ≤ -d := by omega
    have hc : (d.natAbs : ℤ) = -d := by
      calc
        (d.natAbs : ℤ) = ((-d).natAbs : ℕ) := by rw [Int.natAbs_neg]
        _ = -d := Int.natAbs_of_nonneg hn
    simp [strictSignedEnd, strictSignedStart, h, hc]
  · have hp : 0 ≤ d := by omega
    have hc : (d.natAbs : ℤ) = d := Int.natAbs_of_nonneg hp
    simp [strictSignedEnd, strictSignedStart, h, hc]

lemma strictSignedStart_injective (d : ℤ) (hd : d.natAbs ≤ 24) :
    Function.Injective (strictSignedStart d hd) := by
  intro a b h
  apply Fin.ext
  by_cases hn : d < 0
  · simpa [strictSignedStart, hn] using h
  · simpa [strictSignedStart, hn] using h

/-- All legal directed incidences in the 4535-square patch. -/
abbrev StrictThreeHundredIncidence :=
  Σ d : StrictThreeHundredOffset,
    Fin (4535 - d.val.1.natAbs) × Fin (4535 - d.val.2.natAbs)

def strictIncidenceStart (z : StrictThreeHundredIncidence) :
    Fin 4535 × Fin 4535 :=
  (strictSignedStart z.1.val.1 (strictThreeHundredOffset_natAbs_le z.1).1 z.2.1,
   strictSignedStart z.1.val.2 (strictThreeHundredOffset_natAbs_le z.1).2 z.2.2)

def strictIncidenceEnd (z : StrictThreeHundredIncidence) :
    Fin 4535 × Fin 4535 :=
  (strictSignedEnd z.1.val.1 (strictThreeHundredOffset_natAbs_le z.1).1 z.2.1,
   strictSignedEnd z.1.val.2 (strictThreeHundredOffset_natAbs_le z.1).2 z.2.2)

lemma strictIncidence_difference (z : StrictThreeHundredIncidence) :
    (((strictIncidenceEnd z).1.val : ℤ) -
        ((strictIncidenceStart z).1.val : ℤ),
      ((strictIncidenceEnd z).2.val : ℤ) -
        ((strictIncidenceStart z).2.val : ℤ)) = z.1.val := by
  apply Prod.ext
  · exact strictSignedEnd_sub_start z.1.val.1
      (strictThreeHundredOffset_natAbs_le z.1).1 z.2.1
  · exact strictSignedEnd_sub_start z.1.val.2
      (strictThreeHundredOffset_natAbs_le z.1).2 z.2.2

def strictIncidencePair (z : StrictThreeHundredIncidence) :
    (Fin 4535 × Fin 4535) × (Fin 4535 × Fin 4535) :=
  (strictIncidenceStart z, strictIncidenceEnd z)

lemma strictIncidencePair_injective :
    Function.Injective strictIncidencePair := by
  rintro ⟨d, k⟩ ⟨e, l⟩ hp
  have hsx := congrArg (fun q => q.1.1.val) hp
  have hsy := congrArg (fun q => q.1.2.val) hp
  have hex := congrArg (fun q => q.2.1.val) hp
  have hey := congrArg (fun q => q.2.2.val) hp
  have hdval : d.val = e.val := by
    apply Prod.ext
    · calc
        d.val.1 =
            ((strictIncidenceEnd ⟨d, k⟩).1.val : ℤ) -
              ((strictIncidenceStart ⟨d, k⟩).1.val : ℤ) :=
          (congrArg Prod.fst (strictIncidence_difference ⟨d, k⟩)).symm
        _ = ((strictIncidenceEnd ⟨e, l⟩).1.val : ℤ) -
              ((strictIncidenceStart ⟨e, l⟩).1.val : ℤ) := by
          exact congrArg₂ (fun a b : ℕ => (a : ℤ) - (b : ℤ)) hex hsx
        _ = e.val.1 := congrArg Prod.fst (strictIncidence_difference ⟨e, l⟩)
    · calc
        d.val.2 =
            ((strictIncidenceEnd ⟨d, k⟩).2.val : ℤ) -
              ((strictIncidenceStart ⟨d, k⟩).2.val : ℤ) :=
          (congrArg Prod.snd (strictIncidence_difference ⟨d, k⟩)).symm
        _ = ((strictIncidenceEnd ⟨e, l⟩).2.val : ℤ) -
              ((strictIncidenceStart ⟨e, l⟩).2.val : ℤ) := by
          exact congrArg₂ (fun a b : ℕ => (a : ℤ) - (b : ℤ)) hey hsy
        _ = e.val.2 := congrArg Prod.snd (strictIncidence_difference ⟨e, l⟩)
  have hde : d = e := Subtype.ext hdval
  subst e
  have hstart : strictIncidenceStart ⟨d, k⟩ = strictIncidenceStart ⟨d, l⟩ :=
    congrArg Prod.fst hp
  have hkx : k.1 = l.1 :=
    strictSignedStart_injective d.val.1 (strictThreeHundredOffset_natAbs_le d).1
      (congrArg Prod.fst hstart)
  have hky : k.2 = l.2 :=
    strictSignedStart_injective d.val.2 (strictThreeHundredOffset_natAbs_le d).2
      (congrArg Prod.snd hstart)
  have hkl : k = l := Prod.ext hkx hky
  subst l
  rfl

/-- Exact structural cardinality, reduced to the small offset census. -/
theorem strictThreeHundredIncidence_card :
    Fintype.card StrictThreeHundredIncidence = 22088128946 := by
  rw [Fintype.card_sigma]
  simp only [Fintype.card_prod, Fintype.card_fin]
  calc
    (∑ d : StrictThreeHundredOffset,
      (4535 - d.val.1.natAbs) * (4535 - d.val.2.natAbs)) =
        ∑ d ∈ strictThreeHundredOffsets,
          (4535 - d.1.natAbs) * (4535 - d.2.natAbs) := by
      symm
      exact Finset.sum_subtype strictThreeHundredOffsets (fun _ => Iff.rfl)
        (fun d => (4535 - d.1.natAbs) * (4535 - d.2.natAbs))
    _ = 22088128946 := strictThreeHundredOffsets_weighted_sum

/-- Directed pairs strictly below squared radius 300. -/
noncomputable def strictThreeHundredDirectedPairs {α : Type*} [Fintype α]
    [DecidableEq α] (p : α → ℝ × ℝ) : Finset (α × α) :=
  (Finset.univ.product Finset.univ).filter fun q =>
    q.1 ≠ q.2 ∧ sqDist (p q.1) (p q.2) < 300

def StrictThreeHundredPairType {α : Type*} (p : α → ℝ × ℝ) :=
  {q : α × α // q.1 ≠ q.2 ∧ sqDist (p q.1) (p q.2) < 300}

noncomputable instance StrictThreeHundredPairType.instFintype
    {α : Type*} [Fintype α] (p : α → ℝ × ℝ) :
    Fintype (StrictThreeHundredPairType p) := by
  letI : Finite (StrictThreeHundredPairType p) :=
    Finite.of_injective (fun q : StrictThreeHundredPairType p => q.val)
      Subtype.val_injective
  exact Fintype.ofFinite (StrictThreeHundredPairType p)

lemma mem_strictThreeHundredDirectedPairs_iff {α : Type*} [Fintype α]
    [DecidableEq α] (p : α → ℝ × ℝ) (q : α × α) :
    q ∈ strictThreeHundredDirectedPairs p ↔
      q.1 ≠ q.2 ∧ sqDist (p q.1) (p q.2) < 300 := by
  simp [strictThreeHundredDirectedPairs]

theorem StrictThreeHundredPairType_card_eq {α : Type*} [Fintype α]
    [DecidableEq α] (p : α → ℝ × ℝ) :
    Fintype.card (StrictThreeHundredPairType p) =
      (strictThreeHundredDirectedPairs p).card := by
  classical
  let e : StrictThreeHundredPairType p ≃
      {q // q ∈ strictThreeHundredDirectedPairs p} :=
    Equiv.subtypeEquivRight fun q =>
      (mem_strictThreeHundredDirectedPairs_iff p q).symm
  calc
    Fintype.card (StrictThreeHundredPairType p) =
        Fintype.card {q // q ∈ strictThreeHundredDirectedPairs p} :=
      Fintype.card_congr e
    _ = (strictThreeHundredDirectedPairs p).card :=
      Fintype.card_coe (strictThreeHundredDirectedPairs p)

lemma strictIncidencePair_valid (z : StrictThreeHundredIncidence) :
    let q := strictIncidencePair z
    q.1 ≠ q.2 ∧
      sqDist (strictObliquePoint q.1) (strictObliquePoint q.2) < 300 := by
  have hoff := (mem_strictThreeHundredOffsets_iff z.1.val).mp z.1.property
  change strictIncidenceStart z ≠ strictIncidenceEnd z ∧
    sqDist (strictObliquePoint (strictIncidenceStart z))
      (strictObliquePoint (strictIncidenceEnd z)) < 300
  constructor
  · intro heq
    apply hoff.1
    rw [← strictIncidence_difference z, heq]
    simp
  · rw [strictObliquePoint_sqDist_eq, strictIncidence_difference]
    have hzR : (strictObliqueNormNum z.1.val : ℝ) < (300 * 565 : ℝ) := by
      exact_mod_cast hoff.2
    norm_num at hzR ⊢
    linarith

def strictIncidenceToPair :
    StrictThreeHundredIncidence ↪
      StrictThreeHundredPairType strictObliquePoint where
  toFun z := ⟨strictIncidencePair z, strictIncidencePair_valid z⟩
  inj' := by
    intro z w h
    apply strictIncidencePair_injective
    exact congrArg Subtype.val h

/-- At least 22,088,128,946 directed pairs lie strictly below the shell. -/
theorem strictObliquePatch_directed_card_ge :
    22088128946 ≤ (strictThreeHundredDirectedPairs strictObliquePoint).card := by
  calc
    22088128946 = Fintype.card StrictThreeHundredIncidence :=
      strictThreeHundredIncidence_card.symm
    _ ≤ Fintype.card (StrictThreeHundredPairType strictObliquePoint) :=
      Fintype.card_le_of_embedding strictIncidenceToPair
    _ = (strictThreeHundredDirectedPairs strictObliquePoint).card :=
      StrictThreeHundredPairType_card_eq strictObliquePoint

/-- The finite strict patch exceeds the corrected *closed* triangular
comparison `1074 n` by at least 3296 directed pairs. -/
theorem strictObliquePatch_exceeds_closed_triangular_count :
    1074 * Fintype.card (Fin 4535 × Fin 4535) <
      (strictThreeHundredDirectedPairs strictObliquePoint).card := by
  have h := strictObliquePatch_directed_card_ge
  simp only [Fintype.card_prod, Fintype.card_fin]
  norm_num
  omega

/-- One representative of each unordered strict-shell pair. -/
noncomputable def strictThreeHundredOrderedPairs {α : Type*} [Fintype α]
    [LinearOrder α] (p : α → ℝ × ℝ) : Finset (α × α) :=
  (Finset.univ.product Finset.univ).filter fun q =>
    q.1 < q.2 ∧ sqDist (p q.1) (p q.2) < 300

lemma swap_mem_strictThreeHundredDirected_iff {α : Type*} [Fintype α]
    [DecidableEq α] (p : α → ℝ × ℝ) (q : α × α) :
    q.swap ∈ strictThreeHundredDirectedPairs p ↔
      q ∈ strictThreeHundredDirectedPairs p := by
  rw [mem_strictThreeHundredDirectedPairs_iff,
    mem_strictThreeHundredDirectedPairs_iff]
  rcases q with ⟨a, b⟩
  simp only [Prod.swap_prod_mk, Prod.fst, Prod.snd]
  constructor
  · rintro ⟨hne, hd⟩
    exact ⟨hne.symm, by rwa [sqDist_symm]⟩
  · rintro ⟨hne, hd⟩
    exact ⟨hne.symm, by rwa [sqDist_symm]⟩

/-- Directed strict pairs count each direct unordered pair twice. -/
theorem strictThreeHundredDirected_card_eq_twice_ordered {α : Type*}
    [Fintype α] [DecidableEq α] [LinearOrder α] (p : α → ℝ × ℝ) :
    (strictThreeHundredDirectedPairs p).card =
      2 * (strictThreeHundredOrderedPairs p).card := by
  classical
  let inc := strictThreeHundredDirectedPairs p
  let lower := inc.filter fun q : α × α => q.1 < q.2
  let upper := inc.filter fun q : α × α => q.2 < q.1
  have hlower : lower = strictThreeHundredOrderedPairs p := by
    ext q
    simp only [lower, inc, strictThreeHundredOrderedPairs,
      strictThreeHundredDirectedPairs, Finset.mem_filter]
    aesop
  have hsplit : lower ∪ upper = inc := by
    ext q
    simp only [lower, upper, Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro (h | h) <;> exact h.1
    · intro hq
      have hne : q.1 ≠ q.2 :=
        (mem_strictThreeHundredDirectedPairs_iff p q).mp hq |>.1
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · exact Or.inl ⟨hq, hlt⟩
      · exact Or.inr ⟨hq, hgt⟩
  have hdisj : Disjoint lower upper := by
    rw [Finset.disjoint_left]
    intro q hql hqu
    exact (not_lt_of_ge (le_of_lt (Finset.mem_filter.mp hql).2))
      (Finset.mem_filter.mp hqu).2
  have hcards : lower.card = upper.card := by
    apply Finset.card_bij (fun q _ => q.swap)
    · intro q hq
      apply Finset.mem_filter.mpr
      exact ⟨(swap_mem_strictThreeHundredDirected_iff p q).mpr
        (Finset.mem_filter.mp hq).1, (Finset.mem_filter.mp hq).2⟩
    · intro a ha b hb hab
      exact Prod.swap_injective hab
    · intro b hb
      refine ⟨b.swap, ?_, Prod.swap_swap b⟩
      apply Finset.mem_filter.mpr
      exact ⟨(swap_mem_strictThreeHundredDirected_iff p b).mpr
        (Finset.mem_filter.mp hb).1, (Finset.mem_filter.mp hb).2⟩
  have hc := Finset.card_union_of_disjoint hdisj
  calc
    inc.card = lower.card + upper.card := by rw [← hsplit]; exact hc
    _ = lower.card + lower.card := by rw [← hcards]
    _ = 2 * lower.card := by omega
    _ = 2 * (strictThreeHundredOrderedPairs p).card := by rw [hlower]

/-- Direct unordered strict count exceeds `537n`. -/
theorem strictObliquePatch_unordered_excess :
    537 * Fintype.card (Fin 4535 × Fin 4535) <
      (strictThreeHundredOrderedPairs strictObliquePoint).card := by
  have hl := strictObliquePatch_directed_card_ge
  have hd := strictThreeHundredDirected_card_eq_twice_ordered strictObliquePoint
  rw [hd] at hl
  have hbase : 11044064473 ≤
      (strictThreeHundredOrderedPairs strictObliquePoint).card := by omega
  simp only [Fintype.card_prod, Fintype.card_fin]
  norm_num
  omega

/-- Ordinary-distance directed strict pairs at the genuine shell `sqrt 300`. -/
noncomputable def ordinaryStrictThreeHundredDirectedPairs
    {α : Type*} [Fintype α] [DecidableEq α]
    (p : α → ℝ × ℝ) : Finset (α × α) :=
  (Finset.univ.product Finset.univ).filter fun q =>
    q.1 ≠ q.2 ∧
      Real.sqrt (sqDist (p q.1) (p q.2)) < Real.sqrt 300

/-- Ordinary-distance direct unordered strict pairs. -/
noncomputable def ordinaryStrictThreeHundredOrderedPairs
    {α : Type*} [Fintype α] [LinearOrder α]
    (p : α → ℝ × ℝ) : Finset (α × α) :=
  (Finset.univ.product Finset.univ).filter fun q =>
    q.1 < q.2 ∧
      Real.sqrt (sqDist (p q.1) (p q.2)) < Real.sqrt 300

private lemma sqDist_nonneg_strict (p q : ℝ × ℝ) : 0 ≤ sqDist p q := by
  simp only [sqDist]
  positivity

theorem ordinaryStrictThreeHundredDirected_eq {α : Type*} [Fintype α]
    [DecidableEq α] (p : α → ℝ × ℝ) :
    ordinaryStrictThreeHundredDirectedPairs p =
      strictThreeHundredDirectedPairs p := by
  ext q
  simp only [ordinaryStrictThreeHundredDirectedPairs,
    strictThreeHundredDirectedPairs, Finset.mem_filter]
  constructor
  · rintro ⟨hu, hne, hd⟩
    exact ⟨hu, hne, (Real.sqrt_lt_sqrt_iff
      (sqDist_nonneg_strict (p q.1) (p q.2))).mp hd⟩
  · rintro ⟨hu, hne, hd⟩
    exact ⟨hu, hne, (Real.sqrt_lt_sqrt_iff
      (sqDist_nonneg_strict (p q.1) (p q.2))).mpr hd⟩

theorem ordinaryStrictThreeHundredOrdered_eq {α : Type*} [Fintype α]
    [LinearOrder α] (p : α → ℝ × ℝ) :
    ordinaryStrictThreeHundredOrderedPairs p =
      strictThreeHundredOrderedPairs p := by
  ext q
  simp only [ordinaryStrictThreeHundredOrderedPairs,
    strictThreeHundredOrderedPairs, Finset.mem_filter]
  constructor
  · rintro ⟨hu, hlt, hd⟩
    exact ⟨hu, hlt, (Real.sqrt_lt_sqrt_iff
      (sqDist_nonneg_strict (p q.1) (p q.2))).mp hd⟩
  · rintro ⟨hu, hlt, hd⟩
    exact ⟨hu, hlt, (Real.sqrt_lt_sqrt_iff
      (sqDist_nonneg_strict (p q.1) (p q.2))).mpr hd⟩

/-- Coarse coordinate bounds for separating strict-shell patches. -/
theorem strictObliquePoint_coordinate_bounds (q : Fin 4535 × Fin 4535) :
    0 ≤ (strictObliquePoint q).1 ∧ (strictObliquePoint q).1 ≤ 7000 ∧
      0 ≤ (strictObliquePoint q).2 ∧ (strictObliquePoint q).2 ≤ 5000 := by
  have hq1N : q.1.val ≤ 4534 := by omega
  have hq2N : q.2.val ≤ 4534 := by omega
  have hq1 : (q.1.val : ℝ) ≤ 4534 := by exact_mod_cast hq1N
  have hq2 : (q.2.val : ℝ) ≤ 4534 := by exact_mod_cast hq2N
  have hq10 : (0 : ℝ) ≤ q.1.val := by positivity
  have hq20 : (0 : ℝ) ≤ q.2.val := by positivity
  simp only [strictObliquePoint]
  constructor
  · positivity
  · constructor
    · norm_num
      nlinarith
    · constructor
      · positivity
      · norm_num
        nlinarith

/-- Far-separated translated strict-shell patches. -/
noncomputable def strictObliqueBlocks (m : ℕ)
    (q : Fin m × (Fin 4535 × Fin 4535)) : ℝ × ℝ :=
  (20000 * (q.1.val : ℝ) + (strictObliquePoint q.2).1,
    (strictObliquePoint q.2).2)

theorem strictObliqueBlocks_oneSeparated (m : ℕ) :
    ∀ q s : Fin m × (Fin 4535 × Fin 4535), q ≠ s →
      1 ≤ sqDist (strictObliqueBlocks m q) (strictObliqueBlocks m s) := by
  intro q s hqs
  by_cases hb : q.1 = s.1
  · have hp : q.2 ≠ s.2 := by
      intro hp
      exact hqs (Prod.ext hb hp)
    have h := strictObliquePoint_oneSeparated q.2 s.2 hp
    simp only [strictObliqueBlocks, sqDist] at h ⊢
    rw [hb]
    convert h using 1 <;> ring
  · have hbval : q.1.val ≠ s.1.val := fun h => hb (Fin.ext h)
    rcases lt_or_gt_of_ne hbval with hlt | hgt
    · have hstep : (q.1.val : ℝ) + 1 ≤ (s.1.val : ℝ) := by
        exact_mod_cast (Nat.succ_le_iff.mpr hlt)
      have hq := strictObliquePoint_coordinate_bounds q.2
      have hs := strictObliquePoint_coordinate_bounds s.2
      have hdx : 13000 ≤
          (20000 * (s.1.val : ℝ) + (strictObliquePoint s.2).1) -
            (20000 * (q.1.val : ℝ) + (strictObliquePoint q.2).1) := by
        nlinarith
      simp only [strictObliqueBlocks, sqDist]
      nlinarith [sq_nonneg
        ((strictObliquePoint q.2).2 - (strictObliquePoint s.2).2)]
    · have hstep : (s.1.val : ℝ) + 1 ≤ (q.1.val : ℝ) := by
        exact_mod_cast (Nat.succ_le_iff.mpr hgt)
      have hq := strictObliquePoint_coordinate_bounds q.2
      have hs := strictObliquePoint_coordinate_bounds s.2
      have hdx : 13000 ≤
          (20000 * (q.1.val : ℝ) + (strictObliquePoint q.2).1) -
            (20000 * (s.1.val : ℝ) + (strictObliquePoint s.2).1) := by
        nlinarith
      simp only [strictObliqueBlocks, sqDist]
      nlinarith [sq_nonneg
        ((strictObliquePoint q.2).2 - (strictObliquePoint s.2).2)]

abbrev StrictBlockIncidence (m : ℕ) :=
  Fin m × StrictThreeHundredIncidence

def strictBlockIncidencePair (m : ℕ) (z : StrictBlockIncidence m) :
    (Fin m × (Fin 4535 × Fin 4535)) ×
      (Fin m × (Fin 4535 × Fin 4535)) :=
  ((z.1, strictIncidenceStart z.2), (z.1, strictIncidenceEnd z.2))

lemma strictBlockIncidencePair_injective (m : ℕ) :
    Function.Injective (strictBlockIncidencePair m) := by
  rintro ⟨b, z⟩ ⟨c, w⟩ h
  have hbc : b = c := congrArg (fun q => q.1.1) h
  have hs : strictIncidenceStart z = strictIncidenceStart w :=
    congrArg (fun q => q.1.2) h
  have he : strictIncidenceEnd z = strictIncidenceEnd w :=
    congrArg (fun q => q.2.2) h
  have hzw : z = w := strictIncidencePair_injective (Prod.ext hs he)
  exact Prod.ext hbc hzw

lemma strictBlockIncidencePair_valid (m : ℕ) (z : StrictBlockIncidence m) :
    let q := strictBlockIncidencePair m z
    q.1 ≠ q.2 ∧
      sqDist (strictObliqueBlocks m q.1) (strictObliqueBlocks m q.2) < 300 := by
  have hv := strictIncidencePair_valid z.2
  change strictIncidenceStart z.2 ≠ strictIncidenceEnd z.2 ∧
    sqDist (strictObliquePoint (strictIncidenceStart z.2))
      (strictObliquePoint (strictIncidenceEnd z.2)) < 300 at hv
  change (z.1, strictIncidenceStart z.2) ≠
      (z.1, strictIncidenceEnd z.2) ∧
    sqDist (strictObliqueBlocks m (z.1, strictIncidenceStart z.2))
      (strictObliqueBlocks m (z.1, strictIncidenceEnd z.2)) < 300
  constructor
  · intro h
    exact hv.1 (congrArg Prod.snd h)
  · have heq :
        sqDist (strictObliqueBlocks m (z.1, strictIncidenceStart z.2))
          (strictObliqueBlocks m (z.1, strictIncidenceEnd z.2)) =
        sqDist (strictObliquePoint (strictIncidenceStart z.2))
          (strictObliquePoint (strictIncidenceEnd z.2)) := by
        simp only [strictObliqueBlocks, sqDist]
        ring
    rw [heq]
    exact hv.2

def strictBlockIncidenceToPair (m : ℕ) :
    StrictBlockIncidence m ↪ StrictThreeHundredPairType (strictObliqueBlocks m) where
  toFun z := ⟨strictBlockIncidencePair m z,
    strictBlockIncidencePair_valid m z⟩
  inj' := by
    intro z w h
    apply strictBlockIncidencePair_injective m
    exact congrArg Subtype.val h

theorem strictBlockIncidence_card (m : ℕ) :
    Fintype.card (StrictBlockIncidence m) = m * 22088128946 := by
  rw [Fintype.card_prod, Fintype.card_fin, strictThreeHundredIncidence_card]

theorem strictObliqueBlocks_directed_card_ge (m : ℕ) :
    m * 22088128946 ≤
      (strictThreeHundredDirectedPairs (strictObliqueBlocks m)).card := by
  calc
    m * 22088128946 = Fintype.card (StrictBlockIncidence m) :=
      (strictBlockIncidence_card m).symm
    _ ≤ Fintype.card (StrictThreeHundredPairType (strictObliqueBlocks m)) :=
      Fintype.card_le_of_embedding (strictBlockIncidenceToPair m)
    _ = (strictThreeHundredDirectedPairs (strictObliqueBlocks m)).card :=
      StrictThreeHundredPairType_card_eq (strictObliqueBlocks m)

/-- Every nonempty collection of patches beats the corrected closed
triangular comparison 1074, despite using strict distance `< sqrt 300`. -/
theorem strictObliqueBlocks_corrected_excess (m : ℕ) (hm : 0 < m) :
    1074 * Fintype.card (Fin m × (Fin 4535 × Fin 4535)) <
      (strictThreeHundredDirectedPairs (strictObliqueBlocks m)).card := by
  have hl := strictObliqueBlocks_directed_card_ge m
  calc
    1074 * Fintype.card (Fin m × (Fin 4535 × Fin 4535)) =
        m * 22088125650 := by
      simp only [Fintype.card_prod, Fintype.card_fin]
      ring
    _ < m * 22088128946 := Nat.mul_lt_mul_of_pos_left (by norm_num) hm
    _ ≤ (strictThreeHundredDirectedPairs (strictObliqueBlocks m)).card := hl

theorem strictObliqueBlocks_ordered_card_ge (m : ℕ) :
    m * 11044064473 ≤
      (strictThreeHundredOrderedPairs (strictObliqueBlocks m)).card := by
  have hl := strictObliqueBlocks_directed_card_ge m
  have hd := strictThreeHundredDirected_card_eq_twice_ordered
    (strictObliqueBlocks m)
  rw [hd] at hl
  have ht : 2 * (m * 11044064473) ≤
      2 * (strictThreeHundredOrderedPairs (strictObliqueBlocks m)).card := by
    convert hl using 1 <;> ring
  exact Nat.le_of_mul_le_mul_left ht (by norm_num)

theorem strictObliqueBlocks_corrected_unordered_excess
    (m : ℕ) (hm : 0 < m) :
    537 * Fintype.card (Fin m × (Fin 4535 × Fin 4535)) <
      (strictThreeHundredOrderedPairs (strictObliqueBlocks m)).card := by
  have hl := strictObliqueBlocks_ordered_card_ge m
  calc
    537 * Fintype.card (Fin m × (Fin 4535 × Fin 4535)) =
        m * 11044062825 := by
      simp only [Fintype.card_prod, Fintype.card_fin]
      ring
    _ < m * 11044064473 := Nat.mul_lt_mul_of_pos_left (by norm_num) hm
    _ ≤ (strictThreeHundredOrderedPairs (strictObliqueBlocks m)).card := hl

/-- Ordinary one-separation for the strict blocks. -/
theorem strictObliqueBlocks_ordinaryOneSeparated (m : ℕ) :
    OrdinaryOneSeparatedOn (strictObliqueBlocks m) := by
  intro q s hqs
  rw [Real.one_le_sqrt]
  exact strictObliqueBlocks_oneSeparated m q s hqs

/-- Corrected strict-shell global directed claim. -/
def EventualCorrectedStrictShellDirectedBound : Prop :=
  ∃ N : ℕ, ∀ (α : Type) [Fintype α] [DecidableEq α],
    N ≤ Fintype.card α → ∀ p : α → ℝ × ℝ,
      OrdinaryOneSeparatedOn p →
        (ordinaryStrictThreeHundredDirectedPairs p).card ≤
          1074 * Fintype.card α

/-- Corrected strict-shell direct unordered claim. -/
def EventualCorrectedStrictShellUnorderedBound : Prop :=
  ∃ N : ℕ, ∀ (α : Type) [Fintype α] [LinearOrder α],
    N ≤ Fintype.card α → ∀ p : α → ℝ × ℝ,
      OrdinaryOneSeparatedOn p →
        (ordinaryStrictThreeHundredOrderedPairs p).card ≤
          537 * Fintype.card α

/-- The corrected strict-shell directed reading fails above every cutoff. -/
theorem not_eventualCorrectedStrictShellDirectedBound :
    ¬ EventualCorrectedStrictShellDirectedBound := by
  rintro ⟨N, hN⟩
  have hc : N ≤ Fintype.card
      (Fin (N + 1) × (Fin 4535 × Fin 4535)) := by
    simp only [Fintype.card_prod, Fintype.card_fin]
    nlinarith
  have hu := hN (Fin (N + 1) × (Fin 4535 × Fin 4535)) hc
    (strictObliqueBlocks (N + 1))
    (strictObliqueBlocks_ordinaryOneSeparated (N + 1))
  rw [ordinaryStrictThreeHundredDirected_eq] at hu
  have hl := strictObliqueBlocks_corrected_excess (N + 1) (by omega)
  omega

/-- The corrected strict-shell unordered reading also fails. -/
theorem not_eventualCorrectedStrictShellUnorderedBound :
    ¬ EventualCorrectedStrictShellUnorderedBound := by
  rintro ⟨N, hN⟩
  have hc : N ≤ Fintype.card
      (Fin (N + 1) × (Fin 4535 × Fin 4535)) := by
    simp only [Fintype.card_prod, Fintype.card_fin]
    nlinarith
  have hu := hN (Fin (N + 1) × (Fin 4535 × Fin 4535)) hc
    (strictObliqueBlocks (N + 1))
    (strictObliqueBlocks_ordinaryOneSeparated (N + 1))
  rw [ordinaryStrictThreeHundredOrdered_eq] at hu
  have hl := strictObliqueBlocks_corrected_unordered_excess (N + 1) (by omega)
  omega

/-! ## The printed `f(3)=18` strict-shell reading -/

/-- Directed pairs at squared distance strictly below nine. -/
noncomputable def strictThreeDirectedPairsSq {α : Type*} [Fintype α]
    [DecidableEq α] (p : α → ℝ × ℝ) : Finset (α × α) :=
  (Finset.univ.product Finset.univ).filter fun q =>
    q.1 ≠ q.2 ∧ sqDist (p q.1) (p q.2) < 9

lemma mem_strictThreeDirectedPairsSq_iff {α : Type*} [Fintype α]
    [DecidableEq α] (p : α → ℝ × ℝ) (q : α × α) :
    q ∈ strictThreeDirectedPairsSq p ↔
      q.1 ≠ q.2 ∧ sqDist (p q.1) (p q.2) < 9 := by
  simp [strictThreeDirectedPairsSq]

/-- Ordinary-distance version `d<3`. -/
noncomputable def strictThreeOrdinaryDirectedPairs {α : Type*} [Fintype α]
    [DecidableEq α] (p : α → ℝ × ℝ) : Finset (α × α) :=
  (Finset.univ.product Finset.univ).filter fun q =>
    q.1 ≠ q.2 ∧ Real.sqrt (sqDist (p q.1) (p q.2)) < 3

theorem strictThreeOrdinaryDirected_eq_sq {α : Type*} [Fintype α]
    [DecidableEq α] (p : α → ℝ × ℝ) :
    strictThreeOrdinaryDirectedPairs p = strictThreeDirectedPairsSq p := by
  ext q
  simp only [strictThreeOrdinaryDirectedPairs, strictThreeDirectedPairsSq,
    Finset.mem_filter]
  constructor
  · rintro ⟨hu, hne, hd⟩
    refine ⟨hu, hne, ?_⟩
    rw [Real.sqrt_lt (sqDist_nonneg_strict _ _) (by norm_num)] at hd
    norm_num at hd ⊢
    exact hd
  · rintro ⟨hu, hne, hd⟩
    refine ⟨hu, hne, ?_⟩
    rw [Real.sqrt_lt (sqDist_nonneg_strict _ _) (by norm_num)]
    norm_num at hd ⊢
    exact hd

/-- Executable exact strict-pair census on the 38-point packing. -/
def packing38StrictIndexPairs : Finset (Fin 38 × Fin 38) :=
  (Finset.univ.product Finset.univ).filter fun q =>
    q.1 ≠ q.2 ∧ packing38SqNum q.1 q.2 < 90000000000000000

theorem packing38StrictIndexPairs_card :
    packing38StrictIndexPairs.card = 710 := by
  decide

/-- The executable integer census equals the real squared-distance finset. -/
theorem packing38StrictIndexPairs_eq_real :
    packing38StrictIndexPairs = strictThreeDirectedPairsSq packing38 := by
  ext q
  simp only [packing38StrictIndexPairs, strictThreeDirectedPairsSq,
    Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hu, hne, hz⟩
    refine ⟨hu, hne, ?_⟩
    rw [packing38_sqDist_eq]
    have hzR : (packing38SqNum q.1 q.2 : ℝ) < 90000000000000000 := by
      exact_mod_cast hz
    norm_num at hzR ⊢
    nlinarith
  · rintro ⟨hu, hne, hd⟩
    refine ⟨hu, hne, ?_⟩
    rw [packing38_sqDist_eq] at hd
    have hzR : (packing38SqNum q.1 q.2 : ℝ) < 90000000000000000 := by
      norm_num at hd ⊢
      nlinarith
    exact_mod_cast hzR

/-- Predicate type for strict radius-three directed pairs. -/
def StrictThreePairType {α : Type*} (p : α → ℝ × ℝ) :=
  {q : α × α // q.1 ≠ q.2 ∧ sqDist (p q.1) (p q.2) < 9}

noncomputable instance StrictThreePairType.instFintype
    {α : Type*} [Fintype α] (p : α → ℝ × ℝ) :
    Fintype (StrictThreePairType p) := by
  letI : Finite (StrictThreePairType p) :=
    Finite.of_injective (fun q : StrictThreePairType p => q.val)
      Subtype.val_injective
  exact Fintype.ofFinite (StrictThreePairType p)

theorem StrictThreePairType_card_eq {α : Type*} [Fintype α]
    [DecidableEq α] (p : α → ℝ × ℝ) :
    Fintype.card (StrictThreePairType p) =
      (strictThreeDirectedPairsSq p).card := by
  classical
  let e : StrictThreePairType p ≃ {q // q ∈ strictThreeDirectedPairsSq p} :=
    Equiv.subtypeEquivRight fun q =>
      (mem_strictThreeDirectedPairsSq_iff p q).symm
  calc
    Fintype.card (StrictThreePairType p) =
        Fintype.card {q // q ∈ strictThreeDirectedPairsSq p} :=
      Fintype.card_congr e
    _ = (strictThreeDirectedPairsSq p).card :=
      Fintype.card_coe (strictThreeDirectedPairsSq p)

abbrev Packing38StrictOffset :=
  {q : Fin 38 × Fin 38 // q ∈ packing38StrictIndexPairs}

abbrev Packing38StrictBlockIncidence (m : ℕ) :=
  Fin m × Packing38StrictOffset

def packing38StrictBlockPair (m : ℕ)
    (z : Packing38StrictBlockIncidence m) :
    (Fin m × Fin 38) × (Fin m × Fin 38) :=
  ((z.1, z.2.val.1), (z.1, z.2.val.2))

lemma packing38StrictBlockPair_injective (m : ℕ) :
    Function.Injective (packing38StrictBlockPair m) := by
  rintro ⟨b, z⟩ ⟨c, w⟩ h
  have hbc : b = c := congrArg (fun q => q.1.1) h
  have hzval : z.val = w.val := by
    apply Prod.ext
    · exact congrArg (fun q => q.1.2) h
    · exact congrArg (fun q => q.2.2) h
  exact Prod.ext hbc (Subtype.ext hzval)

lemma packing38StrictBlockPair_valid (m : ℕ)
    (z : Packing38StrictBlockIncidence m) :
    let q := packing38StrictBlockPair m z
    q.1 ≠ q.2 ∧
      sqDist (packing38Blocks m q.1) (packing38Blocks m q.2) < 9 := by
  have hm : z.2.val ∈ strictThreeDirectedPairsSq packing38 := by
    rw [← packing38StrictIndexPairs_eq_real]
    exact z.2.property
  have hv := (mem_strictThreeDirectedPairsSq_iff packing38 z.2.val).mp hm
  change (z.1, z.2.val.1) ≠ (z.1, z.2.val.2) ∧
    sqDist (packing38Blocks m (z.1, z.2.val.1))
      (packing38Blocks m (z.1, z.2.val.2)) < 9
  constructor
  · intro h
    exact hv.1 (congrArg Prod.snd h)
  · have heq :
        sqDist (packing38Blocks m (z.1, z.2.val.1))
          (packing38Blocks m (z.1, z.2.val.2)) =
        sqDist (packing38 z.2.val.1) (packing38 z.2.val.2) := by
      simp only [packing38Blocks, sqDist]
      ring
    rw [heq]
    exact hv.2

def packing38StrictBlockToPair (m : ℕ) :
    Packing38StrictBlockIncidence m ↪
      StrictThreePairType (packing38Blocks m) where
  toFun z := ⟨packing38StrictBlockPair m z,
    packing38StrictBlockPair_valid m z⟩
  inj' := by
    intro z w h
    apply packing38StrictBlockPair_injective m
    exact congrArg Subtype.val h

theorem packing38StrictBlockIncidence_card (m : ℕ) :
    Fintype.card (Packing38StrictBlockIncidence m) = m * 710 := by
  rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_coe,
    packing38StrictIndexPairs_card]

/-- Replicated 38-point blocks retain at least `710m` strict directed pairs. -/
theorem packing38Blocks_strict_directed_card_ge (m : ℕ) :
    m * 710 ≤ (strictThreeDirectedPairsSq (packing38Blocks m)).card := by
  calc
    m * 710 = Fintype.card (Packing38StrictBlockIncidence m) :=
      (packing38StrictBlockIncidence_card m).symm
    _ ≤ Fintype.card (StrictThreePairType (packing38Blocks m)) :=
      Fintype.card_le_of_embedding (packing38StrictBlockToPair m)
    _ = (strictThreeDirectedPairsSq (packing38Blocks m)).card :=
      StrictThreePairType_card_eq (packing38Blocks m)

/-- The printed normalized value 18 is violated strictly below radius three:
`710m > 18·38m = 684m`. -/
theorem packing38Blocks_printed_strict_global_excess (m : ℕ) (hm : 0 < m) :
    18 * Fintype.card (Fin m × Fin 38) <
      (strictThreeDirectedPairsSq (packing38Blocks m)).card := by
  have hl := packing38Blocks_strict_directed_card_ge m
  calc
    18 * Fintype.card (Fin m × Fin 38) = m * 684 := by
      simp only [Fintype.card_prod, Fintype.card_fin]
      ring
    _ < m * 710 := Nat.mul_lt_mul_of_pos_left (by norm_num) hm
    _ ≤ (strictThreeDirectedPairsSq (packing38Blocks m)).card := hl

/-- Ordinary one-separation of the replicated 38-point blocks. -/
theorem packing38Blocks_ordinaryOneSeparated (m : ℕ) :
    OrdinaryOneSeparatedOn (packing38Blocks m) := by
  intro q s hqs
  rw [Real.one_le_sqrt]
  exact packing38Blocks_oneSeparated m q s hqs

/-- Eventual global strict-radius-three bound using the printed comparison 18. -/
def EventualPrintedStrictThreeGlobalBound : Prop :=
  ∃ N : ℕ, ∀ (α : Type) [Fintype α] [DecidableEq α],
    N ≤ Fintype.card α → ∀ p : α → ℝ × ℝ,
      OrdinaryOneSeparatedOn p →
        (strictThreeOrdinaryDirectedPairs p).card ≤ 18 * Fintype.card α

theorem not_eventualPrintedStrictThreeGlobalBound :
    ¬ EventualPrintedStrictThreeGlobalBound := by
  rintro ⟨N, hN⟩
  have hc : N ≤ Fintype.card (Fin (N + 1) × Fin 38) := by
    simp only [Fintype.card_prod, Fintype.card_fin]
    omega
  have hu := hN (Fin (N + 1) × Fin 38) hc (packing38Blocks (N + 1))
    (packing38Blocks_ordinaryOneSeparated (N + 1))
  rw [strictThreeOrdinaryDirected_eq_sq] at hu
  have hl := packing38Blocks_printed_strict_global_excess (N + 1) (by omega)
  omega

/-- One representative of each direct unordered pair strictly below three. -/
noncomputable def strictThreeOrderedPairsSq {α : Type*} [Fintype α]
    [LinearOrder α] (p : α → ℝ × ℝ) : Finset (α × α) :=
  (Finset.univ.product Finset.univ).filter fun q =>
    q.1 < q.2 ∧ sqDist (p q.1) (p q.2) < 9

lemma swap_mem_strictThreeDirectedPairsSq_iff {α : Type*} [Fintype α]
    [DecidableEq α] (p : α → ℝ × ℝ) (q : α × α) :
    q.swap ∈ strictThreeDirectedPairsSq p ↔
      q ∈ strictThreeDirectedPairsSq p := by
  rw [mem_strictThreeDirectedPairsSq_iff, mem_strictThreeDirectedPairsSq_iff]
  rcases q with ⟨a, b⟩
  simp only [Prod.swap_prod_mk, Prod.fst, Prod.snd]
  constructor
  · rintro ⟨hne, hd⟩
    exact ⟨hne.symm, by rwa [sqDist_symm]⟩
  · rintro ⟨hne, hd⟩
    exact ⟨hne.symm, by rwa [sqDist_symm]⟩

theorem strictThreeDirected_card_eq_twice_ordered {α : Type*}
    [Fintype α] [DecidableEq α] [LinearOrder α] (p : α → ℝ × ℝ) :
    (strictThreeDirectedPairsSq p).card =
      2 * (strictThreeOrderedPairsSq p).card := by
  classical
  let inc := strictThreeDirectedPairsSq p
  let lower := inc.filter fun q : α × α => q.1 < q.2
  let upper := inc.filter fun q : α × α => q.2 < q.1
  have hlower : lower = strictThreeOrderedPairsSq p := by
    ext q
    simp only [lower, inc, strictThreeOrderedPairsSq,
      strictThreeDirectedPairsSq, Finset.mem_filter]
    aesop
  have hsplit : lower ∪ upper = inc := by
    ext q
    simp only [lower, upper, Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro (h | h) <;> exact h.1
    · intro hq
      have hne : q.1 ≠ q.2 :=
        (mem_strictThreeDirectedPairsSq_iff p q).mp hq |>.1
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · exact Or.inl ⟨hq, hlt⟩
      · exact Or.inr ⟨hq, hgt⟩
  have hdisj : Disjoint lower upper := by
    rw [Finset.disjoint_left]
    intro q hql hqu
    exact (not_lt_of_ge (le_of_lt (Finset.mem_filter.mp hql).2))
      (Finset.mem_filter.mp hqu).2
  have hcards : lower.card = upper.card := by
    apply Finset.card_bij (fun q _ => q.swap)
    · intro q hq
      apply Finset.mem_filter.mpr
      exact ⟨(swap_mem_strictThreeDirectedPairsSq_iff p q).mpr
        (Finset.mem_filter.mp hq).1, (Finset.mem_filter.mp hq).2⟩
    · intro a ha b hb hab
      exact Prod.swap_injective hab
    · intro b hb
      refine ⟨b.swap, ?_, Prod.swap_swap b⟩
      apply Finset.mem_filter.mpr
      exact ⟨(swap_mem_strictThreeDirectedPairsSq_iff p b).mpr
        (Finset.mem_filter.mp hb).1, (Finset.mem_filter.mp hb).2⟩
  have hc := Finset.card_union_of_disjoint hdisj
  calc
    inc.card = lower.card + upper.card := by rw [← hsplit]; exact hc
    _ = lower.card + lower.card := by rw [← hcards]
    _ = 2 * lower.card := by omega
    _ = 2 * (strictThreeOrderedPairsSq p).card := by rw [hlower]

/-- Printed direct-unordered normalization `E<3 ≤9n` also fails. -/
theorem packing38Blocks_printed_strict_unordered_excess
    (m : ℕ) (hm : 0 < m) :
    9 * Fintype.card (Fin m × Fin 38) <
      (strictThreeOrderedPairsSq (packing38Blocks m)).card := by
  have hl := packing38Blocks_strict_directed_card_ge m
  have hd := strictThreeDirected_card_eq_twice_ordered (packing38Blocks m)
  rw [hd] at hl
  have hhalf : m * 355 ≤
      (strictThreeOrderedPairsSq (packing38Blocks m)).card := by
    have ht : 2 * (m * 355) ≤
        2 * (strictThreeOrderedPairsSq (packing38Blocks m)).card := by
      convert hl using 1 <;> ring
    exact Nat.le_of_mul_le_mul_left ht (by norm_num)
  calc
    9 * Fintype.card (Fin m × Fin 38) = m * 342 := by
      simp only [Fintype.card_prod, Fintype.card_fin]
      ring
    _ < m * 355 := Nat.mul_lt_mul_of_pos_left (by norm_num) hm
    _ ≤ (strictThreeOrderedPairsSq (packing38Blocks m)).card := hhalf

/-- Ordinary direct unordered pairs with distance strictly below three. -/
noncomputable def strictThreeOrdinaryOrderedPairs {α : Type*} [Fintype α]
    [LinearOrder α] (p : α → ℝ × ℝ) : Finset (α × α) :=
  (Finset.univ.product Finset.univ).filter fun q =>
    q.1 < q.2 ∧ Real.sqrt (sqDist (p q.1) (p q.2)) < 3

theorem strictThreeOrdinaryOrdered_eq_sq {α : Type*} [Fintype α]
    [LinearOrder α] (p : α → ℝ × ℝ) :
    strictThreeOrdinaryOrderedPairs p = strictThreeOrderedPairsSq p := by
  ext q
  simp only [strictThreeOrdinaryOrderedPairs, strictThreeOrderedPairsSq,
    Finset.mem_filter]
  constructor
  · rintro ⟨hu, hlt, hd⟩
    refine ⟨hu, hlt, ?_⟩
    rw [Real.sqrt_lt (sqDist_nonneg_strict _ _) (by norm_num)] at hd
    norm_num at hd ⊢
    exact hd
  · rintro ⟨hu, hlt, hd⟩
    refine ⟨hu, hlt, ?_⟩
    rw [Real.sqrt_lt (sqDist_nonneg_strict _ _) (by norm_num)]
    norm_num at hd ⊢
    exact hd

/-- Eventual printed direct-unordered strict claim. -/
def EventualPrintedStrictThreeUnorderedBound : Prop :=
  ∃ N : ℕ, ∀ (α : Type) [Fintype α] [LinearOrder α],
    N ≤ Fintype.card α → ∀ p : α → ℝ × ℝ,
      OrdinaryOneSeparatedOn p →
        (strictThreeOrdinaryOrderedPairs p).card ≤ 9 * Fintype.card α

theorem not_eventualPrintedStrictThreeUnorderedBound :
    ¬ EventualPrintedStrictThreeUnorderedBound := by
  rintro ⟨N, hN⟩
  have hc : N ≤ Fintype.card (Fin (N + 1) × Fin 38) := by
    simp only [Fintype.card_prod, Fintype.card_fin]
    omega
  have hu := hN (Fin (N + 1) × Fin 38) hc (packing38Blocks (N + 1))
    (packing38Blocks_ordinaryOneSeparated (N + 1))
  rw [strictThreeOrdinaryOrdered_eq_sq] at hu
  have hl := packing38Blocks_printed_strict_unordered_excess
    (N + 1) (by omega)
  omega

/-- Strict ordinary neighbours below three. -/
noncomputable def strictThreeNeighbors {α : Type*} [Fintype α]
    [DecidableEq α] (p : α → ℝ × ℝ) (v : α) : Finset α :=
  Finset.univ.filter fun w =>
    w ≠ v ∧ Real.sqrt (sqDist (p w) (p v)) < 3

/-- Eventual local strict-shell claim with an arbitrary proposed comparison. -/
def EventualStrictThreeLocalBound (c : ℕ) : Prop :=
  ∃ N : ℕ, ∀ (α : Type) [Fintype α] [DecidableEq α],
    N ≤ Fintype.card α → ∀ p : α → ℝ × ℝ,
      OrdinaryOneSeparatedOn p → ∀ v : α,
        (strictThreeNeighbors p v).card ≤ c

lemma packing38BlockCenterNeighbors_eq_strict (m : ℕ) (b : Fin m) :
    packing38BlockCenterNeighbors m b =
      strictThreeNeighbors (packing38Blocks m) (b, 18) := by
  ext q
  simp [packing38BlockCenterNeighbors, strictThreeNeighbors]

/-- The strict local reading fails for every comparison below 37. -/
theorem not_eventualStrictThreeLocalBound (c : ℕ) (hc : c < 37) :
    ¬ EventualStrictThreeLocalBound c := by
  rintro ⟨N, hN⟩
  have hcard : N ≤ Fintype.card (Fin (N + 1) × Fin 38) := by
    simp only [Fintype.card_prod, Fintype.card_fin]
    omega
  have hu := hN (Fin (N + 1) × Fin 38) hcard
    (packing38Blocks (N + 1))
    (packing38Blocks_ordinaryOneSeparated (N + 1)) (0, 18)
  rw [← packing38BlockCenterNeighbors_eq_strict] at hu
  have hl := packing38BlockCenterNeighbors_card_ge (N + 1) 0
  omega

/-- Hence both the printed local comparison 18 and corrected comparison 36
fail with strict distance `<3`. -/
theorem printed_and_corrected_strict_three_local_bounds_false :
    ¬ EventualStrictThreeLocalBound 18 ∧
      ¬ EventualStrictThreeLocalBound 36 :=
  ⟨not_eventualStrictThreeLocalBound 18 (by norm_num),
    not_eventualStrictThreeLocalBound 36 (by norm_num)⟩

/-- Consolidated formal treatment of the strict-shell readings: printed global
18, printed/corrected local 18/36, and corrected global cumulative 1074 all
fail above every cardinality cutoff. -/
theorem strict_shell_readings_false :
    triCoordsWithinThreeHundred.card = 1074 ∧
    triCoordsStrictThreeHundred.card = 1068 ∧
    ¬ EventualCorrectedStrictShellDirectedBound ∧
    ¬ EventualCorrectedStrictShellUnorderedBound ∧
    ¬ EventualPrintedStrictThreeGlobalBound ∧
    ¬ EventualPrintedStrictThreeUnorderedBound ∧
    ¬ EventualStrictThreeLocalBound 18 ∧
    ¬ EventualStrictThreeLocalBound 36 :=
  ⟨triCoordsWithinThreeHundred_card,
    triCoordsStrictThreeHundred_card,
    not_eventualCorrectedStrictShellDirectedBound,
    not_eventualCorrectedStrictShellUnorderedBound,
    not_eventualPrintedStrictThreeGlobalBound,
    not_eventualPrintedStrictThreeUnorderedBound,
    printed_and_corrected_strict_three_local_bounds_false.1,
    printed_and_corrected_strict_three_local_bounds_false.2⟩

end Research
