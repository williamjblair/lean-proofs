import Research.BallotReflection
import Research.BallotBounds
import Mathlib.Data.Finset.BooleanAlgebra
import Mathlib.Data.Finset.Sort
import Mathlib.Tactic

namespace Erdos521

noncomputable local instance (p : Prop) : Decidable p := Classical.propDecidable p

/-- Boolean functions are equivalent to their finite set of `false` locations. -/
def boolFunEquivFinset (α : Type*) [Fintype α] [DecidableEq α] :
    (α → Bool) ≃ Finset α where
  toFun f := Finset.univ.filter (fun i ↦ f i = false)
  invFun D i := if i ∈ D then false else true
  left_inv f := by
    funext i
    cases h : f i <;> simp [h]
  right_inv D := by
    ext i
    simp

/-- Restrict a Boolean function to a finite set and its complement. -/
def splitBoolEquiv (α : Type*) [Fintype α] [DecidableEq α] (H : Finset α) :
    (α → Bool) ≃ ((H → Bool) × (↥(Hᶜ) → Bool)) where
  toFun f := (fun i ↦ f i, fun i ↦ f i)
  invFun fg i := if hi : i ∈ H then fg.1 ⟨i, hi⟩ else fg.2 ⟨i, by simpa using hi⟩
  left_inv f := by
    funext i
    by_cases hi : i ∈ H <;> simp [hi]
  right_inv fg := by
    apply Prod.ext <;> funext i
    · simp [i.property]
    · have hi : (i : α) ∉ H := Finset.mem_compl.mp i.property
      simp [hi]

/-- A sign assignment, split by a schedule `H`, is equivalently a pair of down-step sets indexed
in their inherited chronological orders. -/
def scheduleDownEquiv {n : ℕ} (H : Finset (Fin n)) :
    (Fin n → Bool) ≃
      (Finset (Fin H.card) × Finset (Fin (Hᶜ).card)) :=
  (splitBoolEquiv (Fin n) H).trans <|
    Equiv.prodCongr
      ((Equiv.piCongrLeft (fun _ : H ↦ Bool) (H.orderIsoOfFin rfl)).symm.trans
        (boolFunEquivFinset (Fin H.card)))
      ((Equiv.piCongrLeft (fun _ : ↥(Hᶜ) ↦ Bool) ((Hᶜ).orderIsoOfFin rfl)).symm.trans
        (boolFunEquivFinset (Fin (Hᶜ).card)))

/-- The increasing enumeration has exactly `j` schedule locations strictly before its `j`th
location. -/
lemma card_filter_lt_orderEmb {n : ℕ} (H : Finset (Fin n)) (j : Fin H.card) :
    (H.filter (fun x ↦ x < H.orderEmbOfFin rfl j)).card = j.val := by
  let e := H.orderEmbOfFin rfl
  have heq : Finset.image e (Finset.Iio j) =
      H.filter (fun x ↦ x < e j) := by
    ext x
    simp only [Finset.mem_image, Finset.mem_Iio, Finset.mem_filter]
    constructor
    · rintro ⟨k, hk, rfl⟩
      exact ⟨Finset.orderEmbOfFin_mem H rfl k, e.strictMono hk⟩
    · rintro ⟨hxH, hxlt⟩
      let k : Fin H.card := (H.orderIsoOfFin rfl).symm ⟨x, hxH⟩
      have happ := (H.orderIsoOfFin rfl).apply_symm_apply ⟨x, hxH⟩
      have hklt : k < j := by
        apply (H.orderIsoOfFin rfl).lt_iff_lt.mp
        rw [happ]
        exact hxlt
      refine ⟨k, hklt, ?_⟩
      exact congrArg Subtype.val happ
  rw [← heq, Finset.card_image_of_injective _ e.injective, Fin.card_Iio]

lemma orderEmb_val_lt_iff_rank_lt {n : ℕ} (H : Finset (Fin n)) (t : ℕ)
    (j : Fin H.card) :
    (H.orderEmbOfFin rfl j).val < t ↔
      j.val < (H.filter (fun x ↦ x.val < t)).card := by
  let e := H.orderEmbOfFin rfl
  let L := H.filter (fun x ↦ x < e j)
  let B := H.filter (fun x ↦ x.val < t)
  change (e j).val < t ↔ j.val < B.card
  have hLcard : L.card = j.val := by simpa [L, e] using card_filter_lt_orderEmb H j
  constructor
  · intro hjt
    have hsub : insert (e j) L ⊆ B := by
      intro x hx
      rw [Finset.mem_insert] at hx
      rcases hx with rfl | hxL
      · exact Finset.mem_filter.mpr ⟨Finset.orderEmbOfFin_mem H rfl j, hjt⟩
      · have hx' := Finset.mem_filter.mp hxL
        exact Finset.mem_filter.mpr ⟨hx'.1, lt_trans hx'.2 hjt⟩
    have hnot : e j ∉ L := by simp [L]
    have hc := Finset.card_le_card hsub
    rw [Finset.card_insert_of_notMem hnot, hLcard] at hc
    exact hc
  · intro hj
    by_contra hnot
    have htle : t ≤ (e j).val := by omega
    have hsub : B ⊆ L := by
      intro x hx
      have hx' := Finset.mem_filter.mp hx
      exact Finset.mem_filter.mpr ⟨hx'.1, by
        change x.val < (e j).val
        omega⟩
    have hc := Finset.card_le_card hsub
    rw [hLcard] at hc
    omega

/-- Down-step set of the sign sequence compressed to schedule positions `A`. -/
def compressedDown {n : ℕ} (A : Finset (Fin n)) (S : Fin n → Bool) :
    Finset (Fin A.card) :=
  Finset.univ.filter (fun j ↦ S (A.orderEmbOfFin rfl j) = false)

@[simp] lemma mem_compressedDown {n : ℕ} (A : Finset (Fin n)) (S : Fin n → Bool)
    (j : Fin A.card) :
    j ∈ compressedDown A S ↔ S (A.orderEmbOfFin rfl j) = false := by
  simp [compressedDown]

/-- The compressed prefix down count equals the down count among schedule locations before global
time `t`. -/
lemma downPrefix_compressedDown {n : ℕ} (A : Finset (Fin n)) (S : Fin n → Bool)
    (t : ℕ) :
    downPrefix (compressedDown A S) (A.filter (fun x ↦ x.val < t)).card =
      ((A.filter (fun x ↦ x.val < t)).filter (fun x ↦ S x = false)).card := by
  let B := A.filter (fun x ↦ x.val < t)
  let q := B.card
  let e := A.orderEmbOfFin rfl
  let U := compressedDown A S ∩ pathPrefix A.card q
  let V := B.filter (fun x ↦ S x = false)
  have heq : Finset.image e U = V := by
    ext x
    simp only [Finset.mem_image]
    constructor
    · rintro ⟨j, hjU, rfl⟩
      have hj := Finset.mem_inter.mp hjU
      have hjfalse : S (e j) = false := by simpa [e] using hj.1
      have hjrank : j.val < q := by simpa [U] using hj.2
      have hjtime : (e j).val < t := by
        apply (orderEmb_val_lt_iff_rank_lt A t j).mpr
        exact hjrank
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_filter.mpr ⟨Finset.orderEmbOfFin_mem A rfl j, hjtime⟩, hjfalse⟩
    · intro hxV
      have hx := Finset.mem_filter.mp hxV
      have hxB := Finset.mem_filter.mp hx.1
      let j : Fin A.card := (A.orderIsoOfFin rfl).symm ⟨x, hxB.1⟩
      have happ := (A.orderIsoOfFin rfl).apply_symm_apply ⟨x, hxB.1⟩
      have hjrank : j.val < q := by
        apply (orderEmb_val_lt_iff_rank_lt A t j).mp
        rw [show e j = x from congrArg Subtype.val happ]
        exact hxB.2
      refine ⟨j, ?_, congrArg Subtype.val happ⟩
      apply Finset.mem_inter.mpr
      constructor
      · apply (mem_compressedDown A S j).mpr
        rw [show e j = x from congrArg Subtype.val happ]
        exact hx.2
      · exact mem_pathPrefix.mpr hjrank
  have hc := congrArg Finset.card heq
  rw [Finset.card_image_of_injective _ e.injective] at hc
  simpa [downPrefix, B, q, U, V] using hc

@[simp] lemma mem_scheduleDownEquiv_fst {n : ℕ} (H : Finset (Fin n))
    (S : Fin n → Bool) (i : Fin H.card) :
    i ∈ (scheduleDownEquiv H S).1 ↔ S (H.orderEmbOfFin rfl i) = false := by
  simp [scheduleDownEquiv, splitBoolEquiv, boolFunEquivFinset]

@[simp] lemma mem_scheduleDownEquiv_snd {n : ℕ} (H : Finset (Fin n))
    (S : Fin n → Bool) (i : Fin (Hᶜ).card) :
    i ∈ (scheduleDownEquiv H S).2 ↔ S ((Hᶜ).orderEmbOfFin rfl i) = false := by
  simp [scheduleDownEquiv, splitBoolEquiv, boolFunEquivFinset]

lemma scheduleDownEquiv_fst_eq {n : ℕ} (H : Finset (Fin n)) (S : Fin n → Bool) :
    (scheduleDownEquiv H S).1 = compressedDown H S := by
  ext i
  simp

lemma scheduleDownEquiv_snd_eq {n : ℕ} (H : Finset (Fin n)) (S : Fin n → Bool) :
    (scheduleDownEquiv H S).2 = compressedDown Hᶜ S := by
  ext i
  simp

/-- For a fixed horizontal/vertical schedule, both compressed coordinate walks stay nonnegative. -/
def AxisGood {n : ℕ} (H : Finset (Fin n)) (S : Fin n → Bool) : Prop :=
  IsMeander (scheduleDownEquiv H S).1 ∧ IsMeander (scheduleDownEquiv H S).2

lemma AxisGood.horizontal_prefix {n : ℕ} {H : Finset (Fin n)} {S : Fin n → Bool}
    (h : AxisGood H S) (t : ℕ) :
    2 * ((H.filter (fun x ↦ x.val < t)).filter (fun x ↦ S x = false)).card ≤
      (H.filter (fun x ↦ x.val < t)).card := by
  let q := (H.filter (fun x ↦ x.val < t)).card
  have hq : q ≤ H.card := Finset.card_filter_le _ _
  have hm := h.1 q hq
  rw [scheduleDownEquiv_fst_eq, downPrefix_compressedDown] at hm
  exact hm

lemma AxisGood.vertical_prefix {n : ℕ} {H : Finset (Fin n)} {S : Fin n → Bool}
    (h : AxisGood H S) (t : ℕ) :
    2 * (((Hᶜ).filter (fun x ↦ x.val < t)).filter (fun x ↦ S x = false)).card ≤
      ((Hᶜ).filter (fun x ↦ x.val < t)).card := by
  let q := ((Hᶜ).filter (fun x ↦ x.val < t)).card
  have hq : q ≤ (Hᶜ).card := Finset.card_filter_le _ _
  have hm := h.2 q hq
  rw [scheduleDownEquiv_snd_eq, downPrefix_compressedDown] at hm
  exact hm

/-- The good sign assignments in a fixed schedule factor exactly into two one-dimensional
meanders. -/
noncomputable def goodSignsEquivMeanders {n : ℕ} (H : Finset (Fin n)) :
    {S : Fin n → Bool // AxisGood H S} ≃
      MeanderPath H.card × MeanderPath (Hᶜ).card where
  toFun S := (⟨(scheduleDownEquiv H S.1).1, S.property.1⟩,
    ⟨(scheduleDownEquiv H S.1).2, S.property.2⟩)
  invFun D := ⟨(scheduleDownEquiv H).symm (D.1.1, D.2.1), by
    rw [AxisGood, (scheduleDownEquiv H).apply_symm_apply]
    exact ⟨D.1.property, D.2.property⟩⟩
  left_inv S := by
    apply Subtype.ext
    exact (scheduleDownEquiv H).symm_apply_apply S.1
  right_inv D := by
    apply Prod.ext <;> apply Subtype.ext
    · exact congrArg Prod.fst ((scheduleDownEquiv H).apply_symm_apply (D.1.1, D.2.1))
    · exact congrArg Prod.snd ((scheduleDownEquiv H).apply_symm_apply (D.1.1, D.2.1))

lemma card_goodSigns {n : ℕ} (H : Finset (Fin n)) :
    Fintype.card {S : Fin n → Bool // AxisGood H S} =
      Nat.choose H.card (H.card / 2) * Nat.choose (Hᶜ).card ((Hᶜ).card / 2) := by
  rw [Fintype.card_congr (goodSignsEquivMeanders H), Fintype.card_prod,
    card_meanderPath, card_meanderPath]

lemma card_schedule_add_compl {n : ℕ} (H : Finset (Fin n)) : H.card + (Hᶜ).card = n := by
  have hle : H.card ≤ n := by simpa using Finset.card_le_univ H
  rw [Finset.card_compl, Fintype.card_fin]
  omega

lemma card_goodSigns_ratio {n : ℕ} (H : Finset (Fin n)) :
    (Fintype.card {S : Fin n → Bool // AxisGood H S} : ℝ) / (2 : ℝ) ^ n =
      ballotMass H.card * ballotMass (Hᶜ).card := by
  rw [card_goodSigns, ballotMass, ballotMass]
  push_cast
  have hp : (2 : ℝ) ^ H.card * (2 : ℝ) ^ (Hᶜ).card = (2 : ℝ) ^ n := by
    rw [← pow_add, card_schedule_add_compl H]
  rw (occs := .pos [1]) [← hp]
  ring

lemma card_goodSigns_ratio_lower {n : ℕ} (H : Finset (Fin n)) :
    1 / (16 * ((n : ℝ) + 1)) ≤
      (Fintype.card {S : Fin n → Bool // AxisGood H S} : ℝ) / (2 : ℝ) ^ n := by
  rw [card_goodSigns_ratio]
  convert ballotMass_mul_lower H.card (Hᶜ).card using 1
  rw [card_schedule_add_compl]

/-- All good schedule/sign pairs of a fixed total length. -/
abbrev AxisGoodPath (n : ℕ) :=
  {p : Finset (Fin n) × (Fin n → Bool) // AxisGood p.1 p.2}

/-- Separate a good path into its schedule and its good sign assignment. -/
def axisGoodEquivSigma (n : ℕ) :
    AxisGoodPath n ≃ Σ H : Finset (Fin n), {S : Fin n → Bool // AxisGood H S} where
  toFun p := ⟨p.1.1, p.1.2, p.property⟩
  invFun p := ⟨(p.1, p.2.1), p.2.property⟩
  left_inv p := by rfl
  right_inv p := by cases p; rfl

lemma card_axisGoodPath (n : ℕ) :
    Fintype.card (AxisGoodPath n) =
      ∑ H : Finset (Fin n), Fintype.card {S : Fin n → Bool // AxisGood H S} := by
  rw [Fintype.card_congr (axisGoodEquivSigma n), Fintype.card_sigma]

/-- A uniformly chosen schedule/sign axis walk stays in the quadrant with probability at least an
absolute constant times `1/(n+1)`. -/
lemma card_axisGoodPath_ratio_lower (n : ℕ) :
    1 / (16 * ((n : ℝ) + 1)) ≤
      (Fintype.card (AxisGoodPath n) : ℝ) / (4 : ℝ) ^ n := by
  let c : ℝ := 1 / (16 * ((n : ℝ) + 1))
  let P : ℝ := (2 : ℝ) ^ n
  have hpoint (H : Finset (Fin n)) : c ≤
      (Fintype.card {S : Fin n → Bool // AxisGood H S} : ℝ) / P :=
    card_goodSigns_ratio_lower H
  have hsum : (∑ H : Finset (Fin n), c) ≤
      ∑ H : Finset (Fin n),
        (Fintype.card {S : Fin n → Bool // AxisGood H S} : ℝ) / P := by
    exact Finset.sum_le_sum fun H hH ↦ hpoint H
  have hschedules : Fintype.card (Finset (Fin n)) = 2 ^ n := by
    rw [Fintype.card_finset, Fintype.card_fin]
  have hcard : (Fintype.card (AxisGoodPath n) : ℝ) =
      ∑ H : Finset (Fin n),
        (Fintype.card {S : Fin n → Bool // AxisGood H S} : ℝ) := by
    exact_mod_cast card_axisGoodPath n
  have hsum' : P * c ≤ (Fintype.card (AxisGoodPath n) : ℝ) / P := by
    rw [Finset.sum_const, Finset.card_univ, hschedules, nsmul_eq_mul] at hsum
    push_cast at hsum
    rw [← Finset.sum_div, ← hcard] at hsum
    simpa [P, mul_comm] using hsum
  have hP : 0 < P := by positivity
  have hp4 : (4 : ℝ) ^ n = P * P := by
    rw [show (4 : ℝ) = 2 * 2 by norm_num, mul_pow]
  change c ≤ (Fintype.card (AxisGoodPath n) : ℝ) / (4 : ℝ) ^ n
  rw [hp4]
  calc
    c = (P * c) / P := by field_simp
    _ ≤ ((Fintype.card (AxisGoodPath n) : ℝ) / P) / P := by
      exact div_le_div_of_nonneg_right hsum' hP.le
    _ = (Fintype.card (AxisGoodPath n) : ℝ) / (P * P) := by ring

end Erdos521
