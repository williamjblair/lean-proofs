import Research.AxisBallot
import Research.FairPrefix
import Research.RecordProbability
import Research.RademacherRecurrence
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Analysis.PSeries
import Mathlib.Tactic

open Filter MeasureTheory Set
open scoped BigOperators

namespace Erdos521

noncomputable local instance (p : Prop) : Decidable p := Classical.propDecidable p

/-- Pair coordinate `j=0` is the even coefficient and `j=1` the odd coefficient. -/
def pairIndexEquiv (n : ℕ) : Fin n × Fin 2 ≃ Fin (2 * n) :=
  finProdFinEquiv.trans (Fin.castOrderIso (Nat.mul_comm n 2)).toEquiv

/-- Curry two Boolean coordinates at each time into a Boolean pair. -/
def uncurryPairBitsEquiv (n : ℕ) :
    (Fin n × Fin 2 → Bool) ≃ (Fin n → Bool × Bool) where
  toFun f i := (f (i, 0), f (i, 1))
  invFun f ij := Fin.cases (f ij.1).1 (fun _ ↦ (f ij.1).2) ij.2
  left_inv f := by
    funext ij
    rcases ij with ⟨i, j⟩
    fin_cases j <;> rfl
  right_inv f := by
    funext i
    apply Prod.ext <;> rfl

/-- Split a `2n`-bit prefix into its chronological `(even,odd)` coefficient pairs. -/
def bitsEquivPairs (n : ℕ) :
    (Fin (2 * n) → Bool) ≃ (Fin n → Bool × Bool) :=
  (Equiv.piCongrLeft (fun _ : Fin (2 * n) ↦ Bool) (pairIndexEquiv n)).symm.trans
    (uncurryPairBitsEquiv n)

lemma bitsEquivPairs_fst {n : ℕ} (x : Fin (2 * n) → Bool) (i : Fin n) :
    (bitsEquivPairs n x i).1 = x ⟨2 * i.val, by omega⟩ := by
  simp [bitsEquivPairs, uncurryPairBitsEquiv, pairIndexEquiv, finProdFinEquiv]

lemma bitsEquivPairs_snd {n : ℕ} (x : Fin (2 * n) → Bool) (i : Fin n) :
    (bitsEquivPairs n x i).2 = x ⟨2 * i.val + 1, by omega⟩ := by
  simp [bitsEquivPairs, uncurryPairBitsEquiv, pairIndexEquiv, finProdFinEquiv]
  congr 1
  apply Fin.ext
  simp [finProdFinEquiv]
  omega

/-- Reversal of a finite index set. -/
def finRevEquiv (n : ℕ) : Fin n ≃ Fin n where
  toFun := Fin.rev
  invFun := Fin.rev
  left_inv := Fin.rev_rev
  right_inv := Fin.rev_rev

/-- Reverse a finite function. -/
def reverseFunEquiv (n : ℕ) (α : Type*) : (Fin n → α) ≃ (Fin n → α) where
  toFun f i := f i.rev
  invFun f i := f i.rev
  left_inv f := by
    funext i
    change f i.rev.rev = f i
    rw [Fin.rev_rev]
  right_inv f := by
    funext i
    change f i.rev.rev = f i
    rw [Fin.rev_rev]

@[simp] lemma reverseFunEquiv_apply {n : ℕ} {α : Type*} (f : Fin n → α) (i : Fin n) :
    reverseFunEquiv n α f i = f i.rev := rfl

/-- A coefficient pair `(even,odd)` is bijectively encoded by `(vertical?, sign)`: the transformed
axis step is horizontal exactly when `vertical? = false`, and its sign is the odd coefficient. -/
def coefficientPairAxisEquiv : (Bool × Bool) ≃ (Bool × Bool) where
  toFun p := (Bool.xor p.1 p.2, p.2)
  invFun p := (Bool.xor p.1 p.2, p.2)
  left_inv p := by rcases p with ⟨a, b⟩; cases a <;> cases b <;> rfl
  right_inv p := by rcases p with ⟨a, b⟩; cases a <;> cases b <;> rfl

/-- Transpose a function of pairs into a pair of functions. -/
def pairFunctionsEquiv (n : ℕ) :
    (Fin n → Bool × Bool) ≃ ((Fin n → Bool) × (Fin n → Bool)) where
  toFun f := (fun i ↦ (f i).1, fun i ↦ (f i).2)
  invFun f i := (f.1 i, f.2 i)
  left_inv f := by
    funext i
    exact Prod.eta (f i)
  right_inv f := by rfl

/-- Exact bijection from a `2n`-coefficient prefix to a reversed axis schedule and sign sequence. -/
def bitsAxisEquiv (n : ℕ) :
    (Fin (2 * n) → Bool) ≃ (Finset (Fin n) × (Fin n → Bool)) :=
  (bitsEquivPairs n).trans <|
    (reverseFunEquiv n (Bool × Bool)).trans <|
      (Equiv.piCongrRight (fun _ ↦ coefficientPairAxisEquiv)).trans <|
        (pairFunctionsEquiv n).trans <|
          Equiv.prodCongr (boolFunEquivFinset (Fin n)) (Equiv.refl _)

lemma bitsAxisEquiv_sign {n : ℕ} (x : Fin (2 * n) → Bool) (j : Fin n) :
    (bitsAxisEquiv n x).2 j =
      x ⟨2 * j.rev.val + 1, by omega⟩ := by
  change (reverseFunEquiv n (Bool × Bool) (bitsEquivPairs n x) j).2 = _
  rw [reverseFunEquiv_apply, bitsEquivPairs_snd]

lemma bitsAxisEquiv_schedule {n : ℕ} (x : Fin (2 * n) → Bool) (j : Fin n) :
    j ∈ (bitsAxisEquiv n x).1 ↔
      x ⟨2 * j.rev.val, by omega⟩ = x ⟨2 * j.rev.val + 1, by omega⟩ := by
  simp [bitsAxisEquiv, pairFunctionsEquiv, coefficientPairAxisEquiv,
    boolFunEquivFinset, reverseFunEquiv]
  rw [bitsEquivPairs_fst, bitsEquivPairs_snd]
  constructor <;> intro h
  · simpa [Fin.rev] using h
  · simpa [Fin.rev] using h

/-- Extend a finite Boolean prefix by `false` outside its range. -/
def extendBits (n : ℕ) (x : Fin (2 * n) → Bool) : ℕ → Bool :=
  fun k ↦ if h : k < 2 * n then x ⟨k, h⟩ else false

lemma extendBits_of_lt {n k : ℕ} (x : Fin (2 * n) → Bool) (hk : k < 2 * n) :
    extendBits n x k = x ⟨k, hk⟩ := by
  simp [extendBits, hk]

/-- Linear map sending the cone `u ≥ |v|` to the closed first quadrant. -/
def coneTransform (z : ℝ × ℝ) : ℝ × ℝ := (z.1 + z.2, z.1 - z.2)

/-- Axis step encoded by a horizontal schedule and a sign. -/
def finiteAxisIncrement {n : ℕ} (H : Finset (Fin n)) (S : Fin n → Bool)
    (j : Fin n) : ℝ × ℝ :=
  if j ∈ H then (2 * sign (S j), 0) else (0, 2 * sign (S j))

lemma sign_add_eq_zero_of_ne (a b : Bool) (h : a ≠ b) : sign b + sign a = 0 := by
  cases a <;> cases b <;> simp_all [sign]

lemma sign_sub_eq_two_mul_of_ne (a b : Bool) (h : a ≠ b) :
    sign b - sign a = 2 * sign b := by
  cases a <;> cases b <;> simp_all [sign] <;> norm_num

lemma sum_sign_eq_card_sub_false {α : Type*} [DecidableEq α]
    (A : Finset α) (S : α → Bool) :
    (∑ i ∈ A, sign (S i)) =
      (A.card : ℝ) - 2 * ((A.filter (fun i ↦ S i = false)).card : ℝ) := by
  have hpoint (i : α) : sign (S i) =
      1 - 2 * (if S i = false then (1 : ℝ) else 0) := by
    cases S i <;> norm_num [sign]
  calc
    (∑ i ∈ A, sign (S i)) =
        ∑ i ∈ A, (1 - 2 * (if S i = false then (1 : ℝ) else 0)) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact hpoint i
    _ = (A.card : ℝ) - 2 *
        ((A.filter (fun i ↦ S i = false)).card : ℝ) := by
      have hfalse : (∑ i ∈ A, if S i = false then (1 : ℝ) else 0) =
          ((A.filter (fun i ↦ S i = false)).card : ℝ) := by
        rw [← Finset.sum_filter]
        simp
      rw [Finset.sum_sub_distrib]
      simp only [Finset.sum_const, nsmul_eq_mul, Nat.cast_ofNat, one_mul]
      rw [← Finset.mul_sum, hfalse]
      ring

/-- Position of the finite encoded axis walk after the first `t` reversed pairs. -/
def finiteAxisWalk {n : ℕ} (H : Finset (Fin n)) (S : Fin n → Bool) (t : ℕ) : ℝ × ℝ :=
  ∑ j ∈ pathPrefix n t, finiteAxisIncrement H S j

lemma finiteAxisWalk_fst {n : ℕ} (H : Finset (Fin n)) (S : Fin n → Bool) (t : ℕ) :
    (finiteAxisWalk H S t).1 =
      2 * ∑ j ∈ H.filter (fun j ↦ j.val < t), sign (S j) := by
  change (AddMonoidHom.fst ℝ ℝ)
      (∑ j ∈ pathPrefix n t, finiteAxisIncrement H S j) = _
  rw [map_sum]
  simp only [finiteAxisIncrement, apply_ite]
  change (∑ j ∈ pathPrefix n t, if j ∈ H then 2 * sign (S j) else 0) = _
  rw [← Finset.sum_filter, ← Finset.mul_sum]
  congr 1
  apply Finset.sum_congr
  · ext j
    simp [and_comm]
  · intro j hj
    ring

lemma finiteAxisWalk_snd {n : ℕ} (H : Finset (Fin n)) (S : Fin n → Bool) (t : ℕ) :
    (finiteAxisWalk H S t).2 =
      2 * ∑ j ∈ (Hᶜ).filter (fun j ↦ j.val < t), sign (S j) := by
  change (AddMonoidHom.snd ℝ ℝ)
      (∑ j ∈ pathPrefix n t, finiteAxisIncrement H S j) = _
  rw [map_sum]
  simp only [finiteAxisIncrement, apply_ite]
  change (∑ j ∈ pathPrefix n t, if j ∈ H then 0 else 2 * sign (S j)) = _
  have hrewrite : (∑ j ∈ pathPrefix n t, if j ∈ H then 0 else 2 * sign (S j)) =
      ∑ j ∈ pathPrefix n t, if j ∈ Hᶜ then 2 * sign (S j) else 0 := by
    apply Finset.sum_congr rfl
    intro j hj
    by_cases hH : j ∈ H <;> simp [hH]
  rw [hrewrite, ← Finset.sum_filter, ← Finset.mul_sum]
  congr 1
  apply Finset.sum_congr
  · ext j
    simp [and_comm]
  · intro j hj
    ring

lemma coneTransform_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ × ℝ) :
    coneTransform (∑ i ∈ s, f i) = ∑ i ∈ s, coneTransform (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [coneTransform]
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih]
      ext <;> simp [coneTransform] <;> ring

lemma inCone_of_coneTransform_nonneg {z : ℝ × ℝ}
    (h₁ : 0 ≤ (coneTransform z).1) (h₂ : 0 ≤ (coneTransform z).2) : InCone z := by
  rw [InCone, abs_le]
  change -z.1 ≤ z.2 ∧ z.2 ≤ z.1
  change 0 ≤ z.1 + z.2 at h₁
  change 0 ≤ z.1 - z.2 at h₂
  constructor <;> linarith

lemma AxisGood.finiteAxisWalk_nonneg {n : ℕ} {H : Finset (Fin n)} {S : Fin n → Bool}
    (h : AxisGood H S) (t : ℕ) :
    0 ≤ (finiteAxisWalk H S t).1 ∧ 0 ≤ (finiteAxisWalk H S t).2 := by
  let A := H.filter (fun j ↦ j.val < t)
  let B := (Hᶜ).filter (fun j ↦ j.val < t)
  have hA := h.horizontal_prefix t
  have hB := h.vertical_prefix t
  have hAR : 2 * ((A.filter (fun j ↦ S j = false)).card : ℝ) ≤ (A.card : ℝ) := by
    exact_mod_cast hA
  have hBR : 2 * ((B.filter (fun j ↦ S j = false)).card : ℝ) ≤ (B.card : ℝ) := by
    exact_mod_cast hB
  constructor
  · rw [finiteAxisWalk_fst, sum_sign_eq_card_sub_false]
    change 0 ≤ 2 * ((A.card : ℝ) - 2 * ((A.filter (fun j ↦ S j = false)).card : ℝ))
    nlinarith
  · rw [finiteAxisWalk_snd, sum_sign_eq_card_sub_false]
    change 0 ≤ 2 * ((B.card : ℝ) - 2 * ((B.filter (fun j ↦ S j = false)).card : ℝ))
    nlinarith

/-- The reversed transformed paired Rademacher increment is exactly the encoded axis step. -/
lemma coneTransform_rademacherIncrement {n : ℕ} (x : Fin (2 * n) → Bool) (j : Fin n) :
    coneTransform (rademacherIncrement (extendBits n x) j.rev.val) =
      finiteAxisIncrement (bitsAxisEquiv n x).1 (bitsAxisEquiv n x).2 j := by
  let a := x ⟨2 * j.rev.val, by omega⟩
  let b := x ⟨2 * j.rev.val + 1, by omega⟩
  have heven : extendBits n x (2 * j.rev.val) = a := extendBits_of_lt x (by omega)
  have hodd : extendBits n x (2 * j.rev.val + 1) = b := extendBits_of_lt x (by omega)
  have hsign : (bitsAxisEquiv n x).2 j = b := bitsAxisEquiv_sign x j
  have hschedule : j ∈ (bitsAxisEquiv n x).1 ↔ a = b := bitsAxisEquiv_schedule x j
  by_cases hj : j ∈ (bitsAxisEquiv n x).1
  · have heq : a = b := hschedule.mp hj
    rw [heq] at heven
    rw [finiteAxisIncrement, if_pos hj, hsign,
      rademacherIncrement, coneTransform, heven, hodd]
    ext <;> dsimp <;> ring
  · have hne : a ≠ b := fun h ↦ hj (hschedule.mpr h)
    have hsum : sign b + sign a = 0 := sign_add_eq_zero_of_ne a b hne
    have hdiff : sign b - sign a = 2 * sign b := sign_sub_eq_two_mul_of_ne a b hne
    rw [finiteAxisIncrement, if_neg hj, hsign,
      rademacherIncrement, coneTransform, heven, hodd]
    ext <;> dsimp
    · exact hsum
    · exact hdiff

lemma coneTransform_reverse_sum_eq_axisWalk {n t : ℕ} (x : Fin (2 * n) → Bool)
    (ht : t ≤ n) :
    coneTransform
        (∑ i ∈ Finset.range t, rademacherIncrement (extendBits n x) (n - 1 - i)) =
      finiteAxisWalk (bitsAxisEquiv n x).1 (bitsAxisEquiv n x).2 t := by
  rw [coneTransform_sum, finiteAxisWalk]
  refine Finset.sum_bij (fun i hi ↦ (⟨i, by
      have hit : i < t := Finset.mem_range.mp hi
      omega⟩ : Fin n)) ?_ ?_ ?_ ?_
  · intro i hi
    simp only [mem_pathPrefix]
    exact Finset.mem_range.mp hi
  · intro i₁ hi₁ i₂ hi₂ heq
    exact Fin.ext_iff.mp heq
  · intro j hj
    refine ⟨j.val, Finset.mem_range.mpr (mem_pathPrefix.mp hj), ?_⟩
    exact Fin.ext rfl
  · intro i hi
    let j : Fin n := ⟨i, by
      have hit : i < t := Finset.mem_range.mp hi
      omega⟩
    have hrev : j.rev.val = n - 1 - i := by
      simp [j, Fin.rev]
      omega
    rw [← hrev]
    exact coneTransform_rademacherIncrement x j

/-- Every finitely encoded axis-good path gives a cone record for its extended coefficient
sequence. -/
lemma axisGood_implies_coneRecord {n : ℕ} (x : Fin (2 * n) → Bool)
    (hgood : AxisGood (bitsAxisEquiv n x).1 (bitsAxisEquiv n x).2) :
    IsConeRecord (rademacherIncrement (extendBits n x)) n := by
  intro k hkn
  let t := n - k
  have htpos : 0 < t := by omega
  have htle : t ≤ n := by omega
  let m := n - 1
  let r := t - 1
  have hrm : r ≤ m := by omega
  have hwalk := walk_sub_eq_reverse_suffix
    (rademacherIncrement (extendBits n x)) (m := m) (r := r) hrm
  have hmn : m + 1 = n := by omega
  have hmk : m - r = k := by omega
  have hrt : r + 1 = t := by omega
  rw [hmn, hmk, hrt] at hwalk
  rw [hwalk]
  apply inCone_of_coneTransform_nonneg
  · rw [coneTransform_reverse_sum_eq_axisWalk x htle]
    exact (hgood.finiteAxisWalk_nonneg t).1
  · rw [coneTransform_reverse_sum_eq_axisWalk x htle]
    exact (hgood.finiteAxisWalk_nonneg t).2

/-- View a `Fin (2n)` Boolean assignment as an assignment on the coordinate finset
`range (2n)`. -/
def bitsToRangePrefix {n : ℕ} (x : Fin (2 * n) → Bool) :
    (Finset.range (2 * n) : Finset ℕ) → Bool :=
  fun i ↦ x ⟨i.val, Finset.mem_range.mp i.property⟩

lemma bitsToRangePrefix_injective {n : ℕ} : Function.Injective (@bitsToRangePrefix n) := by
  intro x y h
  funext i
  have hi := congrFun h (⟨i.val, Finset.mem_range.mpr i.isLt⟩ :
    (Finset.range (2 * n) : Finset ℕ))
  exact hi

/-- Prefix assignment produced by a good schedule/sign path. -/
noncomputable def axisGoodPrefixMap (n : ℕ) :
    AxisGoodPath n → ((Finset.range (2 * n) : Finset ℕ) → Bool) :=
  fun p ↦ bitsToRangePrefix ((bitsAxisEquiv n).symm p.1)

lemma axisGoodPrefixMap_injective (n : ℕ) : Function.Injective (axisGoodPrefixMap n) := by
  intro p q hpq
  apply Subtype.ext
  apply (bitsAxisEquiv n).symm.injective
  exact bitsToRangePrefix_injective hpq

lemma axisGoodPrefixMap_mem_recordImage {n : ℕ} (p : AxisGoodPath n) :
    axisGoodPrefixMap n p ∈
      (fun (ω : ℕ → Bool) (i : (Finset.range (2 * n) : Finset ℕ)) ↦ ω i) ''
        coneRecordEvent n := by
  let x := (bitsAxisEquiv n).symm p.1
  refine ⟨extendBits n x, ?_, ?_⟩
  · exact axisGood_implies_coneRecord x (by
      simpa [x] using p.property)
  · funext i
    change extendBits n x i.val = x ⟨i.val, Finset.mem_range.mp i.property⟩
    exact extendBits_of_lt x (Finset.mem_range.mp i.property)

lemma coneRecordEvent_eq_prefix_preimage (n : ℕ) :
    coneRecordEvent n =
      (fun (ω : ℕ → Bool) (i : (Finset.range (2 * n) : Finset ℕ)) ↦ ω i) ⁻¹'
        ((fun (ω : ℕ → Bool) (i : (Finset.range (2 * n) : Finset ℕ)) ↦ ω i) ''
          coneRecordEvent n) := by
  let S := Finset.range (2 * n)
  let f : (ℕ → Bool) → (S → Bool) := fun ω i ↦ ω i
  let E : Set (S → Bool) := f '' coneRecordEvent n
  change coneRecordEvent n = f ⁻¹' E
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

lemma card_recordPrefixImage_lower (n : ℕ) :
    Fintype.card (AxisGoodPath n) ≤
      ((fun (ω : ℕ → Bool) (i : (Finset.range (2 * n) : Finset ℕ)) ↦ ω i) ''
        coneRecordEvent n).ncard := by
  let f := axisGoodPrefixMap n
  let E := (fun (ω : ℕ → Bool) (i : (Finset.range (2 * n) : Finset ℕ)) ↦ ω i) ''
    coneRecordEvent n
  have hsub : f '' (Set.univ : Set (AxisGoodPath n)) ⊆ E := by
    rintro y ⟨p, hp, rfl⟩
    exact axisGoodPrefixMap_mem_recordImage p
  have hcard := Set.ncard_le_ncard hsub (Set.toFinite E)
  rw [Set.ncard_image_of_injective _ (axisGoodPrefixMap_injective n),
    Set.ncard_univ, Nat.card_eq_fintype_card] at hcard
  exact hcard

lemma coneRecordProbability_eq_prefixCard (n : ℕ) :
    coneRecordProbability n =
      (((fun (ω : ℕ → Bool) (i : (Finset.range (2 * n) : Finset ℕ)) ↦ ω i) ''
        coneRecordEvent n).ncard : ℝ) / (4 : ℝ) ^ n := by
  let S := Finset.range (2 * n)
  let E : Set (S → Bool) :=
    (fun (ω : ℕ → Bool) (i : S) ↦ ω i) '' coneRecordEvent n
  have hm := rademacherMeasure_prefix_preimage S E
  rw [← coneRecordEvent_eq_prefix_preimage n] at hm
  rw [coneRecordProbability, Measure.real, hm]
  rw [ENNReal.toReal_div, ENNReal.toReal_natCast, ENNReal.toReal_natCast]
  change (E.ncard : ℝ) / ((2 ^ S.card : ℕ) : ℝ) = (E.ncard : ℝ) / (4 : ℝ) ^ n
  rw [show S.card = 2 * n by simp [S]]
  congr 1
  push_cast
  rw [pow_mul]
  norm_num

/-- Concrete inverse-linear lower bound for paired Rademacher cone-record probabilities. -/
lemma coneRecordProbability_lower (n : ℕ) :
    1 / (16 * ((n : ℝ) + 1)) ≤ coneRecordProbability n := by
  rw [coneRecordProbability_eq_prefixCard]
  have hc := card_recordPrefixImage_lower n
  have hcR : (Fintype.card (AxisGoodPath n) : ℝ) ≤
      (((fun (ω : ℕ → Bool) (i : (Finset.range (2 * n) : Finset ℕ)) ↦ ω i) ''
        coneRecordEvent n).ncard : ℝ) := by exact_mod_cast hc
  exact (card_axisGoodPath_ratio_lower n).trans
    (div_le_div_of_nonneg_right hcR (by positivity))

lemma coneRecordPartialSums_tendsto_atTop :
    Tendsto (fun N ↦ ∑ i ∈ Finset.range (N + 1), coneRecordProbability i)
      atTop atTop := by
  let lower := fun N : ℕ ↦ (1 / 16 : ℝ) *
    ∑ i ∈ Finset.range (N + 1), (1 / ((i : ℝ) + 1))
  have hlower : Tendsto lower atTop atTop := by
    apply Filter.Tendsto.const_mul_atTop (by norm_num : (0 : ℝ) < 1 / 16)
    change Tendsto
      ((fun n : ℕ ↦ ∑ i ∈ Finset.range n, (1 / ((i : ℝ) + 1))) ∘
        (fun N : ℕ ↦ N + 1)) atTop atTop
    exact Real.tendsto_sum_range_one_div_nat_succ_atTop.comp
      (tendsto_add_atTop_nat 1)
  apply tendsto_atTop_mono (f := lower) (g := fun N ↦
    ∑ i ∈ Finset.range (N + 1), coneRecordProbability i) ?_ hlower
  intro N
  dsimp [lower]
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  have h := coneRecordProbability_lower i
  calc
    (1 / 16 : ℝ) * (1 / ((i : ℝ) + 1)) = 1 / (16 * ((i : ℝ) + 1)) :=
      one_div_mul_one_div 16 ((i : ℝ) + 1)
    _ ≤ coneRecordProbability i := h

/-- The paired Rademacher walk has arbitrarily large cone records on a set of positive product
measure. -/
theorem positive_infinitelyOftenConeRecords :
    0 < rademacherMeasure {ω | InfinitelyOftenConeRecords ω} :=
  positive_infinitelyOftenConeRecords_of_divergence coneRecordPartialSums_tendsto_atTop

end Erdos521
