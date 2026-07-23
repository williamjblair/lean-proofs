import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic

open scoped BigOperators symmDiff

namespace Erdos521

noncomputable local instance (p : Prop) : Decidable p := Classical.propDecidable p

/-- The first `t` locations in a length-`n` path. -/
def pathPrefix (n t : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun i ↦ i.val < t)

@[simp] lemma mem_pathPrefix {n t : ℕ} {i : Fin n} :
    i ∈ pathPrefix n t ↔ i.val < t := by
  simp [pathPrefix]

lemma pathPrefix_card {n t : ℕ} (ht : t ≤ n) : (pathPrefix n t).card = t := by
  by_cases htn : t < n
  · let x : Fin n := ⟨t, htn⟩
    have heq : pathPrefix n t = Finset.Iio x := by
      ext i
      simp only [mem_pathPrefix, Finset.mem_Iio]
      change i.val < t ↔ i.val < x.val
      rfl
    rw [heq, Fin.card_Iio]
  · have htn' : t = n := by omega
    subst t
    simp [pathPrefix]

/-- A finite subset records the down-step locations; this counts downs before time `t`. -/
def downPrefix {n : ℕ} (D : Finset (Fin n)) (t : ℕ) : ℕ :=
  (D ∩ pathPrefix n t).card

lemma downPrefix_le_card {n : ℕ} (D : Finset (Fin n)) (t : ℕ) :
    downPrefix D t ≤ D.card := by
  exact Finset.card_le_card Finset.inter_subset_left

lemma downPrefix_le_time {n : ℕ} (D : Finset (Fin n)) {t : ℕ} (ht : t ≤ n) :
    downPrefix D t ≤ t := by
  calc
    downPrefix D t = (D ∩ pathPrefix n t).card := rfl
    _ ≤ (pathPrefix n t).card := Finset.card_le_card Finset.inter_subset_right
    _ = t := pathPrefix_card ht

lemma downPrefix_succ {n : ℕ} (D : Finset (Fin n)) {t : ℕ} (ht : t < n) :
    downPrefix D (t + 1) = downPrefix D t + if (⟨t, ht⟩ : Fin n) ∈ D then 1 else 0 := by
  let x : Fin n := ⟨t, ht⟩
  have heq : D ∩ pathPrefix n (t + 1) =
      if x ∈ D then insert x (D ∩ pathPrefix n t) else D ∩ pathPrefix n t := by
    ext i
    simp only [Finset.mem_inter, mem_pathPrefix]
    by_cases hx : x ∈ D
    · rw [if_pos hx]
      simp only [Finset.mem_insert]
      by_cases hiD : i ∈ D
      · by_cases hix : i = x
        · subst i
          simp [hx, x]
        · have hval : i.val ≠ t := by
            intro hv
            apply hix
            apply Fin.ext
            exact hv
          simp [hiD, hix]
          omega
      · have hix : i ≠ x := by
          intro h
          subst i
          exact hiD hx
        simp [hiD, hix]
    · rw [if_neg hx]
      by_cases hiD : i ∈ D
      · have hix : i ≠ x := by
          intro h
          subst i
          exact hx hiD
        have hval : i.val ≠ t := by
          intro hv
          apply hix
          apply Fin.ext
          exact hv
        simp [hiD]
        omega
      · simp [hiD]
  rw [downPrefix, downPrefix, heq]
  split_ifs with hx
  · rw [Finset.card_insert_of_notMem]
    simp [x]
  · rfl

lemma downPrefix_succ_le {n : ℕ} (D : Finset (Fin n)) {t : ℕ} (ht : t < n) :
    downPrefix D (t + 1) ≤ downPrefix D t + 1 := by
  rw [downPrefix_succ D ht]
  split_ifs <;> omega

lemma downPrefix_le_succ {n : ℕ} (D : Finset (Fin n)) {t : ℕ} (ht : t < n) :
    downPrefix D t ≤ downPrefix D (t + 1) := by
  rw [downPrefix_succ D ht]
  split_ifs <;> omega

lemma downPrefix_length {n : ℕ} (D : Finset (Fin n)) : downPrefix D n = D.card := by
  have hp : pathPrefix n n = Finset.univ := by
    ext i
    simp
  simp [downPrefix, hp]

/-- Flip every step before time `t`. -/
def flipPrefix {n : ℕ} (D : Finset (Fin n)) (t : ℕ) : Finset (Fin n) :=
  D ∆ pathPrefix n t

@[simp] lemma mem_flipPrefix {n : ℕ} {D : Finset (Fin n)} {t : ℕ} {i : Fin n} :
    i ∈ flipPrefix D t ↔ (i ∈ D) ≠ (i.val < t) := by
  simp only [flipPrefix, Finset.mem_symmDiff, mem_pathPrefix]
  tauto

lemma flipPrefix_involutive {n : ℕ} (D : Finset (Fin n)) (t : ℕ) :
    flipPrefix (flipPrefix D t) t = D := by
  ext i
  rw [mem_flipPrefix, mem_flipPrefix]
  tauto

lemma downPrefix_flipPrefix_of_le {n : ℕ} (D : Finset (Fin n)) {u t : ℕ}
    (hu : u ≤ n) (hut : u ≤ t) :
    downPrefix (flipPrefix D t) u = u - downPrefix D u := by
  have heq : flipPrefix D t ∩ pathPrefix n u = pathPrefix n u \ D := by
    ext i
    simp only [Finset.mem_inter, mem_flipPrefix, mem_pathPrefix, Finset.mem_sdiff]
    by_cases hiD : i ∈ D <;> simp [hiD] <;> omega
  rw [downPrefix, heq, Finset.card_sdiff, pathPrefix_card hu]
  congr 1

lemma card_flipPrefix {n : ℕ} (D : Finset (Fin n)) {t : ℕ} (ht : t ≤ n) :
    (flipPrefix D t).card = D.card + t - 2 * downPrefix D t := by
  have hdis : Disjoint (D \ pathPrefix n t) (pathPrefix n t \ D) := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    have hi' := Finset.mem_sdiff.mp hi
    have hj' := Finset.mem_sdiff.mp hj
    exact hi'.2 hj'.1
  rw [flipPrefix, Finset.symmDiff_def, Finset.card_union_of_disjoint hdis,
    Finset.card_sdiff, Finset.card_sdiff, pathPrefix_card ht]
  have h1 := downPrefix_le_card D t
  have h2 := downPrefix_le_time D ht
  simp only [downPrefix] at h1 h2 ⊢
  rw [Finset.inter_comm (pathPrefix n t) D]
  omega

/-- A down-step set is a nonnegative one-dimensional meander when every prefix has at most as
many down steps as up steps. -/
def IsMeander {n : ℕ} (D : Finset (Fin n)) : Prop :=
  ∀ t ≤ n, 2 * downPrefix D t ≤ t

/-- The endpoint is nonnegative. -/
def EndpointNonnegative {n : ℕ} (D : Finset (Fin n)) : Prop :=
  2 * D.card ≤ n

/-- The endpoint lies at least two units above the parity-minimal nonnegative endpoint. -/
def EndpointMargin {n : ℕ} (D : Finset (Fin n)) : Prop :=
  2 * (D.card + 1) ≤ n

abbrev BadEndpointPath (n : ℕ) :=
  {D : Finset (Fin n) // EndpointNonnegative D ∧ ¬ IsMeander D}

abbrev MarginPath (n : ℕ) :=
  {D : Finset (Fin n) // EndpointMargin D}

lemma IsMeander.endpointNonnegative {n : ℕ} {D : Finset (Fin n)}
    (h : IsMeander D) : EndpointNonnegative D := by
  have := h n le_rfl
  rwa [downPrefix_length] at this

lemma badEndpoint_exists_crossing {n : ℕ} (D : BadEndpointPath n) :
    ∃ t, t ≤ n ∧ t < 2 * downPrefix D.1 t := by
  have hnot := D.property.2
  rw [IsMeander] at hnot
  push_neg at hnot
  obtain ⟨t, htn, hbad⟩ := hnot
  exact ⟨t, htn, hbad⟩

noncomputable def firstBadCrossing {n : ℕ} (D : BadEndpointPath n) : ℕ :=
  Nat.find (badEndpoint_exists_crossing D)

lemma firstBadCrossing_spec {n : ℕ} (D : BadEndpointPath n) :
    firstBadCrossing D ≤ n ∧
      firstBadCrossing D < 2 * downPrefix D.1 (firstBadCrossing D) :=
  Nat.find_spec (badEndpoint_exists_crossing D)

lemma firstBadCrossing_min {n : ℕ} (D : BadEndpointPath n) {t : ℕ}
    (ht : t < firstBadCrossing D) :
    ¬(t ≤ n ∧ t < 2 * downPrefix D.1 t) :=
  Nat.find_min (badEndpoint_exists_crossing D) ht

lemma firstBadCrossing_pos {n : ℕ} (D : BadEndpointPath n) :
    0 < firstBadCrossing D := by
  have hs := (firstBadCrossing_spec D).2
  have hz : downPrefix D.1 0 = 0 := by simp [downPrefix, pathPrefix]
  by_contra h
  have heq : firstBadCrossing D = 0 := Nat.eq_zero_of_not_pos h
  rw [heq, hz] at hs
  omega

lemma firstBadCrossing_exact {n : ℕ} (D : BadEndpointPath n) :
    2 * downPrefix D.1 (firstBadCrossing D) = firstBadCrossing D + 1 := by
  let t := firstBadCrossing D
  have htpos : 0 < t := firstBadCrossing_pos D
  have htle : t ≤ n := (firstBadCrossing_spec D).1
  have hbad : t < 2 * downPrefix D.1 t := (firstBadCrossing_spec D).2
  have hpredlt : t - 1 < t := by omega
  have hpredn : t - 1 ≤ n := by omega
  have hsafe := firstBadCrossing_min D hpredlt
  have hpredsafe : 2 * downPrefix D.1 (t - 1) ≤ t - 1 := by
    by_contra h
    apply hsafe
    exact ⟨hpredn, by omega⟩
  have hstep : downPrefix D.1 t ≤ downPrefix D.1 (t - 1) + 1 := by
    have hlt : t - 1 < n := by omega
    have hs := downPrefix_succ_le D.1 hlt
    have heq : t - 1 + 1 = t := by omega
    rw [heq] at hs
    exact hs
  change 2 * downPrefix D.1 t = t + 1
  omega

lemma margin_exists_crossing {n : ℕ} (D : MarginPath n) :
    ∃ t, t ≤ n ∧ 2 * downPrefix D.1 t < t := by
  refine ⟨n, le_rfl, ?_⟩
  rw [downPrefix_length]
  exact lt_of_lt_of_le (by omega) D.property

noncomputable def firstGoodCrossing {n : ℕ} (D : MarginPath n) : ℕ :=
  Nat.find (margin_exists_crossing D)

lemma firstGoodCrossing_spec {n : ℕ} (D : MarginPath n) :
    firstGoodCrossing D ≤ n ∧
      2 * downPrefix D.1 (firstGoodCrossing D) < firstGoodCrossing D :=
  Nat.find_spec (margin_exists_crossing D)

lemma firstGoodCrossing_min {n : ℕ} (D : MarginPath n) {t : ℕ}
    (ht : t < firstGoodCrossing D) :
    ¬(t ≤ n ∧ 2 * downPrefix D.1 t < t) :=
  Nat.find_min (margin_exists_crossing D) ht

lemma firstGoodCrossing_pos {n : ℕ} (D : MarginPath n) :
    0 < firstGoodCrossing D := by
  have hs := (firstGoodCrossing_spec D).2
  omega

lemma firstGoodCrossing_exact {n : ℕ} (D : MarginPath n) :
    firstGoodCrossing D = 2 * downPrefix D.1 (firstGoodCrossing D) + 1 := by
  let t := firstGoodCrossing D
  have htpos : 0 < t := firstGoodCrossing_pos D
  have htle : t ≤ n := (firstGoodCrossing_spec D).1
  have hgood : 2 * downPrefix D.1 t < t := (firstGoodCrossing_spec D).2
  have hpredlt : t - 1 < t := by omega
  have hpredn : t - 1 ≤ n := by omega
  have hsafe := firstGoodCrossing_min D hpredlt
  have hpredsafe : t - 1 ≤ 2 * downPrefix D.1 (t - 1) := by
    by_contra h
    apply hsafe
    exact ⟨hpredn, by omega⟩
  have hstep : downPrefix D.1 (t - 1) ≤ downPrefix D.1 t := by
    have hlt : t - 1 < n := by omega
    have hs := downPrefix_le_succ D.1 hlt
    have heq : t - 1 + 1 = t := by omega
    rw [heq] at hs
    exact hs
  change t = 2 * downPrefix D.1 t + 1
  omega

lemma card_flip_firstBad {n : ℕ} (D : BadEndpointPath n) :
    (flipPrefix D.1 (firstBadCrossing D)).card = D.1.card - 1 := by
  rw [card_flipPrefix D.1 (firstBadCrossing_spec D).1]
  have hexact := firstBadCrossing_exact D
  have hcard := downPrefix_le_card D.1 (firstBadCrossing D)
  omega

lemma card_flip_firstGood {n : ℕ} (D : MarginPath n) :
    (flipPrefix D.1 (firstGoodCrossing D)).card = D.1.card + 1 := by
  rw [card_flipPrefix D.1 (firstGoodCrossing_spec D).1]
  have hexact := firstGoodCrossing_exact D
  omega

/-- Reflection through the first negative prefix sends a bad nonnegative-endpoint path to a path
whose endpoint has one extra unit of margin. -/
noncomputable def badToMargin {n : ℕ} (D : BadEndpointPath n) : MarginPath n :=
  ⟨flipPrefix D.1 (firstBadCrossing D), by
    rw [EndpointMargin, card_flip_firstBad]
    have hend := D.property.1
    rw [EndpointNonnegative] at hend
    have hcard := downPrefix_le_card D.1 (firstBadCrossing D)
    have hcross := (firstBadCrossing_spec D).2
    omega⟩

/-- Reflection through the first strictly positive prefix is the inverse construction. -/
noncomputable def marginToBad {n : ℕ} (D : MarginPath n) : BadEndpointPath n :=
  ⟨flipPrefix D.1 (firstGoodCrossing D), by
    constructor
    · rw [EndpointNonnegative, card_flip_firstGood]
      exact D.property
    · intro hmeander
      let t := firstGoodCrossing D
      have htle : t ≤ n := (firstGoodCrossing_spec D).1
      have hexact : t = 2 * downPrefix D.1 t + 1 := firstGoodCrossing_exact D
      have hflip := downPrefix_flipPrefix_of_le D.1 htle le_rfl
      have hsafe := hmeander t htle
      change 2 * downPrefix (flipPrefix D.1 t) t ≤ t at hsafe
      omega⟩

lemma firstGoodCrossing_badToMargin {n : ℕ} (D : BadEndpointPath n) :
    firstGoodCrossing (badToMargin D) = firstBadCrossing D := by
  let t := firstBadCrossing D
  apply (Nat.find_eq_iff (margin_exists_crossing (badToMargin D))).2
  constructor
  · constructor
    · exact (firstBadCrossing_spec D).1
    · have htle : t ≤ n := (firstBadCrossing_spec D).1
      have hexact : 2 * downPrefix D.1 t = t + 1 := firstBadCrossing_exact D
      have hflip := downPrefix_flipPrefix_of_le D.1 htle le_rfl
      change 2 * downPrefix (flipPrefix D.1 t) t < t
      omega
  · intro u hut
    intro hu
    rcases hu with ⟨hun, hupos⟩
    have hutle : u ≤ t := hut.le
    have hflip := downPrefix_flipPrefix_of_le D.1 hun hutle
    have hdu : downPrefix D.1 u ≤ u := downPrefix_le_time D.1 hun
    have hmin := firstBadCrossing_min D hut
    have hsafe : 2 * downPrefix D.1 u ≤ u := by
      by_contra h
      apply hmin
      exact ⟨hun, by omega⟩
    change 2 * downPrefix (flipPrefix D.1 t) u < u at hupos
    omega

lemma firstBadCrossing_marginToBad {n : ℕ} (D : MarginPath n) :
    firstBadCrossing (marginToBad D) = firstGoodCrossing D := by
  let t := firstGoodCrossing D
  apply (Nat.find_eq_iff (badEndpoint_exists_crossing (marginToBad D))).2
  constructor
  · constructor
    · exact (firstGoodCrossing_spec D).1
    · have htle : t ≤ n := (firstGoodCrossing_spec D).1
      have hexact : t = 2 * downPrefix D.1 t + 1 := firstGoodCrossing_exact D
      have hflip := downPrefix_flipPrefix_of_le D.1 htle le_rfl
      change t < 2 * downPrefix (flipPrefix D.1 t) t
      omega
  · intro u hut
    intro hu
    rcases hu with ⟨hun, hubad⟩
    have hutle : u ≤ t := hut.le
    have hflip := downPrefix_flipPrefix_of_le D.1 hun hutle
    have hdu : downPrefix D.1 u ≤ u := downPrefix_le_time D.1 hun
    have hmin := firstGoodCrossing_min D hut
    have hsafe : u ≤ 2 * downPrefix D.1 u := by
      by_contra h
      apply hmin
      exact ⟨hun, by omega⟩
    change u < 2 * downPrefix (flipPrefix D.1 t) u at hubad
    omega

/-- The reflection principle as an explicit equivalence between bad endpoint-nonnegative paths
and paths with endpoint margin. -/
noncomputable def badEndpointEquivMargin (n : ℕ) : BadEndpointPath n ≃ MarginPath n where
  toFun := badToMargin
  invFun := marginToBad
  left_inv D := by
    apply Subtype.ext
    change flipPrefix (flipPrefix D.1 (firstBadCrossing D))
      (firstGoodCrossing (badToMargin D)) = D.1
    rw [firstGoodCrossing_badToMargin]
    exact flipPrefix_involutive D.1 (firstBadCrossing D)
  right_inv D := by
    apply Subtype.ext
    change flipPrefix (flipPrefix D.1 (firstGoodCrossing D))
      (firstBadCrossing (marginToBad D)) = D.1
    rw [firstBadCrossing_marginToBad]
    exact flipPrefix_involutive D.1 (firstGoodCrossing D)

abbrev MeanderPath (n : ℕ) := {D : Finset (Fin n) // IsMeander D}
abbrev EndpointPath (n : ℕ) := {D : Finset (Fin n) // EndpointNonnegative D}
abbrev CentralPath (n : ℕ) := {D : Finset (Fin n) // D.card = n / 2}

/-- Endpoint-nonnegative paths split into meanders and bad paths. -/
noncomputable def endpointEquivMeanderSumBad (n : ℕ) :
    EndpointPath n ≃ MeanderPath n ⊕ BadEndpointPath n where
  toFun D := if h : IsMeander D.1 then Sum.inl ⟨D.1, h⟩
    else Sum.inr ⟨D.1, D.property, h⟩
  invFun x := match x with
    | Sum.inl D => ⟨D.1, D.property.endpointNonnegative⟩
    | Sum.inr D => ⟨D.1, D.property.1⟩
  left_inv D := by
    dsimp
    by_cases h : IsMeander D.1
    · rw [dif_pos h]
    · rw [dif_neg h]
  right_inv x := by
    rcases x with D | D
    · dsimp
      rw [dif_pos D.property]
    · dsimp
      rw [dif_neg D.property.2]

lemma centralPath_endpoint {n : ℕ} (D : CentralPath n) : EndpointNonnegative D.1 := by
  rw [EndpointNonnegative, D.property]
  omega

lemma endpoint_margin_or_central {n : ℕ} (D : EndpointPath n) :
    EndpointMargin D.1 ∨ D.1.card = n / 2 := by
  have hend := D.property
  change 2 * D.1.card ≤ n at hend
  change 2 * (D.1.card + 1) ≤ n ∨ D.1.card = n / 2
  by_cases h : 2 * (D.1.card + 1) ≤ n
  · exact Or.inl h
  · right
    omega

/-- Endpoint-nonnegative paths also split into paths with margin and parity-central paths. -/
noncomputable def endpointEquivMarginSumCentral (n : ℕ) :
    EndpointPath n ≃ MarginPath n ⊕ CentralPath n where
  toFun D := if h : EndpointMargin D.1 then Sum.inl ⟨D.1, h⟩
    else Sum.inr ⟨D.1, (endpoint_margin_or_central D).resolve_left h⟩
  invFun x := match x with
    | Sum.inl D => ⟨D.1, by
        rw [EndpointNonnegative]
        exact le_trans (by omega : 2 * D.1.card ≤ 2 * (D.1.card + 1)) D.property⟩
    | Sum.inr D => ⟨D.1, centralPath_endpoint D⟩
  left_inv D := by
    dsimp
    by_cases h : EndpointMargin D.1
    · rw [dif_pos h]
    · rw [dif_neg h]
  right_inv x := by
    rcases x with D | D
    · dsimp
      rw [dif_pos D.property]
    · dsimp
      have hnot : ¬ EndpointMargin D.1 := by
        intro hm
        rw [EndpointMargin, D.property] at hm
        omega
      rw [dif_neg hnot]

/-- Central paths are exactly subsets of the `n` locations of cardinality `n/2`. -/
def centralPathEquivPowerset (n : ℕ) :
    CentralPath n ≃ ↥(Finset.univ.powersetCard (n / 2) : Finset (Finset (Fin n))) where
  toFun D := ⟨D.1, by simp [D.property]⟩
  invFun D := ⟨D.1, by simpa using (Finset.mem_powersetCard.mp D.property).2⟩
  left_inv D := by rfl
  right_inv D := by apply Subtype.ext; rfl

/-- The one-dimensional reflection principle: nonnegative meanders of length `n` are counted by
the middle binomial coefficient. -/
theorem card_meanderPath (n : ℕ) :
    Fintype.card (MeanderPath n) = Nat.choose n (n / 2) := by
  let e₁ := endpointEquivMeanderSumBad n
  let e₂ := endpointEquivMarginSumCentral n
  let e₃ := badEndpointEquivMargin n
  have h₁ := Fintype.card_congr e₁
  have h₂ := Fintype.card_congr e₂
  have h₃ := Fintype.card_congr e₃
  simp only [Fintype.card_sum] at h₁ h₂
  have hmc : Fintype.card (MeanderPath n) = Fintype.card (CentralPath n) := by omega
  rw [hmc, Fintype.card_congr (centralPathEquivPowerset n), Fintype.card_coe,
    Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]

end Erdos521
