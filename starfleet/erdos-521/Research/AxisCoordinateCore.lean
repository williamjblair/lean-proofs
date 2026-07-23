import Research.HorizontalMeanderTransfer
import Mathlib.Tactic

open scoped BigOperators

namespace Erdos521

noncomputable local instance axisCoordinateCoreDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

/-- A schedule together with its horizontal compressed meander, forgetting all vertical signs. -/
abbrev HorizontalCore (n : ℕ) := Σ H : Finset (Fin n), MeanderPath H.card

/-- Full quadrant-good paths are horizontal cores decorated by a vertical meander. -/
noncomputable def axisGoodEquivHorizontalCore (n : ℕ) :
    AxisGoodPath n ≃ Σ c : HorizontalCore n, MeanderPath (c.1ᶜ).card where
  toFun p :=
    let d := goodSignsEquivMeanders p.1.1 ⟨p.1.2, p.property⟩
    ⟨⟨p.1.1, d.1⟩, d.2⟩
  invFun z :=
    let S := (goodSignsEquivMeanders z.1.1).symm (z.1.2, z.2)
    ⟨(z.1.1, S.1), S.property⟩
  left_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact congrArg Subtype.val
        ((goodSignsEquivMeanders p.1.1).symm_apply_apply ⟨p.1.2, p.property⟩)
  right_inv z := by
    cases z with
    | mk c v =>
      cases c with
      | mk H h =>
        have hz := (goodSignsEquivMeanders H).apply_symm_apply (h, v)
        change (⟨⟨H, ((goodSignsEquivMeanders H)
          ((goodSignsEquivMeanders H).symm (h, v))).1⟩,
          ((goodSignsEquivMeanders H)
            ((goodSignsEquivMeanders H).symm (h, v))).2⟩ :
          Σ c : HorizontalCore n, MeanderPath (c.1ᶜ).card) = ⟨⟨H, h⟩, v⟩
        rw [hz]

/-- One-coordinate-good paths are the same horizontal cores decorated by an arbitrary vertical
down-step set. -/
noncomputable def horizontalGoodEquivCore (n : ℕ) :
    HorizontalGoodPath n ≃ Σ c : HorizontalCore n, Finset (Fin (c.1ᶜ).card) where
  toFun p :=
    let d := horizontalGoodSignsEquiv p.1.1 ⟨p.1.2, p.property⟩
    ⟨⟨p.1.1, d.1⟩, d.2⟩
  invFun z :=
    let S := (horizontalGoodSignsEquiv z.1.1).symm (z.1.2, z.2)
    ⟨(z.1.1, S.1), S.property⟩
  left_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact congrArg Subtype.val
        ((horizontalGoodSignsEquiv p.1.1).symm_apply_apply ⟨p.1.2, p.property⟩)
  right_inv z := by
    cases z with
    | mk c v =>
      cases c with
      | mk H h =>
        have hz := (horizontalGoodSignsEquiv H).apply_symm_apply (h, v)
        change (⟨⟨H, ((horizontalGoodSignsEquiv H)
          ((horizontalGoodSignsEquiv H).symm (h, v))).1⟩,
          ((horizontalGoodSignsEquiv H)
            ((horizontalGoodSignsEquiv H).symm (h, v))).2⟩ :
          Σ c : HorizontalCore n, Finset (Fin (c.1ᶜ).card)) = ⟨⟨H, h⟩, v⟩
        rw [hz]

noncomputable def axisHorizontalCore {n : ℕ} (p : AxisGoodPath n) : HorizontalCore n :=
  (axisGoodEquivHorizontalCore n p).1

noncomputable def oneCoordinateHorizontalCore {n : ℕ}
    (p : HorizontalGoodPath n) : HorizontalCore n :=
  (horizontalGoodEquivCore n p).1

lemma card_sigma_core_mem {n : ℕ} (A : Finset (HorizontalCore n))
    (V : HorizontalCore n → Type*) [∀ c, Fintype (V c)] :
    Fintype.card {z : Σ c : HorizontalCore n, V c // z.1 ∈ A} =
      ∑ c ∈ A, Fintype.card (V c) := by
  rw [Fintype.card_congr (Equiv.subtypeSigmaEquiv V (fun c ↦ c ∈ A)),
    Fintype.card_sigma]
  exact Finset.sum_attach A (fun c ↦ Fintype.card (V c))

lemma card_axisGood_core_mem (n : ℕ) (A : Finset (HorizontalCore n)) :
    Fintype.card {p : AxisGoodPath n // axisHorizontalCore p ∈ A} =
      ∑ c ∈ A, Nat.choose (c.1ᶜ).card ((c.1ᶜ).card / 2) := by
  let e := Equiv.subtypeEquiv (axisGoodEquivHorizontalCore n)
    (p := fun p ↦ axisHorizontalCore p ∈ A) (q := fun z ↦ z.1 ∈ A)
    (fun _ ↦ Iff.rfl)
  calc
    Fintype.card {p : AxisGoodPath n // axisHorizontalCore p ∈ A} =
        Fintype.card {z : Σ c : HorizontalCore n, MeanderPath (c.1ᶜ).card //
          z.1 ∈ A} := Fintype.card_congr e
    _ = ∑ c ∈ A, Fintype.card (MeanderPath (c.1ᶜ).card) :=
      card_sigma_core_mem A _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro c hc
      exact card_meanderPath (c.1ᶜ).card

lemma card_horizontalGood_core_mem (n : ℕ) (A : Finset (HorizontalCore n)) :
    Fintype.card {p : HorizontalGoodPath n // oneCoordinateHorizontalCore p ∈ A} =
      ∑ c ∈ A, 2 ^ (c.1ᶜ).card := by
  let e := Equiv.subtypeEquiv (horizontalGoodEquivCore n)
    (p := fun p ↦ oneCoordinateHorizontalCore p ∈ A) (q := fun z ↦ z.1 ∈ A)
    (fun _ ↦ Iff.rfl)
  calc
    Fintype.card {p : HorizontalGoodPath n // oneCoordinateHorizontalCore p ∈ A} =
        Fintype.card {z : Σ c : HorizontalCore n, Finset (Fin (c.1ᶜ).card) //
          z.1 ∈ A} := Fintype.card_congr e
    _ = ∑ c ∈ A, Fintype.card (Finset (Fin (c.1ᶜ).card)) :=
      card_sigma_core_mem A _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro c hc
      simp

lemma ballotMass_le_of_compl_balanced {n : ℕ} (H : Finset (Fin n))
    (hbal : n ≤ 4 * (Hᶜ).card) :
    ballotMass (Hᶜ).card ≤ 2 / Real.sqrt (n + 1 : ℝ) := by
  have hnpos : (0 : ℝ) < n + 1 := by positivity
  have hsqrt : 0 < Real.sqrt (n + 1 : ℝ) := Real.sqrt_pos.2 hnpos
  have hright0 : 0 ≤ 2 / Real.sqrt (n + 1 : ℝ) := by positivity
  apply (sq_le_sq₀ (ballotMass_nonneg _) hright0).1
  have hsqrtSq : (Real.sqrt (n + 1 : ℝ)) ^ 2 = n + 1 := Real.sq_sqrt hnpos.le
  rw [div_pow, hsqrtSq]
  have hbalR : (n : ℝ) ≤ 4 * ((Hᶜ).card : ℝ) := by exact_mod_cast hbal
  calc
    ballotMass (Hᶜ).card ^ 2 ≤ 1 / ((Hᶜ).card + 1 : ℝ) :=
      ballotMass_sq_upper_sharp _
    _ ≤ 4 / (n + 1 : ℝ) := by
      apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < ((Hᶜ).card + 1 : ℝ))
        hnpos).2
      nlinarith
    _ = 2 ^ 2 / (n + 1 : ℝ) := by norm_num

/-- On schedules with at least one quarter vertical moves, imposing the second meander condition
costs at most `2/sqrt(n+1)` relative to imposing only horizontal survival, uniformly for every
family of horizontal cores. -/
theorem card_axisGood_core_mem_le_horizontal {n : ℕ} (A : Finset (HorizontalCore n))
    (hbal : ∀ c ∈ A, n ≤ 4 * (c.1ᶜ).card) :
    (Fintype.card {p : AxisGoodPath n // axisHorizontalCore p ∈ A} : ℝ) ≤
      (2 / Real.sqrt (n + 1 : ℝ)) *
        Fintype.card {p : HorizontalGoodPath n // oneCoordinateHorizontalCore p ∈ A} := by
  rw [card_axisGood_core_mem, card_horizontalGood_core_mem]
  push_cast
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro c hc
  have hb := ballotMass_le_of_compl_balanced c.1 (hbal c hc)
  have hp : (0 : ℝ) ≤ 2 ^ (c.1ᶜ).card := by positivity
  calc
    (Nat.choose (c.1ᶜ).card ((c.1ᶜ).card / 2) : ℝ) =
        ballotMass (c.1ᶜ).card * (2 : ℝ) ^ (c.1ᶜ).card := by
      unfold ballotMass
      field_simp
    _ ≤ (2 / Real.sqrt (n + 1 : ℝ)) * (2 : ℝ) ^ (c.1ᶜ).card :=
      mul_le_mul_of_nonneg_right hb hp

end Erdos521
