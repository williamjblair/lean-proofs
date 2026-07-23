import Research.UpperCombinatorics

namespace Erdos796

section ProjectionCube

variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]

/-- Occupied pairs in the projection of a tripartite edge set to its last two
coordinates. -/
def activeBetaGamma (H : Finset (α × (β × γ))) : Finset (β × γ) :=
  (Finset.univ : Finset (β × γ)).filter fun bc =>
    (alphaFiber H bc).Nonempty

lemma alphaFiber_card_eq_zero_of_not_mem_active
    (H : Finset (α × (β × γ))) {bc : β × γ}
    (hbc : bc ∉ activeBetaGamma H) : (alphaFiber H bc).card = 0 := by
  unfold activeBetaGamma at hbc
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hbc
  exact Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp hbc)

/-- Count edges using only occupied projection pairs. -/
theorem card_eq_sum_active_alphaFiber (H : Finset (α × (β × γ))) :
    H.card = ∑ bc ∈ activeBetaGamma H, (alphaFiber H bc).card := by
  rw [card_eq_sum_alphaFiber]
  symm
  apply Finset.sum_subset (by simp [activeBetaGamma])
  intro bc hbc hactive
  exact alphaFiber_card_eq_zero_of_not_mem_active H hactive

/-- Projection-sensitive Cauchy inequality.  The usual factor `|β||γ|` is
replaced by the number of actually occupied `(β,γ)` cells. -/
theorem cube_card_sq_le_active_commonSlices
    (H : Finset (α × (β × γ))) :
    H.card ^ 2 ≤ (activeBetaGamma H).card *
      ((∑ aa ∈ (Finset.univ : Finset α).offDiag,
          (commonSlice H aa).card) + H.card) := by
  have hcauchy := sq_sum_le_card_mul_sum_sq
    (s := activeBetaGamma H)
    (f := fun bc => (alphaFiber H bc).card)
  have hcard := card_eq_sum_active_alphaFiber H
  have hsquares : (∑ bc ∈ activeBetaGamma H,
      (alphaFiber H bc).card ^ 2) =
      (∑ aa ∈ (Finset.univ : Finset α).offDiag,
        (commonSlice H aa).card) + H.card := by
    have hall : (∑ bc ∈ activeBetaGamma H,
        (alphaFiber H bc).card ^ 2) =
        ∑ bc : β × γ, (alphaFiber H bc).card ^ 2 := by
      apply Finset.sum_subset (by simp [activeBetaGamma])
      intro bc hbc hactive
      rw [alphaFiber_card_eq_zero_of_not_mem_active H hactive]
      simp
    rw [hall]
    have hfull : (∑ bc : β × γ, (alphaFiber H bc).card ^ 2) =
        (∑ bc : β × γ, ((alphaFiber H bc).offDiag).card) +
          ∑ bc : β × γ, (alphaFiber H bc).card := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro bc hbc
      rw [Finset.offDiag_card]
      have hd : (alphaFiber H bc).card ≤
          (alphaFiber H bc).card * (alphaFiber H bc).card := by
        by_cases hz : (alphaFiber H bc).card = 0
        · simp [hz]
        · have : 1 ≤ (alphaFiber H bc).card := Nat.one_le_iff_ne_zero.mpr hz
          nlinarith
      rw [Nat.sub_add_cancel hd]
      ring
    rw [hfull, sum_alphaFiber_offDiag_eq, ← card_eq_sum_alphaFiber]
  rw [← hcard] at hcauchy
  rw [hsquares] at hcauchy
  exact hcauchy

/-- Projection-sensitive exact cube inequality. -/
theorem cubeFree_card_sq_le_active (H : Finset (α × (β × γ)))
    (hfree : CubeFree H) :
    (H.card : ℝ) ^ 2 ≤
      ((activeBetaGamma H).card : ℝ) *
        (((Fintype.card α : ℝ) ^ 2) *
          (Fintype.card β +
            Fintype.card γ * Real.sqrt (Fintype.card β)) + H.card) := by
  have hnat := cube_card_sq_le_active_commonSlices H
  have hbase : (H.card : ℝ) ^ 2 ≤
      ((activeBetaGamma H).card : ℝ) *
        ((∑ aa ∈ (Finset.univ : Finset α).offDiag,
          (commonSlice H aa).card : ℕ) + H.card) := by
    exact_mod_cast hnat
  have hone : ∀ aa ∈ (Finset.univ : Finset α).offDiag,
      ((commonSlice H aa).card : ℝ) ≤
        Fintype.card β +
          Fintype.card γ * Real.sqrt (Fintype.card β) := by
    intro aa haa
    have hne := (Finset.mem_offDiag.mp haa).2.2
    exact rectangleFree_card_le _ (commonSlice_rectangleFree H hfree hne)
  have hsum : ((∑ aa ∈ (Finset.univ : Finset α).offDiag,
      (commonSlice H aa).card : ℕ) : ℝ) ≤
      (Fintype.card α : ℝ) ^ 2 *
        (Fintype.card β +
          Fintype.card γ * Real.sqrt (Fintype.card β)) := by
    push_cast
    calc
      ∑ aa ∈ (Finset.univ : Finset α).offDiag,
          ((commonSlice H aa).card : ℝ)
        ≤ ∑ _aa ∈ (Finset.univ : Finset α).offDiag,
            ((Fintype.card β : ℝ) +
              Fintype.card γ * Real.sqrt (Fintype.card β)) :=
          Finset.sum_le_sum hone
      _ = (((Finset.univ : Finset α).offDiag).card : ℝ) *
          ((Fintype.card β : ℝ) +
            Fintype.card γ * Real.sqrt (Fintype.card β)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (Fintype.card α : ℝ) ^ 2 *
          (Fintype.card β +
            Fintype.card γ * Real.sqrt (Fintype.card β)) := by
          gcongr
          exact_mod_cast (show ((Finset.univ : Finset α).offDiag).card ≤
            Fintype.card α ^ 2 by
              rw [pow_two, Finset.offDiag_card, Finset.card_univ]
              exact Nat.sub_le _ _)
  calc
    (H.card : ℝ) ^ 2 ≤
      ((activeBetaGamma H).card : ℝ) *
        (((∑ aa ∈ (Finset.univ : Finset α).offDiag,
          (commonSlice H aa).card : ℕ) : ℝ) + H.card) := hbase
    _ ≤ _ := by gcongr

/-- Solved form: one incidence per occupied projection cell plus a square-root
excess. -/
theorem cubeFree_card_le_active (H : Finset (α × (β × γ)))
    (hfree : CubeFree H) :
    (H.card : ℝ) ≤
      (activeBetaGamma H).card +
      (Fintype.card α : ℝ) *
        Real.sqrt (((activeBetaGamma H).card : ℝ) *
          (Fintype.card β +
            Fintype.card γ * Real.sqrt (Fintype.card β))) := by
  let e : ℝ := H.card
  let V : ℝ := (activeBetaGamma H).card
  let B : ℝ := (Fintype.card α : ℝ) ^ 2 *
    (Fintype.card β +
      Fintype.card γ * Real.sqrt (Fintype.card β))
  have hmain0 := cubeFree_card_sq_le_active H hfree
  have hmain : e ^ 2 ≤ V * (B + e) := by
    simpa [e, V, B] using hmain0
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hVB : 0 ≤ V * B := mul_nonneg hV hB
  have hs := Real.sq_sqrt hVB
  have he : 0 ≤ e := by dsimp [e]; positivity
  have hroot : e ≤ V + Real.sqrt (V * B) := by
    by_contra h
    have hgt : V + Real.sqrt (V * B) < e := lt_of_not_ge h
    have hs0 : 0 ≤ Real.sqrt (V * B) := Real.sqrt_nonneg _
    nlinarith
  have hα : (0 : ℝ) ≤ Fintype.card α := by positivity
  have hsqrt : Real.sqrt (V * B) =
      (Fintype.card α : ℝ) *
        Real.sqrt (((activeBetaGamma H).card : ℝ) *
          (Fintype.card β +
            Fintype.card γ * Real.sqrt (Fintype.card β))) := by
    dsimp [V, B]
    rw [show ((activeBetaGamma H).card : ℝ) *
        ((Fintype.card α : ℝ) ^ 2 *
          (Fintype.card β +
            Fintype.card γ * Real.sqrt (Fintype.card β))) =
      (Fintype.card α : ℝ) ^ 2 *
        (((activeBetaGamma H).card : ℝ) *
          (Fintype.card β +
            Fintype.card γ * Real.sqrt (Fintype.card β))) by ring,
      Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hα]
  simpa [e, V, hsqrt] using hroot

end ProjectionCube

end Erdos796
