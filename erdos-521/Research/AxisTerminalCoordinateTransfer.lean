import Research.AxisCoordinateDensity
import Research.AxisScheduleTail
import Mathlib.Tactic

set_option maxHeartbeats 2000000

namespace Erdos521

noncomputable local instance axisTerminalCoordinateDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

lemma card_subtype_eq_filter {α : Type*} [Fintype α] (P : α → Prop) [DecidablePred P] :
    Fintype.card {x : α // P x} = (Finset.univ.filter P).card :=
  Fintype.card_subtype P

/-- Generic terminal-event transfer for events determined by the horizontal coordinate core.
Balanced schedules pay the uniform factor `64`, one-coordinate survival pays the square-root
terminal factor, and unbalanced schedules are left as the explicit exponential error. -/
theorem axisGood_horizontal_terminal_event_density_le
    (s r : ℕ) (hsr : 1 ≤ s + r) (E : Finset (AxisWord r))
    (Q : HorizontalCore (s + r) → Prop)
    (EA : AxisGoodPath (s + r) → Prop)
    (haxis : ∀ p, EA p ↔ Q (axisHorizontalCore p))
    (hhorizontal : ∀ p : HorizontalGoodPath (s + r),
      horizontalAxisSuffix p ∈ E ↔ Q (oneCoordinateHorizontalCore p)) :
    (Fintype.card {p : AxisGoodPath (s + r) // EA p} : ℝ) /
        Fintype.card (AxisGoodPath (s + r)) ≤
      128 * Real.sqrt ((s + r + 1 : ℝ) / (s + 1 : ℝ)) *
          ((E.card : ℝ) / (4 : ℝ) ^ r) +
        16 * (s + r + 1 : ℝ) * Real.exp (-(s + r : ℝ) / 8) := by
  let n := s + r
  let A : Finset (HorizontalCore n) := Finset.univ.filter fun c ↦
    Q c ∧ n ≤ 4 * (c.1ᶜ).card
  let X : Finset (AxisGoodPath n) := Finset.univ.filter EA
  let G : Finset (AxisGoodPath n) := Finset.univ.filter fun p ↦ axisHorizontalCore p ∈ A
  let B : Finset (AxisGoodPath n) := Finset.univ.filter fun p ↦ 4 * (p.1.1ᶜ).card < n
  let Y : Finset (HorizontalGoodPath n) := Finset.univ.filter fun p ↦
    oneCoordinateHorizontalCore p ∈ A
  let Z : Finset (HorizontalGoodPath n) := Finset.univ.filter fun p ↦
    horizontalAxisSuffix p ∈ E
  have hbal : ∀ c ∈ A, n ≤ 4 * (c.1ᶜ).card := by
    intro c hc
    simpa [A] using (Finset.mem_filter.mp hc).2.2
  have hXsub : X ⊆ G ∪ B := by
    intro p hp
    rw [Finset.mem_union]
    have hpX : EA p := by simpa [X] using hp
    by_cases hbad : 4 * (p.1.1ᶜ).card < n
    · exact Or.inr (by simp [B, hbad])
    · left
      simp only [G, Finset.mem_filter, Finset.mem_univ, true_and]
      change axisHorizontalCore p ∈
        Finset.univ.filter (fun c ↦ Q c ∧ n ≤ 4 * (c.1ᶜ).card)
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, (haxis p).mp hpX, ?_⟩
      have hcoreSchedule : (axisHorizontalCore p).1 = p.1.1 := by
        rfl
      rw [hcoreSchedule]
      omega
  have hXcard : X.card ≤ G.card + B.card :=
    (Finset.card_le_card hXsub).trans (Finset.card_union_le G B)
  have hYsub : Y ⊆ Z := by
    intro p hp
    have hpA : oneCoordinateHorizontalCore p ∈ A := by simpa [Y] using hp
    have hQ : Q (oneCoordinateHorizontalCore p) := by
      exact (Finset.mem_filter.mp hpA).2.1
    simpa [Z] using (hhorizontal p).mpr hQ
  have hYcard : Y.card ≤ Z.card := Finset.card_le_card hYsub
  have hA := axisGood_balanced_core_density_le_horizontal (n := n) A hbal
  have hGcard : G.card = Fintype.card
      {p : AxisGoodPath n // axisHorizontalCore p ∈ A} := by
    rw [card_subtype_eq_filter]
  have hYcardEq : Y.card = Fintype.card
      {p : HorizontalGoodPath n // oneCoordinateHorizontalCore p ∈ A} := by
    rw [card_subtype_eq_filter]
  have hZcard : Z.card = Fintype.card
      {p : HorizontalGoodPath n // horizontalAxisSuffix p ∈ E} := by
    rw [card_subtype_eq_filter]
  have hXcardEq : X.card = Fintype.card {p : AxisGoodPath n // EA p} := by
    rw [card_subtype_eq_filter]
  have hBcard : B.card = Fintype.card (VerticallyUnbalancedAxisPath n) := by
    rw [card_subtype_eq_filter]
  rw [← hGcard, ← hYcardEq] at hA
  have hgoodPos : (0 : ℝ) < Fintype.card (AxisGoodPath n) := by
    exact_mod_cast card_axisGoodPath_pos n
  have hhorizPos : (0 : ℝ) < Fintype.card (HorizontalGoodPath n) := by
    exact_mod_cast horizontalGoodPath_card_pos n
  have hYdensity : (Y.card : ℝ) / Fintype.card (HorizontalGoodPath n) ≤
      (Z.card : ℝ) / Fintype.card (HorizontalGoodPath n) :=
    div_le_div_of_nonneg_right (by exact_mod_cast hYcard) hhorizPos.le
  have hcore : (G.card : ℝ) / Fintype.card (AxisGoodPath n) ≤
      64 * ((Z.card : ℝ) / Fintype.card (HorizontalGoodPath n)) := by
    exact hA.trans (mul_le_mul_of_nonneg_left hYdensity (by norm_num))
  have hsquare := horizontalGood_suffix_density_sq_le s r E
  rw [← hZcard] at hsquare
  let d : ℝ := (Z.card : ℝ) / Fintype.card (HorizontalGoodPath n)
  let p : ℝ := (E.card : ℝ) / (4 : ℝ) ^ r
  let R : ℝ := (n + 1 : ℝ) / (s + 1 : ℝ)
  have hR : 0 ≤ R := by dsimp [R, n]; positivity
  have hd : 0 ≤ d := by
    dsimp [d]
    exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hp : 0 ≤ p := by
    dsimp [p]
    exact div_nonneg (Nat.cast_nonneg _) (pow_nonneg (by norm_num) _)
  have hsquare' : d ^ 2 ≤ 4 * R * p ^ 2 := by
    dsimp [d, p, R, n]
    convert hsquare using 1 <;> push_cast <;> ring
  have hlinear : d ≤ 2 * Real.sqrt R * p := by
    apply (sq_le_sq₀ hd (by positivity)).1
    calc
      d ^ 2 ≤ 4 * R * p ^ 2 := hsquare'
      _ = (2 * Real.sqrt R * p) ^ 2 := by
        rw [mul_pow, mul_pow, Real.sq_sqrt hR]
        ring
  have hbad := verticallyUnbalancedAxisPath_density_le n hsr
  rw [← hBcard] at hbad
  have hXreal : (X.card : ℝ) ≤ (G.card : ℝ) + (B.card : ℝ) := by exact_mod_cast hXcard
  rw [← hXcardEq]
  change (X.card : ℝ) / Fintype.card (AxisGoodPath n) ≤ _
  calc
    (X.card : ℝ) / Fintype.card (AxisGoodPath n) ≤
        (G.card : ℝ) / Fintype.card (AxisGoodPath n) +
          (B.card : ℝ) / Fintype.card (AxisGoodPath n) := by
      rw [← add_div]
      exact div_le_div_of_nonneg_right hXreal hgoodPos.le
    _ ≤ 64 * d + 16 * (n + 1 : ℝ) * Real.exp (-(n : ℝ) / 8) := by
      exact add_le_add hcore hbad
    _ ≤ 128 * Real.sqrt R * p +
        16 * (n + 1 : ℝ) * Real.exp (-(n : ℝ) / 8) := by
      apply add_le_add_left
      calc
        64 * d ≤ 64 * (2 * Real.sqrt R * p) :=
          mul_le_mul_of_nonneg_left hlinear (by norm_num)
        _ = 128 * Real.sqrt R * p := by ring
    _ = _ := by
      dsimp [R, p, n]
      push_cast
      ring

/-- Instance-independent `Nat.card` form of the terminal coordinate transfer. -/
theorem axisGood_horizontal_terminal_event_natCard_density_le
    (s r : ℕ) (hsr : 1 ≤ s + r)
    (E : Finset (AxisWord r))
    (Q : HorizontalCore (s + r) → Prop)
    (EA : AxisGoodPath (s + r) → Prop)
    (haxis : ∀ p : AxisGoodPath (s + r), EA p ↔ Q (axisHorizontalCore p))
    (hhorizontal : ∀ p : HorizontalGoodPath (s + r),
      horizontalAxisSuffix p ∈ E ↔ Q (oneCoordinateHorizontalCore p)) :
    (Nat.card {p : AxisGoodPath (s + r) // EA p} : ℝ) /
        Nat.card (AxisGoodPath (s + r)) ≤
      128 * Real.sqrt (((s : ℝ) + r + 1) / (s + 1)) *
          ((E.card : ℝ) / (4 : ℝ) ^ r) +
        16 * ((s : ℝ) + r + 1) * Real.exp (-((s : ℝ) + r) / 8) := by
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  exact axisGood_horizontal_terminal_event_density_le s r hsr E Q EA haxis hhorizontal

end Erdos521
