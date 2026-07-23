import Mathlib
import Research.BalancedReservation
import Research.VariableReservation

namespace Erdos254.GrowingReservation

open Filter
open scoped BigOperators Topology
open Erdos254.VariableReservation

noncomputable section

lemma sqrt_half_tendsto_atTop {h : ℕ → ℕ} (hh : Tendsto h atTop atTop) :
    Tendsto (fun j => (h j).sqrt / 2) atTop atTop := by
  rw [tendsto_atTop]
  intro b
  have hb := tendsto_atTop.1 hh ((2 * b) * (2 * b))
  filter_upwards [hb] with j hj
  have hs : 2 * b ≤ (h j).sqrt := by
    rw [Nat.le_sqrt]
    exact hj
  omega

lemma sqrt_half_room (n : ℕ) :
    2 * ((n.sqrt / 2) * (n.sqrt / 2)) ≤ n := by
  have hs := Nat.sqrt_le n
  have hh : 2 * (n.sqrt / 2) ≤ n.sqrt := by omega
  calc
    2 * ((n.sqrt / 2) * (n.sqrt / 2)) ≤
        (2 * (n.sqrt / 2)) * (2 * (n.sqrt / 2)) := by nlinarith
    _ ≤ n.sqrt * n.sqrt := Nat.mul_le_mul hh hh
    _ ≤ n := hs

/-- If every shell already has at least four points and shell cardinalities
run to infinity, one can reserve a number of points tending to infinity while
preserving every divergent series in a prescribed countable nonnegative
family on the complements. -/
theorem exists_growing_reserves_preserving_countable_divergence
    {α : Type*} [DecidableEq α]
    (S : ℕ → Finset α) (w : ℕ → α → ℝ)
    (hw : ∀ i j x, x ∈ S j → 0 ≤ w i x)
    (hfour : ∀ j, 4 ≤ (S j).card)
    (hcard : Tendsto (fun j => (S j).card) atTop atTop)
    (hdiv : ∀ i : ℕ, Tendsto
      (fun N => ∑ j ∈ Finset.range N, ∑ x ∈ S j, w i x) atTop atTop) :
    ∃ R : ℕ → Finset α,
      (∀ j, R j ⊆ S j) ∧
      Tendsto (fun j => (R j).card) atTop atTop ∧
      (∀ i : ℕ, Tendsto
        (fun N => ∑ j ∈ Finset.range N,
          ((∑ x ∈ S j, w i x) - ∑ x ∈ R j, w i x)) atTop atTop) := by
  classical
  let k : ℕ → ℕ := fun j => ((S j).card).sqrt / 2
  have hkpos : ∀ j, 0 < k j := by
    intro j
    have hs : 2 ≤ ((S j).card).sqrt := by
      rw [Nat.le_sqrt]
      nlinarith [hfour j]
    dsimp [k]
    omega
  have hkle : ∀ j, k j ≤ (S j).card := by
    intro j
    dsimp [k]
    exact (Nat.div_le_self _ _).trans (Nat.sqrt_le_self _)
  have hkTop : Tendsto k atTop atTop := sqrt_half_tendsto_atTop hcard
  have hroom : ∀ᶠ j : ℕ in atTop,
      2 * (k j * k j) ≤ (S j).card := by
    exact Filter.Eventually.of_forall fun j => sqrt_half_room (S j).card
  obtain ⟨R, hR, hkeep⟩ :=
    exists_variable_reserves_preserving_countable_divergence
      S w hw k k hkpos hkle hkTop hroom hdiv
  refine ⟨R, fun j => (hR j).1, ?_, hkeep⟩
  have heq : (fun j => (R j).card) = k := by
    funext j
    exact (hR j).2
  rw [heq]
  exact hkTop

end

end Erdos254.GrowingReservation
