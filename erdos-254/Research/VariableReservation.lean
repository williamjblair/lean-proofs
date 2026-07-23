import Mathlib
import Research.BalancedReservation

namespace Erdos254.VariableReservation

open Filter
open scoped BigOperators Topology
open Erdos254.BalancedReservation

noncomputable section

/-- Countably many divergent nonnegative shell-weight series survive reserving
`r j` points from shell `j`, provided both the number `d j` of protected
coordinates and the reserve size can grow while `r j * d j` remains a small
fraction of the shell. -/
theorem exists_variable_reserves_preserving_countable_divergence
    {α : Type*} [DecidableEq α]
    (S : ℕ → Finset α) (w : ℕ → α → ℝ)
    (hw : ∀ i j x, x ∈ S j → 0 ≤ w i x)
    (r d : ℕ → ℕ) (hrpos : ∀ j, 0 < r j)
    (hr : ∀ j, r j ≤ (S j).card)
    (hd : Tendsto d atTop atTop)
    (hroom : ∀ᶠ j : ℕ in atTop, 2 * (r j * d j) ≤ (S j).card)
    (hdiv : ∀ i : ℕ, Tendsto
      (fun N => ∑ j ∈ Finset.range N, ∑ x ∈ S j, w i x) atTop atTop) :
    ∃ R : ℕ → Finset α,
      (∀ j, R j ⊆ S j ∧ (R j).card = r j) ∧
      (∀ i : ℕ, Tendsto
        (fun N => ∑ j ∈ Finset.range N,
          ((∑ x ∈ S j, w i x) - ∑ x ∈ R j, w i x)) atTop atTop) := by
  classical
  have hchoose : ∀ j, ∃ t : Finset α, t ⊆ S j ∧ t.card = r j ∧
      ∀ i : Fin (d j),
        ((S j).card : ℝ) * (∑ x ∈ t, w i.val x) ≤
          (r j * d j : ℕ) * (∑ x ∈ S j, w i.val x) := by
    intro j
    simpa using exists_subset_card_simultaneous_normalized
      (S j) (fun i : Fin (d j) => w i.val)
      (fun i x hx => hw i.val j x hx) (r j) (hr j)
  choose R hRsub hRcard hRbound using hchoose
  refine ⟨R, fun j => ⟨hRsub j, hRcard j⟩, ?_⟩
  intro i
  let full : ℕ → ℝ := fun j => ∑ x ∈ S j, w i x
  let kept : ℕ → ℝ := fun j => full j - ∑ x ∈ R j, w i x
  have hfullnonneg : ∀ j, 0 ≤ full j := by
    intro j
    exact Finset.sum_nonneg fun x hx => hw i j x hx
  have hreserveNonneg : ∀ j, 0 ≤ ∑ x ∈ R j, w i x := by
    intro j
    exact Finset.sum_nonneg fun x hx => hw i j x (hRsub j hx)
  have hreserveLe : ∀ j, (∑ x ∈ R j, w i x) ≤ full j := by
    intro j
    exact Finset.sum_le_sum_of_subset_of_nonneg (hRsub j)
      (fun x hxS hxR => hw i j x hxS)
  have hkeptNonneg : ∀ j, 0 ≤ kept j := by
    intro j
    exact sub_nonneg.mpr (hreserveLe j)
  have hid : ∀ᶠ j : ℕ in atTop, i < d j :=
    (tendsto_atTop.1 hd (i + 1)).mono fun j hj => by omega
  have hhalf : ∀ᶠ j : ℕ in atTop, full j / 2 ≤ kept j := by
    filter_upwards [hroom, hid] with j hjroom hijd
    have hb := hRbound j ⟨i, hijd⟩
    have hrdpos : (0 : ℝ) < (r j * d j : ℕ) := by
      exact_mod_cast Nat.mul_pos (hrpos j) (by omega)
    have hcard : (2 : ℝ) * (r j * d j : ℕ) ≤ (S j).card := by
      exact_mod_cast hjroom
    have hres0 := hreserveNonneg j
    dsimp [kept, full]
    dsimp [full] at hb hcard
    have hscaled : (2 : ℝ) * (r j * d j : ℕ) *
        (∑ x ∈ R j, w i x) ≤
        (r j * d j : ℕ) * (∑ x ∈ S j, w i x) := by
      calc
        _ ≤ ((S j).card : ℝ) * (∑ x ∈ R j, w i x) :=
          mul_le_mul_of_nonneg_right hcard hres0
        _ ≤ _ := hb
    have htwice : (2 : ℝ) * (∑ x ∈ R j, w i x) ≤
        ∑ x ∈ S j, w i x := by
      exact (mul_le_mul_iff_right₀ hrdpos).mp (by
        simpa [mul_assoc, mul_left_comm, mul_comm] using hscaled)
    linarith
  obtain ⟨J₀, hJ₀⟩ := eventually_atTop.1 hhalf
  rw [tendsto_atTop]
  intro b
  have htarget := tendsto_atTop.1 (hdiv i)
    (2 * max b 0 + ∑ j ∈ Finset.range J₀, full j)
  filter_upwards [htarget, eventually_ge_atTop J₀] with N hN hNJ
  have hdecomp : Finset.range N = Finset.range J₀ ∪ Finset.Ico J₀ N := by
    ext j
    simp
    omega
  have hdis : Disjoint (Finset.range J₀) (Finset.Ico J₀ N) := by
    rw [Finset.disjoint_left]
    intro j hj0 hjI
    simp at hj0 hjI
    omega
  have htailFull : 2 * max b 0 ≤ ∑ j ∈ Finset.Ico J₀ N, full j := by
    rw [hdecomp, Finset.sum_union hdis] at hN
    linarith
  have htailKept : ∑ j ∈ Finset.Ico J₀ N, full j / 2 ≤
      ∑ j ∈ Finset.Ico J₀ N, kept j := by
    apply Finset.sum_le_sum
    intro j hj
    exact hJ₀ j (by simpa using (Finset.mem_Ico.mp hj).1)
  have hhalfSum : (∑ j ∈ Finset.Ico J₀ N, full j) / 2 =
      ∑ j ∈ Finset.Ico J₀ N, full j / 2 := by
    rw [Finset.sum_div]
  have hbTail : b ≤ ∑ j ∈ Finset.Ico J₀ N, kept j := by
    rw [← hhalfSum] at htailKept
    have : b ≤ (∑ j ∈ Finset.Ico J₀ N, full j) / 2 := by
      have hbmax : b ≤ max b 0 := le_max_left _ _
      linarith
    exact this.trans htailKept
  have htailSubset : Finset.Ico J₀ N ⊆ Finset.range N := by
    intro j hj
    simp only [Finset.mem_Ico, Finset.mem_range] at hj ⊢
    exact hj.2
  have htailToAll : (∑ j ∈ Finset.Ico J₀ N, kept j) ≤
      ∑ j ∈ Finset.range N, kept j :=
    Finset.sum_le_sum_of_subset_of_nonneg htailSubset
      (fun j hjN hjI => hkeptNonneg j)
  exact hbTail.trans htailToAll

end

end Erdos254.VariableReservation
