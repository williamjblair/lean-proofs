import Mathlib
import Research.PiecewiseAssembly

namespace Erdos254.CesaroErrorThick

open Filter Topology
open scoped BigOperators
open Erdos254.PiecewiseAssembly

noncomputable section

attribute [local instance] Classical.propDecidable

lemma card_hits_of_no_empty_block
    (E : Set ℕ) (N L : ℕ)
    (hblock : ∀ a : ℕ, a + L < N → ∃ k : ℕ, k ≤ L ∧ a + k ∈ E) :
    N / (L + 1) ≤ ((Finset.range N).filter (fun n => n ∈ E)).card := by
  classical
  let Q := N / (L + 1)
  have hex : ∀ j : Fin Q, ∃ k : ℕ, k ≤ L ∧ j.val * (L + 1) + k ∈ E := by
    intro j
    apply hblock
    have hj : (j.val + 1) * (L + 1) ≤ N := by
      apply (Nat.le_div_iff_mul_le (by omega)).mp
      exact j.isLt
    calc
      j.val * (L + 1) + L < j.val * (L + 1) + (L + 1) := by omega
      _ = (j.val + 1) * (L + 1) := by ring
      _ ≤ N := hj
  choose k hkL hkE using hex
  let f : Fin Q → ℕ := fun j => j.val * (L + 1) + k j
  have hfinj : Function.Injective f := by
    intro i j hij
    apply Fin.ext
    by_contra hne
    rcases lt_or_gt_of_ne hne with hijlt | hjilt
    · have hiupper : f i < (i.val + 1) * (L + 1) := by
        dsimp [f]
        calc
          i.val * (L + 1) + k i ≤ i.val * (L + 1) + L :=
            Nat.add_le_add_left (hkL i) _
          _ < i.val * (L + 1) + (L + 1) := by omega
          _ = (i.val + 1) * (L + 1) := by ring
      have hjlower : j.val * (L + 1) ≤ f j := by
        dsimp [f]
        exact Nat.le_add_right _ _
      have hblocks : (i.val + 1) * (L + 1) ≤ j.val * (L + 1) :=
        Nat.mul_le_mul_right (L + 1) (by omega)
      exact (not_lt_of_ge hjlower) (hij ▸ hiupper.trans_le hblocks)
    · have hjupper : f j < (j.val + 1) * (L + 1) := by
        dsimp [f]
        calc
          j.val * (L + 1) + k j ≤ j.val * (L + 1) + L :=
            Nat.add_le_add_left (hkL j) _
          _ < j.val * (L + 1) + (L + 1) := by omega
          _ = (j.val + 1) * (L + 1) := by ring
      have hilower : i.val * (L + 1) ≤ f i := by
        dsimp [f]
        exact Nat.le_add_right _ _
      have hblocks : (j.val + 1) * (L + 1) ≤ i.val * (L + 1) :=
        Nat.mul_le_mul_right (L + 1) (by omega)
      exact (not_lt_of_ge hilower) (hij.symm ▸ hjupper.trans_le hblocks)
  have hfmem : ∀ j, f j ∈ (Finset.range N).filter (fun n => n ∈ E) := by
    intro j
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_range.mpr ?_, hkE j⟩
    have hj : (j.val + 1) * (L + 1) ≤ N := by
      apply (Nat.le_div_iff_mul_le (by omega)).mp
      exact j.isLt
    dsimp [f]
    calc
      j.val * (L + 1) + k j ≤ j.val * (L + 1) + L :=
        Nat.add_le_add_left (hkL j) _
      _ < j.val * (L + 1) + (L + 1) := by omega
      _ = (j.val + 1) * (L + 1) := by ring
      _ ≤ N := hj
  let emb : Fin Q ↪ {n // n ∈ (Finset.range N).filter (fun n => n ∈ E)} :=
    ⟨fun j => ⟨f j, hfmem j⟩, fun i j h => hfinj (congrArg Subtype.val h)⟩
  simpa [Q] using Fintype.card_le_of_injective emb emb.injective

/-- A sequence whose squared Cesàro means tend to zero is below every fixed
positive threshold on arbitrarily long consecutive intervals. -/
theorem small_error_set_is_thick
    (r : ℕ → ℝ)
    (hr : Tendsto
      (fun N : ℕ => (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N, (r n) ^ 2)
      atTop (𝓝 0))
    (η : ℝ) (hη : 0 < η) :
    IsThick {n | |r n| < η} := by
  intro L
  let Q : ℕ := L + 1
  have hsmall' := (tendsto_order.1 hr).2 (η ^ 2 / (4 * Q)) (by
    dsimp [Q]
    positivity)
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 hsmall'
  let N := max N₀ (2 * Q)
  have hNavg : (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N, (r n) ^ 2 <
      η ^ 2 / (4 * Q) := hN₀ N (le_max_left _ _)
  let E : Set ℕ := {n | η ≤ |r n|}
  by_contra hnot
  have hblock : ∀ a : ℕ, a + L < N → ∃ k : ℕ, k ≤ L ∧ a + k ∈ E := by
    intro a ha
    by_contra hempty
    apply hnot
    refine ⟨a, ?_⟩
    intro k hk
    have : ¬η ≤ |r (a + k)| := by
      intro hkE
      exact hempty ⟨k, hk, hkE⟩
    exact lt_of_not_ge this
  let EN := (Finset.range N).filter (fun n => n ∈ E)
  have hcardLower : N / (L + 1) ≤ EN.card := by
    dsimp only [EN]
    exact card_hits_of_no_empty_block E N L hblock
  have hsumLower : (EN.card : ℝ) * η ^ 2 ≤
      ∑ n ∈ Finset.range N, (r n) ^ 2 := by
    calc
      (EN.card : ℝ) * η ^ 2 = ∑ _n ∈ EN, η ^ 2 := by simp [EN]
      _ ≤ ∑ n ∈ EN, (r n) ^ 2 := by
        apply Finset.sum_le_sum
        intro n hn
        have hnE := (Finset.mem_filter.mp hn).2
        dsimp [E] at hnE
        calc
          η ^ 2 ≤ |r n| ^ 2 := (sq_le_sq₀ hη.le (abs_nonneg _)).2 hnE
          _ = (r n) ^ 2 := sq_abs _
      _ ≤ ∑ n ∈ Finset.range N, (r n) ^ 2 := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        intro n hn hn'
        positivity
  have hNpos : 0 < N := by dsimp [N, Q]; omega
  have hcardReal : (N : ℝ) / (2 * Q) ≤ EN.card := by
    have hdiv : N / Q ≤ EN.card := by
      simpa [Q, EN] using hcardLower
    have hfloor : (N : ℝ) / (2 * Q) ≤ (N / Q : ℕ) := by
      have hQpos : 0 < Q := by dsimp [Q]; omega
      have hNQ : 2 * Q ≤ N := le_max_right _ _
      have hq2 : 2 ≤ N / Q := (Nat.le_div_iff_mul_le hQpos).2 hNQ
      have hrem : N < (N / Q + 1) * Q := by
        simpa [Nat.mul_comm] using Nat.lt_mul_div_succ N hQpos
      rw [div_le_iff₀]
      · exact_mod_cast (show N ≤ (N / Q) * (2 * Q) by nlinarith)
      · positivity
    exact hfloor.trans (by exact_mod_cast hdiv)
  have hQreal : (0 : ℝ) < Q := by
    dsimp [Q]
    positivity
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hηsq : 0 ≤ η ^ 2 := sq_nonneg η
  have hfirst : η ^ 2 / (2 * Q) =
      (((N : ℝ) / (2 * Q)) * η ^ 2) / N := by
    field_simp
  have hmiddle : (((N : ℝ) / (2 * Q)) * η ^ 2) / N ≤
      ((EN.card : ℝ) * η ^ 2) / N := by
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hcardReal hηsq) hNreal.le
  have hlast : ((EN.card : ℝ) * η ^ 2) / N ≤
      (∑ n ∈ Finset.range N, (r n) ^ 2) / N :=
    div_le_div_of_nonneg_right hsumLower hNreal.le
  have havgLower : η ^ 2 / (2 * Q) ≤
      (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N, (r n) ^ 2 := by
    rw [inv_mul_eq_div]
    exact hfirst ▸ hmiddle.trans hlast
  have hsep : η ^ 2 / (4 * Q) < η ^ 2 / (2 * Q) := by
    exact div_lt_div_of_pos_left (sq_pos_of_pos hη) (by positivity)
      (by nlinarith [hQreal])
  exact (not_lt_of_ge havgLower) (hNavg.trans hsep)

/-- A Bohr-structured lower bound survives a squared-Cesàro-null error on a
thick set. This is the elementary final step in Følner's almost-Bohr theorem. -/
theorem bohr_lower_bound_survives_cesaro_error
    {d : ℕ} (a : UnitAddTorus (Fin d)) (U : Set (UnitAddTorus (Fin d)))
    (h r φ : ℕ → ℝ) (η : ℝ) (hη : 0 < η)
    (hh : ∀ n : ℕ, n • a ∈ U → η ≤ h n)
    (hdecomp : ∀ n : ℕ, φ n = h n + r n)
    (hr : Tendsto
      (fun N : ℕ => (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N, (r n) ^ 2)
      atTop (𝓝 0))
    (S : Set ℕ) (hpositive : ∀ n : ℕ, 0 < φ n → n ∈ S) :
    ∃ J : Set ℕ, IsThick J ∧
      ∀ n : ℕ, n • a ∈ U → n ∈ J → n ∈ S := by
  let J : Set ℕ := {n | |r n| < η}
  refine ⟨J, small_error_set_is_thick r hr η hη, ?_⟩
  intro n hnU hnJ
  apply hpositive n
  have hhn := hh n hnU
  have hrn : |r n| < η := hnJ
  rw [hdecomp]
  have hrbelow : -η < r n := neg_lt_of_abs_lt hrn
  linarith

end

end Erdos254.CesaroErrorThick
