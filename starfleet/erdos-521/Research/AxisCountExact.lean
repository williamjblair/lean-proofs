import Research.RademacherBallotExact
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.Tactic

open scoped BigOperators

namespace Erdos521

noncomputable local instance axisCountDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

lemma sum_finsets_by_card (n : ℕ) (f : ℕ → ℕ) :
    (∑ H : Finset (Fin n), f H.card) =
      ∑ h ∈ Finset.range (n + 1), Nat.choose n h * f h := by
  let g : Finset (Fin n) → Fin (n + 1) := fun H ↦ ⟨H.card, by
    have := Finset.card_le_univ H
    simp only [Fintype.card_fin] at this
    omega⟩
  let F : ℕ → ℕ := fun h ↦
    ∑ H ∈ Finset.powersetCard h (Finset.univ : Finset (Fin n)), f H.card
  have hfib := Finset.sum_fiberwise (Finset.univ : Finset (Finset (Fin n))) g
    (fun H ↦ f H.card)
  calc
    (∑ H : Finset (Fin n), f H.card) =
        ∑ j : Fin (n + 1),
          ∑ H ∈ (Finset.univ : Finset (Finset (Fin n))) with g H = j, f H.card :=
      hfib.symm
    _ = ∑ j : Fin (n + 1), F j.val := by
      apply Finset.sum_congr rfl
      intro j hj
      dsimp [F]
      apply Finset.sum_congr
      · ext H
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_powersetCard,
          Finset.subset_univ, g]
        exact Fin.ext_iff
      · intro H hH
        rfl
    _ = ∑ h ∈ Finset.range (n + 1), F h := Fin.sum_univ_eq_sum_range F (n + 1)
    _ = ∑ h ∈ Finset.range (n + 1), Nat.choose n h * f h := by
      apply Finset.sum_congr rfl
      intro h hh
      dsimp [F]
      calc
        (∑ H ∈ Finset.powersetCard h (Finset.univ : Finset (Fin n)), f H.card) =
            Nat.choose n h • f h := by
          simpa using Finset.sum_powersetCard h (Finset.univ : Finset (Fin n)) f
        _ = Nat.choose n h * f h := by simp [nsmul_eq_mul]

/-- Explicit schedule-cardinality convolution for the number of surviving axis paths. -/
def axisPathCountFormula (n : ℕ) : ℕ :=
  ∑ h ∈ Finset.range (n + 1),
    Nat.choose n h * Nat.choose h (h / 2) * Nat.choose (n - h) ((n - h) / 2)

lemma card_axisGoodPath_eq_formula (n : ℕ) :
    Fintype.card (AxisGoodPath n) = axisPathCountFormula n := by
  rw [card_axisGoodPath]
  simp_rw [card_goodSigns]
  have hcompl (H : Finset (Fin n)) : Hᶜ.card = n - H.card := by
    rw [Finset.card_compl, Fintype.card_fin]
  simp_rw [hcompl]
  simpa [axisPathCountFormula, mul_assoc] using
    (sum_finsets_by_card n
      (fun h ↦ Nat.choose h (h / 2) * Nat.choose (n - h) ((n - h) / 2)))

lemma axis_sum_range_even_odd (m : ℕ) (f : ℕ → ℕ) :
    (∑ h ∈ Finset.range (2 * m + 1), f h) =
      (∑ a ∈ Finset.range (m + 1), f (2 * a)) +
        ∑ a ∈ Finset.range m, f (2 * a + 1) := by
  rw [show 2 * m + 1 = (2 * m).succ by omega, Finset.sum_range_succ,
    sum_range_even_odd, Finset.sum_add_distrib, Finset.sum_range_succ]
  ring

lemma axis_sum_range_even_odd_succ (m : ℕ) (f : ℕ → ℕ) :
    (∑ h ∈ Finset.range (2 * m + 2), f h) =
      (∑ a ∈ Finset.range (m + 1), f (2 * a)) +
        ∑ a ∈ Finset.range (m + 1), f (2 * a + 1) := by
  rw [show 2 * m + 2 = 2 * (m + 1) by omega, sum_range_even_odd,
    Finset.sum_add_distrib]

lemma even_axis_summand (m a : ℕ) (ha : a ≤ m) :
    Nat.choose (2 * m) (2 * a) * Nat.choose (2 * a) a *
        Nat.choose (2 * m - 2 * a) (m - a) =
      Nat.choose (2 * m) m * Nat.choose m a * Nat.choose m a := by
  have h1 := Nat.choose_mul (n := 2 * m) (k := 2 * a) (s := a) (by omega)
  have h1' : Nat.choose (2 * m) (2 * a) * Nat.choose (2 * a) a =
      Nat.choose (2 * m) a * Nat.choose (2 * m - a) a := by
    simpa [show 2 * a - a = a by omega] using h1
  have h2 := Nat.choose_mul (n := 2 * m - a) (k := m) (s := a) ha
  have hsym : Nat.choose (2 * m - a) m = Nat.choose (2 * m - a) (m - a) := by
    calc
      Nat.choose (2 * m - a) m = Nat.choose (2 * m - a) (2 * m - a - m) :=
        (Nat.choose_symm (by omega : m ≤ 2 * m - a)).symm
      _ = Nat.choose (2 * m - a) (m - a) := by congr 1; omega
  rw [hsym] at h2
  have h2' : Nat.choose (2 * m - a) (m - a) * Nat.choose m a =
      Nat.choose (2 * m - a) a * Nat.choose (2 * m - 2 * a) (m - a) := by
    simpa only [show 2 * m - a - a = 2 * m - 2 * a by omega] using h2
  have h3 := Nat.choose_mul (n := 2 * m) (k := m) (s := a) ha
  have h3' : Nat.choose (2 * m) m * Nat.choose m a =
      Nat.choose (2 * m) a * Nat.choose (2 * m - a) (m - a) := h3
  calc
    _ = (Nat.choose (2 * m) a * Nat.choose (2 * m - a) a) *
        Nat.choose (2 * m - 2 * a) (m - a) := by rw [h1']
    _ = Nat.choose (2 * m) a *
        (Nat.choose (2 * m - a) a * Nat.choose (2 * m - 2 * a) (m - a)) := by ring
    _ = Nat.choose (2 * m) a *
        (Nat.choose (2 * m - a) (m - a) * Nat.choose m a) := by rw [← h2']
    _ = (Nat.choose (2 * m) a * Nat.choose (2 * m - a) (m - a)) *
        Nat.choose m a := by ring
    _ = (Nat.choose (2 * m) m * Nat.choose m a) * Nat.choose m a := by rw [← h3']
    _ = _ := by ring

lemma odd_axis_summand (m a : ℕ) (ha : a < m) :
    Nat.choose (2 * m) (2 * a + 1) * Nat.choose (2 * a + 1) a *
        Nat.choose (2 * m - (2 * a + 1)) ((2 * m - (2 * a + 1)) / 2) =
      Nat.choose (2 * m) m * Nat.choose m a * Nat.choose m (a + 1) := by
  have hfloor : (2 * m - (2 * a + 1)) / 2 = m - a - 1 := by omega
  rw [hfloor, show 2 * m - (2 * a + 1) = 2 * m - 2 * a - 1 by omega]
  have h1 := Nat.choose_mul (n := 2 * m) (k := 2 * a + 1) (s := a) (by omega)
  have h1' : Nat.choose (2 * m) (2 * a + 1) * Nat.choose (2 * a + 1) a =
      Nat.choose (2 * m) a * Nat.choose (2 * m - a) (a + 1) := by
    simpa only [show 2 * a + 1 - a = a + 1 by omega] using h1
  have h2 := Nat.choose_mul (n := 2 * m - a) (k := m) (s := a + 1) (by omega)
  have hsym : Nat.choose (2 * m - a) m = Nat.choose (2 * m - a) (m - a) := by
    calc
      Nat.choose (2 * m - a) m = Nat.choose (2 * m - a) (2 * m - a - m) :=
        (Nat.choose_symm (by omega : m ≤ 2 * m - a)).symm
      _ = Nat.choose (2 * m - a) (m - a) := by congr 1; omega
  rw [hsym] at h2
  have h2' : Nat.choose (2 * m - a) (m - a) * Nat.choose m (a + 1) =
      Nat.choose (2 * m - a) (a + 1) *
        Nat.choose (2 * m - 2 * a - 1) (m - a - 1) := by
    simpa only [show 2 * m - a - (a + 1) = 2 * m - 2 * a - 1 by omega,
      show m - (a + 1) = m - a - 1 by omega] using h2
  have h3 := Nat.choose_mul (n := 2 * m) (k := m) (s := a) (by omega)
  have h3' : Nat.choose (2 * m) m * Nat.choose m a =
      Nat.choose (2 * m) a * Nat.choose (2 * m - a) (m - a) := h3
  calc
    _ = (Nat.choose (2 * m) a * Nat.choose (2 * m - a) (a + 1)) *
        Nat.choose (2 * m - 2 * a - 1) (m - a - 1) := by rw [h1']
    _ = Nat.choose (2 * m) a *
        (Nat.choose (2 * m - a) (a + 1) *
          Nat.choose (2 * m - 2 * a - 1) (m - a - 1)) := by ring
    _ = Nat.choose (2 * m) a *
        (Nat.choose (2 * m - a) (m - a) * Nat.choose m (a + 1)) := by rw [← h2']
    _ = (Nat.choose (2 * m) a * Nat.choose (2 * m - a) (m - a)) *
        Nat.choose m (a + 1) := by ring
    _ = (Nat.choose (2 * m) m * Nat.choose m a) * Nat.choose m (a + 1) := by
      rw [← h3']
    _ = _ := by ring

lemma odd_total_axis_summand (m a : ℕ) (ha : a ≤ m) :
    Nat.choose (2 * m + 1) (2 * a) * Nat.choose (2 * a) a *
        Nat.choose (2 * m + 1 - 2 * a) ((2 * m + 1 - 2 * a) / 2) =
      Nat.choose (2 * m + 1) m * Nat.choose m a * Nat.choose (m + 1) a := by
  have hfloor : (2 * m + 1 - 2 * a) / 2 = m - a := by omega
  rw [hfloor]
  have h1 := Nat.choose_mul (n := 2 * m + 1) (k := 2 * a) (s := a) (by omega)
  have h1' : Nat.choose (2 * m + 1) (2 * a) * Nat.choose (2 * a) a =
      Nat.choose (2 * m + 1) a * Nat.choose (2 * m + 1 - a) a := by
    simpa only [show 2 * a - a = a by omega] using h1
  have h2 := Nat.choose_mul (n := 2 * m + 1 - a) (k := m + 1) (s := a) (by omega)
  have hsym₁ : Nat.choose (2 * m + 1 - a) (m + 1) =
      Nat.choose (2 * m + 1 - a) (m - a) := by
    calc
      Nat.choose (2 * m + 1 - a) (m + 1) =
          Nat.choose (2 * m + 1 - a) (2 * m + 1 - a - (m + 1)) :=
        (Nat.choose_symm (by omega : m + 1 ≤ 2 * m + 1 - a)).symm
      _ = Nat.choose (2 * m + 1 - a) (m - a) := by congr 1; omega
  have hsym₂ : Nat.choose (2 * m + 1 - 2 * a) (m + 1 - a) =
      Nat.choose (2 * m + 1 - 2 * a) (m - a) := by
    calc
      Nat.choose (2 * m + 1 - 2 * a) (m + 1 - a) =
          Nat.choose (2 * m + 1 - 2 * a)
            (2 * m + 1 - 2 * a - (m - a)) := by congr 1; omega
      _ = Nat.choose (2 * m + 1 - 2 * a) (m - a) :=
        Nat.choose_symm (by omega : m - a ≤ 2 * m + 1 - 2 * a)
  have h2norm : Nat.choose (2 * m + 1 - a) (m + 1) * Nat.choose (m + 1) a =
      Nat.choose (2 * m + 1 - a) a *
        Nat.choose (2 * m + 1 - 2 * a) (m + 1 - a) := by
    simpa only [show 2 * m + 1 - a - a = 2 * m + 1 - 2 * a by omega] using h2
  rw [hsym₁, hsym₂] at h2norm
  have h2' : Nat.choose (2 * m + 1 - a) (m - a) * Nat.choose (m + 1) a =
      Nat.choose (2 * m + 1 - a) a *
        Nat.choose (2 * m + 1 - 2 * a) (m - a) := h2norm
  have h3 := Nat.choose_mul (n := 2 * m + 1) (k := m) (s := a) ha
  have h3' : Nat.choose (2 * m + 1) m * Nat.choose m a =
      Nat.choose (2 * m + 1) a * Nat.choose (2 * m + 1 - a) (m - a) := h3
  calc
    _ = (Nat.choose (2 * m + 1) a * Nat.choose (2 * m + 1 - a) a) *
        Nat.choose (2 * m + 1 - 2 * a) (m - a) := by rw [h1']
    _ = Nat.choose (2 * m + 1) a *
        (Nat.choose (2 * m + 1 - a) a *
          Nat.choose (2 * m + 1 - 2 * a) (m - a)) := by ring
    _ = Nat.choose (2 * m + 1) a *
        (Nat.choose (2 * m + 1 - a) (m - a) * Nat.choose (m + 1) a) := by rw [← h2']
    _ = (Nat.choose (2 * m + 1) a * Nat.choose (2 * m + 1 - a) (m - a)) *
        Nat.choose (m + 1) a := by ring
    _ = (Nat.choose (2 * m + 1) m * Nat.choose m a) * Nat.choose (m + 1) a := by
      rw [← h3']
    _ = _ := by ring

lemma odd_total_axis_summand_odd (m a : ℕ) (ha : a ≤ m) :
    Nat.choose (2 * m + 1) (2 * a + 1) * Nat.choose (2 * a + 1) a *
        Nat.choose (2 * m + 1 - (2 * a + 1))
          ((2 * m + 1 - (2 * a + 1)) / 2) =
      Nat.choose (2 * m + 1) m * Nat.choose m a * Nat.choose (m + 1) (a + 1) := by
  have hfloor : (2 * m + 1 - (2 * a + 1)) / 2 = m - a := by omega
  rw [hfloor, show 2 * m + 1 - (2 * a + 1) = 2 * m - 2 * a by omega]
  have h1 := Nat.choose_mul (n := 2 * m + 1) (k := 2 * a + 1) (s := a) (by omega)
  have h1' : Nat.choose (2 * m + 1) (2 * a + 1) * Nat.choose (2 * a + 1) a =
      Nat.choose (2 * m + 1) a * Nat.choose (2 * m + 1 - a) (a + 1) := by
    simpa only [show 2 * a + 1 - a = a + 1 by omega] using h1
  have h2 := Nat.choose_mul (n := 2 * m + 1 - a) (k := m + 1) (s := a + 1)
    (by omega)
  have hsym : Nat.choose (2 * m + 1 - a) (m + 1) =
      Nat.choose (2 * m + 1 - a) (m - a) := by
    calc
      Nat.choose (2 * m + 1 - a) (m + 1) =
          Nat.choose (2 * m + 1 - a) (2 * m + 1 - a - (m + 1)) :=
        (Nat.choose_symm (by omega : m + 1 ≤ 2 * m + 1 - a)).symm
      _ = Nat.choose (2 * m + 1 - a) (m - a) := by congr 1; omega
  rw [hsym] at h2
  have h2' : Nat.choose (2 * m + 1 - a) (m - a) * Nat.choose (m + 1) (a + 1) =
      Nat.choose (2 * m + 1 - a) (a + 1) *
        Nat.choose (2 * m - 2 * a) (m - a) := by
    simpa only [show 2 * m + 1 - a - (a + 1) = 2 * m - 2 * a by omega,
      show m + 1 - (a + 1) = m - a by omega] using h2
  have h3 := Nat.choose_mul (n := 2 * m + 1) (k := m) (s := a) ha
  have h3' : Nat.choose (2 * m + 1) m * Nat.choose m a =
      Nat.choose (2 * m + 1) a * Nat.choose (2 * m + 1 - a) (m - a) := h3
  calc
    _ = (Nat.choose (2 * m + 1) a * Nat.choose (2 * m + 1 - a) (a + 1)) *
        Nat.choose (2 * m - 2 * a) (m - a) := by rw [h1']
    _ = Nat.choose (2 * m + 1) a *
        (Nat.choose (2 * m + 1 - a) (a + 1) *
          Nat.choose (2 * m - 2 * a) (m - a)) := by ring
    _ = Nat.choose (2 * m + 1) a *
        (Nat.choose (2 * m + 1 - a) (m - a) * Nat.choose (m + 1) (a + 1)) := by
      rw [← h2']
    _ = (Nat.choose (2 * m + 1) a * Nat.choose (2 * m + 1 - a) (m - a)) *
        Nat.choose (m + 1) (a + 1) := by ring
    _ = (Nat.choose (2 * m + 1) m * Nat.choose m a) *
        Nat.choose (m + 1) (a + 1) := by rw [← h3']
    _ = _ := by ring

lemma choose_add_eq_sum_range (u v k : ℕ) :
    Nat.choose (u + v) k =
      ∑ a ∈ Finset.range (k + 1), Nat.choose u a * Nat.choose v (k - a) := by
  rw [Nat.add_choose_eq, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]

lemma sum_choose_adjacent (m : ℕ) (hm : 0 < m) :
    (∑ a ∈ Finset.range m, Nat.choose m a * Nat.choose m (a + 1)) =
      Nat.choose (2 * m) (m - 1) := by
  rw [show 2 * m = m + m by omega, choose_add_eq_sum_range]
  rw [show m - 1 + 1 = m by omega]
  apply Finset.sum_congr rfl
  intro a ha
  have ham : a < m := Finset.mem_range.mp ha
  have hs : Nat.choose m (a + 1) = Nat.choose m (m - (a + 1)) :=
    (Nat.choose_symm (by omega : a + 1 ≤ m)).symm
  rw [hs]
  congr 2
  omega

lemma sum_choose_m_msucc_left (m : ℕ) :
    (∑ a ∈ Finset.range (m + 1), Nat.choose m a * Nat.choose (m + 1) a) =
      Nat.choose (2 * m + 1) m := by
  have hv := choose_add_eq_sum_range m (m + 1) (m + 1)
  rw [show m + (m + 1) = 2 * m + 1 by omega, Finset.sum_range_succ] at hv
  have hv' : Nat.choose (2 * m + 1) (m + 1) =
      ∑ a ∈ Finset.range (m + 1), Nat.choose m a * Nat.choose (m + 1) (m + 1 - a) := by
    simpa using hv
  have htop : Nat.choose (2 * m + 1) (m + 1) = Nat.choose (2 * m + 1) m := by
    calc
      Nat.choose (2 * m + 1) (m + 1) =
          Nat.choose (2 * m + 1) (2 * m + 1 - m) := by congr 1; omega
      _ = Nat.choose (2 * m + 1) m :=
        Nat.choose_symm (by omega : m ≤ 2 * m + 1)
  rw [htop] at hv'
  rw [hv']
  apply Finset.sum_congr rfl
  intro a ha
  have ham : a ≤ m := by have := Finset.mem_range.mp ha; omega
  have hs : Nat.choose (m + 1) a = Nat.choose (m + 1) (m + 1 - a) :=
    (Nat.choose_symm (by omega : a ≤ m + 1)).symm
  rw [hs]

lemma sum_choose_m_msucc_right (m : ℕ) :
    (∑ a ∈ Finset.range (m + 1), Nat.choose m a * Nat.choose (m + 1) (a + 1)) =
      Nat.choose (2 * m + 1) m := by
  rw [show 2 * m + 1 = m + (m + 1) by omega, choose_add_eq_sum_range]
  apply Finset.sum_congr rfl
  intro a ha
  have ham : a ≤ m := by have := Finset.mem_range.mp ha; omega
  have hs : Nat.choose (m + 1) (a + 1) = Nat.choose (m + 1) (m + 1 - (a + 1)) :=
    (Nat.choose_symm (by omega : a + 1 ≤ m + 1)).symm
  rw [hs]
  congr 2
  omega

lemma axisPathCountFormula_even (m : ℕ) :
    axisPathCountFormula (2 * m) =
      Nat.choose (2 * m) m * Nat.choose (2 * m + 1) m := by
  by_cases hm : m = 0
  · subst m
    simp [axisPathCountFormula]
  unfold axisPathCountFormula
  rw [axis_sum_range_even_odd]
  have heven :
      (∑ a ∈ Finset.range (m + 1),
        Nat.choose (2 * m) (2 * a) * Nat.choose (2 * a) ((2 * a) / 2) *
          Nat.choose (2 * m - 2 * a) ((2 * m - 2 * a) / 2)) =
        Nat.choose (2 * m) m * Nat.choose (2 * m) m := by
    calc
      _ = ∑ a ∈ Finset.range (m + 1),
          Nat.choose (2 * m) m * Nat.choose m a * Nat.choose m a := by
        apply Finset.sum_congr rfl
        intro a ha
        have ham : a ≤ m := by have := Finset.mem_range.mp ha; omega
        simpa only [show (2 * a) / 2 = a by omega,
          show (2 * m - 2 * a) / 2 = m - a by omega] using
          even_axis_summand m a ham
      _ = Nat.choose (2 * m) m *
          (∑ a ∈ Finset.range (m + 1), (Nat.choose m a) ^ 2) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro a ha
        ring
      _ = _ := by rw [Nat.sum_range_choose_sq]
  have hodd :
      (∑ a ∈ Finset.range m,
        Nat.choose (2 * m) (2 * a + 1) * Nat.choose (2 * a + 1) ((2 * a + 1) / 2) *
          Nat.choose (2 * m - (2 * a + 1)) ((2 * m - (2 * a + 1)) / 2)) =
        Nat.choose (2 * m) m * Nat.choose (2 * m) (m - 1) := by
    calc
      _ = ∑ a ∈ Finset.range m,
          Nat.choose (2 * m) m * Nat.choose m a * Nat.choose m (a + 1) := by
        apply Finset.sum_congr rfl
        intro a ha
        have ham : a < m := Finset.mem_range.mp ha
        simpa only [show (2 * a + 1) / 2 = a by omega] using odd_axis_summand m a ham
      _ = Nat.choose (2 * m) m *
          (∑ a ∈ Finset.range m, Nat.choose m a * Nat.choose m (a + 1)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro a ha
        ring
      _ = _ := by rw [sum_choose_adjacent m (Nat.pos_of_ne_zero hm)]
  rw [heven, hodd]
  have hp := Nat.choose_succ_succ (2 * m) (m - 1)
  have hms : m - 1 + 1 = m := by omega
  simp only [Nat.succ_eq_add_one, hms] at hp
  rw [show Nat.choose (2 * m + 1) m =
      Nat.choose (2 * m) m + Nat.choose (2 * m) (m - 1) by omega]
  ring

lemma axisPathCountFormula_odd (m : ℕ) :
    axisPathCountFormula (2 * m + 1) = 2 * (Nat.choose (2 * m + 1) m) ^ 2 := by
  unfold axisPathCountFormula
  rw [axis_sum_range_even_odd_succ]
  have heven :
      (∑ a ∈ Finset.range (m + 1),
        Nat.choose (2 * m + 1) (2 * a) * Nat.choose (2 * a) ((2 * a) / 2) *
          Nat.choose (2 * m + 1 - 2 * a) ((2 * m + 1 - 2 * a) / 2)) =
        (Nat.choose (2 * m + 1) m) ^ 2 := by
    calc
      _ = ∑ a ∈ Finset.range (m + 1),
          Nat.choose (2 * m + 1) m * Nat.choose m a * Nat.choose (m + 1) a := by
        apply Finset.sum_congr rfl
        intro a ha
        have ham : a ≤ m := by have := Finset.mem_range.mp ha; omega
        simpa only [show (2 * a) / 2 = a by omega] using
          odd_total_axis_summand m a ham
      _ = Nat.choose (2 * m + 1) m *
          (∑ a ∈ Finset.range (m + 1), Nat.choose m a * Nat.choose (m + 1) a) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro a ha
        ring
      _ = _ := by rw [sum_choose_m_msucc_left]; ring
  have hodd :
      (∑ a ∈ Finset.range (m + 1),
        Nat.choose (2 * m + 1) (2 * a + 1) *
          Nat.choose (2 * a + 1) ((2 * a + 1) / 2) *
          Nat.choose (2 * m + 1 - (2 * a + 1))
            ((2 * m + 1 - (2 * a + 1)) / 2)) =
        (Nat.choose (2 * m + 1) m) ^ 2 := by
    calc
      _ = ∑ a ∈ Finset.range (m + 1),
          Nat.choose (2 * m + 1) m * Nat.choose m a * Nat.choose (m + 1) (a + 1) := by
        apply Finset.sum_congr rfl
        intro a ha
        have ham : a ≤ m := by have := Finset.mem_range.mp ha; omega
        simpa only [show (2 * a + 1) / 2 = a by omega] using
          odd_total_axis_summand_odd m a ham
      _ = Nat.choose (2 * m + 1) m *
          (∑ a ∈ Finset.range (m + 1),
            Nat.choose m a * Nat.choose (m + 1) (a + 1)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro a ha
        ring
      _ = _ := by rw [sum_choose_m_msucc_right]; ring
  rw [heven, hodd]
  ring

/-- Exact count of quadrant-surviving paths at an even number of paired steps. -/
theorem card_axisGoodPath_even (m : ℕ) :
    Fintype.card (AxisGoodPath (2 * m)) =
      Nat.choose (2 * m) m * Nat.choose (2 * m + 1) m := by
  rw [card_axisGoodPath_eq_formula, axisPathCountFormula_even]

/-- Exact count of quadrant-surviving paths at an odd number of paired steps. -/
theorem card_axisGoodPath_odd (m : ℕ) :
    Fintype.card (AxisGoodPath (2 * m + 1)) =
      2 * (Nat.choose (2 * m + 1) m) ^ 2 := by
  rw [card_axisGoodPath_eq_formula, axisPathCountFormula_odd]

/-- Consequently, the cone-record probabilities themselves have exact central-binomial forms. -/
theorem coneRecordProbability_even (m : ℕ) :
    coneRecordProbability (2 * m) =
      (Nat.choose (2 * m) m * Nat.choose (2 * m + 1) m : ℝ) / (4 : ℝ) ^ (2 * m) := by
  rw [coneRecordProbability_eq_axisGood_ratio, card_axisGoodPath_even]
  norm_cast

/-- Odd-time companion to `coneRecordProbability_even`. -/
theorem coneRecordProbability_odd (m : ℕ) :
    coneRecordProbability (2 * m + 1) =
      (2 * (Nat.choose (2 * m + 1) m) ^ 2 : ℝ) / (4 : ℝ) ^ (2 * m + 1) := by
  rw [coneRecordProbability_eq_axisGood_ratio, card_axisGoodPath_odd]
  norm_cast

end Erdos521
