import Research.ProjectionCube

namespace Erdos796

section IncidenceExcess

variable {T C : Type*} [Fintype T] [Fintype C]
  [DecidableEq T] [DecidableEq C]

/-- Coefficients occurring in one projection cell. -/
def coefficientFiber (H : Finset (T × C)) (c : C) : Finset T :=
  (Finset.univ : Finset T).filter fun t => (t, c) ∈ H

/-- Occupied projection cells. -/
def activeCells (H : Finset (T × C)) : Finset C :=
  (Finset.univ : Finset C).filter fun c => (coefficientFiber H c).Nonempty

/-- Cells at which a fixed ordered pair of distinct coefficients both occur. -/
def coefficientPairCells (H : Finset (T × C)) (tu : T × T) : Finset C :=
  (Finset.univ : Finset C).filter fun c =>
    (tu.1, c) ∈ H ∧ (tu.2, c) ∈ H

lemma card_eq_sum_coefficientFiber (H : Finset (T × C)) :
    H.card = ∑ c : C, (coefficientFiber H c).card := by
  have hH : H = ((Finset.univ : Finset T).product
      (Finset.univ : Finset C)).filter fun z => z ∈ H := by
    ext z
    simp
  calc
    H.card = (((Finset.univ : Finset T).product
        (Finset.univ : Finset C)).filter fun z => z ∈ H).card := by rw [← hH]
    _ = ∑ z ∈ (Finset.univ : Finset T).product
        (Finset.univ : Finset C), if z ∈ H then 1 else 0 :=
      Finset.card_filter _ _
    _ = ∑ t : T, ∑ c : C, if (t, c) ∈ H then 1 else 0 :=
      Finset.sum_product _ _ _
    _ = ∑ c : C, ∑ t : T, if (t, c) ∈ H then 1 else 0 :=
      Finset.sum_comm
    _ = ∑ c : C, (coefficientFiber H c).card := by
      apply Finset.sum_congr rfl
      intro c hc
      unfold coefficientFiber
      rw [Finset.card_filter]

lemma coefficientFiber_offDiag_eq_pairCells (H : Finset (T × C)) (c : C) :
    ((coefficientFiber H c).offDiag).card =
      ∑ tu ∈ (Finset.univ : Finset T).offDiag,
        if c ∈ coefficientPairCells H tu then 1 else 0 := by
  have hoff :
      (coefficientFiber H c).offDiag =
      (Finset.univ : Finset T).offDiag.filter fun tu =>
        (tu.1, c) ∈ H ∧ (tu.2, c) ∈ H := by
    ext tu
    simp [coefficientFiber, Finset.mem_offDiag,
      and_comm, and_left_comm, and_assoc]
  rw [hoff, Finset.card_filter]
  apply Finset.sum_congr rfl
  intro tu htu
  unfold coefficientPairCells
  simp

/-- Double count ordered coefficient pairs by cells. -/
theorem sum_offDiag_pairCells_card (H : Finset (T × C)) :
    (∑ tu ∈ (Finset.univ : Finset T).offDiag,
      (coefficientPairCells H tu).card) =
      ∑ c : C, ((coefficientFiber H c).offDiag).card := by
  rw [show (∑ c : C, ((coefficientFiber H c).offDiag).card) =
      ∑ c : C, ∑ tu ∈ (Finset.univ : Finset T).offDiag,
        if c ∈ coefficientPairCells H tu then 1 else 0 by
    apply Finset.sum_congr rfl
    intro c hc
    exact coefficientFiber_offDiag_eq_pairCells H c]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro tu htu
  unfold coefficientPairCells
  rw [Finset.card_filter]
  simp

/-- Every incidence is either the first in its occupied projection cell or is
covered by an ordered pair of coefficients in that cell. -/
theorem incidence_card_le_active_add_pairExcess (H : Finset (T × C)) :
    H.card ≤ (activeCells H).card +
      ∑ tu ∈ (Finset.univ : Finset T).offDiag,
        (coefficientPairCells H tu).card := by
  rw [card_eq_sum_coefficientFiber, sum_offDiag_pairCells_card]
  have hactive : (activeCells H).card =
      ∑ c : C, if c ∈ activeCells H then 1 else 0 := by
    simp
  rw [hactive, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro c hc
  by_cases hzero : (coefficientFiber H c).card = 0
  · have hnot : c ∉ activeCells H := by
      unfold activeCells
      simp [Finset.card_eq_zero.mp hzero]
    simp [hzero, hnot]
  · have hmem : c ∈ activeCells H := by
      unfold activeCells
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact Finset.card_pos.mp (Nat.pos_of_ne_zero hzero)
    rw [if_pos hmem, Finset.offDiag_card]
    have hk : 1 ≤ (coefficientFiber H c).card := Nat.one_le_iff_ne_zero.mpr hzero
    have heq :
        (coefficientFiber H c).card * (coefficientFiber H c).card -
          (coefficientFiber H c).card =
        (coefficientFiber H c).card * ((coefficientFiber H c).card - 1) := by
      calc
        _ = (coefficientFiber H c).card * (coefficientFiber H c).card -
            (coefficientFiber H c).card * 1 := by simp
        _ = _ := (Nat.mul_sub_left_distrib _ _ _).symm
    have hoff : (coefficientFiber H c).card - 1 ≤
        (coefficientFiber H c).card * (coefficientFiber H c).card -
          (coefficientFiber H c).card := by
      rw [heq]
      exact Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero hzero)
    omega

end IncidenceExcess

end Erdos796
