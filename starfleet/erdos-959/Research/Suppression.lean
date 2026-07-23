import Mathlib

namespace Erdos959

lemma cross_factor_le {h k j : ℕ} (hhk : h ≤ k) (hjh : j ≤ h) :
    k * (h - j) ≤ h * (k - j) := by
  have hjk : j ≤ k := hjh.trans hhk
  have hab : h - j ≤ k - j := Nat.sub_le_sub_right hhk j
  calc
    k * (h - j) = ((k - j) + j) * (h - j) := by
      rw [Nat.sub_add_cancel hjk]
    _ = (k - j) * (h - j) + j * (h - j) := by ring
    _ ≤ (k - j) * (h - j) + j * (k - j) := by gcongr
    _ = ((h - j) + j) * (k - j) := by ring
    _ = h * (k - j) := by rw [Nat.sub_add_cancel hjh]

lemma descFactorial_ratio_bound {h k j : ℕ} (hhk : h ≤ k) (hjh : j ≤ h) :
    k ^ j * h.descFactorial j ≤ h ^ j * k.descFactorial j := by
  induction j with
  | zero => simp
  | succ j ih =>
      have hjh' : j ≤ h := (Nat.le_succ j).trans hjh
      have hf := cross_factor_le hhk hjh'
      rw [Nat.descFactorial_succ, Nat.descFactorial_succ]
      calc
        k ^ (j + 1) * ((h - j) * h.descFactorial j) =
            (k ^ j * h.descFactorial j) * (k * (h - j)) := by
              simp only [pow_succ]
              ring
        _ ≤ (h ^ j * k.descFactorial j) * (h * (k - j)) :=
          Nat.mul_le_mul (ih hjh') hf
        _ = h ^ (j + 1) * ((k - j) * k.descFactorial j) := by
          simp only [pow_succ]
          ring

lemma choose_containment_ratio_bound {h k j : ℕ} (hhk : h ≤ k) (hjh : j ≤ h) :
    k ^ j * Nat.choose (k - j) (h - j) ≤
      h ^ j * Nat.choose k h := by
  have hjk : j ≤ k := hjh.trans hhk
  have hchoose : k ^ j * Nat.choose h j ≤ h ^ j * Nat.choose k j := by
    apply Nat.le_of_mul_le_mul_left _ (Nat.factorial_pos j)
    simpa only [Nat.descFactorial_eq_factorial_mul_choose, mul_assoc,
      mul_left_comm, mul_comm] using
      descFactorial_ratio_bound hhk hjh
  have hid := Nat.choose_mul (n := k) hjh
  apply Nat.le_of_mul_le_mul_left _ (Nat.choose_pos hjk)
  calc
    Nat.choose k j * (k ^ j * Nat.choose (k - j) (h - j)) =
        k ^ j * (Nat.choose k j * Nat.choose (k - j) (h - j)) := by ring
    _ = k ^ j * (Nat.choose k h * Nat.choose h j) := by rw [← hid]
    _ = Nat.choose k h * (k ^ j * Nat.choose h j) := by ring
    _ ≤ Nat.choose k h * (h ^ j * Nat.choose k j) :=
      Nat.mul_le_mul_left _ hchoose
    _ = Nat.choose k j * (h ^ j * Nat.choose k h) := by ring

lemma containing_subsets_exact_and_suppressed
    {α : Type*} [DecidableEq α] (J U : Finset α) (h : ℕ)
    (hJU : J ⊆ U) (hJh : J.card ≤ h) (hhU : h ≤ U.card) :
    let family := (U.powersetCard h).filter (J ⊆ ·)
    family.card = Nat.choose (U.card - J.card) (h - J.card) ∧
      U.card ^ J.card * family.card ≤
        h ^ J.card * (U.powersetCard h).card := by
  dsimp
  constructor
  · exact Finset.card_filter_powersetCard_subset J U h hJU hJh
  · rw [Finset.card_filter_powersetCard_subset J U h hJU hJh,
      Finset.card_powersetCard]
    exact choose_containment_ratio_bound hhU hJh

end Erdos959
