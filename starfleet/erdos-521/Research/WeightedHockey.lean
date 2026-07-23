import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic

open scoped BigOperators

namespace Erdos521

lemma weighted_hockey_stick (q d : ℕ) :
    (∑ r ∈ Finset.range (d + 1), (d - r + 1) * Nat.choose (q + r) q) =
      Nat.choose (q + d + 2) d := by
  induction d with
  | zero => simp
  | succ d ih =>
      have hsplit :
          (∑ r ∈ Finset.range (d + 1 + 1), (d + 1 - r + 1) * Nat.choose (q + r) q) =
            (∑ r ∈ Finset.range (d + 1), (d - r + 1) * Nat.choose (q + r) q) +
              ∑ r ∈ Finset.range (d + 1 + 1), Nat.choose (q + r) q := by
        have hmain :
            (∑ r ∈ Finset.range (d + 1), (d + 1 - r + 1) * Nat.choose (q + r) q) =
              (∑ r ∈ Finset.range (d + 1), (d - r + 1) * Nat.choose (q + r) q) +
                ∑ r ∈ Finset.range (d + 1), Nat.choose (q + r) q := by
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro r hr
          have hrd : r ≤ d := by
            have := Finset.mem_range.mp hr
            omega
          rw [show d + 1 - r + 1 = (d - r + 1) + 1 by omega,
            Nat.add_mul, one_mul]
        rw [Finset.sum_range_succ, hmain]
        have hchoose :
            (∑ r ∈ Finset.range (d + 1 + 1), Nat.choose (q + r) q) =
              (∑ r ∈ Finset.range (d + 1), Nat.choose (q + r) q) +
                Nat.choose (q + (d + 1)) q := by
          simpa using Finset.sum_range_succ (f := fun r ↦ Nat.choose (q + r) q) (d + 1)
        rw [hchoose]
        simp only [Nat.sub_self, zero_add, one_mul]
        ac_rfl
      rw [hsplit, ih]
      have hsum := Nat.sum_range_add_choose (d + 1) q
      have hsum' :
          (∑ r ∈ Finset.range (d + 1 + 1), Nat.choose (q + r) q) =
            Nat.choose (q + d + 2) (q + 1) := by
        calc
          _ = ∑ r ∈ Finset.range (d + 1 + 1), Nat.choose (r + q) q := by
            apply Finset.sum_congr rfl
            intro r _
            rw [add_comm]
          _ = Nat.choose (d + 1 + q + 1) (q + 1) := hsum
          _ = Nat.choose (q + d + 2) (q + 1) := by
            rw [show d + 1 + q + 1 = q + d + 2 by omega]
      rw [hsum']
      have hsym : Nat.choose (q + d + 2) (q + 1) =
          Nat.choose (q + d + 2) (d + 1) :=
        Nat.choose_symm_of_eq_add (show q + d + 2 = (q + 1) + (d + 1) by omega)
      rw [hsym]
      rw [show q + (d + 1) + 2 = (q + d + 2).succ by omega]
      simpa only [Nat.succ_eq_add_one] using
        (Nat.choose_succ_succ (q + d + 2) d).symm

lemma weighted_choose_convolution (n i j : ℕ) (hij : i ≤ j) (hjn : j + 2 ≤ n) :
    (∑ r ∈ Finset.Icc i j,
        (r - i + 1) * Nat.choose (n - 2 - r) (j - r)) =
      Nat.choose (n - i) (j - i) := by
  let q := n - j - 2
  let d := j - i
  have hqi : q + d = n - 2 - i := by
    dsimp [q, d]
    omega
  have hni : n - i = q + d + 2 := by omega
  rw [← Finset.Ico_add_one_right_eq_Icc]
  rw [Finset.sum_Ico_eq_sum_range]
  rw [show j + 1 - i = d + 1 by dsimp [d]; omega]
  calc
    (∑ s ∈ Finset.range (d + 1),
        (i + s - i + 1) * Nat.choose (n - 2 - (i + s)) (j - (i + s))) =
        ∑ s ∈ Finset.range (d + 1),
          (s + 1) * Nat.choose (q + (d - s)) q := by
      apply Finset.sum_congr rfl
      intro s hs
      have hsd : s ≤ d := by
        have := Finset.mem_range.mp hs
        omega
      have hisj : i + s ≤ j := by
        dsimp [d] at hsd
        omega
      have htop : n - 2 - (i + s) = q + (d - s) := by omega
      have hbot : j - (i + s) = d - s := by
        dsimp [d]
        omega
      rw [Nat.add_sub_cancel_left, htop, hbot]
      have hsym : Nat.choose (q + (d - s)) (d - s) =
          Nat.choose (q + (d - s)) q := by
        rw [← Nat.choose_symm (by omega : q ≤ q + (d - s))]
        congr 1
        omega
      rw [hsym]
    _ = ∑ u ∈ Finset.range (d + 1),
          (d - u + 1) * Nat.choose (q + u) q := by
      rw [← Finset.sum_range_reflect
        (fun u ↦ (d - u + 1) * Nat.choose (q + u) q) (d + 1)]
      apply Finset.sum_congr rfl
      intro s hs
      have hsd : s ≤ d := by
        have := Finset.mem_range.mp hs
        omega
      rw [show d + 1 - 1 - s = d - s by omega,
        show d - (d - s) = s by omega]
    _ = Nat.choose (q + d + 2) d := weighted_hockey_stick q d
    _ = Nat.choose (n - i) (j - i) := by rw [hni]

end Erdos521
