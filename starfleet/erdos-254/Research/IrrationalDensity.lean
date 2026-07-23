import Mathlib
import Research.CircleDensity

namespace Erdos254.IrrationalDensity

open Erdos254.CircleDensity Erdos254.TailSemigroup

noncomputable section

lemma fract_mul_nat_eq (x : ℝ) (n : ℕ) :
    Int.fract (x * (n : ℝ)) = Int.fract (Int.fract x * (n : ℝ)) := by
  have hx : x * (n : ℝ) = Int.fract x * (n : ℝ) +
      ((Int.floor x * (n : ℤ) : ℤ) : ℝ) := by
    rw [Int.cast_mul, Int.cast_natCast]
    nlinarith [Int.fract_add_floor x]
  rw [hx, Int.fract_add_intCast]

lemma nearestIntegerDistance_mul_eq_fract_mul (x : ℝ) (n : ℕ) :
    nearestIntegerDistance (x * (n : ℝ)) =
      nearestIntegerDistance (Int.fract x * (n : ℝ)) := by
  unfold nearestIntegerDistance
  rw [fract_mul_nat_eq]

lemma phasePartialSum_eq_fract (A : Set ℕ) (x : ℝ) (N : ℕ) :
    phasePartialSum A x N = phasePartialSum A (Int.fract x) N := by
  classical
  unfold phasePartialSum
  apply Finset.sum_congr rfl
  intro n hn
  exact nearestIntegerDistance_mul_eq_fract_mul x n

/-- Under the canonical all-phase hypothesis, every irrational rotation has
full distinct-subset-sum tail limit on the unit circle. -/
theorem irrational_tailLimit_eq_univ (A : Set ℕ)
    (hphase : ∀ θ : ℝ, θ ∈ Set.Ioo 0 1 →
      Filter.Tendsto (phasePartialSum A θ)
        (Filter.atTop : Filter ℕ) Filter.atTop)
    (θ : ℝ) (hθ : Irrational θ) :
    tailLimit A (fun n => ((θ * (n : ℝ) : ℝ) : UnitAddCircle)) = Set.univ := by
  apply tailLimit_eq_univ_of_all_multiples_diverge A θ
  intro q hq
  let φ := Int.fract ((q : ℝ) * θ)
  have hqθ : Irrational ((q : ℝ) * θ) :=
    hθ.natCast_mul (Nat.ne_of_gt hq)
  have hφpos : 0 < φ := by
    change 0 < Int.fract ((q : ℝ) * θ)
    rw [Int.fract_pos]
    exact hqθ.ne_int _
  have hφlt : φ < 1 := Int.fract_lt_one _
  have hlim := hphase φ ⟨hφpos, hφlt⟩
  have heq : phasePartialSum A ((q : ℝ) * θ) = phasePartialSum A φ := by
    funext N
    exact phasePartialSum_eq_fract A ((q : ℝ) * θ) N
  rw [heq]
  exact hlim

end

end Erdos254.IrrationalDensity
