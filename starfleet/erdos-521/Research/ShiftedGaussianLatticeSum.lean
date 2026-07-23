import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

open scoped BigOperators

namespace Erdos521

noncomputable local instance shiftedGaussianDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

lemma exp_neg_pos_lt_one {b : ℝ} (hb : 0 < b) :
    0 < Real.exp (-b) ∧ Real.exp (-b) < 1 := by
  constructor
  · positivity
  · rw [Real.exp_lt_one_iff]
    linarith

lemma geometric_exp_neg_inv_le {b : ℝ} (hb : 0 < b) :
    (1 - Real.exp (-b))⁻¹ ≤ 1 + 1 / b := by
  have he : 1 + b ≤ Real.exp b := by
    simpa [add_comm] using Real.add_one_le_exp b
  have heb : 0 < Real.exp b := Real.exp_pos b
  have hmul : Real.exp (-b) * Real.exp b = 1 := by
    rw [← Real.exp_add]
    simp
  have hden : 0 < 1 - Real.exp (-b) := sub_pos.mpr (exp_neg_pos_lt_one hb).2
  rw [← one_div]
  rw [one_div_le hden (by positivity : 0 < 1 + 1 / b)]
  field_simp
  nlinarith

private lemma shifted_exp_left_pointwise {b c : ℝ} (hb : 0 < b) (z : ℤ)
    (hz : z ≤ ⌊c⌋) :
    Real.exp (-b * |(z : ℝ) - c|) ≤
      Real.exp (-b) ^ (⌊c⌋ - z).toNat := by
  have hzcast : (z : ℝ) ≤ (⌊c⌋ : ℝ) := by exact_mod_cast hz
  have hzc : (z : ℝ) ≤ c := hzcast.trans (Int.floor_le c)
  have habs : |(z : ℝ) - c| = c - z := by
    rw [abs_of_nonpos (sub_nonpos.mpr hzc)]
    ring
  have hd0 : 0 ≤ ⌊c⌋ - z := sub_nonneg.mpr hz
  have hnatInt : (((⌊c⌋ - z).toNat : ℕ) : ℤ) = ⌊c⌋ - z :=
    Int.toNat_of_nonneg hd0
  have hnat : (((⌊c⌋ - z).toNat : ℕ) : ℝ) = (⌊c⌋ : ℝ) - z := by
    exact_mod_cast hnatInt
  have hdist : (((⌊c⌋ - z).toNat : ℕ) : ℝ) ≤ |(z : ℝ) - c| := by
    rw [hnat, habs]
    exact sub_le_sub_right (Int.floor_le c) _
  rw [← Real.exp_nat_mul]
  apply Real.exp_le_exp.mpr
  nlinarith

private lemma shifted_exp_right_pointwise {b c : ℝ} (hb : 0 < b) (z : ℤ)
    (hz : ¬z ≤ ⌊c⌋) :
    Real.exp (-b * |(z : ℝ) - c|) ≤
      Real.exp (-b) ^ (z - ⌊c⌋ - 1).toNat := by
  have hqz : ⌊c⌋ < z := lt_of_not_ge hz
  have hcz : c < (z : ℝ) := by
    rw [← Int.floor_lt]
    exact hqz
  have habs : |(z : ℝ) - c| = z - c := abs_of_pos (sub_pos.mpr hcz)
  have hd0 : 0 ≤ z - ⌊c⌋ - 1 := by omega
  have hnat : (((z - ⌊c⌋ - 1).toNat : ℕ) : ℝ) =
      (z : ℝ) - (⌊c⌋ : ℝ) - 1 := by
    rw [show (((z - ⌊c⌋ - 1).toNat : ℕ) : ℝ) =
      ((z - ⌊c⌋ - 1).toNat : ℤ) by norm_num,
      Int.toNat_of_nonneg hd0]
    norm_num
  have hdist : (((z - ⌊c⌋ - 1).toNat : ℕ) : ℝ) ≤ |(z : ℝ) - c| := by
    rw [hnat, habs]
    have hc := Int.lt_floor_add_one c
    linarith
  rw [← Real.exp_nat_mul]
  apply Real.exp_le_exp.mpr
  nlinarith

/-- A uniform finite shifted-lattice Gaussian bound, proved by comparing each side of the center to
a geometric series. -/
lemma finset_sum_shifted_exp_neg_abs_le (S : Finset ℤ) {b c : ℝ} (hb : 0 < b) :
    (∑ z ∈ S, Real.exp (-b * |(z : ℝ) - c|)) ≤ 2 * (1 + 1 / b) := by
  let q : ℤ := ⌊c⌋
  let L := S.filter fun z ↦ z ≤ q
  let R := S.filter fun z ↦ ¬z ≤ q
  let r := Real.exp (-b)
  have hr0 : 0 ≤ r := (Real.exp_pos _).le
  have hr1 : r < 1 := (exp_neg_pos_lt_one hb).2
  have hsumm : Summable (fun n : ℕ ↦ r ^ n) := summable_geometric_of_norm_lt_one (by
    rw [Real.norm_eq_abs, abs_of_nonneg hr0]
    exact hr1)
  have hleft : (∑ z ∈ L, Real.exp (-b * |(z : ℝ) - c|)) ≤ (1 - r)⁻¹ := by
    calc
      _ ≤ ∑ z ∈ L, r ^ (q - z).toNat := by
        apply Finset.sum_le_sum
        intro z hz
        have hzq : z ≤ q := (Finset.mem_filter.mp hz).2
        exact shifted_exp_left_pointwise hb z hzq
      _ = ∑ n ∈ L.image (fun z ↦ (q - z).toNat), r ^ n := by
        rw [Finset.sum_image]
        intro z hz z' hz' heq
        have hzq : z ≤ q := (Finset.mem_filter.mp hz).2
        have hzq' : z' ≤ q := (Finset.mem_filter.mp hz').2
        have h0 : 0 ≤ q - z := sub_nonneg.mpr hzq
        have h0' : 0 ≤ q - z' := sub_nonneg.mpr hzq'
        have hsub : q - z = q - z' := by
          calc
            q - z = (((q - z).toNat : ℕ) : ℤ) := (Int.toNat_of_nonneg h0).symm
            _ = (((q - z').toNat : ℕ) : ℤ) := by exact_mod_cast heq
            _ = q - z' := Int.toNat_of_nonneg h0'
        omega
      _ ≤ ∑' n : ℕ, r ^ n := hsumm.sum_le_tsum _ (fun _ _ ↦ pow_nonneg hr0 _)
      _ = (1 - r)⁻¹ := tsum_geometric_of_norm_lt_one (by
        rw [Real.norm_eq_abs, abs_of_nonneg hr0]
        exact hr1)
  have hright : (∑ z ∈ R, Real.exp (-b * |(z : ℝ) - c|)) ≤ (1 - r)⁻¹ := by
    calc
      _ ≤ ∑ z ∈ R, r ^ (z - q - 1).toNat := by
        apply Finset.sum_le_sum
        intro z hz
        have hzq : ¬z ≤ q := (Finset.mem_filter.mp hz).2
        exact shifted_exp_right_pointwise hb z hzq
      _ = ∑ n ∈ R.image (fun z ↦ (z - q - 1).toNat), r ^ n := by
        rw [Finset.sum_image]
        intro z hz z' hz' heq
        have hzq : ¬z ≤ q := (Finset.mem_filter.mp hz).2
        have hzq' : ¬z' ≤ q := (Finset.mem_filter.mp hz').2
        have h0 : 0 ≤ z - q - 1 := by omega
        have h0' : 0 ≤ z' - q - 1 := by omega
        have hsub : z - q - 1 = z' - q - 1 := by
          calc
            z - q - 1 = (((z - q - 1).toNat : ℕ) : ℤ) :=
              (Int.toNat_of_nonneg h0).symm
            _ = (((z' - q - 1).toNat : ℕ) : ℤ) := by exact_mod_cast heq
            _ = z' - q - 1 := Int.toNat_of_nonneg h0'
        omega
      _ ≤ ∑' n : ℕ, r ^ n := hsumm.sum_le_tsum _ (fun _ _ ↦ pow_nonneg hr0 _)
      _ = (1 - r)⁻¹ := tsum_geometric_of_norm_lt_one (by
        rw [Real.norm_eq_abs, abs_of_nonneg hr0]
        exact hr1)
  have hsplit : (∑ z ∈ S, Real.exp (-b * |(z : ℝ) - c|)) =
      (∑ z ∈ L, Real.exp (-b * |(z : ℝ) - c|)) +
      (∑ z ∈ R, Real.exp (-b * |(z : ℝ) - c|)) := by
    calc
      _ = ∑ z ∈ L ∪ R, Real.exp (-b * |(z : ℝ) - c|) := by
        rw [show L ∪ R = S from
          Finset.filter_union_filter_neg_eq (fun z : ℤ ↦ z ≤ q) S]
      _ = _ := Finset.sum_union (Finset.disjoint_filter_filter_neg S S
        (fun z : ℤ ↦ z ≤ q))
  rw [hsplit]
  calc
    _ ≤ 2 * (1 - r)⁻¹ := by linarith
    _ ≤ 2 * (1 + 1 / b) := by
      gcongr
      exact geometric_exp_neg_inv_le hb

/-- Quadratic Gaussian lattice sum: completing the square and linearizing the square gives a
uniform `O(1/sqrt a)` bound, here in a form avoiding square-root side conditions. -/
lemma finset_sum_shifted_gaussian_le (S : Finset ℤ) {a c L : ℝ}
    (ha : 0 < a) (hL : 0 < L) :
    (∑ z ∈ S, Real.exp (-a * ((z : ℝ) - c) ^ 2)) ≤
      Real.exp (a * L ^ 2) * 2 * (1 + 1 / (2 * a * L)) := by
  have hb : 0 < 2 * a * L := by positivity
  calc
    _ ≤ ∑ z ∈ S, Real.exp (a * L ^ 2) *
        Real.exp (-(2 * a * L) * |(z : ℝ) - c|) := by
      apply Finset.sum_le_sum
      intro z hz
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have hs : 0 ≤ (|(z : ℝ) - c| - L) ^ 2 := sq_nonneg _
      nlinarith [sq_abs ((z : ℝ) - c)]
    _ = Real.exp (a * L ^ 2) *
        (∑ z ∈ S, Real.exp (-(2 * a * L) * |(z : ℝ) - c|)) := by
      rw [Finset.mul_sum]
    _ ≤ Real.exp (a * L ^ 2) * (2 * (1 + 1 / (2 * a * L))) := by
      gcongr
      exact finset_sum_shifted_exp_neg_abs_le S hb
    _ = _ := by ring

end Erdos521
