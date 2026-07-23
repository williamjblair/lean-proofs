import Research.CrossingFinalGate
import Mathlib.Probability.BorelCantelli
import Mathlib.Data.Nat.Sqrt
import Mathlib.Tactic

open Filter MeasureTheory Set
open scoped ENNReal

namespace Erdos521

noncomputable local instance (p : Prop) : Decidable p := Classical.propDecidable p

lemma weakCrossingCount_append_le (l r : List ℝ) :
    weakCrossingCount l ≤ weakCrossingCount (l ++ r) := by
  induction l using List.twoStepInduction with
  | nil => simp [weakCrossingCount]
  | singleton x =>
      cases r with
      | nil => simp
      | cons y ys => simp [weakCrossingCount, weakCrossingsFrom]
  | cons_cons x y xs ih₀ ih₁ =>
      simpa [weakCrossingCount, weakCrossingsFrom] using ih₁ y

lemma initialCoefficientList_prefix {N M : ℕ} (hNM : N ≤ M) (a : ℕ → ℝ) :
    ∃ r, initialCoefficientList M a = initialCoefficientList N a ++ r := by
  let d := M - N
  have hM : M + 1 = (N + 1) + d := by dsimp [d]; omega
  rw [initialCoefficientList_eq_range_map, initialCoefficientList_eq_range_map, hM,
    List.range_add, List.map_append]
  exact ⟨(List.map (fun x ↦ N + 1 + x) (List.range d)).map a, by simp⟩

lemma integratedCrossingCount_mono (ω : ℕ → Bool) :
    Monotone (integratedCrossingCount ω) := by
  intro N M hNM
  unfold integratedCrossingCount
  obtain ⟨r, hr⟩ := initialCoefficientList_prefix hNM (integratedRademacherSum ω)
  rw [hr]
  exact weakCrossingCount_append_le _ _

/-- Superexponentially sparse indices whose logarithms have asymptotically unit ratio. -/
def squareSparse (j : ℕ) : ℕ := 2 ^ (j * j)

/-- Failure of the endpoint estimate needed to control the entire `j`th square-exponential block. -/
def crossingSparseBad (j : ℕ) : Set (ℕ → Bool) :=
  {ω | (3 : ℝ) / 10 * Real.log ((squareSparse j + 2 : ℕ) : ℝ) <
    (integratedCrossingCount ω (squareSparse (j + 1)) : ℝ)}

lemma squareSparse_block (N : ℕ) (hN : N ≠ 0) :
    let j := Nat.sqrt (Nat.log 2 N)
    squareSparse j ≤ N ∧ N < squareSparse (j + 1) := by
  let k := Nat.log 2 N
  let j := Nat.sqrt k
  have hklo : 2 ^ k ≤ N := Nat.pow_log_le_self 2 hN
  have hjk : j * j ≤ k := Nat.sqrt_le k
  have hlo : squareSparse j ≤ N := by
    exact (Nat.pow_le_pow_right (by omega : 0 < 2) hjk).trans hklo
  have hkhi : N < 2 ^ (k + 1) := by
    simpa [Nat.succ_eq_add_one] using Nat.lt_pow_succ_log_self (by omega : 1 < 2) N
  have hkj : k + 1 ≤ (j + 1) * (j + 1) := by
    apply Nat.succ_le_of_lt
    simpa [j, Nat.succ_eq_add_one] using Nat.lt_succ_sqrt k
  have hhi : N < squareSparse (j + 1) :=
    hkhi.trans_le (Nat.pow_le_pow_right (by omega : 0 < 2) hkj)
  exact ⟨hlo, hhi⟩

/-- Summability of endpoint failures on `2^(j²)` implies the full eventual crossing-rate bound,
because the crossing count is monotone and adjacent logarithmic block endpoints have ratio one. -/
lemma crossing_three_tenths_of_sparseBad_summable
    (hsum : (∑' j : ℕ, rademacherMeasure (crossingSparseBad j)) ≠ ∞) :
    IntegratedCrossingUpperThreeTenths := by
  have hae : ∀ᵐ ω ∂rademacherMeasure,
      ∀ᶠ j : ℕ in atTop, ω ∉ crossingSparseBad j := ae_eventually_notMem hsum
  filter_upwards [hae] with ω hω
  obtain ⟨J, hJ⟩ := eventually_atTop.1 hω
  apply eventually_atTop.2
  refine ⟨squareSparse J, ?_⟩
  intro N hNJ
  have hN0 : N ≠ 0 := by
    have hspos : 0 < squareSparse J := pow_pos (by omega) _
    omega
  let k := Nat.log 2 N
  let j := Nat.sqrt k
  have hblock := squareSparse_block N hN0
  change squareSparse j ≤ N ∧ N < squareSparse (j + 1) at hblock
  have hJj : J ≤ j := by
    apply Nat.le_sqrt.mpr
    apply Nat.le_log_of_pow_le (by omega : 1 < 2)
    simpa [squareSparse] using hNJ
  have hnot := hJ j hJj
  have hend : (integratedCrossingCount ω (squareSparse (j + 1)) : ℝ) ≤
      (3 : ℝ) / 10 * Real.log ((squareSparse j + 2 : ℕ) : ℝ) := by
    exact le_of_not_gt hnot
  have hcountN := integratedCrossingCount_mono ω (Nat.le_of_lt hblock.2)
  have hcountR : (integratedCrossingCount ω N : ℝ) ≤
      (integratedCrossingCount ω (squareSparse (j + 1)) : ℝ) := by
    exact_mod_cast hcountN
  have harg : ((squareSparse j + 2 : ℕ) : ℝ) ≤ (N + 2 : ℕ) := by
    exact_mod_cast Nat.add_le_add_right hblock.1 2
  have hargpos : (0 : ℝ) < ((squareSparse j + 2 : ℕ) : ℝ) := by positivity
  have hlogle : Real.log ((squareSparse j + 2 : ℕ) : ℝ) ≤
      Real.log ((N + 2 : ℕ) : ℝ) := Real.log_le_log hargpos harg
  have hlogpos : 0 < Real.log ((N + 2 : ℕ) : ℝ) := by
    apply Real.log_pos
    norm_cast
    omega
  apply (div_le_iff₀ hlogpos).2
  calc
    (integratedCrossingCount ω N : ℝ) ≤
        (integratedCrossingCount ω (squareSparse (j + 1)) : ℝ) := hcountR
    _ ≤ (3 : ℝ) / 10 * Real.log ((squareSparse j + 2 : ℕ) : ℝ) := hend
    _ ≤ (3 : ℝ) / 10 * Real.log ((N + 2 : ℕ) : ℝ) := by nlinarith

end Erdos521
