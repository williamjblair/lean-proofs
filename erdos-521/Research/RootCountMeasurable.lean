import Research.OneSidedReduction
import Mathlib.Tactic

open MeasureTheory Set

namespace Erdos521

/-- Restrict an infinite coefficient sequence to the coefficients through degree `n`. -/
def degreePrefix (n : ℕ) (ω : ℕ → Bool) : Fin (n + 1) → Bool :=
  fun i ↦ ω i.val

/-- Extend a finite degree prefix by `false`; values beyond degree `n` never affect `f_n`. -/
def extendDegreePrefix (n : ℕ) (x : Fin (n + 1) → Bool) : ℕ → Bool :=
  fun k ↦ if h : k < n + 1 then x ⟨k, h⟩ else false

lemma extendDegreePrefix_degreePrefix {n k : ℕ} (ω : ℕ → Bool) (hk : k ≤ n) :
    extendDegreePrefix n (degreePrefix n ω) k = ω k := by
  simp [extendDegreePrefix, degreePrefix, show k < n + 1 by omega]

lemma littlewoodPolynomial_eq_of_degree_prefix {ω η : ℕ → Bool} {n : ℕ}
    (h : ∀ k ≤ n, ω k = η k) :
    littlewoodPolynomial ω n = littlewoodPolynomial η n := by
  unfold littlewoodPolynomial
  apply Finset.sum_congr rfl
  intro k hk
  have hkn : k ≤ n := by
    have := Finset.mem_range.mp hk
    omega
  rw [h k hkn]

lemma rightRootCount_eq_of_degree_prefix {ω η : ℕ → Bool} {n : ℕ}
    (h : ∀ k ≤ n, ω k = η k) :
    rightRootCount ω n = rightRootCount η n := by
  unfold rightRootCount
  rw [littlewoodPolynomial_eq_of_degree_prefix h]

lemma leftRootCount_eq_of_degree_prefix {ω η : ℕ → Bool} {n : ℕ}
    (h : ∀ k ≤ n, ω k = η k) :
    leftRootCount ω n = leftRootCount η n := by
  unfold leftRootCount
  rw [littlewoodPolynomial_eq_of_degree_prefix h]

/-- The one-sided root count computed from a finite coefficient assignment. -/
noncomputable def finiteRightRootCount (n : ℕ) (x : Fin (n + 1) → Bool) : ℕ :=
  rightRootCount (extendDegreePrefix n x) n

lemma finiteRightRootCount_degreePrefix (n : ℕ) (ω : ℕ → Bool) :
    finiteRightRootCount n (degreePrefix n ω) = rightRootCount ω n := by
  apply rightRootCount_eq_of_degree_prefix
  intro k hk
  exact extendDegreePrefix_degreePrefix ω hk

lemma measurable_degreePrefix (n : ℕ) : Measurable (degreePrefix n) := by
  unfold degreePrefix
  fun_prop

lemma measurable_finiteRightRootCount (n : ℕ) : Measurable (finiteRightRootCount n) := by
  exact measurable_of_finite _

/-- For each degree, the positive-side distinct-root count is a measurable finite-cylinder random
variable. -/
lemma measurable_rightRootCount (n : ℕ) :
    Measurable (fun ω : ℕ → Bool ↦ rightRootCount ω n) := by
  have hcomp := (measurable_finiteRightRootCount n).comp (measurable_degreePrefix n)
  rw [show (fun ω : ℕ → Bool ↦ rightRootCount ω n) =
      finiteRightRootCount n ∘ degreePrefix n by
    funext ω
    exact (finiteRightRootCount_degreePrefix n ω).symm]
  exact hcomp

lemma measurable_leftRootCount (n : ℕ) :
    Measurable (fun ω : ℕ → Bool ↦ leftRootCount ω n) := by
  rw [show (fun ω : ℕ → Bool ↦ leftRootCount ω n) =
      (fun η : ℕ → Bool ↦ rightRootCount η n) ∘ oddTwist by
    funext ω
    exact (rightRootCount_oddTwist ω n).symm]
  exact (measurable_rightRootCount n).comp measurePreserving_oddTwist.measurable

lemma measurable_rightRootRatio (n : ℕ) :
    Measurable (fun ω : ℕ → Bool ↦
      (rightRootCount ω n : ℝ) / Real.log (n : ℝ)) := by
  exact ((MeasurableEmbedding.natCast (α := ℝ)).measurable.comp
    (measurable_rightRootCount n)).div_const _

end Erdos521
