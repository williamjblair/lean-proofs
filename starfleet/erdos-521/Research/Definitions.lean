import Mathlib.Probability.ProductMeasure
import Mathlib.Probability.Distributions.Bernoulli
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

open Filter MeasureTheory ProbabilityTheory
open scoped Topology unitInterval

namespace Erdos521

/-- The parameter `1/2` as an element of the unit interval. -/
noncomputable def half : unitInterval := ⟨(1 : ℝ) / 2, by constructor <;> norm_num⟩

/-- One fair coin, represented by a Boolean.  `true` will encode `+1`. -/
noncomputable def fairCoin : Measure Bool :=
  ProbabilityTheory.bernoulliMeasure true false half

/-- The law of an infinite sequence of independent fair coins. -/
noncomputable def rademacherMeasure : Measure (ℕ → Bool) :=
  Measure.infinitePi (fun _ : ℕ ↦ fairCoin)

/-- Turn a Boolean coin into a real Rademacher sign. -/
def sign (b : Bool) : ℝ := if b then 1 else -1

/-- The degree-`n` Littlewood polynomial associated with an infinite sign sequence. -/
noncomputable def littlewoodPolynomial (ω : ℕ → Bool) (n : ℕ) : Polynomial ℝ :=
  ∑ k ∈ Finset.range (n + 1), Polynomial.monomial k (sign (ω k))

/-- Number of distinct real roots of the degree-`n` Littlewood polynomial. -/
noncomputable def realRootCount (ω : ℕ → Bool) (n : ℕ) : ℕ :=
  Set.ncard ((littlewoodPolynomial ω n).rootSet ℝ)

/-- The assertion asked about in Erdős Problem 521.

The first few values at `n = 0, 1` are immaterial to the limit; Lean's totalized division and
logarithm make the displayed sequence defined there as well. -/
def Claim : Prop :=
  ∀ᵐ ω ∂rademacherMeasure,
    Tendsto (fun n : ℕ ↦ (realRootCount ω n : ℝ) / Real.log (n : ℝ))
      atTop (𝓝 ((2 : ℝ) / Real.pi))

end Erdos521
