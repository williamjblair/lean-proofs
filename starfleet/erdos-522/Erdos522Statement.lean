import Mathlib

/-!
This file is the immutable formal statement used by the proof gate for
Erdős Problem 522.  A Boolean coordinate is `true` for sign `+1` and `false`
for sign `-1`.
-/

open scoped BigOperators Topology
open Filter MeasureTheory ProbabilityTheory

namespace Erdos522

universe u_erdos

/-- Encode a Boolean bit as a Rademacher sign in `ℂ`. -/
def rademacherSign (b : Bool) : ℂ := if b then 1 else -1

/-- The degree-`n` truncation `∑_{k=0}^n ε_k z^k`. -/
noncomputable def littlewoodPolynomial {Ω : Type*}
    (ξ : ℕ → Ω → Bool) (n : ℕ) (ω : Ω) : Polynomial ℂ :=
  ∑ k ∈ Finset.range (n + 1),
    Polynomial.C (rademacherSign (ξ k ω)) * Polynomial.X ^ k

/-- Roots in `|z| ≤ 1`, counted with algebraic multiplicity. -/
noncomputable def closedUnitRootCount (p : Polynomial ℂ) : ℕ :=
  (p.roots.filter fun z => ‖z‖ ≤ 1).card

/-- The random root count from the problem. -/
noncomputable def R {Ω : Type*} (ξ : ℕ → Ω → Bool) (n : ℕ) (ω : Ω) : ℕ :=
  closedUnitRootCount (littlewoodPolynomial ξ n ω)

/-- The exact proposition to be proved.  Quantifying over every probability
space carrying measurable independent fair bits makes the formulation
independent of a particular realization of the i.i.d. process. -/
def Erdos522Claim : Prop :=
  ∀ {Ω : Type u_erdos} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : ℕ → Ω → Bool),
    (∀ k, Measurable (ξ k)) →
    iIndepFun ξ μ →
    (∀ k, μ {ω | ξ k ω = true} = (1 : ENNReal) / 2) →
    ∀ᵐ ω ∂μ,
      Tendsto
        (fun n => (R ξ n ω : ℝ) / ((n : ℝ) / 2))
        atTop (𝓝 1)

end Erdos522
