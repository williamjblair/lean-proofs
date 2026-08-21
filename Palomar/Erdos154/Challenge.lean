import Mathlib

/-!
# Erdős Problem #154: sumsets of Sidon sets are equidistributed in residue classes

Lindström (J. Number Theory 1998) proved that a Sidon set `A ⊆ {1, …, N}` with
`|A| ~ √N` is well distributed in residue classes: the proportion of `A` in each class
mod `m` tends to `1/m`. The theorem below is the sumset form: along any sequence of
Sidon sets `A k ⊆ [0, N k]` with `N k → ∞` and `|A k| / √(N k) → 1`, the sumset
`A k + A k` is equidistributed mod `m` — for each `m ≥ 2` and each residue `i < m`, the
proportion of elements of `A k + A k` congruent to `i` tends to `1/m`. This is the
statement recorded for Erdős Problem #154 in Google DeepMind's Formal Conjectures
(`FormalConjectures/ErdosProblems/154.lean`, added in PR #4340).

`IsSidon` is the Sidon condition in the form Formal Conjectures states it: two ways of
writing a number as a sum of two elements of `A` agree up to order.
-/

namespace Palomar.Erdos154

open Filter Finset
open scoped Pointwise

/-- `A` is a Sidon set: any two representations `i₁ + i₂ = j₁ + j₂` with all four
elements in `A` coincide up to swapping the summands. -/
def IsSidon (A : Set ℕ) : Prop :=
  ∀ i₁, i₁ ∈ A → ∀ j₁, j₁ ∈ A → ∀ i₂, i₂ ∈ A → ∀ j₂, j₂ ∈ A →
    i₁ + i₂ = j₁ + j₂ → (i₁ = j₁ ∧ i₂ = j₂) ∨ (i₁ = j₂ ∧ i₂ = j₁)

/-- **Erdős #154, sumset form.** Along Sidon sets `A k ⊆ [0, N k]` with `N k → ∞` and
`|A k| / √(N k) → 1`, the sumset `A k + A k` is equidistributed modulo every `m ≥ 2`. -/
theorem erdos_154_sumset :
    ∀ (m : ℕ) (_hm : 2 ≤ m) (N : ℕ → ℕ) (A : ℕ → Finset ℕ),
      Tendsto (fun k => (N k : ℝ)) atTop atTop →
      (∀ k, ∀ x ∈ A k, x ≤ N k) →
      (∀ k, IsSidon (A k : Set ℕ)) →
      Tendsto (fun k => ((A k).card : ℝ) / Real.sqrt (N k)) atTop (nhds 1) →
      ∀ i < m, Tendsto
        (fun k => (((A k + A k).filter (fun s => s % m = i)).card : ℝ) / ((A k + A k).card : ℝ))
        atTop (nhds (1 / m)) := by
  sorry

end Palomar.Erdos154
