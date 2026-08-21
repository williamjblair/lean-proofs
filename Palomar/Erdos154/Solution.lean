import ErdosProblems.Erdos154Sumset

namespace Palomar.Erdos154

open Filter Finset
open scoped Pointwise

def IsSidon (A : Set ℕ) : Prop :=
  ∀ i₁, i₁ ∈ A → ∀ j₁, j₁ ∈ A → ∀ i₂, i₂ ∈ A → ∀ j₂, j₂ ∈ A →
    i₁ + i₂ = j₁ + j₂ → (i₁ = j₁ ∧ i₂ = j₂) ∨ (i₁ = j₂ ∧ i₂ = j₁)

theorem erdos_154_sumset :
    ∀ (m : ℕ) (_hm : 2 ≤ m) (N : ℕ → ℕ) (A : ℕ → Finset ℕ),
      Tendsto (fun k => (N k : ℝ)) atTop atTop →
      (∀ k, ∀ x ∈ A k, x ≤ N k) →
      (∀ k, IsSidon (A k : Set ℕ)) →
      Tendsto (fun k => ((A k).card : ℝ) / Real.sqrt (N k)) atTop (nhds 1) →
      ∀ i < m, Tendsto
        (fun k => (((A k + A k).filter (fun s => s % m = i)).card : ℝ) / ((A k + A k).card : ℝ))
        atTop (nhds (1 / m)) :=
  _root_.Erdos154.erdos_154_sumset

end Palomar.Erdos154
