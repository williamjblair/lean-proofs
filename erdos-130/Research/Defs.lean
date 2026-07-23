import Mathlib

/-! Definitions faithfully encoding Erdős Problem 130. -/

namespace Erdos130

abbrev Point := ℝ × ℝ

def sqDist (p q : Point) : ℝ :=
  (p.1 - q.1) ^ 2 + (p.2 - q.2) ^ 2

def Collinear (p q r : Point) : Prop :=
  (q.1 - p.1) * (r.2 - p.2) = (q.2 - p.2) * (r.1 - p.1)

def Concyclic4 (p q r s : Point) : Prop :=
  ∃ o : Point,
    sqDist o p = sqDist o q ∧
    sqDist o p = sqDist o r ∧
    sqDist o p = sqDist o s

def GeneralPosition (A : Set Point) : Prop :=
  (∀ ⦃p q r⦄, p ∈ A → q ∈ A → r ∈ A →
      p ≠ q → p ≠ r → q ≠ r → ¬ Collinear p q r) ∧
  (∀ ⦃p q r s⦄, p ∈ A → q ∈ A → r ∈ A → s ∈ A →
      p ≠ q → p ≠ r → p ≠ s → q ≠ r → q ≠ s → r ≠ s →
      ¬ Concyclic4 p q r s)

def Adjacent (p q : Point) : Prop :=
  p ≠ q ∧ ∃ n : ℕ, 0 < n ∧ sqDist p q = (n : ℝ) ^ 2

def HasKColoring (A : Set Point) (k : ℕ) : Prop :=
  ∃ color : A → Fin k,
    ∀ x y : A, Adjacent x.1 y.1 → color x ≠ color y

end Erdos130
