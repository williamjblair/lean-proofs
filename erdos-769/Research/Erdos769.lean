import Mathlib

/-!
# Erdős Problem 769: a faithful formal specification

A homothetic copy of the standard cube has a positive common side length and
is translated without rotation.  We represent all cubes by half-open boxes.
For a finite family with positive side lengths, unique coverage of `[0,1)^n`
is equivalent to the usual decomposition of the closed unit cube into closed
homothetic cubes with pairwise disjoint interiors.  The half-open convention
assigns shared boundary points to one tile and avoids a separate
"disjoint interiors" predicate.
-/

namespace Erdos769

/-- An axis-parallel homothetic copy of the standard `n`-cube. -/
structure Cube (n : ℕ) where
  lower : Fin n → ℝ
  side : ℝ

/-- Membership in the half-open cube `∏ j, [lower j, lower j + side)`. -/
def Cube.Mem {n : ℕ} (Q : Cube n) (x : Fin n → ℝ) : Prop :=
  ∀ j, Q.lower j ≤ x j ∧ x j < Q.lower j + Q.side

/-- Membership in the half-open unit cube `[0,1)^n`. -/
def InUnit {n : ℕ} (x : Fin n → ℝ) : Prop :=
  ∀ j, 0 ≤ x j ∧ x j < 1

/-- A cube is nondegenerate and contained in the closed unit cube. -/
def Cube.InsideUnit {n : ℕ} (Q : Cube n) : Prop :=
  0 < Q.side ∧ ∀ j, 0 ≤ Q.lower j ∧ Q.lower j + Q.side ≤ 1

/-- `tiles` is an exact decomposition of the unit `n`-cube: every tile is a
positive homothet inside the unit cube, and every point of `[0,1)^n` belongs
to exactly one half-open tile. -/
def IsTiling {n k : ℕ} (tiles : Fin k → Cube n) : Prop :=
  (∀ i, (tiles i).InsideUnit) ∧
    ∀ x, InUnit x → ∃! i, (tiles i).Mem x

/-- Exactly `k` homothetic `n`-cubes can tile the unit `n`-cube. -/
def Admissible (n k : ℕ) : Prop :=
  ∃ tiles : Fin k → Cube n, IsTiling tiles

/-- `c` is the minimal eventual-admissibility threshold in dimension `n`.
The second conjunct expresses minimality: when `c > 0`, `c-1` itself is not
admissible. -/
def IsCutoff (n c : ℕ) : Prop :=
  (∀ k, c ≤ k → Admissible n k) ∧ (c = 0 ∨ ¬Admissible n (c - 1))

/-- The highlighted question in Erdős Problem 769, in integer-rational form.
It says that there is an absolute positive constant `A/B` such that every
minimal cutoff satisfies `c(n) ≥ (A/B) n^n` for all sufficiently large `n`.
Using positive natural `A,B` is equivalent to the usual real-valued `≫`
notation. -/
def Erdos769LowerBound : Prop :=
  ∃ A B N : ℕ,
    0 < A ∧ 0 < B ∧
      ∀ n c : ℕ, N ≤ n → IsCutoff n c → A * n ^ n ≤ B * c

end Erdos769
