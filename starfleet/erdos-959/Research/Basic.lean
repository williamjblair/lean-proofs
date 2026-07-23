import Mathlib

/-!
# Erdős Problem 959: formal extremal quantity

This file pins down the quantity in `problem.md`.  Points are enumerated by
`Fin n`; injectivity says that the enumeration represents an `n`-element set.
Squared Euclidean distance is used because squaring is injective on
nonnegative distances and therefore does not change any distance class or its
multiplicity.
-/

noncomputable section

namespace Erdos959

/-- A point of the real affine plane, represented by Cartesian coordinates. -/
abbrev Point := ℝ × ℝ

/-- Squared Euclidean distance.  Equality of `sqDist` is equivalent to equality
of ordinary Euclidean distances. -/
def sqDist (p q : Point) : ℝ :=
  (p.1 - q.1) ^ 2 + (p.2 - q.2) ^ 2

/-- The unordered index pairs, represented uniquely by the orientation `i < j`. -/
def indexPairs (n : ℕ) : Finset (Fin n × Fin n) :=
  (Finset.univ.product Finset.univ).filter fun ij => ij.1 < ij.2

/-- The finite set of distinct squared distances determined by a configuration. -/
def distanceValues {n : ℕ} (P : Fin n → Point) : Finset ℝ :=
  (indexPairs n).image fun ij => sqDist (P ij.1) (P ij.2)

/-- The number of unordered pairs in `P` which determine squared distance `d`. -/
def frequency {n : ℕ} (P : Fin n → Point) (d : ℝ) : ℕ :=
  ((indexPairs n).filter fun ij => sqDist (P ij.1) (P ij.2) = d).card

/-- For a fixed distance `d`, the largest multiplicity among all other
represented distances.  `Finset.sup` returns zero if there is no other value. -/
def runnerUpFrequency {n : ℕ} (P : Fin n → Point) (d : ℝ) : ℕ :=
  ((distanceValues P).erase d).sup (frequency P)

/-- The difference between the largest and second-largest entries in the
multiset of distance multiplicities.  Taking the supremum over all `d` handles
both a unique winner and a tie: non-winners contribute zero by truncated
natural subtraction, while tied winners also contribute zero. -/
def multiplicityGap {n : ℕ} (P : Fin n → Point) : ℕ :=
  (distanceValues P).sup fun d => frequency P d - runnerUpFrequency P d

/-- A configuration faithfully represents a set of size `n`, and has at least
 two distinct distances so that `d₂` exists.  For injective planar
 configurations the latter condition is automatic once `n ≥ 4`; retaining it
 here also resolves the small-`n` ambiguity in the informal problem. -/
def Admissible {n : ℕ} (P : Fin n → Point) : Prop :=
  Function.Injective P ∧ 2 ≤ (distanceValues P).card

/-- A natural number occurs as the top-two multiplicity gap of an admissible
`n`-point configuration. -/
def AttainableGap (n g : ℕ) : Prop :=
  ∃ P : Fin n → Point, Admissible P ∧ multiplicityGap P = g

/-- The extremal quantity asked for in Erdős Problem 959.  There are
`Nat.choose n 2` unordered pairs, so this is a valid finite search interval;
`Nat.findGreatest` returns the largest attainable gap in that interval. -/
def extremalGap (n : ℕ) : ℕ := by
  classical
  exact Nat.findGreatest (AttainableGap n) (Nat.choose n 2)

/-- A two-sided eventual estimate for the extremal gap. -/
def EventuallyBetween (lower upper : ℕ → ℕ) : Prop :=
  ∃ N, ∀ n ≥ N, lower n ≤ extremalGap n ∧ extremalGap n ≤ upper n

/-- The standard meaning of saying that the answer has asymptotic order
`scale`.  Both functions are regarded as real-valued on the filter `atTop`. -/
def HasAsymptoticOrder (scale : ℕ → ℝ) : Prop :=
  Asymptotics.IsTheta Filter.atTop
    (fun n : ℕ => (extremalGap n : ℝ)) scale

end Erdos959
