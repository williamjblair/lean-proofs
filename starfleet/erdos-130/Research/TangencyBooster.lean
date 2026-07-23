import Research.Circles
import Mathlib.Combinatorics.HalesJewett

/-!
# A Hales--Jewett tangency booster

This file formalizes the exact geometric identities behind the circle-family
chromatic induction.  Generic parameter choices ensuring distinct/nondegenerate
circles are treated separately.
-/

namespace Erdos130
namespace TangencyBooster

open Combinatorics
open Circle

variable {α ι : Type*} [Fintype ι]

/-- Weighted word evaluation of scalar data on the alphabet. -/
def weighted (γ : ι → ℝ) (f : α → ℝ) (w : ι → α) : ℝ :=
  ∑ i, γ i * f (w i)

/-- Contribution from the fixed coordinates of a combinatorial line. -/
def fixedPart (γ : ι → ℝ) (f : α → ℝ) (l : Line α ι) : ℝ :=
  ∑ i, match l.idxFun i with
    | none => 0
    | some a => γ i * f a

/-- Scale contributed by the active coordinates of a line. -/
def lineScale (γ : ι → ℝ) (l : Line α ι) : ℝ :=
  ∑ i, match l.idxFun i with
    | none => γ i
    | some _ => 0

/-- Every weighted point of a line is its fixed part plus the line scale times
the corresponding alphabet datum. -/
theorem weighted_line (γ : ι → ℝ) (f : α → ℝ) (l : Line α ι) (a : α) :
    weighted γ f (l a) = fixedPart γ f l + lineScale γ l * f a := by
  simp only [weighted, fixedPart, lineScale, Finset.sum_mul]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  cases h : l.idxFun i with
  | none => simp [Line.coe_apply, h]
  | some b => simp [Line.coe_apply, h]

/-- Weighted center of a word. -/
def wordCenter (γ : ι → ℝ) (F : α → Circle) (w : ι → α) : Point :=
  (weighted γ (fun a => (F a).center.1) w,
   weighted γ (fun a => (F a).center.2) w)

/-- Weighted radius coordinate of a word. -/
def wordRadius (γ : ι → ℝ) (F : α → Circle) (w : ι → α) : ℝ :=
  weighted γ (fun a => (F a).radius) w

/-- Large circle associated with a word. -/
def largeCircle (γ : ι → ℝ) (F : α → Circle) (R : ℝ) (w : ι → α) : Circle where
  center := wordCenter γ F w
  radius := R - wordRadius γ F w

/-- Small circle in the copy attached to a combinatorial line. -/
def smallCircle (γ : ι → ℝ) (F : α → Circle) (R : ℝ)
    (u : Line α ι → Point) (l : Line α ι) (a : α) : Circle where
  center :=
    let shift := R - fixedPart γ (fun b => (F b).radius) l
    ((wordCenter γ F (l a)).1 + shift * (u l).1,
     (wordCenter γ F (l a)).2 + shift * (u l).2)
  radius := lineScale γ l * (F a).radius

/-- Each large circle on a line is externally tangent to its matched small
circle, provided the chosen direction is a unit vector. -/
theorem matched_externallyTangent (γ : ι → ℝ) (F : α → Circle) (R : ℝ)
    (u : Line α ι → Point) (hu : ∀ l, (u l).1 ^ 2 + (u l).2 ^ 2 = 1)
    (l : Line α ι) (a : α) :
    ExternallyTangent (largeCircle γ F R (l a)) (smallCircle γ F R u l a) := by
  rw [ExternallyTangent]
  simp only [largeCircle, smallCircle, wordRadius, wordCenter, sqDist]
  rw [weighted_line γ (fun b => (F b).radius) l a]
  have hunit := hu l
  linear_combination
    (R - fixedPart γ (fun b => (F b).radius) l)^2 * hunit

/-- Every old external tangency is reproduced inside each small homothetic copy. -/
theorem small_externallyTangent (γ : ι → ℝ) (F : α → Circle) (R : ℝ)
    (u : Line α ι → Point) (l : Line α ι) {a b : α}
    (hab : ExternallyTangent (F a) (F b)) :
    ExternallyTangent (smallCircle γ F R u l a) (smallCircle γ F R u l b) := by
  rw [ExternallyTangent] at hab ⊢
  simp only [sqDist] at hab
  simp only [smallCircle, wordCenter, sqDist]
  rw [weighted_line γ (fun z => (F z).center.1) l a,
      weighted_line γ (fun z => (F z).center.1) l b,
      weighted_line γ (fun z => (F z).center.2) l a,
      weighted_line γ (fun z => (F z).center.2) l b]
  linear_combination (lineScale γ l)^2 * hab

/-- The indexed family consisting of all large word circles and one small
copy for every combinatorial line. -/
def boostedCircle (γ : ι → ℝ) (F : α → Circle) (R : ℝ)
    (u : Line α ι → Point) :
    Sum (ι → α) (Line α ι × α) → Circle
  | .inl w => largeCircle γ F R w
  | .inr la => smallCircle γ F R u la.1 la.2

/-- An indexed circle family has no proper coloring by `k` colors when tangent
pairs are regarded as edges. -/
def NoKColoring (F : α → Circle) (k : ℕ) : Prop :=
  ∀ color : α → Fin k,
    ∃ a b : α, a ≠ b ∧ ExternallyTangent (F a) (F b) ∧ color a = color b

/-- Hales--Jewett plus the two exact tangency identities raises the required
number of colors by one.  This theorem concerns an indexed family; later generic
parameter choices ensure that its circle data (and hence centers) are distinct. -/
theorem exists_boosted_noKColoring [Finite α] {k : ℕ} (F : α → Circle)
    (hF : NoKColoring F k) :
    ∃ (ι : Type) (_ : Fintype ι),
      ∀ (γ : ι → ℝ) (R : ℝ) (u : Line α ι → Point),
        (∀ l, (u l).1 ^ 2 + (u l).2 ^ 2 = 1) →
        NoKColoring (boostedCircle γ F R u) (k + 1) := by
  obtain ⟨ι, ιfin, hHJ⟩ := Line.exists_mono_in_high_dimension α (Fin (k + 1))
  refine ⟨ι, ιfin, ?_⟩
  intro γ R u hu color
  obtain ⟨l, c, hmono⟩ := hHJ (fun w => color (.inl w))
  by_cases hex : ∃ a : α, color (.inr (l, a)) = c
  · obtain ⟨a, ha⟩ := hex
    exact ⟨.inl (l a), .inr (l, a), by simp,
      matched_externallyTangent γ F R u hu l a, (hmono a).trans ha.symm⟩
  · have hne (a : α) : color (.inr (l, a)) ≠ c := by
      intro h
      exact hex ⟨a, h⟩
    let smallColor : α → Fin k := fun a =>
      (finSuccAboveEquiv c).symm ⟨color (.inr (l, a)), hne a⟩
    obtain ⟨a, b, hab, ht, hc⟩ := hF smallColor
    have hc' : color (.inr (l, a)) = color (.inr (l, b)) := by
      have hs : (⟨color (.inr (l, a)), hne a⟩ :
          {x : Fin (k + 1) // x ≠ c}) = ⟨color (.inr (l, b)), hne b⟩ := by
        apply (finSuccAboveEquiv c).symm.injective
        exact hc
      exact congrArg Subtype.val hs
    exact ⟨.inr (l, a), .inr (l, b), by simpa using hab,
      small_externallyTangent γ F R u l ht, hc'⟩

/-- Iterating the booster gives finite indexed circle data whose tangency
relation requires arbitrarily many colors.  This statement does not yet assert
injectivity or positivity of the circle-data map; those are open genericity
obligations in the final geometric construction. -/
theorem exists_finite_indexed_noKColoring (k : ℕ) :
    ∃ (α : Type) (_ : Finite α), ∃ F : α → Circle, NoKColoring F k := by
  induction k with
  | zero =>
      let C : Circle := ⟨(0, 0), 1⟩
      refine ⟨Unit, inferInstance, fun _ => C, ?_⟩
      intro color
      exact Fin.elim0 (color ())
  | succ k ih =>
      obtain ⟨α, αfin, F, hF⟩ := ih
      letI : Finite α := αfin
      letI : Fintype α := Fintype.ofFinite α
      obtain ⟨ι, ιfin, hboost⟩ := exists_boosted_noKColoring F hF
      letI : Fintype ι := ιfin
      letI : Finite (Line α ι) := Finite.of_injective
        (fun l : Line α ι => l.idxFun) (by
          rintro ⟨l, hl⟩ ⟨m, hm⟩ h
          simp only at h
          subst m
          rfl)
      let γ : ι → ℝ := fun _ => 1
      let u : Line α ι → Point := fun _ => (1, 0)
      let F' := boostedCircle γ F 0 u
      have hu : ∀ l, (u l).1 ^ 2 + (u l).2 ^ 2 = 1 := by
        intro l
        norm_num [u]
      refine ⟨Sum (ι → α) (Line α ι × α), inferInstance, F', ?_⟩
      exact hboost γ 0 u hu

end TangencyBooster
end Erdos130
