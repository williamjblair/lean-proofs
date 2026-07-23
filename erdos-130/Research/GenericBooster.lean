import Research.TangencyBooster
import Mathlib.Algebra.MvPolynomial.Funext

/-!
# Genericity gates for the Hales--Jewett circle booster

This file develops the finite algebraic selection needed to retain positivity,
distinct centers, absence of internal tangencies, and absence of coaxial triples.
-/

namespace Erdos130
namespace Circle
namespace GenericBooster

open TangencyBooster

/-- The signed squared gap from internal tangency. -/
def internalGap (A B : Circle) : ℝ :=
  sqDist A.center B.center - (A.radius - B.radius) ^ 2

/-- The finite-family genericity package used by the induction. -/
def GoodFamily {α : Type*} (F : α → Circle) : Prop :=
  (∀ a, 0 < (F a).radius) ∧
  Function.Injective (fun a => (F a).center) ∧
  (∀ ⦃a b⦄, a ≠ b → internalGap (F a) (F b) ≠ 0) ∧
  (∀ v : Fin 3 → α, Function.Injective v →
    ¬ Coaxial3 (F (v 0)) (F (v 1)) (F (v 2)))

/-- Two-coordinate Minkowski sum followed by the large-circle radius rule. -/
def cornerCircle (t R : ℝ) (A C : Circle) : Circle where
  center := (t * A.center.1 + C.center.1, t * A.center.2 + C.center.2)
  radius := R - (t * A.radius + C.radius)

/-- Center-area determinant of the three corners `(A+C),(A+D),(B+C)`. -/
theorem corner_center_det (t R : ℝ) (A B C D : Circle) :
    detCols (fun _ => 1) (fun Z => Z.center.1) (fun Z => Z.center.2)
      (cornerCircle t R A C) (cornerCircle t R A D) (cornerCircle t R B C) =
    t * ((D.center.1 - C.center.1) * (B.center.2 - A.center.2) -
      (D.center.2 - C.center.2) * (B.center.1 - A.center.1)) := by
  simp only [detCols, cornerCircle]
  ring

/-- Varying `R` exposes the center/radius cross component in the `1,x,q`
coaxial minor. -/
theorem corner_xq_R_diff (A B C D : Circle) :
    detCols (fun _ => 1) (fun Z => Z.center.1) q
        (cornerCircle 1 1 A C) (cornerCircle 1 1 A D) (cornerCircle 1 1 B C) -
      detCols (fun _ => 1) (fun Z => Z.center.1) q
        (cornerCircle 1 0 A C) (cornerCircle 1 0 A D) (cornerCircle 1 0 B C) =
    2 * ((D.center.1 - C.center.1) * (B.radius - A.radius) -
      (B.center.1 - A.center.1) * (D.radius - C.radius)) := by
  simp only [detCols, cornerCircle, q]
  ring

/-- The analogous `1,y,q` coefficient identity. -/
theorem corner_yq_R_diff (A B C D : Circle) :
    detCols (fun _ => 1) (fun Z => Z.center.2) q
        (cornerCircle 1 1 A C) (cornerCircle 1 1 A D) (cornerCircle 1 1 B C) -
      detCols (fun _ => 1) (fun Z => Z.center.2) q
        (cornerCircle 1 0 A C) (cornerCircle 1 0 A D) (cornerCircle 1 0 B C) =
    2 * ((D.center.2 - C.center.2) * (B.radius - A.radius) -
      (B.center.2 - A.center.2) * (D.radius - C.radius)) := by
  simp only [detCols, cornerCircle, q]
  ring

/-- Exact curvature minor when the two source chords are proportional. -/
theorem corner_xq_of_proportional (t κ : ℝ) (A B C D : Circle)
    (hx : B.center.1 - A.center.1 = κ * (D.center.1 - C.center.1))
    (hy : B.center.2 - A.center.2 = κ * (D.center.2 - C.center.2))
    (hr : B.radius - A.radius = κ * (D.radius - C.radius)) :
    detCols (fun _ => 1) (fun Z => Z.center.1) q
      (cornerCircle t 0 A C) (cornerCircle t 0 A D) (cornerCircle t 0 B C) =
    t * κ * (t * κ - 1) * (D.center.1 - C.center.1) *
      internalGap C D := by
  have bx : B.center.1 = A.center.1 + κ * (D.center.1 - C.center.1) := by linarith
  have hby : B.center.2 = A.center.2 + κ * (D.center.2 - C.center.2) := by linarith
  have br : B.radius = A.radius + κ * (D.radius - C.radius) := by linarith
  simp only [detCols, cornerCircle, q, internalGap, sqDist]
  rw [bx, hby, br]
  ring

theorem corner_yq_of_proportional (t κ : ℝ) (A B C D : Circle)
    (hx : B.center.1 - A.center.1 = κ * (D.center.1 - C.center.1))
    (hy : B.center.2 - A.center.2 = κ * (D.center.2 - C.center.2))
    (hr : B.radius - A.radius = κ * (D.radius - C.radius)) :
    detCols (fun _ => 1) (fun Z => Z.center.2) q
      (cornerCircle t 0 A C) (cornerCircle t 0 A D) (cornerCircle t 0 B C) =
    t * κ * (t * κ - 1) * (D.center.2 - C.center.2) *
      internalGap C D := by
  have bx : B.center.1 = A.center.1 + κ * (D.center.1 - C.center.1) := by linarith
  have hby : B.center.2 = A.center.2 + κ * (D.center.2 - C.center.2) := by linarith
  have br : B.radius = A.radius + κ * (D.radius - C.radius) := by linarith
  simp only [detCols, cornerCircle, q, internalGap, sqDist]
  rw [bx, hby, br]
  ring

/-- The key corner lemma: two nontrivial source chords, one of which is not
Minkowski-null, can be made into a noncoaxial three-corner configuration by
choosing `t,R`. -/
theorem exists_noncoaxial_corner (A B C D : Circle)
    (hAB : A.center ≠ B.center) (hCD : C.center ≠ D.center)
    (hgap : internalGap C D ≠ 0) :
    ∃ t R : ℝ, ¬ Coaxial3 (cornerCircle t R A C)
      (cornerCircle t R A D) (cornerCircle t R B C) := by
  by_contra hn
  push_neg at hn
  have hxy0 := (hn 1 0).1
  rw [corner_center_det] at hxy0
  norm_num at hxy0
  have hxR1 := (hn 1 1).2.1
  have hxR0 := (hn 1 0).2.1
  have hyR1 := (hn 1 1).2.2.1
  have hyR0 := (hn 1 0).2.2.1
  have hxr :
      (D.center.1 - C.center.1) * (B.radius - A.radius) -
        (B.center.1 - A.center.1) * (D.radius - C.radius) = 0 := by
    have hd := corner_xq_R_diff A B C D
    linarith
  have hyr :
      (D.center.2 - C.center.2) * (B.radius - A.radius) -
        (B.center.2 - A.center.2) * (D.radius - C.radius) = 0 := by
    have hd := corner_yq_R_diff A B C D
    linarith
  by_cases hux : D.center.1 - C.center.1 = 0
  · have huy : D.center.2 - C.center.2 ≠ 0 := by
      intro hy
      apply hCD
      apply Prod.ext <;> linarith
    let κ := (B.center.2 - A.center.2) / (D.center.2 - C.center.2)
    have hvy : B.center.2 - A.center.2 = κ * (D.center.2 - C.center.2) := by
      dsimp [κ]
      field_simp
    have hvx : B.center.1 - A.center.1 = κ * (D.center.1 - C.center.1) := by
      rw [hux]
      simp only [mul_zero]
      rw [hux] at hxy0
      simp only [zero_mul, zero_sub] at hxy0
      have hp : (D.center.2 - C.center.2) *
          (B.center.1 - A.center.1) = 0 := by linarith
      exact (mul_eq_zero.mp hp).resolve_left huy
    have hvr : B.radius - A.radius = κ * (D.radius - C.radius) := by
      have hp : (D.center.2 - C.center.2) *
          ((B.radius - A.radius) - κ * (D.radius - C.radius)) = 0 := by
        rw [hvy] at hyr
        linear_combination hyr
      have := (mul_eq_zero.mp hp).resolve_left huy
      linarith
    have hk : κ ≠ 0 := by
      intro hk
      rw [hk] at hvx hvy
      simp only [zero_mul] at hvx hvy
      apply hAB
      apply Prod.ext <;> linarith
    have hy0 := (hn 1 0).2.2.1
    have hy2 := (hn 2 0).2.2.1
    rw [corner_yq_of_proportional 1 κ A B C D hvx hvy hvr] at hy0
    rw [corner_yq_of_proportional 2 κ A B C D hvx hvy hvr] at hy2
    ring_nf at hy0 hy2
    have hz : κ * (D.center.2 - C.center.2) * internalGap C D = 0 := by
      nlinarith [hy0, hy2]
    exact hgap ((mul_eq_zero.mp hz).resolve_left (mul_ne_zero hk huy))
  · let κ := (B.center.1 - A.center.1) / (D.center.1 - C.center.1)
    have hvx : B.center.1 - A.center.1 = κ * (D.center.1 - C.center.1) := by
      dsimp [κ]
      field_simp
    have hvy : B.center.2 - A.center.2 = κ * (D.center.2 - C.center.2) := by
      have hp : (D.center.1 - C.center.1) *
          ((B.center.2 - A.center.2) - κ * (D.center.2 - C.center.2)) = 0 := by
        rw [hvx] at hxy0
        linear_combination hxy0
      have := (mul_eq_zero.mp hp).resolve_left hux
      linarith
    have hvr : B.radius - A.radius = κ * (D.radius - C.radius) := by
      have hp : (D.center.1 - C.center.1) *
          ((B.radius - A.radius) - κ * (D.radius - C.radius)) = 0 := by
        rw [hvx] at hxr
        linear_combination hxr
      have := (mul_eq_zero.mp hp).resolve_left hux
      linarith
    have hk : κ ≠ 0 := by
      intro hk
      rw [hk] at hvx hvy
      simp only [zero_mul] at hvx hvy
      apply hAB
      apply Prod.ext <;> linarith
    have hx0 := (hn 1 0).2.1
    have hx2 := (hn 2 0).2.1
    rw [corner_xq_of_proportional 1 κ A B C D hvx hvy hvr] at hx0
    rw [corner_xq_of_proportional 2 κ A B C D hvx hvy hvr] at hx2
    ring_nf at hx0 hx2
    have hz : κ * (D.center.1 - C.center.1) * internalGap C D = 0 := by
      nlinarith [hx0, hx2]
    exact hgap ((mul_eq_zero.mp hz).resolve_left (mul_ne_zero hk hux))

/-- A single nonzero coordinate weight recovers the corresponding source circle
up to harmless negation of its radius. -/
theorem largeCircle_single_weight {α ι : Type*} [Fintype ι] [DecidableEq ι]
    (F : α → Circle) (i : ι) (R : ℝ) (w : ι → α) :
    largeCircle (fun j => if j = i then 1 else 0) F R w =
      { center := (F (w i)).center, radius := R - (F (w i)).radius } := by
  rw [Circle.mk.injEq]
  constructor
  · apply Prod.ext <;> simp [largeCircle, wordCenter, wordRadius, weighted]
  · simp [largeCircle, wordCenter, wordRadius, weighted]

/-- Evaluation of a sum with two distinct supported coordinates. -/
theorem sum_two_support {ι : Type*} [Fintype ι] [DecidableEq ι]
    {M : Type*} [AddCommMonoid M] [Module ℝ M]
    (f : ι → M) {i j : ι} (hij : i ≠ j) (t : ℝ) :
    (∑ z, if z = i then t • f z else if z = j then f z else 0) =
      t • f i + f j := by
  calc
    _ = ∑ z, ((if i = z then t • f z else 0) + (if j = z then f z else 0)) := by
      apply Finset.sum_congr rfl
      intro z hz
      by_cases hzi : z = i
      · subst z
        simp [hij, Ne.symm hij]
      · have hiz : i ≠ z := Ne.symm hzi
        by_cases hzj : z = j
        · subst z
          simp [hij, Ne.symm hij]
        · have hjz : j ≠ z := Ne.symm hzj
          simp [hzi, hiz, hzj, hjz]
    _ = _ := by
      rw [Finset.sum_add_distrib]
      simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]

/-- With two supported weights, a large word circle is exactly a corner circle. -/
theorem largeCircle_two_weights {α ι : Type*} [Fintype ι] [DecidableEq ι]
    (F : α → Circle) {i j : ι} (hij : i ≠ j) (t R : ℝ) (w : ι → α) :
    largeCircle (fun z => if z = i then t else if z = j then 1 else 0) F R w =
      cornerCircle t R (F (w i)) (F (w j)) := by
  rw [Circle.mk.injEq]
  constructor
  · apply Prod.ext
    · simpa [largeCircle, wordCenter, wordRadius, weighted, cornerCircle,
        smul_eq_mul] using sum_two_support (fun z => (F (w z)).center.1) hij t
    · simpa [largeCircle, wordCenter, wordRadius, weighted, cornerCircle,
        smul_eq_mul] using sum_two_support (fun z => (F (w z)).center.2) hij t
  · simpa [largeCircle, wordCenter, wordRadius, weighted, cornerCircle,
      smul_eq_mul] using sum_two_support (fun z => (F (w z)).radius) hij t

/-- Coaxiality is invariant under the row permutations used below. -/
theorem coaxial3_swap12 (A B C : Circle) : Coaxial3 A B C ↔ Coaxial3 B A C := by
  simp only [Coaxial3, detCols]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · linear_combination -h1
    · linear_combination -h2
    · linear_combination -h3
    · linear_combination -h4
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · linear_combination -h1
    · linear_combination -h2
    · linear_combination -h3
    · linear_combination -h4

theorem coaxial3_rotate (A B C : Circle) : Coaxial3 A B C ↔ Coaxial3 B C A := by
  simp only [Coaxial3, detCols]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · linear_combination h1
    · linear_combination h2
    · linear_combination h3
    · linear_combination h4
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · linear_combination h1
    · linear_combination h2
    · linear_combination h3
    · linear_combination h4

/-- Negating a radius does not change the normalized circle equation. -/
def negRadius (A : Circle) : Circle := { center := A.center, radius := -A.radius }

@[simp] theorem q_negRadius (A : Circle) : q (negRadius A) = q A := by
  simp only [q, negRadius]
  ring

theorem coaxial3_negRadius (A B C : Circle) :
    Coaxial3 (negRadius A) (negRadius B) (negRadius C) ↔ Coaxial3 A B C := by
  simp only [Coaxial3, detCols]
  rw [q_negRadius, q_negRadius, q_negRadius]
  rfl

/-- If one coordinate displays three distinct alphabet symbols, a single weight
witnesses noncoaxiality of the corresponding large circles. -/
theorem exists_large_noncoaxial_of_distinct_coordinate {α ι : Type*}
    [Fintype ι] [DecidableEq ι] (F : α → Circle)
    (hnc : ∀ v : Fin 3 → α, Function.Injective v →
      ¬ Coaxial3 (F (v 0)) (F (v 1)) (F (v 2)))
    (p qword r : ι → α) (i : ι)
    (hpq : p i ≠ qword i) (hpr : p i ≠ r i) (hqr : qword i ≠ r i) :
    ∃ (γ : ι → ℝ) (R : ℝ),
      ¬ Coaxial3 (largeCircle γ F R p) (largeCircle γ F R qword)
        (largeCircle γ F R r) := by
  let v : Fin 3 → α := ![p i, qword i, r i]
  have hvi : Function.Injective v := by
    intro x y hxy
    fin_cases x <;> fin_cases y <;> simp_all [v]
  refine ⟨fun j => if j = i then 1 else 0, 0, ?_⟩
  rw [largeCircle_single_weight F i 0 p,
      largeCircle_single_weight F i 0 qword,
      largeCircle_single_weight F i 0 r]
  simp only [zero_sub]
  change ¬ Coaxial3 (negRadius (F (p i))) (negRadius (F (qword i)))
    (negRadius (F (r i)))
  rw [coaxial3_negRadius]
  simpa [v] using hnc v hvi

/-- Ordered combinatorial case: two words agree at `i`, split at `j`, and the
third word agrees with the first at `j`. -/
theorem exists_large_noncoaxial_of_corner_pattern {α ι : Type*}
    [Fintype ι] [DecidableEq ι] (F : α → Circle)
    (hcent : Function.Injective (fun a => (F a).center))
    (hgap : ∀ ⦃a b⦄, a ≠ b → internalGap (F a) (F b) ≠ 0)
    (p q r : ι → α) {i j : ι} (hpqi : p i = q i) (hpri : p i ≠ r i)
    (hpqj : p j ≠ q j) (hprj : p j = r j) :
    ∃ (γ : ι → ℝ) (R : ℝ),
      ¬ Coaxial3 (largeCircle γ F R p) (largeCircle γ F R q)
        (largeCircle γ F R r) := by
  have hij : i ≠ j := by
    intro h
    subst j
    exact hpqj hpqi
  obtain ⟨t, R, hcorner⟩ := exists_noncoaxial_corner
    (F (p i)) (F (r i)) (F (p j)) (F (q j))
    (fun h => hpri (hcent h)) (fun h => hpqj (hcent h)) (hgap hpqj)
  let γ : ι → ℝ := fun z => if z = i then t else if z = j then 1 else 0
  refine ⟨γ, R, ?_⟩
  rw [show largeCircle γ F R p = cornerCircle t R (F (p i)) (F (p j)) by
        exact largeCircle_two_weights F hij t R p,
      show largeCircle γ F R q = cornerCircle t R (F (q i)) (F (q j)) by
        exact largeCircle_two_weights F hij t R q,
      show largeCircle γ F R r = cornerCircle t R (F (r i)) (F (r j)) by
        exact largeCircle_two_weights F hij t R r]
  rw [← hpqi, ← hprj]
  exact hcorner

/-- If two words agree in one coordinate but are distinct as words, a second
coordinate either gives three distinct symbols or the corner pattern above. -/
theorem exists_large_noncoaxial_of_equal_pair {α ι : Type*}
    [Fintype ι] [DecidableEq ι] (F : α → Circle)
    (hcent : Function.Injective (fun a => (F a).center))
    (hgap : ∀ ⦃a b⦄, a ≠ b → internalGap (F a) (F b) ≠ 0)
    (hnc : ∀ v : Fin 3 → α, Function.Injective v →
      ¬ Coaxial3 (F (v 0)) (F (v 1)) (F (v 2)))
    (p qword r : ι → α) (hpq : p ≠ qword) (i : ι)
    (hpqi : p i = qword i) (hpri : p i ≠ r i) :
    ∃ (γ : ι → ℝ) (R : ℝ),
      ¬ Coaxial3 (largeCircle γ F R p) (largeCircle γ F R qword)
        (largeCircle γ F R r) := by
  have hex : ∃ j, p j ≠ qword j := by
    by_contra hn
    push_neg at hn
    apply hpq
    funext j
    exact hn j
  obtain ⟨j, hpqj⟩ := hex
  by_cases hprj : p j = r j
  · exact exists_large_noncoaxial_of_corner_pattern F hcent hgap
      p qword r hpqi hpri hpqj hprj
  · by_cases hqrj : qword j = r j
    · obtain ⟨γ, R, h⟩ := exists_large_noncoaxial_of_corner_pattern F hcent hgap
        qword p r hpqi.symm (fun he => hpri (hpqi.trans he))
        (Ne.symm hpqj) hqrj
      exact ⟨γ, R, fun hc => h ((coaxial3_swap12 _ _ _).mp hc)⟩
    · exact exists_large_noncoaxial_of_distinct_coordinate F hnc
        p qword r j hpqj hprj hqrj

/-- Every three distinct words have some weights and `R` for which their large
circles are noncoaxial.  This is the nonidentity lemma needed for simultaneous
algebraic parameter avoidance. -/
theorem exists_large_noncoaxial {α ι : Type*}
    [Fintype ι] [DecidableEq ι] (F : α → Circle)
    (hcent : Function.Injective (fun a => (F a).center))
    (hgap : ∀ ⦃a b⦄, a ≠ b → internalGap (F a) (F b) ≠ 0)
    (hnc : ∀ v : Fin 3 → α, Function.Injective v →
      ¬ Coaxial3 (F (v 0)) (F (v 1)) (F (v 2)))
    (v : Fin 3 → (ι → α)) (hvi : Function.Injective v) :
    ∃ (γ : ι → ℝ) (R : ℝ),
      ¬ Coaxial3 (largeCircle γ F R (v 0)) (largeCircle γ F R (v 1))
        (largeCircle γ F R (v 2)) := by
  have hw02 : v 0 ≠ v 2 := fun h =>
    (show (0 : Fin 3) ≠ 2 by decide) (hvi h)
  have hex : ∃ i, v 0 i ≠ v 2 i := by
    by_contra hn
    push_neg at hn
    apply hw02
    funext i
    exact hn i
  obtain ⟨i, hi02⟩ := hex
  by_cases hi01 : v 0 i = v 1 i
  · have hw01 : v 0 ≠ v 1 := fun h =>
      (show (0 : Fin 3) ≠ 1 by decide) (hvi h)
    exact exists_large_noncoaxial_of_equal_pair F hcent hgap hnc
      (v 0) (v 1) (v 2) hw01 i hi01 hi02
  · by_cases hi12 : v 1 i = v 2 i
    · have hw12 : v 1 ≠ v 2 := fun h =>
        (show (1 : Fin 3) ≠ 2 by decide) (hvi h)
      obtain ⟨γ, R, h⟩ := exists_large_noncoaxial_of_equal_pair F hcent hgap hnc
        (v 1) (v 2) (v 0) hw12 i hi12 (Ne.symm hi01)
      exact ⟨γ, R, fun hc => h ((coaxial3_rotate _ _ _).mp hc)⟩
    · exact exists_large_noncoaxial_of_distinct_coordinate F hnc
        (v 0) (v 1) (v 2) i hi01 hi02 hi12

open MvPolynomial

noncomputable section

/-- Polynomial parameter indices: `none` is `R`, and `some i` is `γᵢ`. -/
abbrev LargeParam (ι : Type*) := Option ι

def gammaPoly {ι : Type*} (i : ι) : MvPolynomial (LargeParam ι) ℝ := X (some i)
def RPoly {ι : Type*} : MvPolynomial (LargeParam ι) ℝ := X none

variable {α ι : Type*} [Fintype ι]

/-- Polynomial coordinates of a large word circle. -/
def largeXPoly (F : α → Circle) (w : ι → α) : MvPolynomial (LargeParam ι) ℝ :=
  ∑ i, gammaPoly i * C (F (w i)).center.1

def largeYPoly (F : α → Circle) (w : ι → α) : MvPolynomial (LargeParam ι) ℝ :=
  ∑ i, gammaPoly i * C (F (w i)).center.2

def largeRadiusPoly (F : α → Circle) (w : ι → α) : MvPolynomial (LargeParam ι) ℝ :=
  RPoly - ∑ i, gammaPoly i * C (F (w i)).radius

def largeQPoly (F : α → Circle) (w : ι → α) : MvPolynomial (LargeParam ι) ℝ :=
  largeXPoly F w ^ 2 + largeYPoly F w ^ 2 - largeRadiusPoly F w ^ 2

/-- Evaluating the polynomial circle data recovers `largeCircle`. -/
@[simp] theorem eval_largeXPoly (x : LargeParam ι → ℝ) (F : α → Circle)
    (w : ι → α) :
    MvPolynomial.eval x (largeXPoly F w) =
      (largeCircle (fun i => x (some i)) F (x none) w).center.1 := by
  simp [largeXPoly, gammaPoly, largeCircle, wordCenter, weighted]

@[simp] theorem eval_largeYPoly (x : LargeParam ι → ℝ) (F : α → Circle)
    (w : ι → α) :
    MvPolynomial.eval x (largeYPoly F w) =
      (largeCircle (fun i => x (some i)) F (x none) w).center.2 := by
  simp [largeYPoly, gammaPoly, largeCircle, wordCenter, weighted]

@[simp] theorem eval_largeRadiusPoly (x : LargeParam ι → ℝ) (F : α → Circle)
    (w : ι → α) :
    MvPolynomial.eval x (largeRadiusPoly F w) =
      (largeCircle (fun i => x (some i)) F (x none) w).radius := by
  simp [largeRadiusPoly, gammaPoly, RPoly, largeCircle, wordRadius, weighted]

@[simp] theorem eval_largeQPoly (x : LargeParam ι → ℝ) (F : α → Circle)
    (w : ι → α) :
    MvPolynomial.eval x (largeQPoly F w) =
      q (largeCircle (fun i => x (some i)) F (x none) w) := by
  simp only [largeQPoly, map_sub, map_add, map_pow, eval_largeXPoly,
    eval_largeYPoly, eval_largeRadiusPoly, q]

/-- Polynomial detecting coincidence of two large centers. -/
def largeCenterGapPoly (F : α → Circle) (w z : ι → α) :
    MvPolynomial (LargeParam ι) ℝ :=
  (largeXPoly F w - largeXPoly F z) ^ 2 +
    (largeYPoly F w - largeYPoly F z) ^ 2

/-- Polynomial detecting internal tangency of two large circles. -/
def largeInternalGapPoly (F : α → Circle) (w z : ι → α) :
    MvPolynomial (LargeParam ι) ℝ :=
  largeCenterGapPoly F w z - (largeRadiusPoly F w - largeRadiusPoly F z) ^ 2

/-- Sum of squares of the four coaxial minors. -/
def coaxMeasure (A B Cc : Circle) : ℝ :=
  (detCols (fun _ => 1) (fun Z => Z.center.1) (fun Z => Z.center.2) A B Cc)^2 +
  (detCols (fun _ => 1) (fun Z => Z.center.1) q A B Cc)^2 +
  (detCols (fun _ => 1) (fun Z => Z.center.2) q A B Cc)^2 +
  (detCols (fun Z => Z.center.1) (fun Z => Z.center.2) q A B Cc)^2

/-- Polynomial version of `coaxMeasure` for three large words. -/
def largeCoaxPoly (F : α → Circle) (w₀ w₁ w₂ : ι → α) :
    MvPolynomial (LargeParam ι) ℝ :=
  let d (f g h : (ι → α) → MvPolynomial (LargeParam ι) ℝ) :=
    f w₀ * (g w₁ * h w₂ - g w₂ * h w₁) -
    g w₀ * (f w₁ * h w₂ - f w₂ * h w₁) +
    h w₀ * (f w₁ * g w₂ - f w₂ * g w₁)
  (d (fun _ => 1) (largeXPoly F) (largeYPoly F))^2 +
  (d (fun _ => 1) (largeXPoly F) (largeQPoly F))^2 +
  (d (fun _ => 1) (largeYPoly F) (largeQPoly F))^2 +
  (d (largeXPoly F) (largeYPoly F) (largeQPoly F))^2

@[simp] theorem eval_largeCenterGapPoly (x : LargeParam ι → ℝ) (F : α → Circle)
    (w z : ι → α) :
    MvPolynomial.eval x (largeCenterGapPoly F w z) =
      sqDist (largeCircle (fun i => x (some i)) F (x none) w).center
        (largeCircle (fun i => x (some i)) F (x none) z).center := by
  simp only [largeCenterGapPoly, map_sub, map_add, map_pow, eval_largeXPoly,
    eval_largeYPoly, sqDist]

@[simp] theorem eval_largeInternalGapPoly (x : LargeParam ι → ℝ)
    (F : α → Circle) (w z : ι → α) :
    MvPolynomial.eval x (largeInternalGapPoly F w z) =
      internalGap (largeCircle (fun i => x (some i)) F (x none) w)
        (largeCircle (fun i => x (some i)) F (x none) z) := by
  simp only [largeInternalGapPoly, map_sub, map_pow, eval_largeCenterGapPoly,
    eval_largeRadiusPoly, internalGap]

@[simp] theorem eval_largeCoaxPoly (x : LargeParam ι → ℝ) (F : α → Circle)
    (w₀ w₁ w₂ : ι → α) :
    MvPolynomial.eval x (largeCoaxPoly F w₀ w₁ w₂) =
      coaxMeasure (largeCircle (fun i => x (some i)) F (x none) w₀)
        (largeCircle (fun i => x (some i)) F (x none) w₁)
        (largeCircle (fun i => x (some i)) F (x none) w₂) := by
  simp only [largeCoaxPoly, coaxMeasure, map_add, map_sub, map_mul, map_pow,
    map_one, eval_largeXPoly, eval_largeYPoly, eval_largeQPoly, detCols]

/-- Vanishing of the sum-of-squares measure is exactly coaxiality. -/
theorem coaxMeasure_eq_zero_iff (A B Cc : Circle) :
    coaxMeasure A B Cc = 0 ↔ Coaxial3 A B Cc := by
  simp only [coaxMeasure, Coaxial3]
  constructor
  · intro h
    constructor
    · nlinarith [sq_nonneg (detCols (fun _ => 1) (fun Z => Z.center.1)
        (fun Z => Z.center.2) A B Cc)]
    constructor
    · nlinarith [sq_nonneg (detCols (fun _ => 1) (fun Z => Z.center.1) q A B Cc)]
    constructor <;> nlinarith [sq_nonneg (detCols (fun _ => 1)
      (fun Z => Z.center.2) q A B Cc),
      sq_nonneg (detCols (fun Z => Z.center.1) (fun Z => Z.center.2) q A B Cc)]
  · rintro ⟨h1, h2, h3, h4⟩
    rw [h1, h2, h3, h4]
    norm_num

private theorem vec2_injective {β : Type*} {w z : β} (h : w ≠ z) :
    Function.Injective (![w, z] : Fin 2 → β) := by
  intro a b hab
  fin_cases a <;> fin_cases b <;> simp_all

private theorem vec3_injective {β : Type*} {x y z : β}
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    Function.Injective (![x, y, z] : Fin 3 → β) := by
  intro a b hab
  fin_cases a <;> fin_cases b <;> simp_all

private theorem exists_coord_ne {ι α : Type*} {w z : ι → α} (h : w ≠ z) :
    ∃ i, w i ≠ z i := by
  by_contra hn
  push_neg at hn
  apply h
  funext i
  exact hn i

private theorem sqDist_ne_zero_of_ne {p q : Point} (h : p ≠ q) :
    sqDist p q ≠ 0 := by
  intro hz
  apply h
  apply Prod.ext <;> simp only [sqDist] at hz ⊢ <;> nlinarith

/-- Pair-center and internal-tangency constraint polynomials are genuine for
distinct words. -/
theorem largeCenterGapPoly_ne_zero [DecidableEq ι] (F : α → Circle)
    (hcent : Function.Injective (fun a => (F a).center))
    {w z : ι → α} (hwz : w ≠ z) : largeCenterGapPoly F w z ≠ 0 := by
  obtain ⟨i, hi⟩ := exists_coord_ne hwz
  let x : LargeParam ι → ℝ
    | none => 0
    | some j => if j = i then 1 else 0
  intro hp
  have he := congrArg (MvPolynomial.eval x) hp
  rw [eval_largeCenterGapPoly] at he
  simp only [map_zero] at he
  have hw : largeCircle (fun j => x (some j)) F 0 w =
      { center := (F (w i)).center, radius := -(F (w i)).radius } := by
    simpa [x] using largeCircle_single_weight F i 0 w
  have hz : largeCircle (fun j => x (some j)) F 0 z =
      { center := (F (z i)).center, radius := -(F (z i)).radius } := by
    simpa [x] using largeCircle_single_weight F i 0 z
  rw [hw, hz] at he
  apply sqDist_ne_zero_of_ne (fun hc => hi (hcent hc))
  exact he

theorem largeInternalGapPoly_ne_zero [DecidableEq ι] (F : α → Circle)
    (hgap : ∀ ⦃a b⦄, a ≠ b → internalGap (F a) (F b) ≠ 0)
    {w z : ι → α} (hwz : w ≠ z) : largeInternalGapPoly F w z ≠ 0 := by
  obtain ⟨i, hi⟩ := exists_coord_ne hwz
  let x : LargeParam ι → ℝ
    | none => 0
    | some j => if j = i then 1 else 0
  intro hp
  have he := congrArg (MvPolynomial.eval x) hp
  rw [eval_largeInternalGapPoly] at he
  simp only [map_zero] at he
  have hw : largeCircle (fun j => x (some j)) F 0 w =
      { center := (F (w i)).center, radius := -(F (w i)).radius } := by
    simpa [x] using largeCircle_single_weight F i 0 w
  have hz : largeCircle (fun j => x (some j)) F 0 z =
      { center := (F (z i)).center, radius := -(F (z i)).radius } := by
    simpa [x] using largeCircle_single_weight F i 0 z
  rw [hw, hz] at he
  apply hgap hi
  simp only [internalGap, sqDist] at he ⊢
  nlinarith

/-- The all-large triple constraint polynomial is genuine. -/
theorem largeCoaxPoly_ne_zero [DecidableEq ι] (F : α → Circle)
    (hcent : Function.Injective (fun a => (F a).center))
    (hgap : ∀ ⦃a b⦄, a ≠ b → internalGap (F a) (F b) ≠ 0)
    (hnc : ∀ v : Fin 3 → α, Function.Injective v →
      ¬ Coaxial3 (F (v 0)) (F (v 1)) (F (v 2)))
    (v : Fin 3 → (ι → α)) (hvi : Function.Injective v) :
    largeCoaxPoly F (v 0) (v 1) (v 2) ≠ 0 := by
  obtain ⟨γ, R, hgood⟩ := exists_large_noncoaxial F hcent hgap hnc v hvi
  let x : LargeParam ι → ℝ
    | none => R
    | some i => γ i
  intro hp
  have he := congrArg (MvPolynomial.eval x) hp
  rw [eval_largeCoaxPoly] at he
  exact hgood ((coaxMeasure_eq_zero_iff _ _ _).mp he)

variable [Fintype α] [DecidableEq ι]

noncomputable def largePairFactor (F : α → Circle)
    (v : Fin 2 → (ι → α)) : MvPolynomial (LargeParam ι) ℝ := by
  classical
  exact if Function.Injective v then
    largeCenterGapPoly F (v 0) (v 1) * largeInternalGapPoly F (v 0) (v 1)
  else 1

noncomputable def largeTripleFactor (F : α → Circle)
    (v : Fin 3 → (ι → α)) : MvPolynomial (LargeParam ι) ℝ := by
  classical
  exact if Function.Injective v then largeCoaxPoly F (v 0) (v 1) (v 2) else 1

noncomputable def largeExceptionalProduct (F : α → Circle) :
    MvPolynomial (LargeParam ι) ℝ :=
  (∏ v : Fin 2 → (ι → α), largePairFactor F v) *
    (∏ v : Fin 3 → (ι → α), largeTripleFactor F v)

/-- All pair and triple constraints for the large word family form a nonzero
finite product. -/
theorem largeExceptionalProduct_ne_zero (F : α → Circle)
    (hcent : Function.Injective (fun a => (F a).center))
    (hgap : ∀ ⦃a b⦄, a ≠ b → internalGap (F a) (F b) ≠ 0)
    (hnc : ∀ v : Fin 3 → α, Function.Injective v →
      ¬ Coaxial3 (F (v 0)) (F (v 1)) (F (v 2))) :
    largeExceptionalProduct (ι := ι) F ≠ 0 := by
  classical
  apply mul_ne_zero
  · apply Finset.prod_ne_zero_iff.mpr
    intro v hv
    simp only [largePairFactor]
    split_ifs with hvi
    · apply mul_ne_zero
      · apply largeCenterGapPoly_ne_zero F hcent
        intro h
        exact (show (0 : Fin 2) ≠ 1 by decide) (hvi h)
      · apply largeInternalGapPoly_ne_zero F hgap
        intro h
        exact (show (0 : Fin 2) ≠ 1 by decide) (hvi h)
    · exact one_ne_zero
  · apply Finset.prod_ne_zero_iff.mpr
    intro v hv
    simp only [largeTripleFactor]
    split_ifs with hvi
    · exact largeCoaxPoly_ne_zero F hcent hgap hnc v hvi
    · exact one_ne_zero

/-- Abstract avoidance in a Cartesian box with infinite coordinate sets. -/
theorem exists_eval_ne_zero_in_box {σ : Type*} (P : MvPolynomial σ ℝ)
    (hP : P ≠ 0) (s : σ → Set ℝ) (hs : ∀ i, (s i).Infinite) :
    ∃ x : σ → ℝ, x ∈ Set.pi Set.univ s ∧ MvPolynomial.eval x P ≠ 0 := by
  by_contra hn
  have hall : ∀ x : σ → ℝ, x ∈ Set.pi Set.univ s →
      MvPolynomial.eval x P = 0 := by
    intro x hx
    by_contra hne
    exact hn ⟨x, hx, hne⟩
  apply hP
  apply MvPolynomial.funext_set s hs
  intro x hx
  simpa using hall x hx

/-- Infinite rational set of positive weights at most one. -/
def smallWeightSet : Set ℝ :=
  Set.range (fun n : ℕ => (1 : ℝ) / (n + 1))

private theorem smallWeightSet_infinite : smallWeightSet.Infinite := by
  apply Set.infinite_range_of_injective
  intro m n h
  have hi : ((m + 1 : ℝ))⁻¹ = ((n + 1 : ℝ))⁻¹ := by
    simpa [one_div] using h
  have hc := inv_injective hi
  have hc' : m + 1 = n + 1 := by exact_mod_cast hc
  exact Nat.add_right_cancel hc'

private theorem smallWeightSet_spec {x : ℝ} (hx : x ∈ smallWeightSet) :
    0 < x ∧ x ≤ 1 ∧ ∃ q : ℚ, (q : ℝ) = x := by
  obtain ⟨n, rfl⟩ := hx
  constructor
  · positivity
  constructor
  · apply (div_le_one (by positivity)).2
    norm_num
  · exact ⟨1 / (n + 1), by norm_num⟩

/-- Infinite rational ray starting at the natural number `B`. -/
def largeRSet (B : ℕ) : Set ℝ :=
  Set.range (fun n : ℕ => ((B + n : ℕ) : ℝ))

private theorem largeRSet_infinite (B : ℕ) : (largeRSet B).Infinite := by
  apply Set.infinite_range_of_injective
  intro m n h
  change ((B + m : ℕ) : ℝ) = ((B + n : ℕ) : ℝ) at h
  have hmn : B + m = B + n := by exact_mod_cast h
  exact Nat.add_left_cancel hmn

private theorem largeRSet_spec {B : ℕ} {x : ℝ} (hx : x ∈ largeRSet B) :
    (B : ℝ) ≤ x ∧ ∃ q : ℚ, (q : ℝ) = x := by
  obtain ⟨n, rfl⟩ := hx
  constructor
  · norm_num
  · exact ⟨(B + n : ℕ), by norm_num⟩

/-- Simultaneous rational choice of all large-circle parameters inside a
positivity-friendly box. -/
theorem exists_rational_large_parameters (F : α → Circle)
    (hcent : Function.Injective (fun a => (F a).center))
    (hgap : ∀ ⦃a b⦄, a ≠ b → internalGap (F a) (F b) ≠ 0)
    (hnc : ∀ v : Fin 3 → α, Function.Injective v →
      ¬ Coaxial3 (F (v 0)) (F (v 1)) (F (v 2))) (B : ℕ) :
    ∃ (γ : ι → ℝ) (R : ℝ),
      (∀ i, 0 < γ i ∧ γ i ≤ 1 ∧ ∃ q : ℚ, (q : ℝ) = γ i) ∧
      ((B : ℝ) ≤ R ∧ ∃ q : ℚ, (q : ℝ) = R) ∧
      Function.Injective (fun w : ι → α => (largeCircle γ F R w).center) ∧
      (∀ ⦃w z : ι → α⦄, w ≠ z →
        internalGap (largeCircle γ F R w) (largeCircle γ F R z) ≠ 0) ∧
      (∀ v : Fin 3 → (ι → α), Function.Injective v →
        ¬ Coaxial3 (largeCircle γ F R (v 0)) (largeCircle γ F R (v 1))
          (largeCircle γ F R (v 2))) := by
  classical
  let s : LargeParam ι → Set ℝ
    | none => largeRSet B
    | some _ => smallWeightSet
  obtain ⟨x, hx, heval⟩ := exists_eval_ne_zero_in_box
    (largeExceptionalProduct (ι := ι) F)
    (largeExceptionalProduct_ne_zero (ι := ι) F hcent hgap hnc) s (by
      intro p
      cases p with
      | none => exact largeRSet_infinite B
      | some i => exact smallWeightSet_infinite)
  let γ : ι → ℝ := fun i => x (some i)
  let R : ℝ := x none
  have hγ (i : ι) := smallWeightSet_spec (hx (some i) (Set.mem_univ _))
  have hR := largeRSet_spec (hx none (Set.mem_univ _))
  have hparts : MvPolynomial.eval x
        (∏ v : Fin 2 → (ι → α), largePairFactor F v) ≠ 0 ∧
      MvPolynomial.eval x
        (∏ v : Fin 3 → (ι → α), largeTripleFactor F v) ≠ 0 := by
    rw [largeExceptionalProduct, map_mul] at heval
    exact mul_ne_zero_iff.mp heval
  have hpairProd := hparts.1
  have htripleProd := hparts.2
  rw [map_prod] at hpairProd htripleProd
  refine ⟨γ, R, hγ, hR, ?_, ?_, ?_⟩
  · intro w z hcenter
    by_contra hwz
    let v : Fin 2 → (ι → α) := ![w, z]
    have hvi : Function.Injective v := vec2_injective hwz
    have hf := (Finset.prod_ne_zero_iff.mp hpairProd) v (Finset.mem_univ v)
    simp only [largePairFactor, if_pos hvi, map_mul] at hf
    have hc := (mul_ne_zero_iff.mp hf).1
    rw [eval_largeCenterGapPoly] at hc
    apply hc
    have hvcenter :
        (largeCircle (fun i => x (some i)) F (x none) (v 0)).center =
          (largeCircle (fun i => x (some i)) F (x none) (v 1)).center := by
      simpa [v] using hcenter
    rw [hvcenter]
    simp [sqDist]
  · intro w z hwz
    let v : Fin 2 → (ι → α) := ![w, z]
    have hvi : Function.Injective v := vec2_injective hwz
    have hf := (Finset.prod_ne_zero_iff.mp hpairProd) v (Finset.mem_univ v)
    simp only [largePairFactor, if_pos hvi, map_mul] at hf
    have hg := (mul_ne_zero_iff.mp hf).2
    simpa [γ, R] using (show MvPolynomial.eval x
      (largeInternalGapPoly F w z) ≠ 0 from hg)
  · intro v hvi
    have hf := (Finset.prod_ne_zero_iff.mp htripleProd) v (Finset.mem_univ v)
    simp only [largeTripleFactor, if_pos hvi] at hf
    rw [eval_largeCoaxPoly] at hf
    intro hc
    apply hf
    exact (coaxMeasure_eq_zero_iff _ _ _).mpr hc

/-- Uniform crude bound for all weighted radius words when `0 < γᵢ ≤ 1`. -/
theorem wordRadius_le_total (F : α → Circle) (hpos : ∀ a, 0 < (F a).radius)
    (γ : ι → ℝ) (hγ : ∀ i, 0 < γ i ∧ γ i ≤ 1) (w : ι → α) :
    wordRadius γ F w ≤ ∑ _i : ι, ∑ a : α, (F a).radius := by
  simp only [wordRadius, weighted]
  apply Finset.sum_le_sum
  intro i hi
  calc
    γ i * (F (w i)).radius ≤ (F (w i)).radius :=
      mul_le_of_le_one_left (le_of_lt (hpos _)) (hγ i).2
    _ ≤ ∑ a : α, (F a).radius := by
      have hs := Finset.single_le_sum (s := Finset.univ)
        (f := fun a : α => (F a).radius)
        (fun a ha => le_of_lt (hpos a)) (Finset.mem_univ (w i))
      simpa using hs

/-- The same bound for the fixed part of any line. -/
theorem fixedPart_radius_le_total (F : α → Circle)
    (hpos : ∀ a, 0 < (F a).radius) (γ : ι → ℝ)
    (hγ : ∀ i, 0 < γ i ∧ γ i ≤ 1) (l : Combinatorics.Line α ι) :
    fixedPart γ (fun a => (F a).radius) l ≤
      ∑ _i : ι, ∑ a : α, (F a).radius := by
  simp only [fixedPart]
  apply Finset.sum_le_sum
  intro i hi
  cases h : l.idxFun i with
  | none =>
      simp only
      exact Finset.sum_nonneg fun a ha => le_of_lt (hpos a)
  | some a =>
      simp only
      calc
        γ i * (F a).radius ≤ (F a).radius :=
          mul_le_of_le_one_left (le_of_lt (hpos _)) (hγ i).2
        _ ≤ ∑ b : α, (F b).radius := by
          have hs := Finset.single_le_sum (s := Finset.univ)
            (f := fun b : α => (F b).radius)
            (fun b hb => le_of_lt (hpos b)) (Finset.mem_univ a)
          simpa using hs

/-- Positive weights give every active line a positive scale. -/
theorem lineScale_pos (γ : ι → ℝ) (hγ : ∀ i, 0 < γ i)
    (l : Combinatorics.Line α ι) : 0 < lineScale γ l := by
  simp only [lineScale]
  apply Finset.sum_pos'
  · intro i hi
    cases l.idxFun i <;> simp [le_of_lt (hγ i)]
  · obtain ⟨i, hi⟩ := l.proper
    refine ⟨i, Finset.mem_univ _, ?_⟩
    simp [hi, hγ i]

/-- Strengthened large-parameter selection: all large circles are positive and
good, and every future small-copy scale and translation length is positive. -/
theorem exists_good_rational_large_parameters (F : α → Circle)
    (hgood : GoodFamily F) :
    ∃ (γ : ι → ℝ) (R : ℝ),
      (∀ i, ∃ q : ℚ, (q : ℝ) = γ i) ∧ (∃ q : ℚ, (q : ℝ) = R) ∧
      GoodFamily (fun w : ι → α => largeCircle γ F R w) ∧
      (∀ l : Combinatorics.Line α ι, 0 < lineScale γ l) ∧
      (∀ l : Combinatorics.Line α ι,
        0 < R - fixedPart γ (fun a => (F a).radius) l) := by
  rcases hgood with ⟨hpos, hcent, hgap, hnc⟩
  obtain ⟨B, hB⟩ := exists_nat_gt (∑ _i : ι, ∑ a : α, (F a).radius)
  obtain ⟨γ, R, hγ, hR, hcenterLarge, hgapLarge, hncLarge⟩ :=
    exists_rational_large_parameters (ι := ι) F hcent hgap hnc B
  have hRstrict : (∑ _i : ι, ∑ a : α, (F a).radius) < R :=
    lt_of_lt_of_le hB hR.1
  refine ⟨γ, R, (fun i => (hγ i).2.2), hR.2, ?_,
    (fun l => lineScale_pos γ (fun i => (hγ i).1) l), ?_⟩
  · refine ⟨?_, hcenterLarge, hgapLarge, hncLarge⟩
    intro w
    simp only [largeCircle]
    have hb := wordRadius_le_total F hpos γ (fun i => ⟨(hγ i).1, (hγ i).2.1⟩) w
    linarith
  · intro l
    have hb := fixedPart_radius_le_total F hpos γ
      (fun i => ⟨(hγ i).1, (hγ i).2.1⟩) l
    linarith

open Polynomial

/-- Rational parametrization of the unit circle. -/
def unitParam (t : ℝ) : Point :=
  ((1 - t ^ 2) / (1 + t ^ 2), 2 * t / (1 + t ^ 2))

@[simp] theorem unitParam_norm (t : ℝ) :
    (unitParam t).1 ^ 2 + (unitParam t).2 ^ 2 = 1 := by
  simp only [unitParam]
  field_simp [show 1 + t ^ 2 ≠ 0 by positivity]
  ring

/-- Polynomial homogeneous coordinates for `base + shift * unitParam t`. -/
def moveDen : ℝ[X] := 1 + Polynomial.X ^ 2
def moveXNum (base : Point) (shift : ℝ) : ℝ[X] :=
  Polynomial.C base.1 * moveDen + Polynomial.C shift * (1 - Polynomial.X ^ 2)
def moveYNum (base : Point) (shift : ℝ) : ℝ[X] :=
  Polynomial.C base.2 * moveDen + Polynomial.C shift * (2 * Polynomial.X)

/-- Cleared center-collision and internal-tangency polynomials against a fixed
circle. -/
def moveCenterGapPoly (base : Point) (shift : ℝ) (G : Circle) : ℝ[X] :=
  (moveXNum base shift - Polynomial.C G.center.1 * moveDen) ^ 2 +
  (moveYNum base shift - Polynomial.C G.center.2 * moveDen) ^ 2

def moveInternalGapPoly (base : Point) (shift smallRadius : ℝ)
    (G : Circle) : ℝ[X] :=
  moveCenterGapPoly base shift G -
    Polynomial.C ((smallRadius - G.radius) ^ 2) * moveDen ^ 2

/-- Cleared center-orientation polynomial for one moving point and two fixed
points. -/
def moveOneOrientPoly (base : Point) (shift : ℝ) (p q : Point) : ℝ[X] :=
  moveXNum base shift * (Polynomial.C p.2 * moveDen - Polynomial.C q.2 * moveDen) -
  moveYNum base shift * (Polynomial.C p.1 * moveDen - Polynomial.C q.1 * moveDen) +
  moveDen * (Polynomial.C p.1 * Polynomial.C q.2 * moveDen -
    Polynomial.C q.1 * Polynomial.C p.2 * moveDen)

/-- Cleared orientation for two points translated together and one fixed point. -/
def moveTwoOrientPoly (base₁ base₂ : Point) (shift : ℝ) (p : Point) : ℝ[X] :=
  moveXNum base₁ shift * (moveYNum base₂ shift - Polynomial.C p.2 * moveDen) -
  moveYNum base₁ shift * (moveXNum base₂ shift - Polynomial.C p.1 * moveDen) +
  moveDen * (moveXNum base₂ shift * Polynomial.C p.2 -
    Polynomial.C p.1 * moveYNum base₂ shift)

/-- Three sample directions certify that a moving center cannot coincide with a
fixed center for every parameter. -/
theorem moveCenterGapPoly_ne_zero (base : Point) {shift : ℝ} (hs : shift ≠ 0)
    (G : Circle) : moveCenterGapPoly base shift G ≠ 0 := by
  intro hp
  have h0 := congrArg (Polynomial.eval 0) hp
  have h1 := congrArg (Polynomial.eval 1) hp
  have hm1 := congrArg (Polynomial.eval (-1)) hp
  simp only [moveCenterGapPoly, moveXNum, moveYNum, moveDen, map_sub,
    map_add, map_mul, map_pow, Polynomial.eval_C, Polynomial.eval_X,
    Polynomial.eval_one, Polynomial.eval_zero] at h0 h1 hm1
  norm_num at h0 h1 hm1
  have hdyprod : shift * (base.2 - G.center.2) = 0 := by
    linear_combination (h1 - hm1) / 16
  have hdy : base.2 = G.center.2 := by
    have := (mul_eq_zero.mp hdyprod).resolve_left hs
    linarith
  apply hs
  rw [hdy] at h1
  nlinarith [sq_nonneg (base.1 - G.center.1)]

/-- The internal-gap polynomial is genuine if the only possible concentric
fixed circle has nonzero internal gap. -/
theorem moveInternalGapPoly_ne_zero (base : Point) {shift smallRadius : ℝ}
    (hs : shift ≠ 0) (G : Circle)
    (hconcentric : base = G.center → shift ^ 2 - (smallRadius - G.radius) ^ 2 ≠ 0) :
    moveInternalGapPoly base shift smallRadius G ≠ 0 := by
  intro hp
  have h0 := congrArg (Polynomial.eval 0) hp
  have h1 := congrArg (Polynomial.eval 1) hp
  have hm1 := congrArg (Polynomial.eval (-1)) hp
  simp only [moveInternalGapPoly, moveCenterGapPoly, moveXNum, moveYNum,
    moveDen, map_sub, map_add, map_mul, map_pow, Polynomial.eval_C,
    Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_zero] at h0 h1 hm1
  norm_num at h0 h1 hm1
  have hdyprod : shift * (base.2 - G.center.2) = 0 := by
    linear_combination (h1 - hm1) / 16
  have hdy : base.2 = G.center.2 := by
    have := (mul_eq_zero.mp hdyprod).resolve_left hs
    linarith
  have hdxprod : shift * (base.1 - G.center.1) = 0 := by
    rw [hdy] at h0 h1
    linear_combination (h0 - h1 / 4) / 2
  have hdx : base.1 = G.center.1 := by
    have := (mul_eq_zero.mp hdxprod).resolve_left hs
    linarith
  have hbase : base = G.center := Prod.ext hdx hdy
  apply hconcentric hbase
  rw [hdx, hdy] at h0
  nlinarith

/-- Mixed center-collinearity constraints are genuine. -/
theorem moveOneOrientPoly_ne_zero (base : Point) {shift : ℝ} (hs : shift ≠ 0)
    {p q : Point} (hpq : p ≠ q) : moveOneOrientPoly base shift p q ≠ 0 := by
  intro hp
  have h0 := congrArg (Polynomial.eval 0) hp
  have h1 := congrArg (Polynomial.eval 1) hp
  have hm1 := congrArg (Polynomial.eval (-1)) hp
  simp only [moveOneOrientPoly, moveXNum, moveYNum, moveDen, map_sub,
    map_add, map_mul, map_pow, Polynomial.eval_C, Polynomial.eval_X,
    Polynomial.eval_one, Polynomial.eval_zero] at h0 h1 hm1
  norm_num at h0 h1 hm1
  have hxprod : shift * (p.1 - q.1) = 0 := by
    linear_combination -(h1 - hm1) / 8
  have hx : p.1 = q.1 := by
    have := (mul_eq_zero.mp hxprod).resolve_left hs
    linarith
  have hyprod : shift * (p.2 - q.2) = 0 := by
    rw [hx] at h0 h1
    linear_combination h0 - h1 / 4
  have hy : p.2 = q.2 := by
    have := (mul_eq_zero.mp hyprod).resolve_left hs
    linarith
  exact hpq (Prod.ext hx hy)

theorem moveTwoOrientPoly_ne_zero {base₁ base₂ : Point} (hb : base₁ ≠ base₂)
    {shift : ℝ} (hs : shift ≠ 0) (p : Point) :
    moveTwoOrientPoly base₁ base₂ shift p ≠ 0 := by
  intro hp
  have h0 := congrArg (Polynomial.eval 0) hp
  have h1 := congrArg (Polynomial.eval 1) hp
  have hm1 := congrArg (Polynomial.eval (-1)) hp
  simp only [moveTwoOrientPoly, moveXNum, moveYNum, moveDen, map_sub,
    map_add, map_mul, map_pow, Polynomial.eval_C, Polynomial.eval_X,
    Polynomial.eval_one, Polynomial.eval_zero] at h0 h1 hm1
  norm_num at h0 h1 hm1
  have hxprod : shift * (base₁.1 - base₂.1) = 0 := by
    linear_combination (h1 - hm1) / 8
  have hx : base₁.1 = base₂.1 := by
    have := (mul_eq_zero.mp hxprod).resolve_left hs
    linarith
  have hyprod : shift * (base₂.2 - base₁.2) = 0 := by
    rw [hx] at h0 h1
    linear_combination h0 - h1 / 4
  have hy : base₁.2 = base₂.2 := by
    have := (mul_eq_zero.mp hyprod).resolve_left hs
    linarith
  exact hb (Prod.ext hx hy)

/-- A circle translated along the rationally parametrized unit circle. -/
def movingCircle (base : Point) (radius shift t : ℝ) : Circle where
  center := (base.1 + shift * (unitParam t).1,
    base.2 + shift * (unitParam t).2)
  radius := radius

private theorem move_denom_ne (t : ℝ) : 1 + t ^ 2 ≠ 0 := by positivity

@[simp] theorem eval_moveCenterGapPoly (base : Point) (shift t : ℝ) (G : Circle) :
    Polynomial.eval t (moveCenterGapPoly base shift G) =
      (1 + t ^ 2) ^ 2 * sqDist (movingCircle base 0 shift t).center G.center := by
  simp [moveCenterGapPoly, moveXNum, moveYNum, moveDen, movingCircle,
    unitParam, sqDist, Polynomial.eval_add, Polynomial.eval_sub,
    Polynomial.eval_mul, Polynomial.eval_pow] <;>
    field_simp [move_denom_ne t] <;> ring

@[simp] theorem eval_moveInternalGapPoly (base : Point) (shift radius t : ℝ)
    (G : Circle) :
    Polynomial.eval t (moveInternalGapPoly base shift radius G) =
      (1 + t ^ 2) ^ 2 * internalGap (movingCircle base radius shift t) G := by
  rw [moveInternalGapPoly, Polynomial.eval_sub, Polynomial.eval_mul,
    Polynomial.eval_pow, eval_moveCenterGapPoly, Polynomial.eval_C]
  have hd : Polynomial.eval t moveDen = 1 + t ^ 2 := by simp [moveDen]
  rw [hd]
  simp only [internalGap, movingCircle]
  ring

@[simp] theorem eval_moveOneOrientPoly (base : Point) (shift t : ℝ)
    (p q : Point) :
    Polynomial.eval t (moveOneOrientPoly base shift p q) =
      (1 + t ^ 2) ^ 2 * orient (movingCircle base 0 shift t).center p q := by
  simp [moveOneOrientPoly, moveXNum, moveYNum, moveDen, movingCircle,
    unitParam, orient, Polynomial.eval_add, Polynomial.eval_sub,
    Polynomial.eval_mul, Polynomial.eval_pow] <;>
    field_simp [move_denom_ne t] <;> ring

@[simp] theorem eval_moveTwoOrientPoly (base₁ base₂ : Point) (shift t : ℝ)
    (p : Point) :
    Polynomial.eval t (moveTwoOrientPoly base₁ base₂ shift p) =
      (1 + t ^ 2) ^ 2 * orient (movingCircle base₁ 0 shift t).center
        (movingCircle base₂ 0 shift t).center p := by
  simp [moveTwoOrientPoly, moveXNum, moveYNum, moveDen, movingCircle,
    unitParam, orient, Polynomial.eval_add, Polynomial.eval_sub,
    Polynomial.eval_mul, Polynomial.eval_pow] <;>
    field_simp [move_denom_ne t] <;> ring

/-- Common translation and positive scaling preserve all four coaxial minors. -/
def similarityCircle (scale : ℝ) (trans : Point) (A : Circle) : Circle where
  center := (scale * A.center.1 + trans.1, scale * A.center.2 + trans.2)
  radius := scale * A.radius

set_option maxHeartbeats 500000 in
theorem coaxial3_similarity {scale : ℝ} (hs : scale ≠ 0) (trans : Point)
    (A B Cc : Circle) :
    Coaxial3 (similarityCircle scale trans A) (similarityCircle scale trans B)
      (similarityCircle scale trans Cc) ↔ Coaxial3 A B Cc := by
  simp only [Coaxial3, detCols, similarityCircle, q]
  constructor <;> rintro ⟨h1, h2, h3, h4⟩
  · refine ⟨?_, ?_, ?_, ?_⟩
    · have hp : scale ^ 2 *
          detCols (fun _ => 1) (fun Z => Z.center.1) (fun Z => Z.center.2) A B Cc = 0 := by
        simp only [detCols, q] at h1 ⊢
        linear_combination h1
      exact (mul_eq_zero.mp hp).resolve_left (pow_ne_zero 2 hs)
    · have hp : scale ^ 3 * detCols (fun _ => 1) (fun Z => Z.center.1) q A B Cc = 0 := by
        simp only [detCols, q] at h1 h2 ⊢
        linear_combination h2 - (2 * trans.2) * h1
      exact (mul_eq_zero.mp hp).resolve_left (pow_ne_zero 3 hs)
    · have hp : scale ^ 3 * detCols (fun _ => 1) (fun Z => Z.center.2) q A B Cc = 0 := by
        simp only [detCols, q] at h1 h3 ⊢
        linear_combination h3 + (2 * trans.1) * h1
      exact (mul_eq_zero.mp hp).resolve_left (pow_ne_zero 3 hs)
    · have hp : scale ^ 4 * detCols (fun Z => Z.center.1)
          (fun Z => Z.center.2) q A B Cc = 0 := by
        simp only [detCols, q] at h1 h2 h3 h4 ⊢
        linear_combination h4 - trans.1 * h3 + trans.2 * h2 -
          (trans.1^2 + trans.2^2) * h1
      exact (mul_eq_zero.mp hp).resolve_left (pow_ne_zero 4 hs)
  · refine ⟨?_, ?_, ?_, ?_⟩
    · linear_combination scale^2 * h1
    · linear_combination scale^3 * h2 + 2 * trans.2 * scale^2 * h1
    · linear_combination scale^3 * h3 - 2 * trans.1 * scale^2 * h1
    · linear_combination scale^4 * h4 - trans.2 * scale^3 * h2 +
        trans.1 * scale^3 * h3 - scale^2 * (trans.1^2 + trans.2^2) * h1

variable {β : Type*} [Fintype β]

noncomputable def mixedPairProduct (H : α → Circle) (G : β → Circle)
    (shift : ℝ) : ℝ[X] :=
  ∏ a : α, ∏ b : β,
    moveCenterGapPoly (H a).center shift (G b) *
      moveInternalGapPoly (H a).center shift (H a).radius (G b)

noncomputable def mixedOneTripleFactor (H : α → Circle) (G : β → Circle)
    (shift : ℝ) (a : α) (v : Fin 2 → β) : ℝ[X] := by
  classical
  exact if Function.Injective v then
    moveOneOrientPoly (H a).center shift (G (v 0)).center (G (v 1)).center else 1

noncomputable def mixedOneTripleProduct (H : α → Circle) (G : β → Circle)
    (shift : ℝ) : ℝ[X] :=
  ∏ a : α, ∏ v : Fin 2 → β, mixedOneTripleFactor H G shift a v

noncomputable def mixedTwoTripleFactor (H : α → Circle) (G : β → Circle)
    (shift : ℝ) (v : Fin 2 → α) (b : β) : ℝ[X] := by
  classical
  exact if Function.Injective v then
    moveTwoOrientPoly (H (v 0)).center (H (v 1)).center shift (G b).center else 1

noncomputable def mixedTwoTripleProduct (H : α → Circle) (G : β → Circle)
    (shift : ℝ) : ℝ[X] :=
  ∏ v : Fin 2 → α, ∏ b : β, mixedTwoTripleFactor H G shift v b

noncomputable def mixedExceptionalProduct (H : α → Circle) (G : β → Circle)
    (shift : ℝ) : ℝ[X] :=
  mixedPairProduct H G shift * mixedOneTripleProduct H G shift *
    mixedTwoTripleProduct H G shift

/-- Every mixed constraint polynomial is nonzero under the stated concentric
exception condition. -/
theorem mixedExceptionalProduct_ne_zero (H : α → Circle) (G : β → Circle)
    {shift : ℝ} (hs : shift ≠ 0)
    (hHcent : Function.Injective (fun a => (H a).center))
    (hGcent : Function.Injective (fun b => (G b).center))
    (hconcentric : ∀ a b, (H a).center = (G b).center →
      shift ^ 2 - ((H a).radius - (G b).radius) ^ 2 ≠ 0) :
    mixedExceptionalProduct H G shift ≠ 0 := by
  classical
  apply mul_ne_zero
  · apply mul_ne_zero
    · apply Finset.prod_ne_zero_iff.mpr
      intro a ha
      apply Finset.prod_ne_zero_iff.mpr
      intro b hb
      apply mul_ne_zero
      · exact moveCenterGapPoly_ne_zero (H a).center hs (G b)
      · exact moveInternalGapPoly_ne_zero (H a).center hs (G b)
          (hconcentric a b)
    · apply Finset.prod_ne_zero_iff.mpr
      intro a ha
      apply Finset.prod_ne_zero_iff.mpr
      intro v hv
      simp only [mixedOneTripleFactor]
      split_ifs with hvi
      · exact moveOneOrientPoly_ne_zero (H a).center hs
          (fun h => (show (0 : Fin 2) ≠ 1 by decide) (hvi (hGcent h)))
      · exact one_ne_zero
  · apply Finset.prod_ne_zero_iff.mpr
    intro v hv
    apply Finset.prod_ne_zero_iff.mpr
    intro b hb
    simp only [mixedTwoTripleFactor]
    split_ifs with hvi
    · exact moveTwoOrientPoly_ne_zero
        (fun h => (show (0 : Fin 2) ≠ 1 by decide) (hvi (hHcent h))) hs _
    · exact one_ne_zero

private theorem rationalRange_infinite :
    (Set.range (fun q : ℚ => (q : ℝ))).Infinite :=
  Set.infinite_range_of_injective Rat.cast_injective

/-- A nonzero real univariate polynomial is nonzero at a rational argument. -/
theorem exists_rational_polynomial_eval_ne_zero (P : ℝ[X]) (hP : P ≠ 0) :
    ∃ q : ℚ, Polynomial.eval (q : ℝ) P ≠ 0 := by
  by_contra hn
  push_neg at hn
  apply hP
  apply Polynomial.eq_zero_of_infinite_isRoot
  apply rationalRange_infinite.mono
  intro x hx
  obtain ⟨q, rfl⟩ := hx
  exact hn q

/-- A rational parameter simultaneously avoids all mixed constraints. -/
theorem exists_rational_mixed_parameter (H : α → Circle) (G : β → Circle)
    {shift : ℝ} (hs : shift ≠ 0)
    (hHcent : Function.Injective (fun a => (H a).center))
    (hGcent : Function.Injective (fun b => (G b).center))
    (hconcentric : ∀ a b, (H a).center = (G b).center →
      shift ^ 2 - ((H a).radius - (G b).radius) ^ 2 ≠ 0) :
    ∃ q : ℚ,
      Polynomial.eval (q : ℝ) (mixedPairProduct H G shift) ≠ 0 ∧
      Polynomial.eval (q : ℝ) (mixedOneTripleProduct H G shift) ≠ 0 ∧
      Polynomial.eval (q : ℝ) (mixedTwoTripleProduct H G shift) ≠ 0 := by
  obtain ⟨q, hq⟩ := exists_rational_polynomial_eval_ne_zero
    (mixedExceptionalProduct H G shift)
    (mixedExceptionalProduct_ne_zero H G hs hHcent hGcent hconcentric)
  refine ⟨q, ?_⟩
  have hh := hq
  simp only [mixedExceptionalProduct, Polynomial.eval_mul, mul_ne_zero_iff] at hh
  exact ⟨hh.1.1, hh.1.2, hh.2⟩

/-- Adjoin one translated moving copy to an existing family. -/
def adjoinMoving (H : α → Circle) (G : β → Circle) (shift t : ℝ) :
    Sum β α → Circle
  | .inl b => G b
  | .inr a => movingCircle (H a).center (H a).radius shift t

theorem internalGap_comm (A B : Circle) : internalGap A B = internalGap B A := by
  simp only [internalGap, sqDist]
  ring

set_option maxHeartbeats 1000000 in
/-- The sequential generic-adjoining lemma. -/
theorem exists_good_rational_adjoinMoving (H : α → Circle) (G : β → Circle)
    {shift : ℝ} (hs : shift ≠ 0) (hH : GoodFamily H) (hG : GoodFamily G)
    (hconcentric : ∀ a b, (H a).center = (G b).center →
      shift ^ 2 - ((H a).radius - (G b).radius) ^ 2 ≠ 0) :
    ∃ q : ℚ, GoodFamily (adjoinMoving H G shift (q : ℝ)) := by
  classical
  rcases hH with ⟨hHpos, hHcent, hHgap, hHnc⟩
  rcases hG with ⟨hGpos, hGcent, hGgap, hGnc⟩
  obtain ⟨q, hpairs, hones, htwos⟩ := exists_rational_mixed_parameter
    H G hs hHcent hGcent hconcentric
  let t : ℝ := (q : ℝ)
  have hpairFactors : ∀ a b,
      Polynomial.eval t (moveCenterGapPoly (H a).center shift (G b)) ≠ 0 ∧
      Polynomial.eval t (moveInternalGapPoly (H a).center shift (H a).radius (G b)) ≠ 0 := by
    simp only [mixedPairProduct, Polynomial.eval_prod] at hpairs
    intro a b
    have ha := (Finset.prod_ne_zero_iff.mp hpairs) a (Finset.mem_univ a)
    have hb := (Finset.prod_ne_zero_iff.mp ha) b (Finset.mem_univ b)
    simpa only [Polynomial.eval_mul, mul_ne_zero_iff] using hb
  have honeFactors : ∀ a (v : Fin 2 → β), Function.Injective v →
      Polynomial.eval t (moveOneOrientPoly (H a).center shift
        (G (v 0)).center (G (v 1)).center) ≠ 0 := by
    simp only [mixedOneTripleProduct, Polynomial.eval_prod] at hones
    intro a v hvi
    have ha := (Finset.prod_ne_zero_iff.mp hones) a (Finset.mem_univ a)
    have hv := (Finset.prod_ne_zero_iff.mp ha) v (Finset.mem_univ v)
    simpa only [mixedOneTripleFactor, if_pos hvi] using hv
  have htwoFactors : ∀ (v : Fin 2 → α) b, Function.Injective v →
      Polynomial.eval t (moveTwoOrientPoly (H (v 0)).center (H (v 1)).center
        shift (G b).center) ≠ 0 := by
    simp only [mixedTwoTripleProduct, Polynomial.eval_prod] at htwos
    intro v b hvi
    have hv := (Finset.prod_ne_zero_iff.mp htwos) v (Finset.mem_univ v)
    have hb := (Finset.prod_ne_zero_iff.mp hv) b (Finset.mem_univ b)
    simpa only [mixedTwoTripleFactor, if_pos hvi] using hb
  have hmixedCenter (a : α) (b : β) :
      (movingCircle (H a).center (H a).radius shift t).center ≠ (G b).center := by
    intro heq
    apply (hpairFactors a b).1
    rw [eval_moveCenterGapPoly]
    have heq' : (movingCircle (H a).center 0 shift t).center = (G b).center := heq
    rw [heq']
    simp [sqDist]
  have hmixedGap (a : α) (b : β) :
      internalGap (movingCircle (H a).center (H a).radius shift t) (G b) ≠ 0 := by
    intro hz
    apply (hpairFactors a b).2
    rw [eval_moveInternalGapPoly, hz, mul_zero]
  have hOne (a : α) (b c : β) (hbc : b ≠ c) :
      ¬ Coaxial3 (movingCircle (H a).center (H a).radius shift t) (G b) (G c) := by
    let v : Fin 2 → β := ![b, c]
    have hvi : Function.Injective v := vec2_injective hbc
    intro hc
    apply honeFactors a v hvi
    rw [eval_moveOneOrientPoly]
    have ho : orient (movingCircle (H a).center 0 shift t).center
        (G b).center (G c).center = 0 := by
      have hd := hc.1
      simp only [detCols, orient, movingCircle] at hd ⊢
      linear_combination hd
    have hov : orient (movingCircle (H a).center 0 shift t).center
        (G (v 0)).center (G (v 1)).center = 0 := by simpa [v] using ho
    rw [hov, mul_zero]
  have hTwo (a c : α) (b : β) (hac : a ≠ c) :
      ¬ Coaxial3 (movingCircle (H a).center (H a).radius shift t)
        (movingCircle (H c).center (H c).radius shift t) (G b) := by
    let v : Fin 2 → α := ![a, c]
    have hvi : Function.Injective v := vec2_injective hac
    intro hc
    apply htwoFactors v b hvi
    rw [eval_moveTwoOrientPoly]
    have ho : orient (movingCircle (H a).center 0 shift t).center
        (movingCircle (H c).center 0 shift t).center (G b).center = 0 := by
      have hd := hc.1
      simp only [detCols, orient, movingCircle] at hd ⊢
      linear_combination hd
    have hov : orient (movingCircle (H (v 0)).center 0 shift t).center
        (movingCircle (H (v 1)).center 0 shift t).center (G b).center = 0 := by
      simpa [v] using ho
    rw [hov, mul_zero]
  refine ⟨q, ?_, ?_, ?_, ?_⟩
  · intro x
    cases x with
    | inl b => exact hGpos b
    | inr a => exact hHpos a
  · intro x y hxy
    cases x with
    | inl b =>
      cases y with
      | inl c => exact congrArg Sum.inl (hGcent hxy)
      | inr a => exact False.elim (hmixedCenter a b hxy.symm)
    | inr a =>
      cases y with
      | inl b => exact False.elim (hmixedCenter a b hxy)
      | inr c =>
        apply congrArg Sum.inr
        apply hHcent
        have hx := congrArg Prod.fst hxy
        have hy := congrArg Prod.snd hxy
        simp only [adjoinMoving, movingCircle] at hx hy
        apply Prod.ext <;> linarith
  · intro x y hxy
    cases x with
    | inl b =>
      cases y with
      | inl c => exact hGgap (fun h => hxy (congrArg Sum.inl h))
      | inr a =>
        rw [internalGap_comm]
        exact hmixedGap a b
    | inr a =>
      cases y with
      | inl b => exact hmixedGap a b
      | inr c =>
        have hac : a ≠ c := fun h => hxy (congrArg Sum.inr h)
        intro hz
        apply hHgap hac
        simp only [adjoinMoving, internalGap, movingCircle, sqDist] at hz ⊢
        linear_combination hz
  · intro v hvi
    have h01 : v 0 ≠ v 1 := fun h =>
      (show (0 : Fin 3) ≠ 1 by decide) (hvi h)
    have h02 : v 0 ≠ v 2 := fun h =>
      (show (0 : Fin 3) ≠ 2 by decide) (hvi h)
    have h12 : v 1 ≠ v 2 := fun h =>
      (show (1 : Fin 3) ≠ 2 by decide) (hvi h)
    cases h0 : v 0 with
    | inl b0 =>
      cases h1 : v 1 with
      | inl b1 =>
        cases h2 : v 2 with
        | inl b2 =>
          have hb01 : b0 ≠ b1 := by intro h; apply h01; rw [h0, h1, h]
          have hb02 : b0 ≠ b2 := by intro h; apply h02; rw [h0, h2, h]
          have hb12 : b1 ≠ b2 := by intro h; apply h12; rw [h1, h2, h]
          let w : Fin 3 → β := ![b0, b1, b2]
          have hwi : Function.Injective w := vec3_injective hb01 hb02 hb12
          simpa [adjoinMoving, w] using hGnc w hwi
        | inr a2 =>
          have hb01 : b0 ≠ b1 := by intro h; apply h01; rw [h0, h1, h]
          intro hc
          apply hOne a2 b0 b1 hb01
          exact ((coaxial3_rotate _ _ _).mp ((coaxial3_rotate _ _ _).mp hc))
      | inr a1 =>
        cases h2 : v 2 with
        | inl b2 =>
          have hb02 : b0 ≠ b2 := by intro h; apply h02; rw [h0, h2, h]
          intro hc
          apply hOne a1 b0 b2 hb02
          exact (coaxial3_swap12 _ _ _).mp hc
        | inr a2 =>
          have ha12 : a1 ≠ a2 := by intro h; apply h12; rw [h1, h2, h]
          intro hc
          apply hTwo a1 a2 b0 ha12
          exact (coaxial3_rotate _ _ _).mp hc
    | inr a0 =>
      cases h1 : v 1 with
      | inl b1 =>
        cases h2 : v 2 with
        | inl b2 =>
          have hb12 : b1 ≠ b2 := by intro h; apply h12; rw [h1, h2, h]
          exact hOne a0 b1 b2 hb12
        | inr a2 =>
          have ha02 : a0 ≠ a2 := by intro h; apply h02; rw [h0, h2, h]
          intro hc
          apply hTwo a2 a0 b1 (Ne.symm ha02)
          exact ((coaxial3_rotate _ _ _).mp ((coaxial3_rotate _ _ _).mp hc))
      | inr a1 =>
        cases h2 : v 2 with
        | inl b2 =>
          have ha01 : a0 ≠ a1 := by intro h; apply h01; rw [h0, h1, h]
          exact hTwo a0 a1 b2 ha01
        | inr a2 =>
          have ha01 : a0 ≠ a1 := by intro h; apply h01; rw [h0, h1, h]
          have ha02 : a0 ≠ a2 := by intro h; apply h02; rw [h0, h2, h]
          have ha12 : a1 ≠ a2 := by intro h; apply h12; rw [h1, h2, h]
          let w : Fin 3 → α := ![a0, a1, a2]
          have hwi : Function.Injective w := vec3_injective ha01 ha02 ha12
          intro hc
          apply hHnc w hwi
          have hsimp : ∀ a, movingCircle (H a).center (H a).radius shift t =
              similarityCircle 1 (shift * (unitParam t).1, shift * (unitParam t).2) (H a) := by
            intro a
            rw [Circle.mk.injEq]
            constructor
            · apply Prod.ext <;> simp [movingCircle, similarityCircle]
            · simp [movingCircle, similarityCircle]
          simp only [adjoinMoving] at hc
          rw [hsimp a0, hsimp a1, hsimp a2] at hc
          simpa [w] using (coaxial3_similarity one_ne_zero _ _ _ _).mp hc

/-! ## Folding the generic adjoining lemma over all combinatorial lines -/

/-- The untranslated homothetic copy associated with one combinatorial line. -/
def lineBaseCircle {α ι : Type*} [Fintype ι] (γ : ι → ℝ) (F : α → Circle)
    (l : Combinatorics.Line α ι) (a : α) : Circle where
  center := wordCenter γ F (l a)
  radius := lineScale γ l * (F a).radius

/-- Translation vector of the line-base similarity. -/
def lineFixedCenter {α ι : Type*} [Fintype ι] (γ : ι → ℝ)
    (F : α → Circle) (l : Combinatorics.Line α ι) : Point :=
  (fixedPart γ (fun a => (F a).center.1) l,
    fixedPart γ (fun a => (F a).center.2) l)

/-- Translation length used to attach the small copy. -/
def lineShift {α ι : Type*} [Fintype ι] (γ : ι → ℝ) (F : α → Circle)
    (R : ℝ) (l : Combinatorics.Line α ι) : ℝ :=
  R - fixedPart γ (fun a => (F a).radius) l

@[simp] theorem lineBaseCircle_eq_similarity {α ι : Type*} [Fintype ι]
    (γ : ι → ℝ) (F : α → Circle) (l : Combinatorics.Line α ι) (a : α) :
    lineBaseCircle γ F l a =
      similarityCircle (lineScale γ l) (lineFixedCenter γ F l) (F a) := by
  rw [Circle.mk.injEq]
  constructor
  · apply Prod.ext
    · simp only [lineBaseCircle, similarityCircle, lineFixedCenter, wordCenter]
      rw [weighted_line]
      ring
    · simp only [lineBaseCircle, similarityCircle, lineFixedCenter, wordCenter]
      rw [weighted_line]
      ring
  · simp only [lineBaseCircle, similarityCircle]

/-- A nonzero similarity preserves the complete `GoodFamily` package. -/
theorem goodFamily_similarity {α : Type*} (F : α → Circle) {scale : ℝ}
    (hscale : 0 < scale) (trans : Point) (hF : GoodFamily F) :
    GoodFamily (fun a => similarityCircle scale trans (F a)) := by
  rcases hF with ⟨hpos, hcent, hgap, hnc⟩
  have hs : scale ≠ 0 := ne_of_gt hscale
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a
    simp only [similarityCircle]
    exact mul_pos hscale (hpos a)
  · intro a b hab
    apply hcent
    have hx := congrArg Prod.fst hab
    have hy := congrArg Prod.snd hab
    simp only [similarityCircle] at hx hy
    apply Prod.ext
    · apply (mul_left_cancel₀ hs)
      linarith
    · apply (mul_left_cancel₀ hs)
      linarith
  · intro a b hab
    intro hz
    apply hgap hab
    simp only [internalGap, similarityCircle, sqDist] at hz ⊢
    have hs2 : scale ^ 2 ≠ 0 := pow_ne_zero 2 hs
    apply (mul_left_cancel₀ hs2)
    linear_combination hz
  · intro v hvi hc
    apply hnc v hvi
    exact (coaxial3_similarity hs trans _ _ _).mp hc

/-- Every positive line scale gives a good untranslated line copy. -/
theorem goodFamily_lineBaseCircle {α ι : Type*} [Fintype ι]
    (γ : ι → ℝ) (F : α → Circle) (l : Combinatorics.Line α ι)
    (hscale : 0 < lineScale γ l) (hF : GoodFamily F) :
    GoodFamily (lineBaseCircle γ F l) := by
  have heq : lineBaseCircle γ F l = fun a =>
      similarityCircle (lineScale γ l) (lineFixedCenter γ F l) (F a) := by
    funext a
    exact lineBaseCircle_eq_similarity γ F l a
  rw [heq]
  exact goodFamily_similarity F hscale (lineFixedCenter γ F l) hF

@[simp] theorem lineBase_center_eq_large_center {α ι : Type*} [Fintype ι]
    (γ : ι → ℝ) (F : α → Circle) (R : ℝ)
    (l : Combinatorics.Line α ι) (a : α) :
    (lineBaseCircle γ F l a).center = (largeCircle γ F R (l a)).center := rfl

/-- The line shift is the sum of the matched base and large radii. -/
theorem lineShift_eq_radius_add {α ι : Type*} [Fintype ι]
    (γ : ι → ℝ) (F : α → Circle) (R : ℝ)
    (l : Combinatorics.Line α ι) (a : α) :
    lineShift γ F R l = (lineBaseCircle γ F l a).radius +
      (largeCircle γ F R (l a)).radius := by
  simp only [lineShift, lineBaseCircle, largeCircle, wordRadius]
  rw [weighted_line]
  ring

/-- Moving the line base in direction `unitParam t` is exactly the small circle
with that constant direction assignment. -/
theorem moving_lineBase_eq_smallCircle {α ι : Type*} [Fintype ι]
    (γ : ι → ℝ) (F : α → Circle) (R t : ℝ)
    (l : Combinatorics.Line α ι) (a : α) :
    movingCircle (lineBaseCircle γ F l a).center (lineBaseCircle γ F l a).radius
        (lineShift γ F R l) t =
      smallCircle γ F R (fun _ => unitParam t) l a := by
  rfl

/-- Recursive index type: all large words, followed by one alphabet copy for
successive lines in a list.  The final construction only needs finite types in
universe zero. -/
def BuiltIndex (W α L : Type) : List L → Type
  | [] => W
  | _ :: ls => Sum (BuiltIndex W α L ls) α

instance builtIndexFintype {W α L : Type} [Fintype W] [Fintype α]
    (ls : List L) : Fintype (BuiltIndex W α L ls) := by
  induction ls with
  | nil => simpa [BuiltIndex]
  | cons l ls ih => simpa [BuiltIndex] using (inferInstance : Fintype (Sum (BuiltIndex W α L ls) α))

/-- One rational direction parameter for every line in the recursive list. -/
def BuildParams (L : Type) : List L → Type
  | [] => Unit
  | _ :: ls => ℚ × BuildParams L ls

/-- Circle family obtained by recursively adjoining the listed line copies. -/
def builtCircle {α ι : Type} [Fintype ι] (γ : ι → ℝ) (F : α → Circle)
    (R : ℝ) : (ls : List (Combinatorics.Line α ι)) → BuildParams _ ls →
      BuiltIndex (ι → α) α (Combinatorics.Line α ι) ls → Circle
  | [], _, w => largeCircle γ F R w
  | l :: ls, ⟨q, ps⟩, x =>
      adjoinMoving (lineBaseCircle γ F l) (builtCircle γ F R ls ps)
        (lineShift γ F R l) (q : ℝ) x

/-- Embedding of the large-word indices into every recursive stage. -/
def largeEmbed {W α L : Type} : (ls : List L) → W → BuiltIndex W α L ls
  | [], w => w
  | _ :: ls, w => Sum.inl (largeEmbed ls w)

/-- Embedding of the alphabet copy at the `j`th listed line. -/
def smallEmbed {W α L : Type} : (ls : List L) → Fin ls.length → α → BuiltIndex W α L ls
  | [], j, _ => Fin.elim0 j
  | _ :: ls, j, a => Fin.cases (Sum.inr a)
      (fun j' => Sum.inl (smallEmbed ls j' a)) j

/-- Rational direction parameter at a listed line. -/
def directionAt {L : Type} : (ls : List L) → BuildParams L ls → Fin ls.length → ℚ
  | [], _, j => Fin.elim0 j
  | _ :: ls, ⟨q, ps⟩, j => Fin.cases q (directionAt ls ps) j

@[simp] theorem builtCircle_largeEmbed {α ι : Type} [Fintype ι]
    (γ : ι → ℝ) (F : α → Circle) (R : ℝ)
    (ls : List (Combinatorics.Line α ι)) (ps : BuildParams _ ls) (w : ι → α) :
    builtCircle γ F R ls ps (largeEmbed (α := α) ls w) = largeCircle γ F R w := by
  induction ls with
  | nil =>
      rcases ps with ⟨⟩
      simp [builtCircle, largeEmbed]
  | cons l ls ih =>
      rcases ps with ⟨q, ps⟩
      simp only [builtCircle, largeEmbed, adjoinMoving]
      exact ih ps

@[simp] theorem builtCircle_smallEmbed {α ι : Type} [Fintype ι]
    (γ : ι → ℝ) (F : α → Circle) (R : ℝ)
    (ls : List (Combinatorics.Line α ι)) (ps : BuildParams _ ls)
    (j : Fin ls.length) (a : α) :
    builtCircle γ F R ls ps (smallEmbed ls j a) =
      movingCircle (lineBaseCircle γ F (ls.get j) a).center
        (lineBaseCircle γ F (ls.get j) a).radius
        (lineShift γ F R (ls.get j)) (directionAt ls ps j : ℝ) := by
  induction ls with
  | nil => exact Fin.elim0 j
  | cons l ls ih =>
      rcases ps with ⟨q, ps⟩
      refine Fin.cases ?_ (fun j' => ?_) j
      · simp [builtCircle, smallEmbed, adjoinMoving, directionAt]
      · simp only [builtCircle, adjoinMoving, directionAt]
        exact ih ps j'

/-- Large and small recursive indices are definitionally separated. -/
theorem largeEmbed_ne_smallEmbed {W α L : Type} (ls : List L)
    (w : W) (j : Fin ls.length) (a : α) :
    largeEmbed (α := α) ls w ≠ smallEmbed ls j a := by
  induction ls with
  | nil => exact Fin.elim0 j
  | cons l ls ih =>
      refine Fin.cases ?_ (fun j' => ?_) j
      · simp [largeEmbed, smallEmbed]
      · intro h
        apply ih j'
        change (Sum.inl (largeEmbed ls w) : Sum (BuiltIndex W α L ls) α) =
          Sum.inl (smallEmbed ls j' a) at h
        exact Sum.inl.inj h

/-- Each listed small-copy embedding is injective in the alphabet. -/
theorem smallEmbed_injective {W α L : Type} (ls : List L) (j : Fin ls.length) :
    Function.Injective (smallEmbed (W := W) (α := α) ls j) := by
  induction ls with
  | nil => exact Fin.elim0 j
  | cons l ls ih =>
      refine Fin.cases ?_ (fun j' => ?_) j
      · intro a b h
        exact Sum.inr.inj h
      · intro a b h
        exact ih j' (Sum.inl.inj h)

set_option maxHeartbeats 1000000 in
/-- Sequential rational direction choices make all listed small copies and all
large circles into one good family. -/
theorem exists_good_builtCircle {α ι : Type} [Fintype α] [Fintype ι]
    [DecidableEq ι] (γ : ι → ℝ) (F : α → Circle) (R : ℝ)
    (hF : GoodFamily F)
    (hLarge : GoodFamily (fun w : ι → α => largeCircle γ F R w))
    (hscale : ∀ l : Combinatorics.Line α ι, 0 < lineScale γ l)
    (hshift : ∀ l : Combinatorics.Line α ι, 0 < lineShift γ F R l)
    (ls : List (Combinatorics.Line α ι)) :
    ∃ ps : BuildParams _ ls, GoodFamily (builtCircle γ F R ls ps) := by
  induction ls with
  | nil =>
      exact ⟨(), hLarge⟩
  | cons l ls ih =>
      obtain ⟨ps, hG⟩ := ih
      let H : α → Circle := lineBaseCircle γ F l
      let G := builtCircle γ F R ls ps
      have hH : GoodFamily H := by
        exact goodFamily_lineBaseCircle γ F l (hscale l) hF
      have hs : lineShift γ F R l ≠ 0 := ne_of_gt (hshift l)
      have hconcentric : ∀ a b, (H a).center = (G b).center →
          lineShift γ F R l ^ 2 - ((H a).radius - (G b).radius) ^ 2 ≠ 0 := by
        intro a b hc
        have hmatch : G (largeEmbed (α := α) ls (l a)) =
            largeCircle γ F R (l a) := builtCircle_largeEmbed γ F R ls ps (l a)
        have hcentMatch : (G (largeEmbed (α := α) ls (l a))).center =
            (H a).center := by
          rw [hmatch]
          exact (lineBase_center_eq_large_center γ F R l a).symm
        have hib : largeEmbed (α := α) ls (l a) = b := hG.2.1 (hcentMatch.trans hc)
        have hr : (G b).radius = (largeCircle γ F R (l a)).radius := by
          rw [← hib, hmatch]
        have hsum := lineShift_eq_radius_add γ F R l a
        change lineShift γ F R l = (H a).radius +
          (largeCircle γ F R (l a)).radius at hsum
        rw [← hr] at hsum
        have hpH : 0 < (H a).radius := hH.1 a
        have hpG : 0 < (G b).radius := hG.1 b
        have hp := mul_pos hpH hpG
        nlinarith
      obtain ⟨q, hnew⟩ := exists_good_rational_adjoinMoving H G hs hH hG hconcentric
      refine ⟨(q, ps), ?_⟩
      change GoodFamily (adjoinMoving (lineBaseCircle γ F l)
        (builtCircle γ F R ls ps) (lineShift γ F R l) (q : ℝ))
      exact hnew

/-- The recursively represented matched pair is externally tangent. -/
theorem built_matched_externallyTangent {α ι : Type} [Fintype ι]
    (γ : ι → ℝ) (F : α → Circle) (R : ℝ)
    (ls : List (Combinatorics.Line α ι)) (ps : BuildParams _ ls)
    (j : Fin ls.length) (a : α) :
    ExternallyTangent
      (builtCircle γ F R ls ps
        (largeEmbed (α := α) ls ((ls.get j) a)))
      (builtCircle γ F R ls ps (smallEmbed ls j a)) := by
  rw [builtCircle_largeEmbed, builtCircle_smallEmbed,
    moving_lineBase_eq_smallCircle]
  apply matched_externallyTangent
  intro l
  exact unitParam_norm _

/-- Every old tangency is reproduced in each recursively represented small copy. -/
theorem built_small_externallyTangent {α ι : Type} [Fintype ι]
    (γ : ι → ℝ) (F : α → Circle) (R : ℝ)
    (ls : List (Combinatorics.Line α ι)) (ps : BuildParams _ ls)
    (j : Fin ls.length) {a b : α} (hab : ExternallyTangent (F a) (F b)) :
    ExternallyTangent
      (builtCircle γ F R ls ps (smallEmbed ls j a))
      (builtCircle γ F R ls ps (smallEmbed ls j b)) := by
  rw [builtCircle_smallEmbed, builtCircle_smallEmbed,
    moving_lineBase_eq_smallCircle, moving_lineBase_eq_smallCircle]
  exact small_externallyTangent γ F R
    (fun _ => unitParam (directionAt ls ps j : ℝ)) (ls.get j) hab

/-- The Hales--Jewett coloring argument only needs every line to occur in the
recursive list; its geometric parameters may be chosen independently. -/
theorem built_noKColoring {α ι : Type} [Fintype ι] {k : ℕ}
    (F : α → Circle) (hF : NoKColoring F k)
    (hHJ : ∀ color : (ι → α) → Fin (k + 1),
      ∃ (l : Combinatorics.Line α ι) (c : Fin (k + 1)), ∀ a, color (l a) = c)
    (γ : ι → ℝ) (R : ℝ) (ls : List (Combinatorics.Line α ι))
    (hcomplete : ∀ l : Combinatorics.Line α ι, l ∈ ls)
    (ps : BuildParams _ ls) :
    NoKColoring (builtCircle γ F R ls ps) (k + 1) := by
  intro color
  let largeColor : (ι → α) → Fin (k + 1) := fun w =>
    color (largeEmbed (α := α) ls w)
  obtain ⟨l, c, hmono⟩ := hHJ largeColor
  obtain ⟨j, hj⟩ := List.get_of_mem (hcomplete l)
  subst l
  by_cases hex : ∃ a : α, color (smallEmbed ls j a) = c
  · obtain ⟨a, ha⟩ := hex
    refine ⟨largeEmbed (α := α) ls ((ls.get j) a), smallEmbed ls j a,
      largeEmbed_ne_smallEmbed ls _ j a,
      built_matched_externallyTangent γ F R ls ps j a, ?_⟩
    exact (hmono a).trans ha.symm
  · have hne (a : α) : color (smallEmbed ls j a) ≠ c := by
      intro h
      exact hex ⟨a, h⟩
    let smallColor : α → Fin k := fun a =>
      (finSuccAboveEquiv c).symm ⟨color (smallEmbed ls j a), hne a⟩
    obtain ⟨a, b, hab, ht, hc⟩ := hF smallColor
    have hc' : color (smallEmbed ls j a) = color (smallEmbed ls j b) := by
      have hs : (⟨color (smallEmbed ls j a), hne a⟩ :
          {x : Fin (k + 1) // x ≠ c}) =
          ⟨color (smallEmbed ls j b), hne b⟩ := by
        apply (finSuccAboveEquiv c).symm.injective
        exact hc
      exact congrArg Subtype.val hs
    exact ⟨smallEmbed ls j a, smallEmbed ls j b,
      fun h => hab (smallEmbed_injective ls j h),
      built_small_externallyTangent γ F R ls ps j ht, hc'⟩

/-! ## Rationality of the complete boosted family -/

/-- A real number lying in the canonical copy of the rationals. -/
def IsRationalReal (x : ℝ) : Prop := ∃ q : ℚ, (q : ℝ) = x

/-- A circle with rational center coordinates and rational radius. -/
def RationalCircle (A : Circle) : Prop :=
  IsRationalReal A.center.1 ∧ IsRationalReal A.center.2 ∧ IsRationalReal A.radius

/-- Pointwise rationality of an indexed circle family. -/
def RationalFamily {α : Type*} (F : α → Circle) : Prop := ∀ a, RationalCircle (F a)

@[simp] theorem rationalReal_zero : IsRationalReal 0 := ⟨0, by norm_num⟩
@[simp] theorem rationalReal_one : IsRationalReal 1 := ⟨1, by norm_num⟩

theorem rationalReal_add {x y : ℝ} (hx : IsRationalReal x) (hy : IsRationalReal y) :
    IsRationalReal (x + y) := by
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, rfl⟩ := hy
  exact ⟨a + b, by norm_num⟩

theorem rationalReal_sub {x y : ℝ} (hx : IsRationalReal x) (hy : IsRationalReal y) :
    IsRationalReal (x - y) := by
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, rfl⟩ := hy
  exact ⟨a - b, by norm_num⟩

theorem rationalReal_mul {x y : ℝ} (hx : IsRationalReal x) (hy : IsRationalReal y) :
    IsRationalReal (x * y) := by
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, rfl⟩ := hy
  exact ⟨a * b, by norm_num⟩

theorem rationalReal_sum {σ : Type*} (s : Finset σ) (f : σ → ℝ)
    (hf : ∀ i ∈ s, IsRationalReal (f i)) : IsRationalReal (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact rationalReal_add (hf a (Finset.mem_insert_self a s))
        (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

/-- Rational parameters give a rational point on the unit circle. -/
theorem rational_unitParam (q : ℚ) :
    IsRationalReal (unitParam (q : ℝ)).1 ∧
      IsRationalReal (unitParam (q : ℝ)).2 := by
  constructor
  · refine ⟨(1 - q ^ 2) / (1 + q ^ 2), ?_⟩
    norm_num [unitParam]
  · refine ⟨2 * q / (1 + q ^ 2), ?_⟩
    norm_num [unitParam]

/-- Rational source data and rational weights produce rational large circles. -/
theorem rational_largeCircle {α ι : Type*} [Fintype ι]
    (γ : ι → ℝ) (F : α → Circle) (R : ℝ)
    (hγ : ∀ i, IsRationalReal (γ i)) (hF : RationalFamily F)
    (hR : IsRationalReal R) (w : ι → α) :
    RationalCircle (largeCircle γ F R w) := by
  have hx : IsRationalReal (weighted γ (fun a => (F a).center.1) w) := by
    apply rationalReal_sum Finset.univ (fun i => γ i * (F (w i)).center.1)
    intro i hi
    exact rationalReal_mul (hγ i) (hF (w i)).1
  have hy : IsRationalReal (weighted γ (fun a => (F a).center.2) w) := by
    apply rationalReal_sum Finset.univ (fun i => γ i * (F (w i)).center.2)
    intro i hi
    exact rationalReal_mul (hγ i) (hF (w i)).2.1
  have hr : IsRationalReal (wordRadius γ F w) := by
    apply rationalReal_sum Finset.univ (fun i => γ i * (F (w i)).radius)
    intro i hi
    exact rationalReal_mul (hγ i) (hF (w i)).2.2
  exact ⟨hx, hy, rationalReal_sub hR hr⟩

/-- Rational source data give rational untranslated line copies. -/
theorem rational_lineBaseCircle {α ι : Type*} [Fintype ι]
    (γ : ι → ℝ) (F : α → Circle)
    (hγ : ∀ i, IsRationalReal (γ i)) (hF : RationalFamily F)
    (l : Combinatorics.Line α ι) (a : α) :
    RationalCircle (lineBaseCircle γ F l a) := by
  have hx : IsRationalReal (weighted γ (fun z => (F z).center.1) (l a)) := by
    apply rationalReal_sum Finset.univ (fun i => γ i * (F (l a i)).center.1)
    intro i hi
    exact rationalReal_mul (hγ i) (hF _).1
  have hy : IsRationalReal (weighted γ (fun z => (F z).center.2) (l a)) := by
    apply rationalReal_sum Finset.univ (fun i => γ i * (F (l a i)).center.2)
    intro i hi
    exact rationalReal_mul (hγ i) (hF _).2.1
  have hs : IsRationalReal (lineScale γ l) := by
    apply rationalReal_sum Finset.univ (fun i =>
      match l.idxFun i with | none => γ i | some _ => 0)
    intro i hi
    cases l.idxFun i <;> simp [hγ i]
  exact ⟨hx, hy, rationalReal_mul hs (hF a).2.2⟩

/-- Every line translation length is rational. -/
theorem rational_lineShift {α ι : Type*} [Fintype ι]
    (γ : ι → ℝ) (F : α → Circle) (R : ℝ)
    (hγ : ∀ i, IsRationalReal (γ i)) (hF : RationalFamily F)
    (hR : IsRationalReal R) (l : Combinatorics.Line α ι) :
    IsRationalReal (lineShift γ F R l) := by
  apply rationalReal_sub hR
  apply rationalReal_sum Finset.univ (fun i =>
    match l.idxFun i with | none => 0 | some a => γ i * (F a).radius)
  intro i hi
  cases h : l.idxFun i with
  | none => simp
  | some a =>
      simp only
      exact rationalReal_mul (hγ i) (hF a).2.2

/-- Rational translation along a rational unit direction preserves circle
rationality. -/
theorem rational_movingCircle (A : Circle) (hA : RationalCircle A)
    {shift : ℝ} (hshift : IsRationalReal shift) (q : ℚ) :
    RationalCircle (movingCircle A.center A.radius shift (q : ℝ)) := by
  obtain ⟨hu, hv⟩ := rational_unitParam q
  exact ⟨rationalReal_add hA.1 (rationalReal_mul hshift hu),
    rationalReal_add hA.2.1 (rationalReal_mul hshift hv), hA.2.2⟩

/-- All circles produced by the recursive rational-direction fold are rational. -/
theorem rational_builtCircle {α ι : Type} [Fintype ι]
    (γ : ι → ℝ) (F : α → Circle) (R : ℝ)
    (hγ : ∀ i, IsRationalReal (γ i)) (hF : RationalFamily F)
    (hR : IsRationalReal R) (ls : List (Combinatorics.Line α ι))
    (ps : BuildParams _ ls) : RationalFamily (builtCircle γ F R ls ps) := by
  induction ls with
  | nil =>
      intro w
      exact rational_largeCircle γ F R hγ hF hR w
  | cons l ls ih =>
      rcases ps with ⟨q, ps⟩
      intro x
      cases x with
      | inl b => exact ih ps b
      | inr a =>
          exact rational_movingCircle (lineBaseCircle γ F l a)
            (rational_lineBaseCircle γ F hγ hF l a)
            (rational_lineShift γ F R hγ hF hR l) q

instance builtIndexNonempty {W α L : Type} [Nonempty W]
    (ls : List L) : Nonempty (BuiltIndex W α L ls) := by
  induction ls with
  | nil => simpa [BuiltIndex] using (inferInstance : Nonempty W)
  | cons l ls ih =>
      exact ⟨Sum.inl (Classical.choice ih)⟩

/-- Fully geometric Hales--Jewett successor: positivity, center injectivity,
absence of internal tangencies and coaxial triples all survive while the
required number of colors rises by one. -/
theorem exists_good_rational_noKColoring_succ {α : Type} [Fintype α] [Nonempty α]
    {k : ℕ} (F : α → Circle) (hgood : GoodFamily F)
    (hrat : RationalFamily F) (hno : NoKColoring F k) :
    ∃ (β : Type) (_ : Fintype β) (_ : Nonempty β),
      ∃ G : β → Circle,
        GoodFamily G ∧ RationalFamily G ∧ NoKColoring G (k + 1) := by
  classical
  obtain ⟨ι, ιfin, hHJ⟩ :=
    Combinatorics.Line.exists_mono_in_high_dimension α (Fin (k + 1))
  letI : Fintype ι := ιfin
  letI : Finite (Combinatorics.Line α ι) := Finite.of_injective
    (fun l : Combinatorics.Line α ι => l.idxFun) (by
      rintro ⟨l, hl⟩ ⟨m, hm⟩ h
      simp only at h
      subst m
      rfl)
  letI : Fintype (Combinatorics.Line α ι) := Fintype.ofFinite _
  obtain ⟨γ, R, hγrat, hRrat, hLarge, hscale, hshift0⟩ :=
    exists_good_rational_large_parameters (ι := ι) F hgood
  have hshift : ∀ l : Combinatorics.Line α ι, 0 < lineShift γ F R l := by
    intro l
    exact hshift0 l
  let ls : List (Combinatorics.Line α ι) := Finset.univ.toList
  obtain ⟨ps, hbuilt⟩ :=
    exists_good_builtCircle γ F R hgood hLarge hscale hshift ls
  let β := BuiltIndex (ι → α) α (Combinatorics.Line α ι) ls
  let G : β → Circle := builtCircle γ F R ls ps
  have hbuiltRat : RationalFamily G :=
    rational_builtCircle γ F R (fun i => hγrat i) hrat hRrat ls ps
  refine ⟨β, inferInstance, inferInstance, G, hbuilt, hbuiltRat, ?_⟩
  apply built_noKColoring F hno hHJ γ R ls
  intro l
  simp [ls]

/-- Starting from one positive circle and iterating the geometric successor
produces finite good rational-parameter circle data of arbitrary chromatic
number.  Rationality of the resulting circle coordinates is packaged below. -/
theorem exists_finite_good_rational_noKColoring (k : ℕ) :
    ∃ (α : Type) (_ : Fintype α) (_ : Nonempty α),
      ∃ F : α → Circle,
        GoodFamily F ∧ RationalFamily F ∧ NoKColoring F k := by
  induction k with
  | zero =>
      let F : Unit → Circle := fun _ => ⟨(0, 0), 1⟩
      have hgood : GoodFamily F := by
        refine ⟨?_, ?_, ?_, ?_⟩
        · intro a
          norm_num [F]
        · intro a b h
          exact Subsingleton.elim a b
        · intro a b hab
          exact (hab (Subsingleton.elim a b)).elim
        · intro v hvi hc
          have hv : v 0 = v 1 := Subsingleton.elim _ _
          exact (show (0 : Fin 3) ≠ 1 by decide) (hvi hv)
      have hrat : RationalFamily F := by
        intro a
        refine ⟨⟨0, ?_⟩, ⟨0, ?_⟩, ⟨1, ?_⟩⟩ <;> norm_num [F]
      have hno : NoKColoring F 0 := by
        intro color
        exact Fin.elim0 (color ())
      exact ⟨Unit, inferInstance, inferInstance, F, hgood, hrat, hno⟩
  | succ k ih =>
      obtain ⟨α, αfin, αne, F, hgood, hrat, hno⟩ := ih
      letI : Fintype α := αfin
      letI : Nonempty α := αne
      exact exists_good_rational_noKColoring_succ F hgood hrat hno

end

end GenericBooster
end Circle
end Erdos130
