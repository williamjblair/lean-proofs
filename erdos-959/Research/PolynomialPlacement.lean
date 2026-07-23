import Research.CrossBlock

noncomputable section
open Polynomial
namespace Erdos959

/-- Squared translated cross distance along the parabola `t=(r,r²)`. -/
def crossDistancePolynomial (d : Point) : Polynomial ℝ :=
  monomial 4 1 + monomial 2 (1 + 2 * d.2) + monomial 1 (2 * d.1) +
    monomial 0 (d.1 ^ 2 + d.2 ^ 2)

lemma eval_crossDistancePolynomial (d : Point) (r : ℝ) :
    (crossDistancePolynomial d).eval r =
      (r + d.1) ^ 2 + (r ^ 2 + d.2) ^ 2 := by
  simp [crossDistancePolynomial]
  ring

lemma crossDistancePolynomial_coeff_four (d : Point) :
    (crossDistancePolynomial d).coeff 4 = 1 := by
  simp only [crossDistancePolynomial, coeff_add, coeff_monomial]
  norm_num

lemma crossDistancePolynomial_coeff_two (d : Point) :
    (crossDistancePolynomial d).coeff 2 = 1 + 2 * d.2 := by
  simp only [crossDistancePolynomial, coeff_add, coeff_monomial]
  norm_num

lemma crossDistancePolynomial_coeff_one (d : Point) :
    (crossDistancePolynomial d).coeff 1 = 2 * d.1 := by
  simp only [crossDistancePolynomial, coeff_add, coeff_monomial]
  norm_num

lemma crossDistancePolynomial_sub_C_ne_zero (d : Point) (c : ℝ) :
    crossDistancePolynomial d - C c ≠ 0 := by
  intro h
  have h4 := congrArg (fun q : Polynomial ℝ => q.coeff 4) h
  rw [coeff_sub, crossDistancePolynomial_coeff_four, coeff_C] at h4
  norm_num at h4

lemma crossDistancePolynomial_sub_ne_zero {d e : Point} (hde : d ≠ e) :
    crossDistancePolynomial d - crossDistancePolynomial e ≠ 0 := by
  intro h
  have h1 := congrArg (fun q : Polynomial ℝ => q.coeff 1) h
  have h2 := congrArg (fun q : Polynomial ℝ => q.coeff 2) h
  rw [coeff_sub, crossDistancePolynomial_coeff_one,
    crossDistancePolynomial_coeff_one] at h1
  rw [coeff_sub, crossDistancePolynomial_coeff_two,
    crossDistancePolynomial_coeff_two] at h2
  norm_num at h1 h2
  apply hde
  apply Prod.ext <;> nlinarith

lemma exists_avoiding_finitely_many_polynomials
    (S : Finset (Polynomial ℝ)) (hS : ∀ p ∈ S, p ≠ 0) :
    ∃ r : ℝ, ∀ p ∈ S, p.eval r ≠ 0 := by
  have hprod : (∏ p ∈ S, p) ≠ 0 :=
    (Finset.prod_ne_zero_iff.mpr hS)
  by_contra h
  push Not at h
  apply hprod
  apply Polynomial.zero_of_eval_zero
  intro r
  rw [Polynomial.eval_prod]
  rcases h r with ⟨p, hp, hp0⟩
  exact Finset.prod_eq_zero hp hp0

/-- Polynomials encoding collisions with already used squared distances. -/
def forbiddenDistancePolynomials
    (A Y : Finset Point) (D : Finset ℝ) : Finset (Polynomial ℝ) :=
  ((A.product Y).product D).image fun ayd =>
    crossDistancePolynomial (crossDisplacement ayd.1.1 ayd.1.2) - C ayd.2

/-- Polynomials encoding equal cross distances from unequal local displacements. -/
def unequalDisplacementPolynomials
    (A Y : Finset Point) : Finset (Polynomial ℝ) :=
  (((A.product Y).product (A.product Y)).filter fun uv =>
    crossDisplacement uv.1.1 uv.1.2 ≠ crossDisplacement uv.2.1 uv.2.2).image fun uv =>
      crossDistancePolynomial (crossDisplacement uv.1.1 uv.1.2) -
        crossDistancePolynomial (crossDisplacement uv.2.1 uv.2.2)

def translationBadPolynomials
    (A Y : Finset Point) (D : Finset ℝ) : Finset (Polynomial ℝ) :=
  forbiddenDistancePolynomials A Y D ∪ unequalDisplacementPolynomials A Y

lemma translationBadPolynomials_ne_zero
    (A Y : Finset Point) (D : Finset ℝ) :
    ∀ p ∈ translationBadPolynomials A Y D, p ≠ 0 := by
  intro p hp
  rcases Finset.mem_union.mp hp with hpForbid | hpUnequal
  · rcases Finset.mem_image.mp hpForbid with ⟨ayd, _, rfl⟩
    exact crossDistancePolynomial_sub_C_ne_zero _ _
  · rcases Finset.mem_image.mp hpUnequal with ⟨uv, huv, rfl⟩
    have hne := (Finset.mem_filter.mp huv).2
    exact crossDistancePolynomial_sub_ne_zero hne

lemma parabola_translation_distance (r : ℝ) (a y : Point) :
    translatedCrossSqDist (r, r ^ 2) a y =
      (crossDistancePolynomial (crossDisplacement a y)).eval r := by
  rw [translatedCrossSqDist_eq_normSq, eval_crossDistancePolynomial]
  rfl

/-- A single generic translation simultaneously avoids every old distance and
makes equal new cross distances come only from equal local displacements. -/
theorem exists_separating_translation
    (A Y : Finset Point) (D : Finset ℝ) :
    ∃ t : Point,
      (∀ a ∈ A, ∀ y ∈ Y, ∀ d ∈ D,
        translatedCrossSqDist t a y ≠ d) ∧
      (∀ a ∈ A, ∀ y ∈ Y, ∀ a' ∈ A, ∀ y' ∈ Y,
        translatedCrossSqDist t a y = translatedCrossSqDist t a' y' →
          crossDisplacement a y = crossDisplacement a' y') := by
  obtain ⟨r, hr⟩ := exists_avoiding_finitely_many_polynomials
    (translationBadPolynomials A Y D)
    (translationBadPolynomials_ne_zero A Y D)
  refine ⟨(r, r ^ 2), ?_, ?_⟩
  · intro a ha y hy d hd hdist
    let p := crossDistancePolynomial (crossDisplacement a y) - C d
    have hpBad : p ∈ translationBadPolynomials A Y D := by
      apply Finset.mem_union_left
      apply Finset.mem_image.mpr
      exact ⟨((a, y), d), Finset.mem_product.mpr
        ⟨Finset.mem_product.mpr ⟨ha, hy⟩, hd⟩, rfl⟩
    apply hr p hpBad
    rw [Polynomial.eval_sub, Polynomial.eval_C,
      ← parabola_translation_distance]
    exact sub_eq_zero.mpr hdist
  · intro a ha y hy a' ha' y' hy' hdist
    by_contra hdisp
    let p := crossDistancePolynomial (crossDisplacement a y) -
      crossDistancePolynomial (crossDisplacement a' y')
    have hpBad : p ∈ translationBadPolynomials A Y D := by
      apply Finset.mem_union_right
      apply Finset.mem_image.mpr
      refine ⟨((a, y), (a', y')), ?_, rfl⟩
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_product.mpr
        ⟨Finset.mem_product.mpr ⟨ha, hy⟩,
          Finset.mem_product.mpr ⟨ha', hy'⟩⟩, hdisp⟩
    apply hr p hpBad
    rw [Polynomial.eval_sub, ← parabola_translation_distance,
      ← parabola_translation_distance]
    exact sub_eq_zero.mpr hdist

end Erdos959
