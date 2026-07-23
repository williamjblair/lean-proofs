import Research.Defs

/-!
# Circle inversion and coaxial triples

Algebraic infrastructure for the circle-tangency approach to Erdős Problem 130.
-/

namespace Erdos130

/-- A (not necessarily positive-radius) circle datum. -/
structure Circle where
  center : Point
  radius : ℝ

namespace Circle

/-- Constant term of the normalized circle equation
`X²+Y²-2 c₁ X-2 c₂ Y+q=0`. -/
def q (C : Circle) : ℝ := C.center.1 ^ 2 + C.center.2 ^ 2 - C.radius ^ 2

/-- Determinant of three columns of scalar-valued circle data. -/
def detCols (f g h : Circle → ℝ) (A B C : Circle) : ℝ :=
  f A * (g B * h C - g C * h B) -
  g A * (f B * h C - f C * h B) +
  h A * (f B * g C - f C * g B)

/-- Three normalized circle-equation vectors span a projective line.  For
ordinary distinct circles this is the standard algebraic definition of a
coaxial triple. -/
def Coaxial3 (A B C : Circle) : Prop :=
  detCols (fun _ => 1) (fun Z => Z.center.1) (fun Z => Z.center.2) A B C = 0 ∧
  detCols (fun _ => 1) (fun Z => Z.center.1) q A B C = 0 ∧
  detCols (fun _ => 1) (fun Z => Z.center.2) q A B C = 0 ∧
  detCols (fun Z => Z.center.1) (fun Z => Z.center.2) q A B C = 0

/-- Algebraic external tangency: center distance is the square of the sum of
radii.  Positivity/distinctness can be imposed separately when needed. -/
def ExternallyTangent (A B : Circle) : Prop :=
  sqDist A.center B.center = (A.radius + B.radius) ^ 2

/-- Power of an inversion center with respect to a circle. -/
def inversionDenom (O : Point) (C : Circle) : ℝ :=
  sqDist C.center O - C.radius ^ 2

/-- Center of the image circle under unit inversion about `O`, relative to `O`.
The actual image center is obtained by adding `O`; common translation is
irrelevant to collinearity and concyclicity. -/
noncomputable def inverseRelativeCenter (O : Point) (C : Circle) : Point :=
  ((C.center.1 - O.1) / inversionDenom O C,
   (C.center.2 - O.2) / inversionDenom O C)

/-- Oriented area determinant of three points. -/
def orient (p₁ p₂ p₃ : Point) : ℝ :=
  p₁.1 * (p₂.2 - p₃.2) - p₁.2 * (p₂.1 - p₃.1) +
    (p₂.1 * p₃.2 - p₃.1 * p₂.2)

/-- The determinant criterion agrees with the pinned collinearity definition. -/
theorem collinear_iff_orient_eq_zero (p₁ p₂ p₃ : Point) :
    Collinear p₁ p₂ p₃ ↔ orient p₁ p₂ p₃ = 0 := by
  simp only [Collinear, orient]
  constructor <;> intro h <;> nlinarith [h]

/-- Inversion preserves the external-tangency equation with signed transformed
radii.  Depending on denominator signs this is external or internal tangency for
the ordinary positive image radii; in either case the transformed center
distance is rational whenever the input data and inversion center are rational. -/
theorem sqDist_inverseRelativeCenter_of_externallyTangent (O : Point)
    (A B : Circle) (hA : inversionDenom O A ≠ 0)
    (hB : inversionDenom O B ≠ 0) (ht : ExternallyTangent A B) :
    sqDist (inverseRelativeCenter O A) (inverseRelativeCenter O B) =
      (A.radius / inversionDenom O A + B.radius / inversionDenom O B) ^ 2 := by
  simp only [ExternallyTangent, sqDist] at ht ⊢
  simp only [inverseRelativeCenter]
  field_simp [hA, hB]
  have hDA : inversionDenom O A =
      (A.center.1 - O.1)^2 + (A.center.2 - O.2)^2 - A.radius^2 := by
    simp only [inversionDenom, sqDist]
  have hDB : inversionDenom O B =
      (B.center.1 - O.1)^2 + (B.center.2 - O.2)^2 - B.radius^2 := by
    simp only [inversionDenom, sqDist]
  rw [hDA, hDB]
  linear_combination
    (((A.center.1 - O.1)^2 + (A.center.2 - O.2)^2 - A.radius^2) *
      ((B.center.1 - O.1)^2 + (B.center.2 - O.2)^2 - B.radius^2)) * ht

/-- The denominator-cleared determinant testing collinearity of three image
circle centers. -/
def clearedInverseCenterTriple (O : Point) (A B C : Circle) : ℝ :=
  detCols (fun Z => Z.center.1 - O.1)
    (fun Z => Z.center.2 - O.2) (inversionDenom O) A B C

/-- Clearing the three inversion denominators gives exactly the oriented-area
determinant of the three relative image centers. -/
theorem clearedInverseCenterTriple_eq_denom_mul_orient (O : Point)
    (A B C : Circle)
    (hA : inversionDenom O A ≠ 0) (hB : inversionDenom O B ≠ 0)
    (hC : inversionDenom O C ≠ 0) :
    clearedInverseCenterTriple O A B C =
      inversionDenom O A * inversionDenom O B * inversionDenom O C *
        orient (inverseRelativeCenter O A) (inverseRelativeCenter O B)
          (inverseRelativeCenter O C) := by
  simp only [clearedInverseCenterTriple, detCols, inverseRelativeCenter, orient]
  field_simp [hA, hB, hC]

/-- Exact coefficient expansion of the inversion-center collinearity
polynomial. -/
theorem clearedInverseCenterTriple_eq (O : Point) (A B C : Circle) :
    clearedInverseCenterTriple O A B C =
      -detCols (fun _ => 1) (fun Z => Z.center.1) (fun Z => Z.center.2) A B C *
          (O.1 ^ 2 + O.2 ^ 2)
      -detCols (fun _ => 1) (fun Z => Z.center.2) q A B C * O.1
      +detCols (fun _ => 1) (fun Z => Z.center.1) q A B C * O.2
      +detCols (fun Z => Z.center.1) (fun Z => Z.center.2) q A B C := by
  simp only [clearedInverseCenterTriple, detCols, inversionDenom, sqDist, q]
  ring

/-- Determinant of four columns of scalar-valued circle data. -/
def det4Cols (f g h j : Circle → ℝ) (A B C D : Circle) : ℝ :=
  f A * detCols g h j B C D - g A * detCols f h j B C D +
    h A * detCols f g j B C D - j A * detCols f g h B C D

/-- The ordinary determinant criterion for four points to lie on a generalized
circle (an ordinary circle or a line). -/
def cyclicDet (p₁ p₂ p₃ p₄ : Point) : ℝ :=
  let N : Point → ℝ := fun p => p.1^2 + p.2^2
  N p₁ * (p₂.1 * (p₃.2 - p₄.2) - p₂.2 * (p₃.1 - p₄.1) +
      (p₃.1 * p₄.2 - p₄.1 * p₃.2)) -
  p₁.1 * (N p₂ * (p₃.2 - p₄.2) - p₂.2 * (N p₃ - N p₄) +
      (N p₃ * p₄.2 - N p₄ * p₃.2)) +
  p₁.2 * (N p₂ * (p₃.1 - p₄.1) - p₂.1 * (N p₃ - N p₄) +
      (N p₃ * p₄.1 - N p₄ * p₃.1)) -
  (N p₂ * (p₃.1 * p₄.2 - p₄.1 * p₃.2) -
    p₂.1 * (N p₃ * p₄.2 - N p₄ * p₃.2) +
    p₂.2 * (N p₃ * p₄.1 - N p₄ * p₃.1))

/-- Four genuinely concyclic points have zero cyclic determinant. -/
theorem cyclicDet_eq_zero_of_concyclic4 {p₁ p₂ p₃ p₄ : Point}
    (h : Concyclic4 p₁ p₂ p₃ p₄) : cyclicDet p₁ p₂ p₃ p₄ = 0 := by
  rcases h with ⟨o, h12, h13, h14⟩
  simp only [sqDist] at h12 h13 h14
  simp only [cyclicDet, orient]
  linear_combination
    (p₁.1 * (p₃.2 - p₄.2) - p₁.2 * (p₃.1 - p₄.1) +
      (p₃.1 * p₄.2 - p₄.1 * p₃.2)) * h12 -
    (p₁.1 * (p₂.2 - p₄.2) - p₁.2 * (p₂.1 - p₄.1) +
      (p₂.1 * p₄.2 - p₄.1 * p₂.2)) * h13 +
    (p₁.1 * (p₂.2 - p₃.2) - p₁.2 * (p₂.1 - p₃.1) +
      (p₂.1 * p₃.2 - p₃.1 * p₂.2)) * h14

/-- Denominator-cleared cyclic determinant of four inverse-circle centers. -/
def clearedInverseCenterQuad (O : Point) (A B C D : Circle) : ℝ :=
  let X : Circle → ℝ := fun Z => Z.center.1 - O.1
  let Y : Circle → ℝ := fun Z => Z.center.2 - O.2
  let P : Circle → ℝ := inversionDenom O
  det4Cols (fun Z => X Z ^ 2 + Y Z ^ 2)
    (fun Z => X Z * P Z) (fun Z => Y Z * P Z) (fun Z => P Z ^ 2)
    A B C D

/-- A four-cycle of determinant rows changes the sign. -/
theorem det4Cols_rotate (f g h j : Circle → ℝ) (A B C D : Circle) :
    det4Cols f g h j B C D A = -det4Cols f g h j A B C D := by
  simp only [det4Cols, detCols]
  ring

/-- The even row permutation `(A,B,C,D) ↦ (A,C,D,B)` preserves the determinant. -/
theorem det4Cols_cycle_last_three (f g h j : Circle → ℝ) (A B C D : Circle) :
    det4Cols f g h j A C D B = det4Cols f g h j A B C D := by
  simp only [det4Cols, detCols]
  ring

/-- Row-permutation laws for the cleared four-circle determinant. -/
theorem clearedInverseCenterQuad_rotate (O : Point) (A B C D : Circle) :
    clearedInverseCenterQuad O B C D A =
      -clearedInverseCenterQuad O A B C D := by
  simp only [clearedInverseCenterQuad]
  apply det4Cols_rotate

theorem clearedInverseCenterQuad_cycle_last_three (O : Point) (A B C D : Circle) :
    clearedInverseCenterQuad O A C D B =
      clearedInverseCenterQuad O A B C D := by
  simp only [clearedInverseCenterQuad]
  apply det4Cols_cycle_last_three

/-- Laplace expansion when the last row has only its first entry nonzero. -/
theorem det4Cols_last_only (f g h j : Circle → ℝ) (A B C D : Circle)
    (hg : g D = 0) (hh : h D = 0) (hj : j D = 0) :
    det4Cols f g h j A B C D = -f D * detCols g h j A B C := by
  simp only [det4Cols, detCols, hg, hh, hj]
  ring

/-- Factoring one common scalar from each of three determinant rows. -/
theorem detCols_row_factors (f g p : Circle → ℝ) (A B C : Circle) :
    detCols (fun Z => f Z * p Z) (fun Z => g Z * p Z)
      (fun Z => p Z ^ 2) A B C =
      p A * p B * p C * detCols f g p A B C := by
  simp only [detCols]
  ring

/-- On the inversion circle of `D`, the four-circle determinant factors as
the product of the other three denominators and their triple determinant. -/
theorem clearedInverseCenterQuad_on_circle (O : Point) (A B C D : Circle)
    (hD : inversionDenom O D = 0) :
    clearedInverseCenterQuad O A B C D =
      -D.radius ^ 2 * inversionDenom O A * inversionDenom O B *
        inversionDenom O C * clearedInverseCenterTriple O A B C := by
  let X : Circle → ℝ := fun Z => Z.center.1 - O.1
  let Y : Circle → ℝ := fun Z => Z.center.2 - O.2
  let P : Circle → ℝ := inversionDenom O
  change det4Cols (fun Z => X Z ^ 2 + Y Z ^ 2)
      (fun Z => X Z * P Z) (fun Z => Y Z * P Z) (fun Z => P Z ^ 2)
      A B C D = _
  rw [det4Cols_last_only, detCols_row_factors]
  · change -(X D ^ 2 + Y D ^ 2) * (P A * P B * P C *
        detCols X Y P A B C) = _
    have hnorm : X D ^ 2 + Y D ^ 2 = D.radius ^ 2 := by
      dsimp [P, X, Y]
      simp only [inversionDenom, sqDist] at hD
      linarith
    rw [hnorm]
    change -D.radius ^ 2 * (inversionDenom O A * inversionDenom O B *
      inversionDenom O C * clearedInverseCenterTriple O A B C) = _
    ring
  · simp [P, hD]
  · simp [P, hD]
  · simp [P, hD]

/-- Clearing all four inversion denominators gives the actual cyclic determinant
of the relative image centers. -/
theorem clearedInverseCenterQuad_eq_denom_mul_cyclicDet (O : Point)
    (A B C D : Circle)
    (hA : inversionDenom O A ≠ 0) (hB : inversionDenom O B ≠ 0)
    (hC : inversionDenom O C ≠ 0) (hD : inversionDenom O D ≠ 0) :
    clearedInverseCenterQuad O A B C D =
      (inversionDenom O A)^2 * (inversionDenom O B)^2 *
      (inversionDenom O C)^2 * (inversionDenom O D)^2 *
      cyclicDet (inverseRelativeCenter O A) (inverseRelativeCenter O B)
        (inverseRelativeCenter O C) (inverseRelativeCenter O D) := by
  simp only [clearedInverseCenterQuad, det4Cols, detCols,
    inverseRelativeCenter, cyclicDet]
  field_simp [hA, hB, hC, hD]
  <;> ring

/-- Inversive Lorentz bilinear form on normalized circle-equation vectors. -/
def inversiveInner (A B : Circle) : ℝ :=
  q A + q B - 2 * A.center.1 * B.center.1 - 2 * A.center.2 * B.center.2

theorem inversiveInner_comm (A B : Circle) :
    inversiveInner A B = inversiveInner B A := by
  simp only [inversiveInner]
  ring

@[simp] theorem inversiveInner_self (A : Circle) :
    inversiveInner A A = -2 * A.radius ^ 2 := by
  simp only [inversiveInner, q]
  ring

set_option maxHeartbeats 1000000 in
/-- Gram determinant identity for four circle-equation vectors.  The form has
signature `(1,3)`, reflected by the negative constant on the right. -/
theorem inversive_gram_det (A B C D : Circle) :
    det4Cols (fun Z => inversiveInner Z A) (fun Z => inversiveInner Z B)
      (fun Z => inversiveInner Z C) (fun Z => inversiveInner Z D) A B C D =
      -4 * (det4Cols (fun _ => 1) (fun Z => Z.center.1)
        (fun Z => Z.center.2) q A B C D) ^ 2 := by
  simp only [det4Cols, detCols, inversiveInner, q]
  ring

set_option maxHeartbeats 1000000 in
/-- Four positive-radius circle vectors cannot be pairwise orthogonal for the
inversive Lorentz form. -/
theorem not_four_pairwise_inversiveOrthogonal (A B C D : Circle)
    (hA : 0 < A.radius) (hB : 0 < B.radius)
    (hC : 0 < C.radius) (hD : 0 < D.radius)
    (hAB : inversiveInner A B = 0) (hAC : inversiveInner A C = 0)
    (hAD : inversiveInner A D = 0) (hBC : inversiveInner B C = 0)
    (hBD : inversiveInner B D = 0) (hCD : inversiveInner C D = 0) : False := by
  have hBA : inversiveInner B A = 0 := by
    rw [inversiveInner]
    rw [inversiveInner] at hAB
    linarith
  have hCA : inversiveInner C A = 0 := by
    rw [inversiveInner]
    rw [inversiveInner] at hAC
    linarith
  have hDA : inversiveInner D A = 0 := by
    rw [inversiveInner]
    rw [inversiveInner] at hAD
    linarith
  have hCB : inversiveInner C B = 0 := by
    rw [inversiveInner]
    rw [inversiveInner] at hBC
    linarith
  have hDB : inversiveInner D B = 0 := by
    rw [inversiveInner]
    rw [inversiveInner] at hBD
    linarith
  have hDC : inversiveInner D C = 0 := by
    rw [inversiveInner]
    rw [inversiveInner] at hCD
    linarith
  have hgram := inversive_gram_det A B C D
  simp only [det4Cols, detCols] at hgram
  rw [hAB, hAC, hAD, hBA, hBC, hBD, hCA, hCB, hCD, hDA, hDB, hDC] at hgram
  simp only [zero_mul, mul_zero, sub_zero, add_zero,
    inversiveInner_self] at hgram
  have hp : 0 < A.radius ^ 2 * B.radius ^ 2 * C.radius ^ 2 * D.radius ^ 2 := by
    positivity
  nlinarith [sq_nonneg (det4Cols (fun _ => 1) (fun Z => Z.center.1)
    (fun Z => Z.center.2) q A B C D)]

/-- If the inverse-center collinearity locus of `A,B,C` is exactly the circle
`D` (up to a nonzero scalar equation), then `D` is inversively orthogonal to
each of `A,B,C`. -/
theorem orthogonal_of_triple_locus (A B C D : Circle) {μ : ℝ} (hμ : μ ≠ 0)
    (hlocus : ∀ O : Point,
      clearedInverseCenterTriple O A B C = μ * inversionDenom O D) :
    inversiveInner D A = 0 ∧ inversiveInner D B = 0 ∧
      inversiveInner D C = 0 := by
  let m₁ := detCols (fun _ => 1) (fun Z => Z.center.1)
    (fun Z => Z.center.2) A B C
  let m₂ := detCols (fun _ => 1) (fun Z => Z.center.2) q A B C
  let m₃ := detCols (fun _ => 1) (fun Z => Z.center.1) q A B C
  let m₄ := detCols (fun Z => Z.center.1) (fun Z => Z.center.2) q A B C
  have h00 := hlocus (0, 0)
  have h10 := hlocus (1, 0)
  have hm10 := hlocus (-1, 0)
  have h01 := hlocus (0, 1)
  rw [clearedInverseCenterTriple_eq] at h00 h10 hm10 h01
  simp only [inversionDenom, sqDist] at h00 h10 hm10 h01
  have hm1 : m₁ = -μ := by
    dsimp [m₁, m₂, m₃, m₄] at *
    nlinarith [h00, h10, hm10]
  have hm2 : m₂ = 2 * μ * D.center.1 := by
    dsimp [m₁, m₂, m₃, m₄] at *
    nlinarith [h10, hm10]
  have hm3 : m₃ = -2 * μ * D.center.2 := by
    dsimp [m₁, m₂, m₃, m₄] at *
    nlinarith [h00, h01, hm1]
  have hm4 : m₄ = μ * q D := by
    dsimp [m₁, m₂, m₃, m₄]
    simpa [q] using h00
  have hminor (Z : Circle) (hZ : Z = A ∨ Z = B ∨ Z = C) :
      m₄ - Z.center.1 * m₂ + Z.center.2 * m₃ - q Z * m₁ = 0 := by
    rcases hZ with (rfl | rfl | rfl) <;>
      dsimp [m₁, m₂, m₃, m₄] <;> simp only [detCols] <;> ring
  have hprod (Z : Circle) (hZ : Z = A ∨ Z = B ∨ Z = C) :
      μ * inversiveInner D Z = 0 := by
    have hz := hminor Z hZ
    rw [hm1, hm2, hm3, hm4] at hz
    simp only [inversiveInner]
    linear_combination hz
  exact ⟨(mul_eq_zero.mp (hprod A (Or.inl rfl))).resolve_left hμ,
    (mul_eq_zero.mp (hprod B (Or.inr (Or.inl rfl)))).resolve_left hμ,
    (mul_eq_zero.mp (hprod C (Or.inr (Or.inr rfl)))).resolve_left hμ⟩

/-- A triple is coaxial exactly when every inversion leaves its three image
centers collinear (after denominator clearing). -/
theorem coaxial3_iff_cleared_eq_zero (A B C : Circle) :
    Coaxial3 A B C ↔
      ∀ O : Point, clearedInverseCenterTriple O A B C = 0 := by
  rw [Coaxial3]
  constructor
  · rintro ⟨h₁, h₂, h₃, h₄⟩ O
    rw [clearedInverseCenterTriple_eq]
    rw [h₁, h₂, h₃, h₄]
    ring
  · intro h
    have h00 := h (0, 0)
    have h10 := h (1, 0)
    have hm10 := h (-1, 0)
    have h01 := h (0, 1)
    rw [clearedInverseCenterTriple_eq] at h00 h10 hm10 h01
    constructor
    · linarith
    constructor
    · linarith
    constructor <;> linarith

end Circle

end Erdos130
