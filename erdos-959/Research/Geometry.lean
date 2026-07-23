import Research.Basic

noncomputable section
set_option maxHeartbeats 2000000
namespace Erdos959

lemma collinear_of_common_linear
    (A B C : ℝ) (x y z : Point)
    (hAB : A ≠ 0 ∨ B ≠ 0)
    (hx : A * x.1 + B * x.2 = C)
    (hy : A * y.1 + B * y.2 = C)
    (hz : A * z.1 + B * z.2 = C) :
    (y.1 - x.1) * (z.2 - x.2) =
      (y.2 - x.2) * (z.1 - x.1) := by
  rcases hAB with hA | hB
  · have hAy : A * (y.1 - x.1) + B * (y.2 - x.2) = 0 := by
      linarith
    have hAz : A * (z.1 - x.1) + B * (z.2 - x.2) = 0 := by
      linarith
    have hmul : A * ((y.1 - x.1) * (z.2 - x.2) -
        (y.2 - x.2) * (z.1 - x.1)) = 0 := by
      linear_combination (z.2 - x.2) * hAy - (y.2 - x.2) * hAz
    exact sub_eq_zero.mp ((mul_eq_zero.mp hmul).resolve_left hA)
  · have hBy : A * (y.1 - x.1) + B * (y.2 - x.2) = 0 := by
      linarith
    have hBz : A * (z.1 - x.1) + B * (z.2 - x.2) = 0 := by
      linarith
    have hmul : B * ((y.1 - x.1) * (z.2 - x.2) -
        (y.2 - x.2) * (z.1 - x.1)) = 0 := by
      linear_combination (y.1 - x.1) * hBz - (z.1 - x.1) * hBy
    exact sub_eq_zero.mp ((mul_eq_zero.mp hmul).resolve_left hB)

lemma three_cospherical_not_collinear
    (p x y z : Point) (r : ℝ)
    (hx : sqDist p x = r) (hy : sqDist p y = r) (hz : sqDist p z = r)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hcol : (y.1 - x.1) * (z.2 - x.2) =
      (y.2 - x.2) * (z.1 - x.1)) : False := by
  by_cases hdx : y.1 - x.1 = 0
  · have hdy : y.2 - x.2 ≠ 0 := by
      intro h
      apply hxy
      apply Prod.ext
      · exact (sub_eq_zero.mp hdx).symm
      · exact (sub_eq_zero.mp h).symm
    let t : ℝ := (z.2 - x.2) / (y.2 - x.2)
    have hz2diff : z.2 - x.2 = t * (y.2 - x.2) := by
      dsimp [t]
      field_simp
    have hz2 : z.2 = x.2 + t * (y.2 - x.2) := by linarith
    have hz1diff0 : z.1 - x.1 = 0 := by
      have hm : (y.2 - x.2) * (z.1 - x.1) = 0 := by
        rw [hdx] at hcol
        simpa only [zero_mul] using hcol.symm
      exact (mul_eq_zero.mp hm).resolve_left hdy
    have hz1 : z.1 = x.1 + t * (y.1 - x.1) := by
      rw [hdx]
      simp only [mul_zero, add_zero]
      exact sub_eq_zero.mp hz1diff0
    dsimp [sqDist] at hx hy hz
    rw [hz1, hz2] at hz
    have hvpos : 0 < (y.1 - x.1) ^ 2 + (y.2 - x.2) ^ 2 := by
      positivity
    have hdot : 2 * ((p.1 - x.1) * (y.1 - x.1) +
        (p.2 - x.2) * (y.2 - x.2)) -
        ((y.1 - x.1) ^ 2 + (y.2 - x.2) ^ 2) = 0 := by
      nlinarith [hx, hy]
    have hzquad : -2 * t * ((p.1 - x.1) * (y.1 - x.1) +
        (p.2 - x.2) * (y.2 - x.2)) + t ^ 2 *
        ((y.1 - x.1) ^ 2 + (y.2 - x.2) ^ 2) = 0 := by
      nlinarith [hx, hz]
    have htprod : t * (t - 1) *
        ((y.1 - x.1) ^ 2 + (y.2 - x.2) ^ 2) = 0 := by
      linear_combination hzquad + t * hdot
    have ht : t = 0 ∨ t = 1 := by
      rcases mul_eq_zero.mp htprod with h | h
      · exact (mul_eq_zero.mp h).imp_right (sub_eq_zero.mp)
      · exact False.elim ((ne_of_gt hvpos) h)
    rcases ht with ht | ht
    · apply hxz
      apply Prod.ext <;> simp [hz1, hz2, ht]
    · apply hyz
      apply Prod.ext <;> simp [hz1, hz2, ht]
  · let t : ℝ := (z.1 - x.1) / (y.1 - x.1)
    have hz1diff : z.1 - x.1 = t * (y.1 - x.1) := by
      dsimp [t]
      field_simp
    have hz1 : z.1 = x.1 + t * (y.1 - x.1) := by linarith
    have hz2diff : z.2 - x.2 = t * (y.2 - x.2) := by
      have hm : (y.1 - x.1) *
          ((z.2 - x.2) - t * (y.2 - x.2)) = 0 := by
        calc
          _ = (y.1 - x.1) * (z.2 - x.2) -
              (y.2 - x.2) * (z.1 - x.1) := by rw [hz1]; ring
          _ = 0 := sub_eq_zero.mpr hcol
      exact sub_eq_zero.mp ((mul_eq_zero.mp hm).resolve_left hdx)
    have hz2 : z.2 = x.2 + t * (y.2 - x.2) := by linarith
    dsimp [sqDist] at hx hy hz
    rw [hz1, hz2] at hz
    have hvpos : 0 < (y.1 - x.1) ^ 2 + (y.2 - x.2) ^ 2 := by
      positivity
    have hdot : 2 * ((p.1 - x.1) * (y.1 - x.1) +
        (p.2 - x.2) * (y.2 - x.2)) -
        ((y.1 - x.1) ^ 2 + (y.2 - x.2) ^ 2) = 0 := by
      nlinarith [hx, hy]
    have hzquad : -2 * t * ((p.1 - x.1) * (y.1 - x.1) +
        (p.2 - x.2) * (y.2 - x.2)) + t ^ 2 *
        ((y.1 - x.1) ^ 2 + (y.2 - x.2) ^ 2) = 0 := by
      nlinarith [hx, hz]
    have htprod : t * (t - 1) *
        ((y.1 - x.1) ^ 2 + (y.2 - x.2) ^ 2) = 0 := by
      linear_combination hzquad + t * hdot
    have ht : t = 0 ∨ t = 1 := by
      rcases mul_eq_zero.mp htprod with h | h
      · exact (mul_eq_zero.mp h).imp_right (sub_eq_zero.mp)
      · exact False.elim ((ne_of_gt hvpos) h)
    rcases ht with ht | ht
    · apply hxz
      apply Prod.ext <;> simp [hz1, hz2, ht]
    · apply hyz
      apply Prod.ext <;> simp [hz1, hz2, ht]

lemma at_most_two_common_distance_points
    (p q x y z : Point) (r : ℝ)
    (hpq : p ≠ q)
    (hxp : sqDist p x = r) (hxq : sqDist q x = r)
    (hyp : sqDist p y = r) (hyq : sqDist q y = r)
    (hzp : sqDist p z = r) (hzq : sqDist q z = r) :
    x = y ∨ x = z ∨ y = z := by
  by_contra h
  push_neg at h
  have hAB : (q.1 - p.1) ≠ 0 ∨ (q.2 - p.2) ≠ 0 := by
    by_contra hab
    push_neg at hab
    apply hpq
    apply Prod.ext
    · exact (sub_eq_zero.mp hab.1).symm
    · exact (sub_eq_zero.mp hab.2).symm
  have line (u : Point) (hup : sqDist p u = r) (huq : sqDist q u = r) :
      (q.1 - p.1) * u.1 + (q.2 - p.2) * u.2 =
        ((q.1 ^ 2 + q.2 ^ 2) - (p.1 ^ 2 + p.2 ^ 2)) / 2 := by
    dsimp [sqDist] at hup huq
    nlinarith
  have hcol := collinear_of_common_linear
    (q.1 - p.1) (q.2 - p.2)
    (((q.1 ^ 2 + q.2 ^ 2) - (p.1 ^ 2 + p.2 ^ 2)) / 2)
    x y z hAB (line x hxp hxq) (line y hyp hyq) (line z hzp hzq)
  exact three_cospherical_not_collinear p x y z r hxp hyp hzp h.1 h.2.1 h.2.2 hcol

end Erdos959
