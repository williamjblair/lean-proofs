import Research.RepresentationCount
import Research.Denominator

noncomputable section
namespace Erdos959

/-- Embed an integer lattice point after scaling squared target `s` to one. -/
def scaledIntPoint (s : ℕ) (x : IntPoint) : Point :=
  ((x.1 : ℝ) / Real.sqrt s, (x.2 : ℝ) / Real.sqrt s)

lemma sqrt_nat_ne_zero {s : ℕ} (hs : 1 ≤ s) : Real.sqrt (s : ℝ) ≠ 0 := by
  positivity

lemma sqDist_scaledIntPoint {s : ℕ} (hs : 1 ≤ s) (x y : IntPoint) :
    sqDist (scaledIntPoint s x) (scaledIntPoint s y) =
      (intNormSq (x - y) : ℝ) / s := by
  have hs0 : (0 : ℝ) ≤ s := by positivity
  have hsqrt : Real.sqrt (s : ℝ) ≠ 0 := sqrt_nat_ne_zero hs
  have hsqrtSq : (Real.sqrt (s : ℝ)) ^ 2 = s := Real.sq_sqrt hs0
  dsimp [sqDist, scaledIntPoint, intNormSq]
  push_cast
  field_simp
  nlinarith

lemma sqDist_scaled_target {s : ℕ} (hs : 1 ≤ s) (x y : IntPoint)
    (hxy : intNormSq (x - y) = s) :
    sqDist (scaledIntPoint s x) (scaledIntPoint s y) = 1 := by
  rw [sqDist_scaledIntPoint hs]
  norm_cast at hxy
  rw [hxy]
  exact div_self (by positivity)

/-- Equality of two normalized lattice distances is an exact cross-multiplied
integer equation. -/
lemma normalized_distance_eq_iff_crossmul
    {s u t v : ℕ} (hs : 1 ≤ s) (hu : 1 ≤ u) :
    (t : ℝ) / s = (v : ℝ) / u ↔ u * t = s * v := by
  constructor
  · intro h
    have hsR : (s : ℝ) ≠ 0 := by positivity
    have huR : (u : ℝ) ≠ 0 := by positivity
    field_simp at h
    have hNat : t * u = s * v := by exact_mod_cast h
    simpa [mul_comm] using hNat
  · intro h
    have hR : (u : ℝ) * t = (s : ℝ) * v := by exact_mod_cast h
    have hsR : (s : ℝ) ≠ 0 := by positivity
    have huR : (u : ℝ) ≠ 0 := by positivity
    field_simp
    simpa [mul_comm] using hR

lemma exists_reduced_natural_ratio (t s : ℕ) (hs : 1 ≤ s) :
    ∃ A D : ℕ, D.Coprime A ∧ D * t = A * s ∧ 1 ≤ D := by
  let g := t.gcd s
  let A := t / g
  let D := s / g
  have hg : 0 < g := by
    dsimp [g]
    exact Nat.gcd_pos_of_pos_right t (by omega)
  have ht : A * g = t := Nat.div_mul_cancel (Nat.gcd_dvd_left t s)
  have hs' : D * g = s := Nat.div_mul_cancel (Nat.gcd_dvd_right t s)
  have hcopAD : A.Coprime D := Nat.coprime_div_gcd_div_gcd hg
  have hD : 1 ≤ D := by
    have hDpos : 0 < D := by
      apply Nat.div_pos
      · exact Nat.gcd_le_right t (by omega)
      · exact hg
    omega
  refine ⟨A, D, hcopAD.symm, ?_, hD⟩
  calc
    D * t = D * (A * g) := by rw [ht]
    _ = A * (D * g) := by ring
    _ = A * s := by rw [hs']

/-- Reduce one integer ratio `t/s`; its denominator divides every target
integer `u` on which the same normalized class is integral. -/
lemma reduced_support_from_equal_normalized_distances
    {s t u v A D : ℕ}
    (hs : 1 ≤ s) (hu : 1 ≤ u)
    (hcop : D.Coprime A) (href : D * t = A * s)
    (hequal : (t : ℝ) / s = (v : ℝ) / u) :
    D ∣ u := by
  have huv : u * t = s * v :=
    (normalized_distance_eq_iff_crossmul hs hu).mp hequal
  have hcancel : s * (D * v) = s * (A * u) := by
    calc
      s * (D * v) = D * (s * v) := by ring
      _ = D * (u * t) := by rw [← huv]
      _ = u * (D * t) := by ring
      _ = u * (A * s) := by rw [href]
      _ = s * (A * u) := by ring
  have hDv : D * v = A * u := Nat.eq_of_mul_eq_mul_left hs hcancel
  apply hcop.dvd_of_dvd_mul_left
  exact ⟨v, hDv.symm⟩

end Erdos959
