import Research.Definitions
import Research.ConePolynomial
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic

open scoped BigOperators Polynomial

namespace Erdos521

@[simp] lemma sign_ne_zero (b : Bool) : sign b ≠ 0 := by
  cases b <;> simp [sign]

/-- Coefficients of the finite Littlewood polynomial are the chosen signs through degree `n`. -/
lemma littlewoodPolynomial_coeff (ω : ℕ → Bool) (n k : ℕ) :
    (littlewoodPolynomial ω n).coeff k = if k ≤ n then sign (ω k) else 0 := by
  classical
  simp [littlewoodPolynomial, Polynomial.coeff_monomial]

lemma littlewoodPolynomial_natDegree_le (ω : ℕ → Bool) (n : ℕ) :
    (littlewoodPolynomial ω n).natDegree ≤ n := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro k hk
  rw [littlewoodPolynomial_coeff]
  simp [Nat.not_le.mpr hk]

/-- The suffix-cone condition at odd degree `2m+1`.  It says that every terminal block of
coefficient pairs lies in the cone `u ≥ |v|`. -/
def SuffixCone (ω : ℕ → Bool) (m : ℕ) : Prop :=
  ∀ r ≤ m,
    |prefixSum (fun i ↦ sign (ω (2 * m - 2 * i))) r| ≤
      prefixSum (fun i ↦ sign (ω (2 * m + 1 - 2 * i))) r

/-- A suffix-cone event forces the reflected odd-degree Littlewood polynomial to be positive
throughout the punctured interval `(-1,1)`. -/
lemma SuffixCone.reflect_eval_pos {ω : ℕ → Bool} {m : ℕ} (hcone : SuffixCone ω m)
    {x : ℝ} (hx0 : 0 < |x|) (hx1 : |x| < 1) :
    0 < ((littlewoodPolynomial ω (2 * m + 1)).reflect (2 * m + 1)).eval x := by
  apply eval_reflect_odd_pos_of_cone (littlewoodPolynomial ω (2 * m + 1)) m
    (littlewoodPolynomial_natDegree_le _ _) hx0 hx1
  · intro r hr
    have h1 (i : ℕ) : 2 * m - 2 * i ≤ 2 * m + 1 :=
      (Nat.sub_le _ _).trans (by omega)
    have h2 (i : ℕ) : 2 * m + 1 - 2 * i ≤ 2 * m + 1 := Nat.sub_le _ _
    simpa only [littlewoodPolynomial_coeff, if_pos (h1 _), if_pos (h2 _)] using hcone r hr
  · exact ⟨0, Nat.zero_le _, Or.inl (by simp [littlewoodPolynomial_coeff])⟩

/-- Therefore a suffix-cone Littlewood polynomial has no real roots outside `[-1,1]`. -/
lemma SuffixCone.no_exterior_root {ω : ℕ → Bool} {m : ℕ} (hcone : SuffixCone ω m)
    {y : ℝ} (hy : 1 < |y|) :
    (littlewoodPolynomial ω (2 * m + 1)).eval y ≠ 0 := by
  have hy0 : y ≠ 0 := by
    intro h
    subst y
    norm_num at hy
  letI : Invertible y := invertibleOfNonzero hy0
  have hx0 : 0 < |y⁻¹| := abs_pos.mpr (inv_ne_zero hy0)
  have hx1 : |y⁻¹| < 1 := by
    rw [abs_inv]
    exact inv_lt_one_of_one_lt₀ hy
  have href := hcone.reflect_eval_pos hx0 hx1
  have hiff := Polynomial.eval₂_reflect_eq_zero_iff (RingHom.id ℝ) y (2 * m + 1)
    (littlewoodPolynomial ω (2 * m + 1)) (littlewoodPolynomial_natDegree_le _ _)
  intro hp
  apply ne_of_gt href
  apply hiff.mpr
  simpa using hp

end Erdos521
