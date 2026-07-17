/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import ErdosProblems.Erdos686K5PrimitiveFactorMatching

/-!
# Erdős 686, k=5: nonlinear primitive-scale resultant

Put the centered coordinates in primitive form `X=g*u`, `Y=g*v`, set
`z=g^2`, and write the first scale divisibility as `4v-u=z*t`.  Dividing
the centered quintic equation by this forced first-order factor leaves the
polynomial below.  Its reductions modulo `z` and `t` are independent
nonlinear constraints.  Together with `gcd(u,v)=1`, they bound the overlap
of the scale and its first quotient by a fixed integer.
-/

namespace Erdos686
namespace Erdos686Variant

/-- The exact quotient after substituting `u=4v-z*t` in the primitive
centered quintic and cancelling the forced factor `z`. -/
def k5PrimitiveScaleResidual (z t v : ℤ) : ℤ :=
  t^5*z^6 - 20*t^4*v*z^5 + 160*t^3*v^2*z^4 - 5*t^3*z^3 -
    640*t^2*v^3*z^3 + 60*t^2*v*z^2 + 1280*t*v^4*z^2 -
    240*t*v^2*z + 4*t - 1020*v^5*z + 300*v^3

/-- Exact cancellation of the first scale factor. -/
theorem k5_primitive_scale_residual_eq_zero
    {u v z t : ℕ} (hz : 0 < z)
    (hscale : u + z*t = 4*v)
    (heq : (u : ℤ) * ((z : ℤ)*(u : ℤ)^2-1) *
          ((z : ℤ)*(u : ℤ)^2-4) =
        4*(v : ℤ)*((z : ℤ)*(v : ℤ)^2-1)*
          ((z : ℤ)*(v : ℤ)^2-4)) :
    k5PrimitiveScaleResidual (z : ℤ) (t : ℤ) (v : ℤ) = 0 := by
  have hscaleZ : (u : ℤ) + (z : ℤ)*(t : ℤ) = 4*(v : ℤ) := by
    exact_mod_cast hscale
  have hu : (u : ℤ) = 4*(v : ℤ) - (z : ℤ)*(t : ℤ) := by linarith
  have hid :
      (u : ℤ) * ((z : ℤ)*(u : ℤ)^2-1) * ((z : ℤ)*(u : ℤ)^2-4) -
          4*(v : ℤ)*((z : ℤ)*(v : ℤ)^2-1)*
            ((z : ℤ)*(v : ℤ)^2-4) =
        -(z : ℤ) * k5PrimitiveScaleResidual (z : ℤ) (t : ℤ) (v : ℤ) := by
    rw [hu]
    simp only [k5PrimitiveScaleResidual]
    ring
  have hprod : (z : ℤ) *
      k5PrimitiveScaleResidual (z : ℤ) (t : ℤ) (v : ℤ) = 0 := by
    calc
      (z : ℤ) * k5PrimitiveScaleResidual (z : ℤ) (t : ℤ) (v : ℤ) =
          -((u : ℤ) * ((z : ℤ)*(u : ℤ)^2-1) *
              ((z : ℤ)*(u : ℤ)^2-4) -
            4*(v : ℤ)*((z : ℤ)*(v : ℤ)^2-1)*
              ((z : ℤ)*(v : ℤ)^2-4)) := by rw [hid]; ring
      _ = 0 := by rw [heq]; ring
  exact (mul_eq_zero.mp hprod).resolve_left (by exact_mod_cast hz.ne')

/-- The first nonlinear endpoint congruence.  It is obtained only after
cancelling the forced scale factor, so it is not the tautological reduction
of the original equation modulo `z`. -/
theorem k5_primitive_scale_z_dvd_cubic
    {z t v : ℤ} (hres : k5PrimitiveScaleResidual z t v = 0) :
    z ∣ 4*t + 300*v^3 := by
  refine ⟨-(t^5*z^5 - 20*t^4*v*z^4 + 160*t^3*v^2*z^3 -
      5*t^3*z^2 - 640*t^2*v^3*z^2 + 60*t^2*v*z +
      1280*t*v^4*z - 240*t*v^2 - 1020*v^5), ?_⟩
  have := hres
  simp only [k5PrimitiveScaleResidual] at this
  linear_combination this

/-- The opposite endpoint congruence. -/
theorem k5_primitive_scale_t_dvd_quadratic
    {z t v : ℤ} (hres : k5PrimitiveScaleResidual z t v = 0) :
    t ∣ 60*v^3*(5-17*z*v^2) := by
  refine ⟨-(t^4*z^6 - 20*t^3*v*z^5 + 160*t^2*v^2*z^4 -
      5*t^2*z^3 - 640*t*v^3*z^3 + 60*t*v*z^2 +
      1280*v^4*z^2 - 240*v^2*z + 4), ?_⟩
  have := hres
  simp only [k5PrimitiveScaleResidual] at this
  linear_combination this

private theorem k5_primitive_scale_coprime_z_v
    {u v z t : ℕ} (hcop : Nat.Coprime u v)
    (hscale : u + z*t = 4*v) :
    Nat.Coprime z v := by
  let q := Nat.gcd z v
  have hqz : q ∣ z := Nat.gcd_dvd_left z v
  have hqv : q ∣ v := Nat.gcd_dvd_right z v
  have hqzt : q ∣ z*t := dvd_mul_of_dvd_left hqz t
  have hqsum : q ∣ u + z*t := by
    rw [hscale]
    exact dvd_mul_of_dvd_right hqv 4
  have hqu : q ∣ u := (Nat.dvd_add_iff_left hqzt).mpr hqsum
  have hqone : q ∣ 1 := by
    have : q ∣ Nat.gcd u v := Nat.dvd_gcd hqu hqv
    simpa [hcop.gcd_eq_one] using this
  exact Nat.dvd_one.mp hqone

/-- Fixed primitive-scale overlap.  This is the resultant consequence used
by later owner-profile or continued-fraction arguments. -/
theorem k5_primitive_scale_gcd_dvd_three_hundred
    {u v z t : ℕ} (hz : 0 < z)
    (hcop : Nat.Coprime u v)
    (hscale : u + z*t = 4*v)
    (heq : (u : ℤ) * ((z : ℤ)*(u : ℤ)^2-1) *
          ((z : ℤ)*(u : ℤ)^2-4) =
        4*(v : ℤ)*((z : ℤ)*(v : ℤ)^2-1)*
          ((z : ℤ)*(v : ℤ)^2-4)) :
    Nat.gcd z t ∣ 300 := by
  have hres := k5_primitive_scale_residual_eq_zero hz hscale heq
  have hzdivZ := k5_primitive_scale_z_dvd_cubic hres
  have hzdiv : z ∣ 4*t + 300*v^3 := by exact_mod_cast hzdivZ
  let h := Nat.gcd z t
  have hhz : h ∣ z := Nat.gcd_dvd_left z t
  have hht : h ∣ t := Nat.gcd_dvd_right z t
  have hsum : h ∣ 4*t + 300*v^3 := dvd_trans hhz hzdiv
  have hfour : h ∣ 4*t := dvd_mul_of_dvd_right hht 4
  have hprod : h ∣ 300*v^3 := by
    have := Nat.dvd_sub hsum hfour
    convert this using 1 <;> omega
  have hzv := k5_primitive_scale_coprime_z_v hcop hscale
  have hhv : Nat.Coprime h v := Nat.Coprime.of_dvd_left hhz hzv
  exact (hhv.pow_right 3).dvd_of_dvd_mul_right (by
    simpa [mul_assoc] using hprod)

/-- On the odd-scale branch the fixed overlap loses its factor four. -/
theorem k5_odd_primitive_scale_gcd_dvd_seventy_five
    {u v z t : ℕ} (hz : 0 < z)
    (hodd : Nat.Coprime z 2)
    (hcop : Nat.Coprime u v)
    (hscale : u + z*t = 4*v)
    (heq : (u : ℤ) * ((z : ℤ)*(u : ℤ)^2-1) *
          ((z : ℤ)*(u : ℤ)^2-4) =
        4*(v : ℤ)*((z : ℤ)*(v : ℤ)^2-1)*
          ((z : ℤ)*(v : ℤ)^2-4)) :
    Nat.gcd z t ∣ 75 := by
  let h := Nat.gcd z t
  have hh300 := k5_primitive_scale_gcd_dvd_three_hundred
    hz hcop hscale heq
  have hh2 : Nat.Coprime h 2 :=
    Nat.Coprime.of_dvd_left (Nat.gcd_dvd_left z t) hodd
  have hh4 : Nat.Coprime h 4 := by
    simpa using hh2.pow_right 2
  have hprod : h ∣ 4*75 := by norm_num at hh300 ⊢; exact hh300
  exact hh4.dvd_of_dvd_mul_left hprod

#print axioms k5_primitive_scale_residual_eq_zero
#print axioms k5_primitive_scale_z_dvd_cubic
#print axioms k5_primitive_scale_t_dvd_quadratic
#print axioms k5_primitive_scale_gcd_dvd_three_hundred
#print axioms k5_odd_primitive_scale_gcd_dvd_seventy_five

end Erdos686Variant
end Erdos686
