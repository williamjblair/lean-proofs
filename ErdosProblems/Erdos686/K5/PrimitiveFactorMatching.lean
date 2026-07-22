/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import ErdosProblems.Erdos686.Core.CFTailScale

/-!
# Erdős 686, k=5: primitive centered-factor matching

This file isolates exact consequences of

`u (z*u^2-1)(z*u^2-4) = 4 v (z*v^2-1)(z*v^2-4)`

after `X=g*u`, `Y=g*v`, `z=g^2`, and `gcd(u,v)=1`.  It deliberately does
not assert the open odd-tail theorem.

The central point is that the two divisibilities have the *same* quotient.
That quotient is almost coprime to both primitive coordinates.  For odd
`g`, the scale divisibility also turns the quadratic roots into a single
linear-factor matching problem at `W=g*(4v-u)`.

The accompanying exact verifier is
`compute/campaign686/agent_t1_primitive_matching/k5_primitive_matching_verify.py`.
-/

namespace Erdos686
namespace Erdos686Variant

/-- Coprimality extracts one common quotient from the two primitive sides. -/
theorem k5_common_matching_quotient
    {u v U V : ℕ}
    (hv : 0 < v) (hcop : Nat.Coprime u v)
    (heq : u * U = 4 * v * V) :
    ∃ a : ℕ, U = v * a ∧ 4 * V = u * a := by
  have hvU : v ∣ u * U := by
    rw [heq]
    exact ⟨4 * V, by ring⟩
  have hU : v ∣ U := hcop.symm.dvd_of_dvd_mul_left hvU
  obtain ⟨a, ha⟩ := hU
  refine ⟨a, ha, ?_⟩
  have hcancel : v * (u * a) = v * (4 * V) := by
    calc
      v * (u * a) = u * U := by rw [ha]; ring
      _ = 4 * v * V := heq
      _ = v * (4 * V) := by ring
  exact Nat.mul_left_cancel hv hcancel.symm

/-- If the upper quadratic product is `4` modulo `u`, its complementary
common quotient has no common factor with `u` outside `4`. -/
lemma k5_common_quotient_gcd_u_dvd_four
    {u v U a L : ℕ}
    (hU : U = v * a) (hrem : U = u * L + 4) :
    Nat.gcd a u ∣ 4 := by
  let h := Nat.gcd a u
  have ha : h ∣ a := Nat.gcd_dvd_left a u
  have hu : h ∣ u := Nat.gcd_dvd_right a u
  have hUdvd : h ∣ U := by
    rw [hU]
    exact dvd_mul_of_dvd_right ha v
  have huL : h ∣ u * L := dvd_mul_of_dvd_left hu L
  rw [hrem] at hUdvd
  exact (Nat.dvd_add_iff_right huL).mpr hUdvd

/-- The lower product is `4` modulo `v`; the extra outer factor `4` leaves
only a fixed `16` loss in the common quotient. -/
lemma k5_common_quotient_gcd_v_dvd_sixteen
    {u v V a L : ℕ}
    (ha : 4 * V = u * a) (hrem : V = v * L + 4) :
    Nat.gcd a v ∣ 16 := by
  let h := Nat.gcd a v
  have hadvd : h ∣ a := Nat.gcd_dvd_left a v
  have hv : h ∣ v := Nat.gcd_dvd_right a v
  have hua : h ∣ u * a := dvd_mul_of_dvd_right hadvd u
  have hfourV : h ∣ 4 * V := by rwa [ha]
  have hfourvL : h ∣ 4 * (v * L) := by
    exact dvd_mul_of_dvd_right (dvd_mul_of_dvd_left hv L) 4
  rw [hrem] at hfourV
  have hsum : 4 * (v * L + 4) = 4 * (v * L) + 16 := by ring
  rw [hsum] at hfourV
  exact (Nat.dvd_add_iff_right hfourvL).mpr hfourV

/-- The upper remainder is also `4` modulo the square scale. -/
lemma k5_scale_gcd_upper_common_part_dvd_four
    {z v U a L : ℕ}
    (hU : U = v * a) (hrem : U = z * L + 4) :
    Nat.gcd z (v * a) ∣ 4 := by
  let h := Nat.gcd z (v * a)
  have hz : h ∣ z := Nat.gcd_dvd_left z (v * a)
  have hva : h ∣ v * a := Nat.gcd_dvd_right z (v * a)
  have hUdvd : h ∣ U := by simpa [hU] using hva
  have hzL : h ∣ z * L := dvd_mul_of_dvd_left hz L
  rw [hrem] at hUdvd
  exact (Nat.dvd_add_iff_right hzL).mpr hUdvd

/-- The lower remainder and its outer coefficient leave a fixed `16` loss
against the square scale. -/
lemma k5_scale_gcd_lower_common_part_dvd_sixteen
    {z u V a L : ℕ}
    (ha : 4 * V = u * a) (hrem : V = z * L + 4) :
    Nat.gcd z (u * a) ∣ 16 := by
  let h := Nat.gcd z (u * a)
  have hz : h ∣ z := Nat.gcd_dvd_left z (u * a)
  have hua : h ∣ u * a := Nat.gcd_dvd_right z (u * a)
  have hfourV : h ∣ 4 * V := by simpa [ha] using hua
  have hfourzL : h ∣ 4 * (z * L) := by
    exact dvd_mul_of_dvd_right (dvd_mul_of_dvd_left hz L) 4
  rw [hrem] at hfourV
  have hsum : 4 * (z * L + 4) = 4 * (z * L) + 16 := by ring
  rw [hsum] at hfourV
  exact (Nat.dvd_add_iff_right hfourzL).mpr hfourV

/-- The two factors `T-1` and `T-4` are coprime away from `3`. -/
lemma k5_quadratic_factor_gcd_dvd_three {T : ℕ} (hT : 4 ≤ T) :
    Nat.gcd (T - 1) (T - 4) ∣ 3 := by
  have hsub : (T - 1) - (T - 4) = 3 := by omega
  have hleft := Nat.gcd_dvd_left (T - 1) (T - 4)
  have hright := Nat.gcd_dvd_right (T - 1) (T - 4)
  rw [← hsub]
  exact Nat.dvd_sub hleft hright

/-- On an odd-scale branch, the exact k=5 lower ratio bracket sharpens the
square-scale constant from `12v` to `2.69v`.  The exponent is unchanged. -/
lemma k5_odd_scale_lt_two_sixty_nine_hundredths
    {u v z t : ℕ}
    (ht : 0 < t) (hscale : u + z * t = 4 * v)
    (hratio : 131 * v < 100 * u) :
    100 * z < 269 * v := by
  have ht1 : 1 ≤ t := ht
  have hzle : z ≤ z * t := by
    simpa using Nat.mul_le_mul_left z ht1
  have hzt : 100 * (z * t) < 269 * v := by omega
  exact lt_of_le_of_lt (Nat.mul_le_mul_left 100 hzle) hzt

/-- Integer polynomial remainder behind the fixed-affine-ray certificate.
If `u=A*t`, `v=B*t-1`, then upper matching forces `v` to divide one fixed
quartic resultant in `A,B`. -/
theorem k5_affine_ray_resultant_dvd
    {A B t u v : ℤ}
    (hu : u = A * t) (hv : B * t = v + 1)
    (hmatch : v ∣ (u ^ 2 - 1) * (u ^ 2 - 4)) :
    v ∣ (A ^ 2 - B ^ 2) * (A ^ 2 - 4 * B ^ 2) := by
  have hlin : v ∣ B * u - A := by
    refine ⟨A, ?_⟩
    rw [hu]
    linear_combination A * hv
  have hsquare : v ∣ B ^ 2 * u ^ 2 - A ^ 2 := by
    obtain ⟨q, hq⟩ := hlin
    refine ⟨q * (B * u + A), ?_⟩
    calc
      B ^ 2 * u ^ 2 - A ^ 2 = (B * u - A) * (B * u + A) := by ring
      _ = (v * q) * (B * u + A) := by rw [hq]
      _ = v * (q * (B * u + A)) := by ring
  have hscaled : v ∣ B ^ 4 * ((u ^ 2 - 1) * (u ^ 2 - 4)) :=
    dvd_mul_of_dvd_right hmatch (B ^ 4)
  have hdiff : v ∣
      (A ^ 2 - B ^ 2) * (A ^ 2 - 4 * B ^ 2) -
        B ^ 4 * ((u ^ 2 - 1) * (u ^ 2 - 4)) := by
    obtain ⟨q, hq⟩ := hsquare
    refine ⟨-q * (A ^ 2 + B ^ 2 * u ^ 2 - 5 * B ^ 2), ?_⟩
    calc
      (A ^ 2 - B ^ 2) * (A ^ 2 - 4 * B ^ 2) -
          B ^ 4 * ((u ^ 2 - 1) * (u ^ 2 - 4)) =
          -(B ^ 2 * u ^ 2 - A ^ 2) *
            (A ^ 2 + B ^ 2 * u ^ 2 - 5 * B ^ 2) := by ring
      _ = -(v * q) * (A ^ 2 + B ^ 2 * u ^ 2 - 5 * B ^ 2) := by rw [hq]
      _ = v * (-q * (A ^ 2 + B ^ 2 * u ^ 2 - 5 * B ^ 2)) := by ring
  convert dvd_add hdiff hscaled using 1 <;> ring

/-- Once the odd-scale relation is written `u+z*t=4v`, upper matching is
the four-linear-factor condition at `W=g^3*t`. -/
theorem k5_upper_matching_compresses_to_W
    {g z u v t W : ℤ}
    (hz : z = g ^ 2) (hscale : u + z * t = 4 * v)
    (hW : W = g ^ 3 * t)
    (hmatch : v ∣ (z * u ^ 2 - 1) * (z * u ^ 2 - 4)) :
    v ∣ (W - 1) * (W + 1) * (W - 2) * (W + 2) := by
  have hbase : v ∣ W ^ 2 - z * u ^ 2 := by
    refine ⟨4 * z * (z * t - u), ?_⟩
    calc
      W ^ 2 - z * u ^ 2 = z * (z * t - u) * (u + z * t) := by
        rw [hz, hW]
        ring
      _ = z * (z * t - u) * (4 * v) := by rw [hscale]
      _ = v * (4 * z * (z * t - u)) := by ring
  have hdiff : v ∣
      (W ^ 2 - 1) * (W ^ 2 - 4) -
        (z * u ^ 2 - 1) * (z * u ^ 2 - 4) := by
    obtain ⟨q, hq⟩ := hbase
    refine ⟨q * (W ^ 2 + z * u ^ 2 - 5), ?_⟩
    calc
      (W ^ 2 - 1) * (W ^ 2 - 4) -
          (z * u ^ 2 - 1) * (z * u ^ 2 - 4) =
          (W ^ 2 - z * u ^ 2) * (W ^ 2 + z * u ^ 2 - 5) := by ring
      _ = (v * q) * (W ^ 2 + z * u ^ 2 - 5) := by rw [hq]
      _ = v * (q * (W ^ 2 + z * u ^ 2 - 5)) := by ring
  have hpoly : v ∣ (W ^ 2 - 1) * (W ^ 2 - 4) := by
    convert dvd_add hdiff hmatch using 1 <;> ring
  convert hpoly using 1 <;> ring

/-- Symmetrically, the outer coefficient `4` costs only a fixed factor and
lower matching becomes the four factors at offsets `4` and `8`. -/
theorem k5_lower_matching_compresses_to_W
    {g z u v t W : ℤ}
    (hz : z = g ^ 2) (hscale : u + z * t = 4 * v)
    (hW : W = g ^ 3 * t)
    (hmatch : u ∣ 4 * ((z * v ^ 2 - 1) * (z * v ^ 2 - 4))) :
    u ∣ (W - 4) * (W + 4) * (W - 8) * (W + 8) := by
  have hbase : u ∣ W ^ 2 - 16 * z * v ^ 2 := by
    refine ⟨-z * (z * t + 4 * v), ?_⟩
    have hminus : z * t - 4 * v = -u := by linarith
    calc
      W ^ 2 - 16 * z * v ^ 2 = z * (z * t - 4 * v) * (z * t + 4 * v) := by
        rw [hz, hW]
        ring
      _ = z * (-u) * (z * t + 4 * v) := by rw [hminus]
      _ = u * (-z * (z * t + 4 * v)) := by ring
  have hdiff : u ∣
      (W ^ 2 - 16) * (W ^ 2 - 64) -
        256 * ((z * v ^ 2 - 1) * (z * v ^ 2 - 4)) := by
    obtain ⟨q, hq⟩ := hbase
    refine ⟨q * (W ^ 2 + 16 * z * v ^ 2 - 80), ?_⟩
    calc
      (W ^ 2 - 16) * (W ^ 2 - 64) -
          256 * ((z * v ^ 2 - 1) * (z * v ^ 2 - 4)) =
          (W ^ 2 - 16 * z * v ^ 2) *
            (W ^ 2 + 16 * z * v ^ 2 - 80) := by ring
      _ = (u * q) * (W ^ 2 + 16 * z * v ^ 2 - 80) := by rw [hq]
      _ = u * (q * (W ^ 2 + 16 * z * v ^ 2 - 80)) := by ring
  have hscaled : u ∣ 256 * ((z * v ^ 2 - 1) * (z * v ^ 2 - 4)) := by
    convert dvd_mul_of_dvd_right hmatch 64 using 1 <;> ring
  have hpoly : u ∣ (W ^ 2 - 16) * (W ^ 2 - 64) := by
    convert dvd_add hdiff hscaled using 1 <;> ring
  convert hpoly using 1 <;> ring

#print axioms k5_common_matching_quotient
#print axioms k5_common_quotient_gcd_u_dvd_four
#print axioms k5_common_quotient_gcd_v_dvd_sixteen
#print axioms k5_scale_gcd_upper_common_part_dvd_four
#print axioms k5_scale_gcd_lower_common_part_dvd_sixteen
#print axioms k5_quadratic_factor_gcd_dvd_three
#print axioms k5_odd_scale_lt_two_sixty_nine_hundredths
#print axioms k5_affine_ray_resultant_dvd
#print axioms k5_upper_matching_compresses_to_W
#print axioms k5_lower_matching_compresses_to_W

end Erdos686Variant
end Erdos686
