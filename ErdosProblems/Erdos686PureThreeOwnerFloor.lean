/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import ErdosProblems.Erdos686ReflectedThirdComposition

/-!
# Erdős 686: pure three-owner floor elimination

In the branch where the reflection center is the product of exactly three
cleaned large components, write

`S = P * Q * R`, `h = d + k + 1`, and `e_i = h - 2*i`.

The reflected square lift at the owner of `P` is, after clearing the harmless
factor two,

* `P^2 | 5*S - 3*e_i` in an even row;
* `P^2 | 3*S - 5*e_i` in an odd row.

For `k >= 220`, the exact product window pins `t = a*b*c` to `15*S+r`
in an even row and `3*S+r` in an odd row, with `0 < r < S`.  Combining the
pinned floor, the square lift, and the reflected third composition eliminates
`S` completely.  The two theorems below record that integer elimination.

They are deliberately local: construction of `P,Q,R`, the product window,
and the three cyclic equation-facing lifts remain explicit hypotheses at the
eventual application site.
-/

namespace Erdos686
namespace Erdos686Variant

/-- Even-row pure-three-owner elimination.

`delta` is the product of the two owner differences.  No inverse of `3` or
`5` is used: both potentially dangerous cancellations are represented by
explicit coprimality hypotheses. -/
theorem even_pure_three_owner_floor_component
    {P C D E delta t S r e : ℤ}
    (hcop9 : IsCoprime (P ^ 2) 9)
    (hthird : P ^ 2 ∣
      9 * C * t - 108 * D * delta + 180 * E * delta * S)
    (hfloor : t = 15 * S + r)
    (hsquare : P ^ 2 ∣ 5 * S - 3 * e) :
    P ^ 2 ∣
      5 * C * r + 45 * C * e + 60 * delta * (E * e - D) := by
  have hscaled : P ^ 2 ∣
      9 * (C * t - 12 * D * delta + 20 * E * delta * S) := by
    convert hthird using 1 <;> ring
  have hbase : P ^ 2 ∣
      C * t - 12 * D * delta + 20 * E * delta * S :=
    hcop9.dvd_of_dvd_mul_left hscaled
  rw [hfloor] at hbase
  have hbaseFive := dvd_mul_of_dvd_right hbase 5
  have hsquareScaled := dvd_mul_of_dvd_right hsquare
    (15 * C + 20 * E * delta)
  have hdiff := dvd_sub hbaseFive hsquareScaled
  convert hdiff using 1 <;> ring

/-- Odd-row pure-three-owner elimination. -/
theorem odd_pure_three_owner_floor_component
    {P C D E delta t S r e : ℤ}
    (hcop5 : IsCoprime (P ^ 2) 5)
    (hthird : P ^ 2 ∣
      5 * C * t + 100 * D * delta - 60 * E * delta * S)
    (hfloor : t = 3 * S + r)
    (hsquare : P ^ 2 ∣ 3 * S - 5 * e) :
    P ^ 2 ∣
      3 * C * r + 15 * C * e + 60 * delta * (D - E * e) := by
  have hscaled : P ^ 2 ∣
      5 * (C * t + 20 * D * delta - 12 * E * delta * S) := by
    convert hthird using 1 <;> ring
  have hbase : P ^ 2 ∣
      C * t + 20 * D * delta - 12 * E * delta * S :=
    hcop5.dvd_of_dvd_mul_left hscaled
  rw [hfloor] at hbase
  have hbaseThree := dvd_mul_of_dvd_right hbase 3
  have hsquareScaled := dvd_mul_of_dvd_right hsquare
    (3 * C - 12 * E * delta)
  have hdiff := dvd_sub hbaseThree hsquareScaled
  convert hdiff using 1 <;> ring

/-- The affine even-row expression, named for downstream exact CRT work. -/
def evenPureThreeFloorForm
    (C D E delta r e : ℤ) : ℤ :=
  5 * C * r + 45 * C * e + 60 * delta * (E * e - D)

/-- The affine odd-row expression, named for downstream exact CRT work. -/
def oddPureThreeFloorForm
    (C D E delta r e : ℤ) : ℤ :=
  3 * C * r + 15 * C * e + 60 * delta * (D - E * e)

#print axioms even_pure_three_owner_floor_component
#print axioms odd_pure_three_owner_floor_component

end Erdos686Variant
end Erdos686
