/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import ErdosProblems.Erdos686K5PrimitiveApproximation

/-!
# Erdős 686, k=5: exact Euclidean constraint on primitive convergents

For a primitive centered solution put `z = g^2` and
`A_j = 4 v^j - u^j`.  Expanding the primitive quintic gives

`z^2 A_5 + 4 A_1 = 5 z A_3`.

On the below-root interval `3u < 4v`, the correction term is strictly
smaller than one denominator interval.  Consequently Euclidean division is
exact:

`(5 A_3) / A_5 = g^2` and `(5 A_3) % A_5 = 4t`.

Thus every odd nontrivially scaled primitive solution is not merely a
continued-fraction convergent: a specific quotient attached to that
convergent must be a square and its remainder has one of six fixed overlap
types.
-/

namespace Erdos686
namespace Erdos686Variant

/-- The positive-side power gap used by the primitive scale equation. -/
def k5PrimitivePowerGap (j u v : ℕ) : ℕ := 4 * v ^ j - u ^ j

/-- Expansion of the primitive centered quintic as a quadratic equation in
the square scale. -/
theorem k5_primitive_scale_quadratic_identity
    {g u v : ℕ} (hg : 0 < g)
    (hu1 : u ≤ 4 * v) (hu3 : u ^ 3 ≤ 4 * v ^ 3)
    (hu5 : u ^ 5 ≤ 4 * v ^ 5)
    (hsol : K5CenteredEq (g * u) (g * v)) :
    (g ^ 2) ^ 2 * k5PrimitivePowerGap 5 u v +
        4 * k5PrimitivePowerGap 1 u v =
      5 * (g ^ 2) * k5PrimitivePowerGap 3 u v := by
  have heq := k5_centered_primitive_factor_equation hg hsol
  have hid :
      ((g : ℤ) ^ 2) ^ 2 * (4 * (v : ℤ) ^ 5 - (u : ℤ) ^ 5) +
          4 * (4 * (v : ℤ) - (u : ℤ)) =
        5 * (g : ℤ) ^ 2 * (4 * (v : ℤ) ^ 3 - (u : ℤ) ^ 3) := by
    linear_combination -heq
  have hcast :
      (((g ^ 2) ^ 2 * k5PrimitivePowerGap 5 u v +
          4 * k5PrimitivePowerGap 1 u v : ℕ) : ℤ) =
        ((5 * (g ^ 2) * k5PrimitivePowerGap 3 u v : ℕ) : ℤ) := by
    have hu1' : u ^ 1 ≤ 4 * v ^ 1 := by simpa using hu1
    simp only [k5PrimitivePowerGap]
    push_cast [Nat.cast_sub hu1', Nat.cast_sub hu3, Nat.cast_sub hu5]
    simpa [pow_two] using hid
  exact_mod_cast hcast

/-- A numerical inequality behind the floor pin.  It is deliberately split
out: this is the only place where the coarse interval `3u < 4v` is used. -/
theorem k5_primitive_five_cubic_gap_gt_eight_linear_gap
    {u v : ℕ} (hv : 2 ≤ v) (hratio : 3 * u < 4 * v) :
    8 * k5PrimitivePowerGap 1 u v <
      5 * k5PrimitivePowerGap 3 u v := by
  have hcub := Nat.pow_lt_pow_left hratio (by norm_num : 3 ≠ 0)
  have hcub' : 27 * u ^ 3 < 64 * v ^ 3 := by
    simpa [mul_pow] using hcub
  have hu3 : u ^ 3 < 4 * v ^ 3 := by
    omega
  have hu1 : u < 4 * v := by omega
  have hv2 : 2 ^ 2 ≤ v ^ 2 := Nat.pow_le_pow_left hv 2
  have hv3 : 4 * v ≤ v ^ 3 := by
    calc
      4 * v = 2 ^ 2 * v := by norm_num
      _ ≤ v ^ 2 * v := Nat.mul_le_mul_right v hv2
      _ = v ^ 3 := by ring
  have hA1le : k5PrimitivePowerGap 1 u v ≤ 4 * v := by
    simp [k5PrimitivePowerGap]
  have hA3eq : k5PrimitivePowerGap 3 u v + u ^ 3 = 4 * v ^ 3 := by
    exact Nat.sub_add_cancel hu3.le
  nlinarith [hcub', hv3]

/-- Generic floor pin for a positive integral root of the primitive scale
quadratic. -/
theorem k5_primitive_scale_floor_pin
    {z u v : ℕ} (hz : 0 < z) (hv : 2 ≤ v)
    (hratio : 3 * u < 4 * v) (hu5 : u ^ 5 < 4 * v ^ 5)
    (hquad :
      z ^ 2 * k5PrimitivePowerGap 5 u v +
          4 * k5PrimitivePowerGap 1 u v =
        5 * z * k5PrimitivePowerGap 3 u v) :
    5 * k5PrimitivePowerGap 3 u v / k5PrimitivePowerGap 5 u v = z ∧
      4 * k5PrimitivePowerGap 1 u v <
        z * k5PrimitivePowerGap 5 u v := by
  let A1 := k5PrimitivePowerGap 1 u v
  let A3 := k5PrimitivePowerGap 3 u v
  let A5 := k5PrimitivePowerGap 5 u v
  have hA1 : 0 < A1 := by
    dsimp [A1, k5PrimitivePowerGap]
    exact Nat.sub_pos_of_lt (by simpa using (show u < 4 * v by omega))
  have hA5 : 0 < A5 := by
    dsimp [A5, k5PrimitivePowerGap]
    exact Nat.sub_pos_of_lt hu5
  have hgap : 8 * A1 < 5 * A3 := by
    simpa [A1, A3] using
      k5_primitive_five_cubic_gap_gt_eight_linear_gap hv hratio
  change z ^ 2 * A5 + 4 * A1 = 5 * z * A3 at hquad
  have hcorr : 4 * A1 < z * A5 := by
    by_contra hnot
    have hle : z * A5 ≤ 4 * A1 := Nat.le_of_not_gt hnot
    have hzquad : z ^ 2 * A5 ≤ 4 * z * A1 := by
      calc
        z ^ 2 * A5 = z * (z * A5) := by ring
        _ ≤ z * (4 * A1) := Nat.mul_le_mul_left z hle
        _ = 4 * z * A1 := by ring
    have hscaled : 5 * z * A3 ≤ 8 * z * A1 := by
      rw [← hquad]
      calc
        z ^ 2 * A5 + 4 * A1 ≤ 4 * z * A1 + 4 * A1 :=
          Nat.add_le_add_right hzquad (4 * A1)
        _ ≤ 4 * z * A1 + 4 * z * A1 := by
          apply Nat.add_le_add_left
          calc
            4 * A1 = 1 * (4 * A1) := by ring
            _ ≤ z * (4 * A1) := Nat.mul_le_mul_right (4 * A1) hz
            _ = 4 * z * A1 := by ring
        _ = 8 * z * A1 := by ring
    have : 5 * A3 ≤ 8 * A1 := by
      exact Nat.le_of_mul_le_mul_left
        (by simpa [mul_assoc, mul_left_comm, mul_comm] using hscaled) hz
    omega
  have hlo : z * A5 < 5 * A3 := by
    have hpos : 0 < 4 * A1 := by positivity
    have hzlt : z * (z * A5) < z * (5 * A3) := by
      calc
        z * (z * A5) = z ^ 2 * A5 := by ring
        _ < z ^ 2 * A5 + 4 * A1 := Nat.lt_add_of_pos_right hpos
        _ = 5 * z * A3 := hquad
        _ = z * (5 * A3) := by ring
    exact (Nat.mul_lt_mul_left hz).mp hzlt
  have hhi : 5 * A3 < (z + 1) * A5 := by
    have hzlt : z * (5 * A3) < z * ((z + 1) * A5) := by
      calc
        z * (5 * A3) = z ^ 2 * A5 + 4 * A1 := by
          rw [hquad]
          ring
        _ < z ^ 2 * A5 + z * A5 := Nat.add_lt_add_left hcorr _
        _ = z * ((z + 1) * A5) := by ring
    exact (Nat.mul_lt_mul_left hz).mp hzlt
  constructor
  · exact Nat.div_eq_of_lt_le hlo.le hhi
  · exact hcorr

/-- Exact quotient and remainder forced by the scale equation. -/
theorem k5_primitive_scale_euclidean_division
    {g u v t : ℕ} (hg : 0 < g) (hv : 2 ≤ v)
    (hscale : u + g ^ 2 * t = 4 * v)
    (hratio : 3 * u < 4 * v) (hu5 : u ^ 5 < 4 * v ^ 5)
    (hsol : K5CenteredEq (g * u) (g * v)) :
    5 * k5PrimitivePowerGap 3 u v / k5PrimitivePowerGap 5 u v = g ^ 2 ∧
      5 * k5PrimitivePowerGap 3 u v % k5PrimitivePowerGap 5 u v = 4 * t ∧
      4 * t < k5PrimitivePowerGap 5 u v := by
  have hu1 : u ≤ 4 * v := by omega
  have hu3 : u ^ 3 ≤ 4 * v ^ 3 := by
    have hcub := Nat.pow_lt_pow_left hratio (by norm_num : 3 ≠ 0)
    have hcub' : 27 * u ^ 3 < 64 * v ^ 3 := by
      simpa [mul_pow] using hcub
    omega
  have hquad := k5_primitive_scale_quadratic_identity
    hg hu1 hu3 hu5.le hsol
  have hpin := k5_primitive_scale_floor_pin
    (pow_pos hg 2) hv hratio hu5 hquad
  have hA1 : k5PrimitivePowerGap 1 u v = g ^ 2 * t := by
    simp only [k5PrimitivePowerGap, pow_one]
    omega
  have hlinear :
      g ^ 2 * k5PrimitivePowerGap 5 u v + 4 * t =
        5 * k5PrimitivePowerGap 3 u v := by
    apply Nat.mul_left_cancel (pow_pos hg 2)
    calc
      g ^ 2 * (g ^ 2 * k5PrimitivePowerGap 5 u v + 4 * t) =
          (g ^ 2) ^ 2 * k5PrimitivePowerGap 5 u v +
            4 * k5PrimitivePowerGap 1 u v := by rw [hA1]; ring
      _ = 5 * g ^ 2 * k5PrimitivePowerGap 3 u v := hquad
      _ = g ^ 2 * (5 * k5PrimitivePowerGap 3 u v) := by ring
  have hrem : 4 * t < k5PrimitivePowerGap 5 u v := by
    have hscaled : g ^ 2 * (4 * t) <
        g ^ 2 * k5PrimitivePowerGap 5 u v := by
      simpa [hA1, mul_assoc, mul_left_comm, mul_comm] using hpin.2
    exact (Nat.mul_lt_mul_left (pow_pos hg 2)).mp hscaled
  refine ⟨hpin.1, ?_, hrem⟩
  rw [← hlinear]
  simp [Nat.add_mod, Nat.mod_eq_of_lt hrem]

/-- The analytic-looking hypotheses of the floor pin are automatic for a
centered solution in the established approximation range. -/
theorem k5_primitive_power_gap_window
    {g u v : ℕ} (hg : 0 < g) (hlarge : 1425 ≤ g * v)
    (hsol : K5CenteredEq (g * u) (g * v)) :
    3 * u < 4 * v ∧ u ^ 5 < 4 * v ^ 5 := by
  have hbr := k5_bracket_upper hsol (by omega : 665 ≤ g * v)
  have hbr' : g * (100 * u) < g * (132 * v) := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using hbr
  have huv : 100 * u < 132 * v := (Nat.mul_lt_mul_left hg).mp hbr'
  have hratio : 3 * u < 4 * v := by omega
  have hdef := k5_fifth_defect_bounds hlarge hsol
  have hpow : (g * u) ^ 5 < 4 * (g * v) ^ 5 := by
    have hz : ((g * u : ℕ) : ℤ) ^ 5 <
        4 * ((g * v : ℕ) : ℤ) ^ 5 := by
      linarith [hdef.1]
    exact_mod_cast hz
  have hpow' : g ^ 5 * u ^ 5 < g ^ 5 * (4 * v ^ 5) := by
    simpa [mul_pow, mul_assoc, mul_left_comm, mul_comm] using hpow
  exact ⟨hratio, (Nat.mul_lt_mul_left (pow_pos hg 5)).mp hpow'⟩

/-- All exact arithmetic constraints on an odd primitive convergent.  The
Euclidean quotient is the square scale, the remainder is four times the
scale quotient, and their gcd belongs to the six-value resultant list. -/
theorem k5_odd_primitive_convergent_euclidean_constraint
    {g u v t : ℕ} (hg : 2 ≤ g) (hv : 2 ≤ v)
    (hodd : Nat.Coprime g 2) (hcop : Nat.Coprime u v)
    (hscale : u + g ^ 2 * t = 4 * v)
    (hlarge : 1425 ≤ g * v)
    (hsol : K5CenteredEq (g * u) (g * v)) :
    (∃ n : ℕ, ((u : ℚ) / (v : ℚ)) = k5Alpha.convergent n) ∧
      5 * k5PrimitivePowerGap 3 u v / k5PrimitivePowerGap 5 u v = g ^ 2 ∧
      5 * k5PrimitivePowerGap 3 u v % k5PrimitivePowerGap 5 u v = 4 * t ∧
      0 < t ∧ 4 * t < k5PrimitivePowerGap 5 u v ∧
      (Nat.gcd (g ^ 2) t = 1 ∨ Nat.gcd (g ^ 2) t = 3 ∨
        Nat.gcd (g ^ 2) t = 5 ∨ Nat.gcd (g ^ 2) t = 15 ∨
        Nat.gcd (g ^ 2) t = 25 ∨ Nat.gcd (g ^ 2) t = 75) := by
  have hg0 : 0 < g := by omega
  have hv0 : 0 < v := by omega
  have hwindow := k5_primitive_power_gap_window hg0 hlarge hsol
  have heuc := k5_primitive_scale_euclidean_division
    hg0 hv hscale hwindow.1 hwindow.2 hsol
  have hA1 : k5PrimitivePowerGap 1 u v = g ^ 2 * t := by
    simp only [k5PrimitivePowerGap, pow_one]
    omega
  have hA1pos : 0 < k5PrimitivePowerGap 1 u v := by
    simp only [k5PrimitivePowerGap, pow_one]
    omega
  have ht : 0 < t := by
    rw [hA1] at hA1pos
    exact Nat.pos_of_mul_pos_left hA1pos
  exact ⟨k5_primitive_ratio_is_convergent hg hv0 hcop hlarge hsol,
    heuc.1, heuc.2.1, ht, heuc.2.2,
    k5_odd_primitive_scale_overlap_six_values hg0 hodd hcop hscale hsol⟩

/-- A scale-free, directly computable filter on the numerator and denominator
of the forced convergent.  It is the interface needed by an all-index
continued-fraction exclusion: calculate `Q` and `R` from `(u,v)` alone, then
reject unless `Q` is an odd square at least four and the normalized remainder
has one of the six fixed gcd values. -/
theorem k5_odd_primitive_convergent_computable_filter
    {g u v t : ℕ} (hg : 2 ≤ g) (hv : 2 ≤ v)
    (hodd : Nat.Coprime g 2) (hcop : Nat.Coprime u v)
    (hscale : u + g ^ 2 * t = 4 * v)
    (hlarge : 1425 ≤ g * v)
    (hsol : K5CenteredEq (g * u) (g * v)) :
    let Q :=
      5 * k5PrimitivePowerGap 3 u v / k5PrimitivePowerGap 5 u v
    let R :=
      5 * k5PrimitivePowerGap 3 u v % k5PrimitivePowerGap 5 u v
    (∃ n : ℕ, ((u : ℚ) / (v : ℚ)) = k5Alpha.convergent n) ∧
      (∃ s : ℕ, Q = s ^ 2) ∧
      4 ≤ Q ∧ Nat.Coprime Q 2 ∧ 4 ∣ R ∧ 0 < R ∧
      R < k5PrimitivePowerGap 5 u v ∧
      (Nat.gcd Q (R / 4) = 1 ∨ Nat.gcd Q (R / 4) = 3 ∨
        Nat.gcd Q (R / 4) = 5 ∨ Nat.gcd Q (R / 4) = 15 ∨
        Nat.gcd Q (R / 4) = 25 ∨ Nat.gcd Q (R / 4) = 75) := by
  dsimp only
  rcases k5_odd_primitive_convergent_euclidean_constraint
      hg hv hodd hcop hscale hlarge hsol with
    ⟨hconv, hQ, hR, ht, hRlt, hoverlap⟩
  have hQfour : 4 ≤
      5 * k5PrimitivePowerGap 3 u v / k5PrimitivePowerGap 5 u v := by
    rw [hQ]
    exact Nat.pow_le_pow_left hg 2
  have hQodd : Nat.Coprime
      (5 * k5PrimitivePowerGap 3 u v / k5PrimitivePowerGap 5 u v) 2 := by
    rw [hQ]
    exact hodd.pow_left 2
  have hRpos : 0 <
      5 * k5PrimitivePowerGap 3 u v % k5PrimitivePowerGap 5 u v := by
    rw [hR]
    positivity
  have hRnorm :
      (5 * k5PrimitivePowerGap 3 u v % k5PrimitivePowerGap 5 u v) / 4 = t := by
    rw [hR]
    simp
  refine ⟨hconv, ⟨g, hQ⟩, hQfour, hQodd, ?_, hRpos, ?_, ?_⟩
  · rw [hR]
    simp
  · rw [hR]
    exact hRlt
  · rw [hQ, hRnorm]
    exact hoverlap

#print axioms k5_primitive_scale_quadratic_identity
#print axioms k5_primitive_five_cubic_gap_gt_eight_linear_gap
#print axioms k5_primitive_scale_floor_pin
#print axioms k5_primitive_scale_euclidean_division
#print axioms k5_primitive_power_gap_window
#print axioms k5_odd_primitive_convergent_euclidean_constraint
#print axioms k5_odd_primitive_convergent_computable_filter

end Erdos686Variant
end Erdos686
