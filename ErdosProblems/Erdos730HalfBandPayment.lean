/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import ErdosProblems.Erdos730NearAffinePayment

/-!
# Erdős 730: enlarged half-band payment arithmetic

The stronger affine-progression obstruction reaches beyond the former
near-affine cut.  This module verifies the arithmetic spine for paying the
larger uniform band `2 * max (2*r-a) 0 < r`.

As in the imported module, the infinite reciprocal-prime-power summation and
the positive-real root/monotonicity transfer remain outside the kernel.  No
far-range estimate or Erdős 730 conclusion is claimed.
-/

namespace Erdos730

/-- Uniform enlarged band that contains the full currently known affine
progression obstruction. -/
def HalfBandEnvelope (a r : ℕ) : Prop :=
  2 * (2 * r - a) < r

/-- The half band forces a high valuation and `3r<2a`. -/
theorem halfBandEnvelope_forces_high_exponent
    {a r : ℕ} (hr : 1 ≤ r) (ha : 1 ≤ a)
    (hnear : HalfBandEnvelope a r) :
    2 ≤ a ∧ 3 * r < 2 * a := by
  have _hr := hr
  unfold HalfBandEnvelope at hnear
  by_cases h : a < 2 * r
  · have hsub : 2 * r - a + a = 2 * r := Nat.sub_add_cancel (by omega)
    omega
  · have har : 2 * r ≤ a := by omega
    omega

/-- Cleared form of `r+1 < 7a/6`. -/
theorem halfBandEnvelope_exponent_clearance
    {a r : ℕ} (hr : 1 ≤ r) (ha : 1 ≤ a)
    (hnear : HalfBandEnvelope a r) :
    6 * (r + 1) < 7 * a := by
  obtain ⟨ha2, har⟩ := halfBandEnvelope_forces_high_exponent hr ha hnear
  omega

/-- Powered prime-power comparison used by the enlarged payment. -/
theorem halfBandEnvelope_prime_power_clearance
    {p a r : ℕ} (hp : 2 ≤ p) (hr : 1 ≤ r) (ha : 1 ≤ a)
    (hnear : HalfBandEnvelope a r) :
    (p ^ (r + 1)) ^ 6 < (p ^ a) ^ 7 := by
  rw [← Nat.pow_mul, ← Nat.pow_mul]
  exact Nat.pow_lt_pow_right hp (by
    simpa [mul_comm] using halfBandEnvelope_exponent_clearance hr ha hnear)

/-- Exact threshold `X^6 < (2W)^6 q^13` from the enlarged half band and
maximality of the analytic block length. -/
theorem powered_threshold_of_halfBand_maximal
    {X p a r N : ℕ} {nextWeight globalWeight : ℚ}
    (hp : 5 ≤ p) (hr : 1 ≤ r) (ha : 1 ≤ a)
    (hnear : HalfBandEnvelope a r)
    (hcount : X ≤ p ^ a * (N + 1))
    (hmax : (N : ℚ) < (p ^ (r + 1) : ℕ) * nextWeight)
    (hweight : 1 ≤ nextWeight)
    (hglobal : nextWeight ≤ globalWeight) :
    (X : ℚ) ^ 6 <
      (2 * globalWeight) ^ 6 * ((p ^ a : ℕ) : ℚ) ^ 13 := by
  have hp2 : 2 ≤ p := by omega
  have hX := cutoff_lt_of_residue_count_and_maximality hp2 hcount hmax hweight
  have hglobal_pos : (0 : ℚ) < globalWeight :=
    lt_of_lt_of_le (by norm_num) (hweight.trans hglobal)
  have hpowpos : (0 : ℚ) < (p ^ (r + 1) : ℕ) := by positivity
  have hqpos : (0 : ℚ) < (p ^ a : ℕ) := by positivity
  have hlinear : (X : ℚ) <
      (p ^ a : ℕ) * (2 * globalWeight * (p ^ (r + 1) : ℕ)) := by
    calc
      (X : ℚ) <
          (p ^ a : ℕ) * (2 * ((p ^ (r + 1) : ℕ) * nextWeight)) := hX
      _ ≤ (p ^ a : ℕ) * (2 * ((p ^ (r + 1) : ℕ) * globalWeight)) := by
        gcongr
      _ = (p ^ a : ℕ) * (2 * globalWeight * (p ^ (r + 1) : ℕ)) := by ring
  have hXnonneg : (0 : ℚ) ≤ (X : ℚ) := by positivity
  have hraised := pow_lt_pow_left₀ hlinear hXnonneg (by norm_num : (6 : ℕ) ≠ 0)
  have hexp := halfBandEnvelope_prime_power_clearance hp2 hr ha hnear
  have hexpQ : (((p ^ (r + 1)) ^ 6 : ℕ) : ℚ) <
      (((p ^ a) ^ 7 : ℕ) : ℚ) := by exact_mod_cast hexp
  calc
    (X : ℚ) ^ 6 <
        ((p ^ a : ℕ) * (2 * globalWeight * (p ^ (r + 1) : ℕ))) ^ 6 := hraised
    _ = (2 * globalWeight) ^ 6 * ((p ^ a : ℕ) : ℚ) ^ 6 *
        (((p ^ (r + 1)) ^ 6 : ℕ) : ℚ) := by
      push_cast
      ring
    _ < (2 * globalWeight) ^ 6 * ((p ^ a : ℕ) : ℚ) ^ 6 *
        (((p ^ a) ^ 7 : ℕ) : ℚ) := by
      gcongr
    _ = (2 * globalWeight) ^ 6 * ((p ^ a : ℕ) : ℚ) ^ 13 := by
      push_cast
      ring

/-- Dyadic threshold base for the enlarged half band. -/
def halfBandDyadicThresholdBase (m : ℕ) : ℚ :=
  (2 : ℚ) ^ m / (2 * (((7 : ℚ) * (m + 21) / 6) ^ 2))

/-- The enlarged threshold base increases on successive dyadic ranges. -/
theorem halfBandDyadicThresholdBase_strictMono_step {m : ℕ} (hm : 57 ≤ m) :
    halfBandDyadicThresholdBase m < halfBandDyadicThresholdBase (m + 1) := by
  have hstep := dyadic_threshold_base_step hm
  have hstepQ : (((m + 22) ^ 2 : ℕ) : ℚ) <
      2 * (((m + 21) ^ 2 : ℕ) : ℚ) := by exact_mod_cast hstep
  have hden : 2 * (((7 : ℚ) * (m + 22) / 6) ^ 2) <
      2 * (2 * (((7 : ℚ) * (m + 21) / 6) ^ 2)) := by
    push_cast at hstepQ
    nlinarith
  have hpowsucc : (2 : ℚ) ^ (m + 1) = (2 : ℚ) ^ m * 2 := by
    rw [pow_succ]
  unfold halfBandDyadicThresholdBase
  rw [hpowsucc]
  norm_num only [Nat.cast_add, Nat.cast_one]
  have hd0 : (0 : ℚ) < 2 * (((7 : ℚ) * (m + 21) / 6) ^ 2) := by positivity
  have hd1 : (0 : ℚ) < 2 * (((7 : ℚ) * (m + 1 + 21) / 6) ^ 2) := by positivity
  rw [div_lt_div_iff₀ hd0 hd1]
  have hden' : 2 * (((7 : ℚ) * (m + 1 + 21) / 6) ^ 2) <
      2 * (2 * (((7 : ℚ) * (m + 21) / 6) ^ 2)) := by
    nlinarith [hden]
  have hpowpos : (0 : ℚ) < 2 ^ m := by positivity
  nlinarith

/-- Exact floor certificate for the enlarged threshold at `m=57`. -/
theorem halfBand_endpoint_powered_threshold_certificate :
    (937824 : ℚ) ^ 13 *
        (2 * (((7 : ℚ) * 78 / 6) ^ 2)) ^ 6
      ≤ (((2 : ℚ) ^ 57) ^ 6) ∧
    (((2 : ℚ) ^ 57) ^ 6) <
      (937825 : ℚ) ^ 13 *
        (2 * (((7 : ℚ) * 78 / 6) ^ 2)) ^ 6 := by
  norm_num

theorem halfBand_endpoint_sqrt_floor_certificate :
    968 ^ 2 ≤ 937824 ∧ 937824 < 969 ^ 2 := by
  norm_num

theorem halfBand_endpoint_cuberoot_floor_certificate :
    97 ^ 3 ≤ 937824 ∧ 937824 < 98 ^ 3 := by
  norm_num

/-- Exact assembly of the enlarged endpoint payment. -/
theorem halfBand_endpoint_payment_identity :
    4 * ((2 : ℚ) / 968 + 3 / 97 ^ 2) +
        4 * ((388736063997 : ℚ) + 78 * 53264341) / 2 ^ 57 =
      391756066143304555403 / 41018389089323268964352 := by
  norm_num

theorem halfBand_endpoint_payment_lt_one_percent :
    (391756066143304555403 : ℚ) / 41018389089323268964352 < 1 / 100 := by
  norm_num

theorem halfBand_endpoint_payment_margin :
    41018389089323268964352 - 100 * 391756066143304555403 =
      1842782474992813424052 := by
  norm_num

end Erdos730
