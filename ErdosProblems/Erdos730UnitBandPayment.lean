/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import ErdosProblems.Erdos730NearAffinePayment

/-!
# Erdős 730: full high-valuation-band payment arithmetic

This module verifies the arithmetic spine for paying the whole strict band

`max (2*r-a) 0 < r`.

The band forces `r+1<=a`, so maximality gives the clean threshold
`X < 2 W (p^a)^2`.  As in the imported module, the infinite reciprocal
prime-power sum and the positive-real root/monotonicity transfer remain
outside the kernel.  No incomplete-block estimate or Erdős 730 conclusion
is claimed.
-/

namespace Erdos730

/-- The maximal strict band that uniformly excludes first-power valuations. -/
def UnitBandEnvelope (a r : ℕ) : Prop :=
  2 * r - a < r

/-- The full strict band forces `a>=2` and `r+1<=a`. -/
theorem unitBandEnvelope_forces_high_exponent
    {a r : ℕ} (hr : 1 ≤ r) (ha : 1 ≤ a)
    (hnear : UnitBandEnvelope a r) :
    2 ≤ a ∧ r + 1 ≤ a := by
  have _hr := hr
  unfold UnitBandEnvelope at hnear
  by_cases h : a < 2 * r
  · have hsub : 2 * r - a + a = 2 * r := Nat.sub_add_cancel (by omega)
    omega
  · have har : 2 * r ≤ a := by omega
    omega

/-- Prime-power comparison supplied by the full strict band. -/
theorem unitBandEnvelope_prime_power_clearance
    {p a r : ℕ} (hp : 1 ≤ p) (hr : 1 ≤ r) (ha : 1 ≤ a)
    (hnear : UnitBandEnvelope a r) :
    p ^ (r + 1) ≤ p ^ a := by
  exact Nat.pow_le_pow_right hp
    (unitBandEnvelope_forces_high_exponent hr ha hnear).2

/-- Exact threshold `X < 2Wq^2` from the full strict band and maximality. -/
theorem cutoff_lt_of_unitBand_maximal
    {X p a r N : ℕ} {nextWeight globalWeight : ℚ}
    (hp : 5 ≤ p) (hr : 1 ≤ r) (ha : 1 ≤ a)
    (hnear : UnitBandEnvelope a r)
    (hcount : X ≤ p ^ a * (N + 1))
    (hmax : (N : ℚ) < (p ^ (r + 1) : ℕ) * nextWeight)
    (hweight : 1 ≤ nextWeight)
    (hglobal : nextWeight ≤ globalWeight) :
    (X : ℚ) < 2 * globalWeight * ((p ^ a : ℕ) : ℚ) ^ 2 := by
  have hp2 : 2 ≤ p := by omega
  have hX := cutoff_lt_of_residue_count_and_maximality hp2 hcount hmax hweight
  have hqpos : (0 : ℚ) < (p ^ a : ℕ) := by positivity
  have hglobal_nonneg : (0 : ℚ) ≤ globalWeight :=
    (show (0 : ℚ) ≤ nextWeight by linarith).trans hglobal
  have hpow := unitBandEnvelope_prime_power_clearance
    (p := p) (a := a) (r := r) (by omega) hr ha hnear
  have hpowQ : (((p ^ (r + 1) : ℕ) : ℚ)) ≤ (p ^ a : ℕ) := by
    exact_mod_cast hpow
  calc
    (X : ℚ) <
        (p ^ a : ℕ) * (2 * ((p ^ (r + 1) : ℕ) * nextWeight)) := hX
    _ ≤ (p ^ a : ℕ) * (2 * ((p ^ (r + 1) : ℕ) * globalWeight)) := by
      gcongr
    _ ≤ (p ^ a : ℕ) * (2 * ((p ^ a : ℕ) * globalWeight)) := by
      gcongr
    _ = 2 * globalWeight * ((p ^ a : ℕ) : ℚ) ^ 2 := by ring

/-- Dyadic threshold base `X/(2B^2)` for the full strict band. -/
def unitBandDyadicThresholdBase (m : ℕ) : ℚ :=
  (2 : ℚ) ^ m / (2 * (m + 21) ^ 2)

/-- The full-band threshold base increases on successive dyadic ranges. -/
theorem unitBandDyadicThresholdBase_strictMono_step
    {m : ℕ} (hm : 57 ≤ m) :
    unitBandDyadicThresholdBase m < unitBandDyadicThresholdBase (m + 1) := by
  have hstep := dyadic_threshold_base_step hm
  have hstepQ : (((m + 22) ^ 2 : ℕ) : ℚ) <
      2 * (((m + 21) ^ 2 : ℕ) : ℚ) := by exact_mod_cast hstep
  have hpowsucc : (2 : ℚ) ^ (m + 1) = (2 : ℚ) ^ m * 2 := by
    rw [pow_succ]
  unfold unitBandDyadicThresholdBase
  rw [hpowsucc]
  norm_num only [Nat.cast_add, Nat.cast_one]
  have hd0 : (0 : ℚ) < 2 * (m + 21 : ℚ) ^ 2 := by positivity
  have hd1 : (0 : ℚ) < 2 * (m + 1 + 21 : ℚ) ^ 2 := by positivity
  rw [div_lt_div_iff₀ hd0 hd1]
  push_cast at hstepQ
  have hpowpos : (0 : ℚ) < 2 ^ m := by positivity
  nlinarith

/-- Exact floor certificate at `X=2^57`, `B=78`. -/
theorem unitBand_endpoint_threshold_certificate :
    2 * (78 : ℕ) ^ 2 * 3441480 ^ 2 ≤ 2 ^ 57 ∧
      2 ^ 57 < 2 * (78 : ℕ) ^ 2 * 3441481 ^ 2 := by
  norm_num

theorem unitBand_endpoint_sqrt_floor_certificate :
    1855 ^ 2 ≤ 3441480 ∧ 3441480 < 1856 ^ 2 := by
  norm_num

theorem unitBand_endpoint_cuberoot_floor_certificate :
    150 ^ 3 ≤ 3441480 ∧ 3441480 < 151 ^ 3 := by
  norm_num

/-- Exact assembly of the full-band endpoint payment. -/
theorem unitBand_endpoint_payment_identity :
    4 * ((2 : ℚ) / 1855 + 3 / 150 ^ 2) +
        4 * ((388736063997 : ℚ) + 78 * 53264341) / 2 ^ 57 =
      121726379332007683003 / 25062531926316810240000 := by
  norm_num

theorem unitBand_endpoint_payment_lt_one_percent :
    (121726379332007683003 : ℚ) /
        25062531926316810240000 < 1 / 100 := by
  norm_num

theorem unitBand_endpoint_payment_margin :
    25062531926316810240000 - 100 * 121726379332007683003 =
      12889893993116041939700 := by
  norm_num

end Erdos730
