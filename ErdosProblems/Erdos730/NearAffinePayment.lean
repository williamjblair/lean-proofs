/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import Mathlib

/-!
# Erdős 730: exact near-affine valuation payment

This module is the kernel intake of the elementary arithmetic spine in
`compute730/campaign_uniform/repair/near_affine_payment_findings.md`.

The analytic block length is represented by a maximality inequality rather
than by logarithms.  In particular, the powered-threshold theorem below takes
the actual residue count `N`, the next-block weight, and its global upper
bound as separate, quantified inputs.  No digit-distribution or incomplete
quadratic-sum estimate is assumed.

The sharper infinite reciprocal-prime-power estimate

`sum_{p prime, a >= 2, p^a >= Y} p^(-a) <= 2 Y^(-1/2) + 3 Y^(-2/3)`

and the real dyadic monotonicity step that propagates the endpoint payment to
all `X >= 2^57` are not formalized here.  We instead prove a finite reciprocal
tail bound from an explicit pair-count envelope and certify the exact endpoint
rational arithmetic.  Thus the module does not claim the full uniform
near-affine payment, the far-range estimate, or Erdős 730.
-/

namespace Erdos730

/-! ## The algebraic `kappa_p <= 1/3` certificate -/

/-- The integer inequality obtained by cubing
`2p/(p+1) <= p^(1/3)`. -/
theorem eight_mul_sq_le_succ_cube {p : ℕ} (hp : 5 ≤ p) :
    8 * p ^ 2 ≤ (p + 1) ^ 3 := by
  have hdecomp :
      (p + 1) ^ 3 = 8 * p ^ 2 + (p - 5) * p ^ 2 + 3 * p + 1 := by
    have hp' : p = 5 + (p - 5) := by omega
    rw [hp']
    simp only [Nat.add_sub_cancel_left]
    ring
  rw [hdecomp]
  omega

/-! ## Rational near-envelope arithmetic -/

/-- The rational envelope implied by `kappa_p <= 1/3` and `eta = 1/12`.
The slack is `max (2r-a) 0`, represented by natural subtraction. -/
def NearEnvelope (a r : ℕ) : Prop :=
  12 * (2 * r - a) < 5 * r

/-- A tuple in the rational near envelope has exponent at least two and obeys
the strict valuation/block relation `19r < 12a`. -/
theorem nearEnvelope_forces_high_exponent
    {a r : ℕ} (hr : 1 ≤ r) (ha : 1 ≤ a)
    (hnear : NearEnvelope a r) :
    2 ≤ a ∧ 19 * r < 12 * a := by
  have _hr := hr
  unfold NearEnvelope at hnear
  by_cases h : a < 2 * r
  · have hsub : 2 * r - a + a = 2 * r := Nat.sub_add_cancel (by omega)
    omega
  · have har : 2 * r ≤ a := by omega
    omega

/-- The exponent inequality used to clear the fractional power
`p^(r+1) < (p^a)^(43/38)`. -/
theorem nearEnvelope_exponent_clearance
    {a r : ℕ} (hr : 1 ≤ r) (ha : 1 ≤ a)
    (hnear : NearEnvelope a r) :
    38 * (r + 1) < 43 * a := by
  obtain ⟨ha2, har⟩ := nearEnvelope_forces_high_exponent hr ha hnear
  omega

/-- Powered form of the fractional-exponent comparison. -/
theorem nearEnvelope_prime_power_clearance
    {p a r : ℕ} (hp : 2 ≤ p) (hr : 1 ≤ r) (ha : 1 ≤ a)
    (hnear : NearEnvelope a r) :
    (p ^ (r + 1)) ^ 38 < (p ^ a) ^ 43 := by
  rw [← Nat.pow_mul, ← Nat.pow_mul]
  exact Nat.pow_lt_pow_right hp (by
    simpa [mul_comm] using nearEnvelope_exponent_clearance hr ha hnear)

/-! ## Maximal-block threshold -/

/-- The residue-count inequality and maximality of `r` give an explicit
strict upper bound for `X`.  This is the exact abstract replacement for the
two appearances of `((r+1) log p)^2` in the paper proof. -/
lemma cutoff_lt_of_residue_count_and_maximality
    {X p a r N : ℕ} {nextWeight : ℚ}
    (hp : 2 ≤ p)
    (hcount : X ≤ p ^ a * (N + 1))
    (hmax : (N : ℚ) < (p ^ (r + 1) : ℕ) * nextWeight)
    (hweight : 1 ≤ nextWeight) :
    (X : ℚ) <
      (p ^ a : ℕ) * (2 * ((p ^ (r + 1) : ℕ) * nextWeight)) := by
  have hppos : (0 : ℚ) < (p ^ (r + 1) : ℕ) := by positivity
  have hone : (1 : ℚ) ≤ (p ^ (r + 1) : ℕ) * nextWeight := by
    have hpone : (1 : ℚ) ≤ (p ^ (r + 1) : ℕ) := by
      exact_mod_cast Nat.one_le_pow (r + 1) p (by omega : 0 < p)
    nlinarith
  have hNnext : (N + 1 : ℕ) <
      2 * ((p ^ (r + 1) : ℕ) * nextWeight) := by
    calc
      ((N + 1 : ℕ) : ℚ) = (N : ℚ) + 1 := by norm_num
      _ < (p ^ (r + 1) : ℕ) * nextWeight + 1 := by linarith
      _ ≤ (p ^ (r + 1) : ℕ) * nextWeight +
          (p ^ (r + 1) : ℕ) * nextWeight := by linarith
      _ = 2 * ((p ^ (r + 1) : ℕ) * nextWeight) := by ring
  have hcountQ : (X : ℚ) ≤ (p ^ a : ℕ) * (N + 1 : ℕ) := by
    exact_mod_cast hcount
  have hqpos : (0 : ℚ) < (p ^ a : ℕ) := by positivity
  nlinarith

/-- Exact powered threshold from the near envelope, an actual residue-count
bound, maximality at `r+1`, and a quantified upper bound for the next-block
weight.  This is equation (14) of the findings file with all non-algebraic
inputs exposed.

The conclusion is deliberately over `ℚ`; it avoids introducing a floor or a
choice of real roots. -/
theorem powered_threshold_of_near_maximal
    {X p a r N : ℕ} {nextWeight globalWeight : ℚ}
    (hp : 5 ≤ p) (hr : 1 ≤ r) (ha : 1 ≤ a)
    (hnear : NearEnvelope a r)
    (hcount : X ≤ p ^ a * (N + 1))
    (hmax : (N : ℚ) < (p ^ (r + 1) : ℕ) * nextWeight)
    (hweight : 1 ≤ nextWeight)
    (hglobal : nextWeight ≤ globalWeight) :
    (X : ℚ) ^ 38 <
      (2 * globalWeight) ^ 38 * ((p ^ a : ℕ) : ℚ) ^ 81 := by
  have hp2 : 2 ≤ p := by omega
  have hX := cutoff_lt_of_residue_count_and_maximality hp2 hcount hmax hweight
  have hglobal_pos : (0 : ℚ) < globalWeight := lt_of_lt_of_le (by norm_num) (hweight.trans hglobal)
  have hnext_nonneg : (0 : ℚ) ≤ nextWeight := by linarith
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
  have hraised := pow_lt_pow_left₀ hlinear hXnonneg (by norm_num : (38 : ℕ) ≠ 0)
  have hexp := nearEnvelope_prime_power_clearance hp2 hr ha hnear
  have hexpQ : (((p ^ (r + 1)) ^ 38 : ℕ) : ℚ) <
      (((p ^ a) ^ 43 : ℕ) : ℚ) := by exact_mod_cast hexp
  calc
    (X : ℚ) ^ 38 <
        ((p ^ a : ℕ) * (2 * globalWeight * (p ^ (r + 1) : ℕ))) ^ 38 := hraised
    _ = (2 * globalWeight) ^ 38 * ((p ^ a : ℕ) : ℚ) ^ 38 *
        (((p ^ (r + 1)) ^ 38 : ℕ) : ℚ) := by
      push_cast
      ring
    _ < (2 * globalWeight) ^ 38 * ((p ^ a : ℕ) : ℚ) ^ 38 *
        (((p ^ a) ^ 43 : ℕ) : ℚ) := by
      gcongr
    _ = (2 * globalWeight) ^ 38 * ((p ^ a : ℕ) : ℚ) ^ 81 := by
      push_cast
      ring

/-! ## Elementary finite pair and reciprocal-tail bounds -/

/-- A finite version of the prime-power pair-count bound.  Primality is not
needed: the statement dominates all integer bases.  `S` and `C` are any
certified square- and cube-root ceilings for `M`.

The exponent cap is explicit (`a < B`), so this theorem is not a substitute
for the missing infinite reciprocal-tail summation. -/
theorem finite_prime_power_pair_count
    (pairs : Finset (ℕ × ℕ)) {M B S C : ℕ}
    (hpairs : ∀ pa ∈ pairs,
      2 ≤ pa.1 ∧ 2 ≤ pa.2 ∧ pa.2 < B ∧ pa.1 ^ pa.2 ≤ M)
    (hsquare : M < (S + 1) ^ 2)
    (hcube : M < (C + 1) ^ 3) :
    pairs.card ≤ S + B * C := by
  classical
  let squares := pairs.filter (fun pa => pa.2 = 2)
  let higher := pairs.filter (fun pa => pa.2 ≠ 2)
  have hsquares : squares.card ≤ S := by
    have hmap : Set.MapsTo Prod.fst (↑squares : Set (ℕ × ℕ))
        (↑(Finset.Icc 1 S) : Set ℕ) := by
      intro pa hpa
      change pa ∈ squares at hpa
      simp only [squares, Finset.mem_filter] at hpa
      obtain ⟨hmem, haeq⟩ := hpa
      obtain ⟨hp, _ha, _hB, hpow⟩ := hpairs pa hmem
      have hpS : pa.1 ≤ S := by
        by_contra hnot
        have hSp : S + 1 ≤ pa.1 := by omega
        have := Nat.pow_le_pow_left hSp 2
        rw [haeq] at hpow
        omega
      exact Finset.mem_Icc.mpr ⟨by omega, hpS⟩
    have hinj : Set.InjOn Prod.fst (↑squares : Set (ℕ × ℕ)) := by
      intro x hx y hy hxy
      change x ∈ squares at hx
      change y ∈ squares at hy
      simp only [squares, Finset.mem_filter] at hx hy
      apply Prod.ext
      · exact hxy
      · omega
    have hcard := Finset.card_le_card_of_injOn Prod.fst hmap hinj
    simpa [Nat.card_Icc] using hcard
  have hhigher : higher.card ≤ B * C := by
    have hmap : Set.MapsTo id (↑higher : Set (ℕ × ℕ))
        (↑(Finset.Icc 1 C ×ˢ Finset.range B) : Set (ℕ × ℕ)) := by
      intro pa hpa
      change pa ∈ higher at hpa
      simp only [higher, Finset.mem_filter] at hpa
      obtain ⟨hmem, hane⟩ := hpa
      obtain ⟨hp, ha2, haB, hpow⟩ := hpairs pa hmem
      have ha3 : 3 ≤ pa.2 := by omega
      have hpC : pa.1 ≤ C := by
        by_contra hnot
        have hCp : C + 1 ≤ pa.1 := by omega
        have hp3a : pa.1 ^ 3 ≤ pa.1 ^ pa.2 :=
          Nat.pow_le_pow_right (by omega) ha3
        have hC3p3 := Nat.pow_le_pow_left hCp 3
        omega
      exact Finset.mem_product.mpr
        ⟨Finset.mem_Icc.mpr ⟨(by omega : 1 ≤ pa.1), hpC⟩,
          Finset.mem_range.mpr haB⟩
    have hinj : Set.InjOn id (↑higher : Set (ℕ × ℕ)) :=
      Set.injOn_id (↑higher : Set (ℕ × ℕ))
    have hcard := Finset.card_le_card_of_injOn id hmap hinj
    simpa [Finset.card_product, Nat.card_Icc, mul_comm] using hcard
  have hsplit := Finset.card_filter_add_card_filter_not
      (s := pairs) (fun pa : ℕ × ℕ => pa.2 = 2)
  change squares.card + higher.card = pairs.card at hsplit
  omega

/-- Crude but fully finite reciprocal tail: if every represented prime power
is at least `Y`, each reciprocal is at most `1/Y`. -/
theorem finite_reciprocal_prime_power_tail
    (pairs : Finset (ℕ × ℕ)) {Y : ℕ}
    (hY : 1 ≤ Y)
    (hthreshold : ∀ pa ∈ pairs, Y ≤ pa.1 ^ pa.2) :
    ∑ pa ∈ pairs, (1 : ℚ) / (pa.1 ^ pa.2 : ℕ) ≤
      (pairs.card : ℚ) / Y := by
  calc
    ∑ pa ∈ pairs, (1 : ℚ) / (pa.1 ^ pa.2 : ℕ) ≤
        ∑ _pa ∈ pairs, (1 : ℚ) / Y := by
      apply Finset.sum_le_sum
      intro pa hpa
      exact one_div_le_one_div_of_le (by exact_mod_cast hY)
        (by exact_mod_cast hthreshold pa hpa)
    _ = (pairs.card : ℚ) / Y := by simp [div_eq_mul_inv]

/-- Combination of the finite pair-count and pointwise reciprocal bounds. -/
theorem finite_reciprocal_tail_from_root_envelopes
    (pairs : Finset (ℕ × ℕ)) {M B S C Y : ℕ}
    (hpairs : ∀ pa ∈ pairs,
      2 ≤ pa.1 ∧ 2 ≤ pa.2 ∧ pa.2 < B ∧ pa.1 ^ pa.2 ≤ M)
    (hsquare : M < (S + 1) ^ 2)
    (hcube : M < (C + 1) ^ 3)
    (hY : 1 ≤ Y)
    (hthreshold : ∀ pa ∈ pairs, Y ≤ pa.1 ^ pa.2) :
    ∑ pa ∈ pairs, (1 : ℚ) / (pa.1 ^ pa.2 : ℕ) ≤
      ((S + B * C : ℕ) : ℚ) / Y := by
  calc
    ∑ pa ∈ pairs, (1 : ℚ) / (pa.1 ^ pa.2 : ℕ) ≤
        (pairs.card : ℚ) / Y :=
      finite_reciprocal_prime_power_tail pairs hY hthreshold
    _ ≤ ((S + B * C : ℕ) : ℚ) / Y := by
      gcongr
      exact_mod_cast finite_prime_power_pair_count pairs hpairs hsquare hcube

/-- A finite geometric-series bound for all exponents `a >= 3` at one base
`p >= 2`.  This is the kernel-checked local ingredient behind the factor `2`
in the paper's higher-exponent tail estimate. -/
theorem finite_geometric_prime_power_tail {p n : ℕ} (hp : 2 ≤ p) :
    ∑ j ∈ Finset.range n, (1 : ℚ) / (p ^ (j + 3) : ℕ) ≤
      2 / (p ^ 3 : ℕ) := by
  have hx0 : (0 : ℚ) ≤ 1 / p := by positivity
  have hxhalf : (1 : ℚ) / p ≤ 1 / 2 := by
    exact one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast hp)
  have hgeom : ∑ j ∈ Finset.range n, ((1 : ℚ) / p) ^ j ≤ 2 := by
    let T : ℚ := ∑ j ∈ Finset.range n, ((1 : ℚ) / p) ^ j
    have hT0 : 0 ≤ T := by
      dsimp [T]
      positivity
    have hxpow : 0 ≤ ((1 : ℚ) / p) ^ n := by positivity
    have hid := geom_sum_mul ((1 : ℚ) / p) n
    have hxT : T * ((1 : ℚ) / p) ≤ T * (1 / 2 : ℚ) :=
      mul_le_mul_of_nonneg_left hxhalf hT0
    change T * ((1 : ℚ) / p - 1) = ((1 : ℚ) / p) ^ n - 1 at hid
    nlinarith
  calc
    ∑ j ∈ Finset.range n, (1 : ℚ) / (p ^ (j + 3) : ℕ) =
        ((1 : ℚ) / (p ^ 3 : ℕ)) *
          ∑ j ∈ Finset.range n, ((1 : ℚ) / p) ^ j := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _hj
      push_cast
      rw [pow_add]
      field_simp
      rw [← mul_pow]
      field_simp
      simp
    _ ≤ ((1 : ℚ) / (p ^ 3 : ℕ)) * 2 := by
      gcongr
    _ = 2 / (p ^ 3 : ℕ) := by ring

private lemma reciprocal_sq_le_telescope {m : ℕ} (hm : 2 ≤ m) :
    (1 : ℚ) / (m ^ 2 : ℕ) ≤ 1 / (m - 1 : ℕ) - 1 / m := by
  have hmpos : (0 : ℚ) < m := by positivity
  have hmpred : (0 : ℚ) < (m - 1 : ℕ) := by
    exact_mod_cast (by omega : 0 < m - 1)
  have hmQ : (2 : ℚ) ≤ (m : ℚ) := by exact_mod_cast hm
  have hm1pos : (0 : ℚ) < (m : ℚ) - 1 := by linarith
  have heq : (1 : ℚ) / (m - 1 : ℕ) - 1 / m =
      1 / ((m : ℚ) * (m - 1 : ℕ)) := by
    norm_num only [Nat.cast_sub (by omega : 1 ≤ m), Nat.cast_one]
    field_simp [ne_of_gt hmpos, ne_of_gt hm1pos]
    ring
  rw [heq]
  apply one_div_le_one_div_of_le (mul_pos hmpos hmpred)
  norm_num only [Nat.cast_pow, Nat.cast_sub (by omega : 1 ≤ m), Nat.cast_one]
  nlinarith

/-- Finite telescoping form of the reciprocal-square tail. -/
theorem finite_reciprocal_square_tail_telescoping
    {K n : ℕ} (hK : 2 ≤ K) :
    ∑ j ∈ Finset.range n, (1 : ℚ) / ((K + j) ^ 2 : ℕ) ≤
      1 / (K - 1 : ℕ) - 1 / (K + n - 1 : ℕ) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ]
      have hterm := reciprocal_sq_le_telescope (m := K + n) (by omega)
      have hsub : K + (n + 1) - 1 = K + n := by omega
      rw [hsub]
      linarith

/-- A convenient non-telescoping corollary for finite square tails. -/
theorem finite_reciprocal_square_tail {K n : ℕ} (hK : 2 ≤ K) :
    ∑ j ∈ Finset.range n, (1 : ℚ) / ((K + j) ^ 2 : ℕ) ≤
      1 / (K - 1 : ℕ) := by
  have h := finite_reciprocal_square_tail_telescoping (K := K) (n := n) hK
  have hnonneg : (0 : ℚ) ≤ 1 / (K + n - 1 : ℕ) := by positivity
  linarith

/-! ## Exact dyadic endpoint certificates -/

/-!
The remaining summation statement needed to turn the finite lemmas above into
equation (17) is, with `Y >= 1`,

`sum_{p prime, a >= 2, p^a >= Y} p^(-a)
    <= 2*Y^(-1/2) + 3*Y^(-2/3)`.

The remaining monotonicity transfer needed after the exact endpoint below is
to combine `dyadicThresholdBase_strictMono_step` and
`dyadic_cuberoot_boundary_step` with monotonicity of the positive real powers
`t |-> t^(38/81)`, `t |-> t^(-1/2)`, and `t |-> t^(-2/3)`, while carrying the
integer floor/ceiling root relaxations.  Neither statement is introduced as a
hypothesis in this module.
-/

/-- The branch ceiling used at the dyadic cutoff. -/
theorem branch_ceiling_lt_two_pow_nineteen
    {X : ℕ} (hX : 1 ≤ X) :
    380808 * X + 19 < 2 ^ 19 * X := by
  norm_num [pow_succ]
  omega

/-- Algebraic monotonicity certificate for the lower-threshold base on
successive dyadic ranges. -/
theorem dyadic_threshold_base_step {m : ℕ} (hm : 57 ≤ m) :
    (m + 22) ^ 2 < 2 * (m + 21) ^ 2 := by
  nlinarith [sq_nonneg (m : ℤ)]

/-- The actual exact-rational threshold base on the `m`th dyadic range. -/
def dyadicThresholdBase (m : ℕ) : ℚ :=
  (2 : ℚ) ^ m / (2 * (((43 : ℚ) * (m + 21) / 38) ^ 2))

/-- Exact-rational monotonicity of the threshold base. -/
theorem dyadicThresholdBase_strictMono_step {m : ℕ} (hm : 57 ≤ m) :
    dyadicThresholdBase m < dyadicThresholdBase (m + 1) := by
  have hstep := dyadic_threshold_base_step hm
  have hstepQ : (((m + 22) ^ 2 : ℕ) : ℚ) <
      2 * (((m + 21) ^ 2 : ℕ) : ℚ) := by exact_mod_cast hstep
  have hden : 2 * (((43 : ℚ) * (m + 22) / 38) ^ 2) <
      2 * (2 * (((43 : ℚ) * (m + 21) / 38) ^ 2)) := by
    push_cast at hstepQ
    nlinarith
  have hpowsucc : (2 : ℚ) ^ (m + 1) = (2 : ℚ) ^ m * 2 := by
    rw [pow_succ]
  unfold dyadicThresholdBase
  rw [hpowsucc]
  norm_num only [Nat.cast_add, Nat.cast_one]
  have hd0 : (0 : ℚ) < 2 * (((43 : ℚ) * (m + 21) / 38) ^ 2) := by
    positivity
  have hd1 : (0 : ℚ) < 2 * (((43 : ℚ) * (m + 1 + 21) / 38) ^ 2) := by
    positivity
  rw [div_lt_div_iff₀ hd0 hd1]
  have hden' : 2 * (((43 : ℚ) * (m + 1 + 21) / 38) ^ 2) <
      2 * (2 * (((43 : ℚ) * (m + 21) / 38) ^ 2)) := by
    nlinarith [hden]
  have hpowpos : (0 : ℚ) < 2 ^ m := by positivity
  nlinarith

/-- Cubed algebraic certificate for the decreasing `B M^(1/3)/X` dyadic
envelope. -/
theorem dyadic_cuberoot_boundary_step {m : ℕ} (hm : 57 ≤ m) :
    (m + 22) ^ 3 < 4 * (m + 21) ^ 3 := by
  nlinarith [sq_nonneg (m : ℤ),
    mul_nonneg (show (0 : ℤ) ≤ (m : ℤ) by positivity) (sq_nonneg (m : ℤ))]

/-- Exact cleared threshold calculation at `m=57`, `B=78`. -/
theorem endpoint_powered_threshold_certificate :
    (1210239 : ℚ) ^ 81 *
        (2 * (((43 : ℚ) * 78 / 38) ^ 2)) ^ 38
      ≤ (((2 : ℚ) ^ 57) ^ 38) := by
  norm_num

/-- The exact floor-square-root certificate in equation (21). -/
theorem endpoint_sqrt_floor_certificate :
    1100 ^ 2 ≤ 1210239 ∧ 1210239 < 1101 ^ 2 := by
  norm_num

/-- The exact floor-cube-root certificate in equation (21). -/
theorem endpoint_cuberoot_floor_certificate :
    106 ^ 3 ≤ 1210239 ∧ 1210239 < 107 ^ 3 := by
  norm_num

/-- Ceiling roots of the deliberately enlarged branch envelope `2^77`. -/
theorem endpoint_boundary_root_certificates :
    388736063996 ^ 2 < 2 ^ 77 ∧ 2 ^ 77 ≤ 388736063997 ^ 2 ∧
    53264340 ^ 3 < 2 ^ 77 ∧ 2 ^ 77 ≤ 53264341 ^ 3 := by
  norm_num

/-- Exact assembly of the endpoint tail and boundary envelopes. -/
theorem endpoint_payment_identity :
    4 * ((2 : ℚ) / 1100 + 3 / 106 ^ 2) +
        4 * ((388736063997 : ℚ) + 78 * 53264341) / 2 ^ 57 =
      232437037423222418449 / 27831344977224191180800 := by
  norm_num

/-- The exact rational one-percent certificate, with no decimal arithmetic. -/
theorem endpoint_payment_lt_one_percent :
    (232437037423222418449 : ℚ) / 27831344977224191180800 < 1 / 100 := by
  norm_num

/-- Cleared positive margin behind the preceding rational comparison. -/
theorem endpoint_payment_margin :
    27831344977224191180800 - 100 * 232437037423222418449 =
      4587641234901949335900 := by
  norm_num

end Erdos730
