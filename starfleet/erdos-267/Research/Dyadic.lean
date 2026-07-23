import Mathlib

/-!
# Dyadic telescoping series

The analytic core of Millin's reciprocal-Fibonacci identity.  Kept independent
of the open target in `Research.Basic`, so this file can be checked with
`lake --wfail build +Research.Dyadic`.
-/

namespace Research

open Filter Topology
open scoped BigOperators

/-- The elementary dyadic telescoping identity. -/
theorem hasSum_dyadic_telescoping (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x < 1) :
    HasSum (fun j : ℕ => x ^ (2 ^ j) / (1 - x ^ (2 ^ (j + 1)))) (x / (1 - x)) := by
  let u : ℕ → ℝ := fun j => x ^ (2 ^ j) / (1 - x ^ (2 ^ j))
  have hpow : Tendsto (fun j : ℕ => x ^ (2 ^ j)) atTop (𝓝 0) := by
    exact (tendsto_pow_atTop_nhds_zero_of_lt_one hx0 hx1).comp
      (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℕ) < 2))
  have hu : Tendsto u atTop (𝓝 0) := by
    have hden : Tendsto (fun j : ℕ => 1 - x ^ (2 ^ j)) atTop (𝓝 (1 - 0)) :=
      tendsto_const_nhds.sub hpow
    change Tendsto
      ((fun j : ℕ => x ^ (2 ^ j)) / (fun j : ℕ => 1 - x ^ (2 ^ j)))
      atTop (𝓝 0)
    convert hpow.div hden (by norm_num : (1 - 0 : ℝ) ≠ 0) using 1
    norm_num
  have hden_pos (j : ℕ) : 0 < 1 - x ^ (2 ^ j) := by
    have hp : x ^ (2 ^ j) < 1 := pow_lt_one₀ hx0 hx1 (by positivity)
    linarith
  have hterm (j : ℕ) :
      x ^ (2 ^ j) / (1 - x ^ (2 ^ (j + 1))) = u j - u (j + 1) := by
    have hpow2 : x ^ (2 ^ (j + 1)) = (x ^ (2 ^ j)) ^ 2 := by
      rw [pow_succ, pow_mul]
    dsimp [u]
    rw [hpow2]
    have h₁ : 1 - x ^ (2 ^ j) ≠ 0 := ne_of_gt (hden_pos j)
    have h₂ : 1 - (x ^ (2 ^ j)) ^ 2 ≠ 0 := by
      rw [← hpow2]
      exact ne_of_gt (hden_pos (j + 1))
    field_simp
    ring
  have hnonneg (j : ℕ) : 0 ≤ x ^ (2 ^ j) / (1 - x ^ (2 ^ (j + 1))) := by
    exact div_nonneg (pow_nonneg hx0 _) (le_of_lt (hden_pos (j + 1)))
  rw [hasSum_iff_tendsto_nat_of_nonneg hnonneg]
  have htel (N : ℕ) :
      (∑ j ∈ Finset.range N, x ^ (2 ^ j) / (1 - x ^ (2 ^ (j + 1)))) = u 0 - u N := by
    calc
      _ = ∑ j ∈ Finset.range N, (u j - u (j + 1)) := by
        apply Finset.sum_congr rfl
        intro j hj
        exact hterm j
      _ = u 0 - u N := Finset.sum_range_sub' u N
  have hlim : Tendsto (fun N : ℕ => u 0 - u N) atTop (𝓝 (u 0 - 0)) :=
    tendsto_const_nhds.sub hu
  simpa [htel, u] using hlim

open Real goldenRatio

/-- Binet's formula rewritten as a positive geometric fraction at an even
Fibonacci index. -/
theorem inv_fib_two_mul (r : ℕ) (hr : 0 < r) :
    (Nat.fib (2 * r) : ℝ)⁻¹ =
      √5 * (φ⁻¹) ^ (2 * r) / (1 - ((φ⁻¹) ^ (2 * r)) ^ 2) := by
  have hpsi : ψ = -φ⁻¹ := by
    linarith [Real.inv_goldenRatio]
  have hpsi_pow : ψ ^ (2 * r) = (φ⁻¹) ^ (2 * r) := by
    rw [hpsi, pow_mul, pow_mul]
    congr 1
    ring
  have hphi_ne : φ ≠ 0 := Real.goldenRatio_ne_zero
  have hunit : φ ^ (2 * r) * (φ⁻¹) ^ (2 * r) = 1 := by
    rw [inv_pow, mul_inv_cancel₀ (pow_ne_zero _ hphi_ne)]
  have hinv0 : 0 ≤ φ⁻¹ := le_of_lt (inv_pos.mpr Real.goldenRatio_pos)
  have hinv1 : φ⁻¹ < 1 := inv_lt_one_of_one_lt₀ Real.one_lt_goldenRatio
  have hy1 : (φ⁻¹) ^ (2 * r) < 1 :=
    pow_lt_one₀ hinv0 hinv1
      (Nat.ne_of_gt (Nat.mul_pos (by norm_num : 0 < (2 : ℕ)) hr))
  have hy0 : 0 ≤ (φ⁻¹) ^ (2 * r) := pow_nonneg hinv0 _
  have hden : 1 - ((φ⁻¹) ^ (2 * r)) ^ 2 ≠ 0 := by
    have hsquare : ((φ⁻¹) ^ (2 * r)) ^ 2 < 1 :=
      pow_lt_one₀ hy0 hy1 (by norm_num : (2 : ℕ) ≠ 0)
    linarith
  apply inv_eq_of_mul_eq_one_right
  rw [Real.coe_fib_eq, hpsi_pow]
  have hsqrt : √5 ≠ 0 := by positivity
  calc
    ((φ ^ (2 * r) - (φ⁻¹) ^ (2 * r)) / √5) *
        (√5 * (φ⁻¹) ^ (2 * r) / (1 - ((φ⁻¹) ^ (2 * r)) ^ 2)) =
        (φ ^ (2 * r) * (φ⁻¹) ^ (2 * r) - ((φ⁻¹) ^ (2 * r)) ^ 2) /
          (1 - ((φ⁻¹) ^ (2 * r)) ^ 2) := by
            field_simp [hsqrt, hden]
    _ = 1 := by rw [hunit]; exact div_self hden

/-- The reciprocal Fibonacci numbers on every dyadic orbit beginning at a
positive even index have the explicit quadratic sum given below. -/
theorem hasSum_reciprocal_fib_dyadic_even (r : ℕ) (hr : 0 < r) :
    HasSum (fun j : ℕ => (Nat.fib (2 * (r * 2 ^ j)) : ℝ)⁻¹)
      (√5 * ((φ⁻¹) ^ (2 * r) / (1 - (φ⁻¹) ^ (2 * r)))) := by
  let x : ℝ := (φ⁻¹) ^ (2 * r)
  have hinv0 : 0 ≤ φ⁻¹ := le_of_lt (inv_pos.mpr Real.goldenRatio_pos)
  have hinv1 : φ⁻¹ < 1 := inv_lt_one_of_one_lt₀ Real.one_lt_goldenRatio
  have hx0 : 0 ≤ x := pow_nonneg hinv0 _
  have hx1 : x < 1 := by
    exact pow_lt_one₀ hinv0 hinv1
      (Nat.ne_of_gt (Nat.mul_pos (by norm_num : 0 < (2 : ℕ)) hr))
  have hscaled := (hasSum_dyadic_telescoping x hx0 hx1).const_smul √5
  have hscaled' :
      HasSum (fun j : ℕ => √5 * (x ^ (2 ^ j) / (1 - x ^ (2 ^ (j + 1)))))
        (√5 * (x / (1 - x))) := by
    simpa only [smul_eq_mul] using hscaled
  apply hscaled'.congr_fun
  intro j
  rw [inv_fib_two_mul (r * 2 ^ j) (Nat.mul_pos hr (by positivity))]
  have hexp : 2 * (r * 2 ^ j) = (2 * r) * 2 ^ j := by ring
  have hnext : x ^ (2 ^ (j + 1)) = (x ^ (2 ^ j)) ^ 2 := by
    rw [pow_succ, pow_mul]
  rw [hexp, pow_mul, ← hnext]
  dsimp [x]
  ring

/-- The even powers of the golden ratio in the rational basis `1, √5`. -/
theorem goldenRatio_pow_two_mul_fib (r : ℕ) (hr : 0 < r) :
    φ ^ (2 * r) =
      ((Nat.fib (2 * r) : ℝ) / 2 + Nat.fib (2 * r - 1)) +
        ((Nat.fib (2 * r) : ℝ) / 2) * √5 := by
  have hn : (2 * r - 1) + 1 = 2 * r := by omega
  calc
    φ ^ (2 * r) = φ ^ ((2 * r - 1) + 1) := by rw [hn]
    _ = φ * Nat.fib ((2 * r - 1) + 1) + Nat.fib (2 * r - 1) :=
      (Real.goldenRatio_mul_fib_succ_add_fib (2 * r - 1)).symm
    _ = _ := by rw [hn]; change ((1 + √5) / 2) * _ + _ = _; ring

/-- The matching even powers of the conjugate golden ratio. -/
theorem goldenConj_pow_two_mul_fib (r : ℕ) (hr : 0 < r) :
    ψ ^ (2 * r) =
      ((Nat.fib (2 * r) : ℝ) / 2 + Nat.fib (2 * r - 1)) -
        ((Nat.fib (2 * r) : ℝ) / 2) * √5 := by
  have hn : (2 * r - 1) + 1 = 2 * r := by omega
  calc
    ψ ^ (2 * r) = ψ ^ ((2 * r - 1) + 1) := by rw [hn]
    _ = ψ * Nat.fib ((2 * r - 1) + 1) + Nat.fib (2 * r - 1) :=
      (Real.goldenConj_mul_fib_succ_add_fib (2 * r - 1)).symm
    _ = _ := by rw [hn]; change ((1 - √5) / 2) * _ + _ = _; ring

/-- Every complete positive even dyadic orbit has the same irrational component
`-√5/2`; the other displayed component is rational. -/
theorem dyadic_even_value_decomposition (r : ℕ) (hr : 0 < r) :
    √5 / (φ ^ (2 * r) - 1) =
      5 * ((Nat.fib (2 * r) : ℝ) / 2) /
          (2 * ((Nat.fib (2 * r) : ℝ) / 2 + Nat.fib (2 * r - 1) - 1)) - √5 / 2 := by
  let F : ℝ := Nat.fib (2 * r)
  let G : ℝ := Nat.fib (2 * r - 1)
  let A : ℝ := F / 2 + G - 1
  let B : ℝ := F / 2
  have hp : φ ^ (2 * r) = A + 1 + B * √5 := by
    rw [goldenRatio_pow_two_mul_fib r hr]
    dsimp [A, B, F, G]
    ring
  have hc : ψ ^ (2 * r) = A + 1 - B * √5 := by
    rw [goldenConj_pow_two_mul_fib r hr]
    dsimp [A, B, F, G]
    ring
  have hprod : φ ^ (2 * r) * ψ ^ (2 * r) = 1 := by
    rw [← mul_pow, Real.goldenRatio_mul_goldenConj, pow_mul]
    norm_num
  rw [hp, hc] at hprod
  have hsqrt_sq : (√5) ^ 2 = (5 : ℝ) := by norm_num
  have hnorm : A ^ 2 - 5 * B ^ 2 = -2 * A := by
    nlinarith
  have hn : 0 < 2 * r := Nat.mul_pos (by norm_num) hr
  have hnprev : 0 < 2 * r - 1 := by omega
  have hFpos : 0 < F := by
    dsimp [F]
    exact_mod_cast (Nat.fib_pos.mpr hn)
  have hGone : 1 ≤ G := by
    dsimp [G]
    exact_mod_cast (show 1 ≤ Nat.fib (2 * r - 1) by
      have := Nat.fib_pos.mpr hnprev
      omega)
  have hA : 0 < A := by dsimp [A]; linarith
  have heq : φ ^ (2 * r) - 1 = A + B * √5 := by rw [hp]; ring
  have hpgt : 1 < φ ^ (2 * r) :=
    one_lt_pow₀ Real.one_lt_goldenRatio (Nat.ne_of_gt hn)
  have hden : A + B * √5 ≠ 0 := by rw [← heq]; linarith
  have hden' : A + √5 * B ≠ 0 := by
    have he : A + √5 * B = A + B * √5 := by ring
    rwa [he]
  have habstract :
      √5 / (φ ^ (2 * r) - 1) = 5 * B / (2 * A) - √5 / 2 := by
    rw [heq]
    field_simp [hden, hden', ne_of_gt hA]
    linear_combination √5 * hnorm + A * B * hsqrt_sq
  simpa [A, B, F, G] using habstract

/-- The geometric form of the dyadic-orbit limit equals its simpler closed
form. -/
theorem dyadic_even_geometric_eq (r : ℕ) (hr : 0 < r) :
    √5 * ((φ⁻¹) ^ (2 * r) / (1 - (φ⁻¹) ^ (2 * r))) =
      √5 / (φ ^ (2 * r) - 1) := by
  let a : ℝ := φ ^ (2 * r)
  let y : ℝ := (φ⁻¹) ^ (2 * r)
  have hphi_ne : φ ≠ 0 := Real.goldenRatio_ne_zero
  have hunit : a * y = 1 := by
    dsimp [a, y]
    rw [inv_pow, mul_inv_cancel₀ (pow_ne_zero _ hphi_ne)]
  have hn : 0 < 2 * r := Nat.mul_pos (by norm_num) hr
  have ha1 : 1 < a := by
    dsimp [a]
    exact one_lt_pow₀ Real.one_lt_goldenRatio (Nat.ne_of_gt hn)
  have hinv0 : 0 ≤ φ⁻¹ := le_of_lt (inv_pos.mpr Real.goldenRatio_pos)
  have hinv1 : φ⁻¹ < 1 := inv_lt_one_of_one_lt₀ Real.one_lt_goldenRatio
  have hy1 : y < 1 := by
    dsimp [y]
    exact pow_lt_one₀ hinv0 hinv1 (Nat.ne_of_gt hn)
  have hya : 1 - y ≠ 0 := by linarith
  have hay : a - 1 ≠ 0 := by linarith
  have hfrac : y / (1 - y) = 1 / (a - 1) := by
    field_simp [hya, hay]
    nlinarith
  rw [hfrac]
  dsimp [a, y]
  ring

/-- Closed form for the reciprocal-Fibonacci series on a positive even dyadic
orbit. -/
theorem hasSum_reciprocal_fib_dyadic_even_closed (r : ℕ) (hr : 0 < r) :
    HasSum (fun j : ℕ => (Nat.fib (2 * (r * 2 ^ j)) : ℝ)⁻¹)
      (√5 / (φ ^ (2 * r) - 1)) := by
  rw [← dyadic_even_geometric_eq r hr]
  exact hasSum_reciprocal_fib_dyadic_even r hr

/-- The closed value of every complete positive even dyadic orbit is
irrational. -/
theorem irrational_dyadic_even_value (r : ℕ) (hr : 0 < r) :
    Irrational (√5 / (φ ^ (2 * r) - 1)) := by
  let q : ℚ :=
    5 * ((Nat.fib (2 * r) : ℚ) / 2) /
      (2 * ((Nat.fib (2 * r) : ℚ) / 2 + Nat.fib (2 * r - 1) - 1))
  have hsqrt : Irrational (√5) :=
    Nat.Prime.irrational_sqrt (show Nat.Prime 5 by norm_num)
  have hhalf : Irrational (√5 / (2 : ℚ)) :=
    hsqrt.div_ratCast (by norm_num)
  have hqsub : Irrational ((q : ℝ) - √5 / 2) := by
    simpa using hhalf.ratCast_sub q
  have hqcast :
      (q : ℝ) =
        5 * ((Nat.fib (2 * r) : ℝ) / 2) /
          (2 * ((Nat.fib (2 * r) : ℝ) / 2 + Nat.fib (2 * r - 1) - 1)) := by
    simp [q]
  rw [hqcast] at hqsub
  rw [dyadic_even_value_decomposition r hr]
  exact hqsub

/-- Every complete dyadic orbit, with an arbitrary positive starting index,
has a closed form obtained by separating its first term. -/
theorem hasSum_reciprocal_fib_complete_dyadic (m : ℕ) (hm : 0 < m) :
    HasSum (fun j : ℕ => (Nat.fib (m * 2 ^ j) : ℝ)⁻¹)
      ((Nat.fib m : ℝ)⁻¹ + √5 / (φ ^ (2 * m) - 1)) := by
  let f : ℕ → ℝ := fun j => (Nat.fib (m * 2 ^ j) : ℝ)⁻¹
  have htail := hasSum_reciprocal_fib_dyadic_even_closed m hm
  have htail' : HasSum (fun j : ℕ => f (j + 1)) (√5 / (φ ^ (2 * m) - 1)) := by
    apply htail.congr_fun
    intro j
    dsimp [f]
    congr 3
    rw [pow_succ]
    ring
  simpa [f] using htail'.zero_add

/-- The closed value of every complete dyadic orbit is irrational, irrespective
of the parity of its starting index. -/
theorem irrational_complete_dyadic_value (m : ℕ) (hm : 0 < m) :
    Irrational ((Nat.fib m : ℝ)⁻¹ + √5 / (φ ^ (2 * m) - 1)) := by
  let q : ℚ := (Nat.fib m : ℚ)⁻¹
  have htail := irrational_dyadic_even_value m hm
  have h := htail.ratCast_add q
  simpa [q] using h

/-- The `tsum` over any complete positive dyadic Fibonacci orbit is
irrational. -/
theorem irrational_tsum_reciprocal_fib_complete_dyadic (m : ℕ) (hm : 0 < m) :
    Irrational (∑' j : ℕ, (Nat.fib (m * 2 ^ j) : ℝ)⁻¹) := by
  rw [(hasSum_reciprocal_fib_complete_dyadic m hm).tsum_eq]
  exact irrational_complete_dyadic_value m hm

/-- The arbitrary-start complete dyadic orbit again has irrational component
exactly `-√5/2`. -/
theorem complete_dyadic_value_decomposition (m : ℕ) (hm : 0 < m) :
    (Nat.fib m : ℝ)⁻¹ + √5 / (φ ^ (2 * m) - 1) =
      (Nat.fib m : ℝ)⁻¹ +
        5 * ((Nat.fib (2 * m) : ℝ) / 2) /
          (2 * ((Nat.fib (2 * m) : ℝ) / 2 + Nat.fib (2 * m - 1) - 1)) - √5 / 2 := by
  rw [dyadic_even_value_decomposition m hm]
  ring

/-- No nonempty finite sum of complete positive dyadic-orbit values can be
rational.  This is the algebraic obstruction behind the failure of finite
unions of such orbits as counterexamples. -/
theorem irrational_finset_sum_complete_dyadic_values
    (s : Finset ℕ) (hs : s.Nonempty) (hpos : ∀ m ∈ s, 0 < m) :
    Irrational
      (∑ m ∈ s, ((Nat.fib m : ℝ)⁻¹ + √5 / (φ ^ (2 * m) - 1))) := by
  let p : ℕ → ℚ := fun m =>
    (Nat.fib m : ℚ)⁻¹ +
      5 * ((Nat.fib (2 * m) : ℚ) / 2) /
        (2 * ((Nat.fib (2 * m) : ℚ) / 2 + Nat.fib (2 * m - 1) - 1))
  let Q : ℚ := ∑ m ∈ s, p m
  let C : ℚ := (s.card : ℚ) / 2
  have hterm (m : ℕ) (hm : m ∈ s) :
      (Nat.fib m : ℝ)⁻¹ + √5 / (φ ^ (2 * m) - 1) = (p m : ℝ) - √5 / 2 := by
    simpa [p] using complete_dyadic_value_decomposition m (hpos m hm)
  have hsum :
      (∑ m ∈ s, ((Nat.fib m : ℝ)⁻¹ + √5 / (φ ^ (2 * m) - 1))) =
        (Q : ℝ) - (C : ℝ) * √5 := by
    calc
      _ = ∑ m ∈ s, ((p m : ℝ) - √5 / 2) := by
        apply Finset.sum_congr rfl
        intro m hm
        exact hterm m hm
      _ = (Q : ℝ) - (C : ℝ) * √5 := by
        simp [Q, C]
        ring
  have hcard : s.card ≠ 0 := Finset.card_ne_zero.mpr hs
  have hC : C ≠ 0 := by
    dsimp [C]
    exact div_ne_zero (by exact_mod_cast hcard) (by norm_num)
  have hsqrt : Irrational (√5) :=
    Nat.Prime.irrational_sqrt (show Nat.Prime 5 by norm_num)
  have hscaled : Irrational ((C : ℝ) * √5) := hsqrt.ratCast_mul hC
  have hirr : Irrational ((Q : ℝ) - (C : ℝ) * √5) := hscaled.ratCast_sub Q
  rw [hsum]
  exact hirr

end Research
