import Research.MaximalCover

/-!
# Exact integer tail states forced by a rational reciprocal sum
-/

namespace Research

open Filter Topology
open scoped BigOperators

/-- If a positive unit-fraction sum is represented as `a/b`, this is the
integer obtained by clearing the first `N` denominators from its tail. -/
def rationalTailState (d : ℕ → ℕ) (a b N : ℕ) : ℤ :=
  (a : ℤ) * reciprocalDenomProd d N -
    (b : ℤ) * reciprocalScaledNumerator d N

/-- The integer state is exactly the product denominator times the analytic
tail. -/
theorem rationalTailState_cast_eq_scaled_tail
    (d : ℕ → ℕ) (a b : ℕ) (hpos : ∀ k, 0 < d k)
    (hsum : Summable (fun k : ℕ => (d k : ℝ)⁻¹))
    (hb : 0 < b)
    (hrat : (∑' k : ℕ, (d k : ℝ)⁻¹) = (a : ℝ) / (b : ℝ))
    (N : ℕ) :
    (rationalTailState d a b N : ℝ) =
      (b : ℝ) * (reciprocalDenomProd d N : ℝ) *
        (∑' j : ℕ, (d (N + j) : ℝ)⁻¹) := by
  let P : ℝ := ∑ k ∈ Finset.range N, (d k : ℝ)⁻¹
  let T : ℝ := ∑' j : ℕ, (d (N + j) : ℝ)⁻¹
  have hsplit : P + T = ∑' k : ℕ, (d k : ℝ)⁻¹ := by
    have h := hsum.sum_add_tsum_nat_add N
    simpa [P, T, add_comm] using h
  have hDP :
      (reciprocalDenomProd d N : ℝ) * P =
        (reciprocalScaledNumerator d N : ℝ) := by
    simpa [P] using denomProd_mul_partialSum_eq_scaledNumerator d hpos N
  have hb0 : (b : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hb)
  change (rationalTailState d a b N : ℝ) =
    (b : ℝ) * (reciprocalDenomProd d N : ℝ) * T
  rw [show T = (a : ℝ) / (b : ℝ) - P by linarith [hsplit, hrat]]
  dsimp [rationalTailState]
  push_cast
  rw [← hDP]
  field_simp

/-- Every state forced by a rational positive sum is a strictly positive
integer. -/
theorem rationalTailState_pos
    (d : ℕ → ℕ) (a b : ℕ) (hpos : ∀ k, 0 < d k)
    (hsum : Summable (fun k : ℕ => (d k : ℝ)⁻¹))
    (hb : 0 < b)
    (hrat : (∑' k : ℕ, (d k : ℝ)⁻¹) = (a : ℝ) / (b : ℝ))
    (N : ℕ) :
    0 < rationalTailState d a b N := by
  have hcast := rationalTailState_cast_eq_scaled_tail d a b hpos hsum hb hrat N
  have hD : 0 < reciprocalDenomProd d N := by
    exact Finset.prod_pos fun k hk => hpos k
  have ht : Summable (fun j : ℕ => (d (N + j) : ℝ)⁻¹) := by
    have h := (summable_nat_add_iff N).2 hsum
    simpa [add_comm] using h
  have hT : 0 < ∑' j : ℕ, (d (N + j) : ℝ)⁻¹ :=
    ht.tsum_pos (fun _ => inv_nonneg.mpr (by positivity)) 0
      (inv_pos.mpr (by exact_mod_cast hpos N))
  have hr : (0 : ℝ) < (rationalTailState d a b N : ℝ) := by
    rw [hcast]
    positivity
  exact_mod_cast hr

/-- The product denominator grows by the next denominator. -/
theorem reciprocalDenomProd_succ (d : ℕ → ℕ) (N : ℕ) :
    reciprocalDenomProd d (N + 1) = reciprocalDenomProd d N * d N := by
  simp [reciprocalDenomProd, Finset.prod_range_succ]

/-- Exact Engel-type recurrence for the positive integer tail states:
`z_{N+1} = d_N z_N - b D_N`. -/
theorem rationalTailState_succ
    (d : ℕ → ℕ) (a b : ℕ) (hpos : ∀ k, 0 < d k)
    (hsum : Summable (fun k : ℕ => (d k : ℝ)⁻¹))
    (hb : 0 < b)
    (hrat : (∑' k : ℕ, (d k : ℝ)⁻¹) = (a : ℝ) / (b : ℝ))
    (N : ℕ) :
    rationalTailState d a b (N + 1) =
      (d N : ℤ) * rationalTailState d a b N -
        (b : ℤ) * reciprocalDenomProd d N := by
  have hN := rationalTailState_cast_eq_scaled_tail d a b hpos hsum hb hrat N
  have hNs := rationalTailState_cast_eq_scaled_tail d a b hpos hsum hb hrat (N + 1)
  have hshift :
      (∑' j : ℕ, (d (N + j) : ℝ)⁻¹) =
        (d N : ℝ)⁻¹ + ∑' j : ℕ, (d (N + 1 + j) : ℝ)⁻¹ := by
    have ht : Summable (fun j : ℕ => (d (N + j) : ℝ)⁻¹) := by
      have h := (summable_nat_add_iff N).2 hsum
      simpa [add_comm] using h
    have h := (ht.sum_add_tsum_nat_add 1).symm
    simpa [add_assoc, add_comm, add_left_comm] using h
  have hd0 : (d N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (hpos N))
  have hreal :
      (rationalTailState d a b (N + 1) : ℝ) =
        (d N : ℝ) * (rationalTailState d a b N : ℝ) -
          (b : ℝ) * (reciprocalDenomProd d N : ℝ) := by
    rw [hNs, reciprocalDenomProd_succ, Nat.cast_mul, hN, hshift]
    field_simp
    ring
  exact_mod_cast hreal

/-- Fibonacci specialization of the exact positive integer recurrence. -/
theorem rational_fibonacci_tail_states
    (n : ℕ → ℕ) (a b : ℕ) (hpos : ∀ k, 0 < n k)
    (hmono : StrictMono n) (hb : 0 < b)
    (hrat : (∑' k : ℕ, (Nat.fib (n k) : ℝ)⁻¹) = (a : ℝ) / (b : ℝ)) :
    let z := rationalTailState (fun k => Nat.fib (n k)) a b
    let D := reciprocalDenomProd (fun k => Nat.fib (n k))
    (∀ N, 0 < z N) ∧
      (∀ N, z (N + 1) =
        (Nat.fib (n N) : ℤ) * z N - (b : ℤ) * D N) := by
  let d : ℕ → ℕ := fun k => Nat.fib (n k)
  have hdpos : ∀ k, 0 < d k := fun k => Nat.fib_pos.mpr (hpos k)
  have hsum : Summable (fun k : ℕ => (d k : ℝ)⁻¹) := by
    simpa [d] using (summable_and_tsum_shift_le n hpos hmono 0).1
  dsimp only
  constructor
  · exact fun N => rationalTailState_pos d a b hdpos hsum hb (by simpa [d] using hrat) N
  · exact fun N => rationalTailState_succ d a b hdpos hsum hb (by simpa [d] using hrat) N

end Research
