import Research.RationalState

/-!
# Prime-divisibility invariants of rational tail states
-/

namespace Research

open scoped BigOperators

/-- Natural-number version of the positive integer tail state. -/
def rationalTailStateNat (d : ℕ → ℕ) (a b N : ℕ) : ℕ :=
  (rationalTailState d a b N).toNat

/-- Once rationality supplies positivity, coercing the natural state back to
`ℤ` recovers the original state exactly. -/
theorem rationalTailStateNat_cast
    (d : ℕ → ℕ) (a b : ℕ) (hpos : ∀ k, 0 < d k)
    (hsum : Summable (fun k : ℕ => (d k : ℝ)⁻¹))
    (hb : 0 < b)
    (hrat : (∑' k : ℕ, (d k : ℝ)⁻¹) = (a : ℝ) / (b : ℝ))
    (N : ℕ) :
    (rationalTailStateNat d a b N : ℤ) = rationalTailState d a b N := by
  exact Int.toNat_of_nonneg
    (le_of_lt (rationalTailState_pos d a b hpos hsum hb hrat N))

/-- Subtraction-free natural form of the exact recurrence. -/
theorem rationalTailStateNat_succ_add
    (d : ℕ → ℕ) (a b : ℕ) (hpos : ∀ k, 0 < d k)
    (hsum : Summable (fun k : ℕ => (d k : ℝ)⁻¹))
    (hb : 0 < b)
    (hrat : (∑' k : ℕ, (d k : ℝ)⁻¹) = (a : ℝ) / (b : ℝ))
    (N : ℕ) :
    rationalTailStateNat d a b (N + 1) + b * reciprocalDenomProd d N =
      d N * rationalTailStateNat d a b N := by
  have hz := rationalTailState_succ d a b hpos hsum hb hrat N
  have hcN := rationalTailStateNat_cast d a b hpos hsum hb hrat N
  have hcNs := rationalTailStateNat_cast d a b hpos hsum hb hrat (N + 1)
  exact_mod_cast (show
    (rationalTailStateNat d a b (N + 1) : ℤ) +
        (b * reciprocalDenomProd d N : ℕ) =
      (d N * rationalTailStateNat d a b N : ℕ) by
        push_cast
        rw [hcN, hcNs, hz]
        ring)

/-- A prime appearing for the first time in `d_N` cannot divide the next tail
state, provided it does not divide the fixed rational denominator `b`. -/
theorem prime_not_dvd_tailState_after_first_denominator
    (d : ℕ → ℕ) (a b p : ℕ) (hpos : ∀ k, 0 < d k)
    (hsum : Summable (fun k : ℕ => (d k : ℝ)⁻¹))
    (hb : 0 < b)
    (hrat : (∑' k : ℕ, (d k : ℝ)⁻¹) = (a : ℝ) / (b : ℝ))
    (hp : p.Prime) (hpb : ¬p ∣ b) (N : ℕ)
    (hpnew : ∀ i < N, ¬p ∣ d i) (hpd : p ∣ d N) :
    ¬p ∣ rationalTailStateNat d a b (N + 1) := by
  have hrec := rationalTailStateNat_succ_add d a b hpos hsum hb hrat N
  have hpD : ¬p ∣ reciprocalDenomProd d N := by
    rw [← hp.coprime_iff_not_dvd]
    apply Nat.Coprime.prod_right
    intro i hi
    exact hp.coprime_iff_not_dvd.mpr (hpnew i (Finset.mem_range.mp hi))
  have hpbD : ¬p ∣ b * reciprocalDenomProd d N :=
    hp.not_dvd_mul hpb hpD
  intro hpz
  have hpright : p ∣ d N * rationalTailStateNat d a b N :=
    dvd_mul_of_dvd_left hpd _
  have hpsum : p ∣ rationalTailStateNat d a b (N + 1) +
      b * reciprocalDenomProd d N := by rwa [hrec]
  have hpbd : p ∣ b * reciprocalDenomProd d N :=
    (Nat.dvd_add_iff_right hpz).mpr (by simpa [add_comm] using hpsum)
  exact hpbD hpbd

/-- Once `p` is already in the product denominator, nondivisibility of both the
current denominator and current state propagates to the next state. -/
theorem prime_not_dvd_tailState_propagates
    (d : ℕ → ℕ) (a b p : ℕ) (hpos : ∀ k, 0 < d k)
    (hsum : Summable (fun k : ℕ => (d k : ℝ)⁻¹))
    (hb : 0 < b)
    (hrat : (∑' k : ℕ, (d k : ℝ)⁻¹) = (a : ℝ) / (b : ℝ))
    (hp : p.Prime) (N : ℕ)
    (hpD : p ∣ reciprocalDenomProd d N)
    (hpd : ¬p ∣ d N)
    (hpz : ¬p ∣ rationalTailStateNat d a b N) :
    ¬p ∣ rationalTailStateNat d a b (N + 1) := by
  have hrec := rationalTailStateNat_succ_add d a b hpos hsum hb hrat N
  intro hpzs
  have hpbd : p ∣ b * reciprocalDenomProd d N := dvd_mul_of_dvd_right hpD _
  have hpsum : p ∣ rationalTailStateNat d a b (N + 1) +
      b * reciprocalDenomProd d N := dvd_add hpzs hpbd
  have hpprod : p ∣ d N * rationalTailStateNat d a b N := by rwa [← hrec]
  rcases hp.dvd_mul.mp hpprod with h | h
  · exact hpd h
  · exact hpz h

/-- If an already-seen prime reappears in the current denominator, then it must
divide the next state. -/
theorem prime_dvd_tailState_after_reappearance
    (d : ℕ → ℕ) (a b p : ℕ) (hpos : ∀ k, 0 < d k)
    (hsum : Summable (fun k : ℕ => (d k : ℝ)⁻¹))
    (hb : 0 < b)
    (hrat : (∑' k : ℕ, (d k : ℝ)⁻¹) = (a : ℝ) / (b : ℝ))
    (N : ℕ) (hpD : p ∣ reciprocalDenomProd d N) (hpd : p ∣ d N) :
    p ∣ rationalTailStateNat d a b (N + 1) := by
  have hrec := rationalTailStateNat_succ_add d a b hpos hsum hb hrat N
  have hpbd : p ∣ b * reciprocalDenomProd d N := dvd_mul_of_dvd_right hpD _
  have hpright : p ∣ d N * rationalTailStateNat d a b N :=
    dvd_mul_of_dvd_left hpd _
  have hpsum : p ∣ rationalTailStateNat d a b (N + 1) +
      b * reciprocalDenomProd d N := by rwa [hrec]
  exact (Nat.dvd_add_iff_right hpbd).mpr (by simpa [add_comm] using hpsum)

end Research
