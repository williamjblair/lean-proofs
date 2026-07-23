import Research.ValuationState

/-!
# Exact rational tail states with least-common-multiple denominators
-/

namespace Research

/-- Integer state obtained by clearing a finite prefix with its exact lcm. -/
def rationalLcmTailState (d : ℕ → ℕ) (a b N : ℕ) : ℤ :=
  (a : ℤ) * reciprocalLcm d N -
    (b : ℤ) * reciprocalLcmNumerator d N

/-- New lcm factor paid when adjoining `d_N`. -/
def reciprocalLcmGrowth (d : ℕ → ℕ) (N : ℕ) : ℕ :=
  reciprocalLcm d (N + 1) / reciprocalLcm d N

/-- Complementary factor of the enlarged lcm after dividing by `d_N`. -/
def reciprocalLcmCofactor (d : ℕ → ℕ) (N : ℕ) : ℕ :=
  reciprocalLcm d (N + 1) / d N

/-- The old lcm divides the enlarged lcm. -/
theorem reciprocalLcm_dvd_succ (d : ℕ → ℕ) (N : ℕ) :
    reciprocalLcm d N ∣ reciprocalLcm d (N + 1) := by
  rw [reciprocalLcm_succ]
  exact Nat.dvd_lcm_right _ _

/-- The newly adjoined denominator divides the enlarged lcm. -/
theorem denominator_dvd_reciprocalLcm_succ (d : ℕ → ℕ) (N : ℕ) :
    d N ∣ reciprocalLcm d (N + 1) := by
  rw [reciprocalLcm_succ]
  exact Nat.dvd_lcm_left _ _

/-- Exact factorizations associated with lcm growth. -/
theorem reciprocalLcm_growth_mul (d : ℕ → ℕ) (_hpos : ∀ k, 0 < d k) (N : ℕ) :
    reciprocalLcmGrowth d N * reciprocalLcm d N = reciprocalLcm d (N + 1) := by
  rw [reciprocalLcmGrowth, Nat.div_mul_cancel (reciprocalLcm_dvd_succ d N)]

theorem reciprocalLcm_cofactor_mul (d : ℕ → ℕ) (N : ℕ) :
    reciprocalLcmCofactor d N * d N = reciprocalLcm d (N + 1) := by
  rw [reciprocalLcmCofactor,
    Nat.div_mul_cancel (denominator_dvd_reciprocalLcm_succ d N)]

/-- Exact analytic meaning of the lcm state. -/
theorem rationalLcmTailState_cast_eq_scaled_tail
    (d : ℕ → ℕ) (a b : ℕ) (hpos : ∀ k, 0 < d k)
    (hsum : Summable (fun k : ℕ => (d k : ℝ)⁻¹))
    (hb : 0 < b)
    (hrat : (∑' k : ℕ, (d k : ℝ)⁻¹) = (a : ℝ) / (b : ℝ))
    (N : ℕ) :
    (rationalLcmTailState d a b N : ℝ) =
      (b : ℝ) * (reciprocalLcm d N : ℝ) *
        (∑' j : ℕ, (d (N + j) : ℝ)⁻¹) := by
  let P : ℝ := ∑ k ∈ Finset.range N, (d k : ℝ)⁻¹
  let T : ℝ := ∑' j : ℕ, (d (N + j) : ℝ)⁻¹
  have hsplit : P + T = ∑' k : ℕ, (d k : ℝ)⁻¹ := by
    have h := hsum.sum_add_tsum_nat_add N
    simpa [P, T, add_comm] using h
  have hLP :
      (reciprocalLcm d N : ℝ) * P =
        (reciprocalLcmNumerator d N : ℝ) := by
    simpa [P] using reciprocalLcm_mul_partialSum_eq d hpos N
  have hb0 : (b : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hb)
  change (rationalLcmTailState d a b N : ℝ) =
    (b : ℝ) * (reciprocalLcm d N : ℝ) * T
  rw [show T = (a : ℝ) / (b : ℝ) - P by linarith [hsplit, hrat]]
  dsimp [rationalLcmTailState]
  push_cast
  rw [← hLP]
  field_simp

/-- Lcm states are strictly positive integers. -/
theorem rationalLcmTailState_pos
    (d : ℕ → ℕ) (a b : ℕ) (hpos : ∀ k, 0 < d k)
    (hsum : Summable (fun k : ℕ => (d k : ℝ)⁻¹))
    (hb : 0 < b)
    (hrat : (∑' k : ℕ, (d k : ℝ)⁻¹) = (a : ℝ) / (b : ℝ))
    (N : ℕ) :
    0 < rationalLcmTailState d a b N := by
  have hcast := rationalLcmTailState_cast_eq_scaled_tail d a b hpos hsum hb hrat N
  have hL := reciprocalLcm_pos d hpos N
  have ht : Summable (fun j : ℕ => (d (N + j) : ℝ)⁻¹) := by
    have h := (summable_nat_add_iff N).2 hsum
    simpa [add_comm] using h
  have hT : 0 < ∑' j : ℕ, (d (N + j) : ℝ)⁻¹ :=
    ht.tsum_pos (fun _ => inv_nonneg.mpr (by positivity)) 0
      (inv_pos.mpr (by exact_mod_cast hpos N))
  have hr : (0 : ℝ) < (rationalLcmTailState d a b N : ℝ) := by
    rw [hcast]
    positivity
  exact_mod_cast hr

/-- Exact lcm-state recurrence.  It pays only the genuinely new lcm factor,
not the full new denominator. -/
theorem rationalLcmTailState_succ
    (d : ℕ → ℕ) (a b : ℕ) (hpos : ∀ k, 0 < d k)
    (hsum : Summable (fun k : ℕ => (d k : ℝ)⁻¹))
    (hb : 0 < b)
    (hrat : (∑' k : ℕ, (d k : ℝ)⁻¹) = (a : ℝ) / (b : ℝ))
    (N : ℕ) :
    rationalLcmTailState d a b (N + 1) =
      (reciprocalLcmGrowth d N : ℤ) * rationalLcmTailState d a b N -
        (b : ℤ) * reciprocalLcmCofactor d N := by
  have hN := rationalLcmTailState_cast_eq_scaled_tail d a b hpos hsum hb hrat N
  have hNs := rationalLcmTailState_cast_eq_scaled_tail d a b hpos hsum hb hrat (N + 1)
  have hshift :
      (∑' j : ℕ, (d (N + j) : ℝ)⁻¹) =
        (d N : ℝ)⁻¹ + ∑' j : ℕ, (d (N + 1 + j) : ℝ)⁻¹ := by
    have ht : Summable (fun j : ℕ => (d (N + j) : ℝ)⁻¹) := by
      have h := (summable_nat_add_iff N).2 hsum
      simpa [add_comm] using h
    have h := (ht.sum_add_tsum_nat_add 1).symm
    simpa [add_assoc, add_comm, add_left_comm] using h
  have hLpos := reciprocalLcm_pos d hpos N
  have hLNpos := reciprocalLcm_pos d hpos (N + 1)
  have hg : reciprocalLcmGrowth d N * reciprocalLcm d N =
      reciprocalLcm d (N + 1) := reciprocalLcm_growth_mul d hpos N
  have hc : reciprocalLcmCofactor d N * d N =
      reciprocalLcm d (N + 1) := reciprocalLcm_cofactor_mul d N
  have hd0 : (d N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (hpos N))
  have hreal :
      (rationalLcmTailState d a b (N + 1) : ℝ) =
        (reciprocalLcmGrowth d N : ℝ) *
            (rationalLcmTailState d a b N : ℝ) -
          (b : ℝ) * reciprocalLcmCofactor d N := by
    rw [hNs, hN, hshift]
    have hg' : (reciprocalLcmGrowth d N : ℝ) * reciprocalLcm d N =
        reciprocalLcm d (N + 1) := by exact_mod_cast hg
    have hc' : (reciprocalLcmCofactor d N : ℝ) * d N =
        reciprocalLcm d (N + 1) := by exact_mod_cast hc
    have hgc : (reciprocalLcmGrowth d N : ℝ) * reciprocalLcm d N =
        (reciprocalLcmCofactor d N : ℝ) * d N := hg'.trans hc'.symm
    calc
      (b : ℝ) * reciprocalLcm d (N + 1) *
          (∑' j : ℕ, (d (N + 1 + j) : ℝ)⁻¹) =
          (b : ℝ) * ((reciprocalLcmGrowth d N : ℝ) * reciprocalLcm d N) *
            (∑' j : ℕ, (d (N + 1 + j) : ℝ)⁻¹) := by rw [hg']
      _ = (reciprocalLcmGrowth d N : ℝ) *
            ((b : ℝ) * reciprocalLcm d N *
              ((d N : ℝ)⁻¹ +
                ∑' j : ℕ, (d (N + 1 + j) : ℝ)⁻¹)) -
            (b : ℝ) * reciprocalLcmCofactor d N := by
              field_simp
              linear_combination -hgc
  exact_mod_cast hreal

end Research
