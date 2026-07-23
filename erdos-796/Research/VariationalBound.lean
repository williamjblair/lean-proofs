import Research.VariationalUpper
import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas

namespace Erdos796

lemma primeCounting_le_self (M : ℕ) : Nat.primeCounting M ≤ M := by
  rw [← Nat.primesLE_card_eq_primeCounting]
  have hsub : Nat.primesLE M ⊆ Finset.Icc 1 M := by
    intro p hp
    have h := Nat.mem_primesLE.mp hp
    exact Finset.mem_Icc.mpr ⟨h.2.one_le, h.1⟩
  calc
    _ ≤ (Finset.Icc 1 M).card := Finset.card_le_card hsub
    _ ≤ M := by simp

/-- The explicit sixth-power factor bound of F-024 has a simpler `8 N^5`
error term. -/
theorem selfCompatible_card_le_prime_add_eight_pow
    (S : Finset ℕ) (M N : ℕ)
    (hS : S ⊆ Finset.Icc 1 M) (hcompat : CrossCompatible S S)
    (hM : M ≤ N ^ 6) (hN : 1 < N) :
    (S.card : ℝ) ≤ Nat.primeCounting M + 8 * (N : ℝ) ^ 5 := by
  have hpi : Nat.primeCounting M ≤ N ^ 6 :=
    (primeCounting_le_self M).trans hM
  have hpiR : (Nat.primeCounting M : ℝ) ≤ (N : ℝ) ^ 6 := by
    exact_mod_cast hpi
  have hsqrtpi : Real.sqrt (Nat.primeCounting M : ℝ) ≤ (N : ℝ) ^ 3 := by
    rw [Real.sqrt_le_iff]
    constructor
    · positivity
    · nlinarith
  have hsqrtN : Real.sqrt (N ^ 4 + 1 : ℕ) ≤ (N : ℝ) ^ 2 + 1 := by
    rw [Real.sqrt_le_iff]
    constructor
    · positivity
    · norm_num
      nlinarith [sq_nonneg ((N : ℝ) ^ 2)]
  have h1 : (1 : ℝ) ≤ (N : ℝ) ^ 5 := by
    norm_cast
    simpa using (Nat.pow_le_pow_right (n := N) (by omega) (show 0 ≤ 5 by omega))
  have h2 : (N : ℝ) ^ 2 ≤ (N : ℝ) ^ 5 := by
    norm_cast
    exact Nat.pow_le_pow_right (by omega) (by omega)
  have h3 : (N : ℝ) ^ 3 ≤ (N : ℝ) ^ 5 := by
    norm_cast
    exact Nat.pow_le_pow_right (by omega) (by omega)
  have h4 : (N : ℝ) ^ 4 ≤ (N : ℝ) ^ 5 := by
    norm_cast
    exact Nat.pow_le_pow_right (by omega) (by omega)
  have herror :
      ((N ^ 2 + 1 : ℕ) : ℝ) * Real.sqrt (Nat.primeCounting M) +
          ((N ^ 4 + 1 : ℕ) : ℝ) +
          ((N ^ 3 + 1 : ℕ) : ℝ) * Real.sqrt (N ^ 4 + 1 : ℕ) ≤
        8 * (N : ℝ) ^ 5 := by
    calc
      _ ≤ ((N ^ 2 + 1 : ℕ) : ℝ) * ((N : ℝ) ^ 3) +
          ((N ^ 4 + 1 : ℕ) : ℝ) +
          ((N ^ 3 + 1 : ℕ) : ℝ) * ((N : ℝ) ^ 2 + 1) := by gcongr
      _ ≤ 8 * (N : ℝ) ^ 5 := by
        norm_num
        nlinarith
  have hbase := selfCompatible_card_le_of_le_sixthPower hN hM S hS hcompat
  linarith

/-- A numerical sixth-root choice strictly larger than one always covers its
argument. -/
lemma le_nthRoot_six_add_two_pow (M : ℕ) :
    M ≤ (Nat.nthRoot 6 M + 2) ^ 6 := by
  exact (Nat.lt_pow_nthRoot_add_one (by norm_num) M).le.trans
    (Nat.pow_le_pow_left (by omega) 6)

/-- Uniform pointwise power saving for every finite self-compatible type. -/
theorem selfCompatible_card_le_prime_add_root_error
    (S : Finset ℕ) (M : ℕ)
    (hS : S ⊆ Finset.Icc 1 M) (hcompat : CrossCompatible S S) :
    (S.card : ℝ) ≤ Nat.primeCounting M +
      8 * (Nat.nthRoot 6 M + 2 : ℕ) ^ 5 := by
  exact selfCompatible_card_le_prime_add_eight_pow S M
    (Nat.nthRoot 6 M + 2) hS hcompat
    (le_nthRoot_six_add_two_pow M) (by omega)

/-- The cast of the numerical sixth root is bounded by the real sixth root. -/
lemma cast_nthRoot_six_le_rpow (M : ℕ) :
    (Nat.nthRoot 6 M : ℝ) ≤ (M : ℝ) ^ (6 : ℝ)⁻¹ := by
  apply (Real.le_rpow_inv_iff_of_pos (by positivity) (by positivity)
    (show (0 : ℝ) < 6 by norm_num)).2
  exact_mod_cast (Nat.pow_nthRoot_le (n := 6) (a := M) (Or.inl (by norm_num)))

/-- Pointwise error appearing in the sixth-root core estimate. -/
noncomputable def rootErrorRaw (M : ℕ) : ℝ :=
  8 * ((Nat.nthRoot 6 M + 2 : ℕ) : ℝ) ^ 5

/-- Majorant summand for the sixth-root error in the layer objective. -/
noncomputable def rootErrorWeight (M : ℕ) : ℝ :=
  if M = 0 then 0 else
    rootErrorRaw M / ((M : ℝ) * (M + 1 : ℕ))

lemma rootErrorWeight_nonneg (M : ℕ) : 0 ≤ rootErrorWeight M := by
  unfold rootErrorWeight rootErrorRaw
  split <;> positivity

/-- The sixth-root layer error is dominated by a convergent p-series. -/
theorem rootErrorWeight_le_pseries (M : ℕ) :
    rootErrorWeight M ≤ 1944 * (M : ℝ) ^ (-(7 : ℝ) / 6) := by
  by_cases hM : M = 0
  · subst M
    simp [rootErrorWeight]
  have hMpos : (0 : ℝ) < M := by exact_mod_cast (Nat.pos_of_ne_zero hM)
  have hone : (1 : ℝ) ≤ (M : ℝ) ^ (6 : ℝ)⁻¹ :=
    Real.one_le_rpow (by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hM)) (by positivity)
  have hroot := cast_nthRoot_six_le_rpow M
  have hadd : ((Nat.nthRoot 6 M + 2 : ℕ) : ℝ) ≤
      3 * (M : ℝ) ^ (6 : ℝ)⁻¹ := by
    norm_num at hroot ⊢
    linarith
  have hpow : (((Nat.nthRoot 6 M + 2 : ℕ) : ℝ) ^ 5) ≤
      243 * ((M : ℝ) ^ (6 : ℝ)⁻¹) ^ 5 := by
    calc
      _ ≤ (3 * (M : ℝ) ^ (6 : ℝ)⁻¹) ^ 5 := by gcongr
      _ = 243 * ((M : ℝ) ^ (6 : ℝ)⁻¹) ^ 5 := by ring
  rw [rootErrorWeight, if_neg hM]
  unfold rootErrorRaw
  calc
    8 * ((Nat.nthRoot 6 M + 2 : ℕ) : ℝ) ^ 5 /
          ((M : ℝ) * (M + 1 : ℕ))
        ≤ 1944 * (((M : ℝ) ^ (6 : ℝ)⁻¹) ^ 5) /
          ((M : ℝ) * (M + 1 : ℕ)) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      nlinarith [hpow]
    _ ≤ 1944 * (((M : ℝ) ^ (6 : ℝ)⁻¹) ^ 5) / ((M : ℝ) ^ 2) := by
      gcongr
      norm_num
      nlinarith
    _ = 1944 * (M : ℝ) ^ (-(7 : ℝ) / 6) := by
      rw [← Real.rpow_natCast]
      rw [← Real.rpow_mul (le_of_lt hMpos)]
      rw [mul_div_assoc]
      congr 1
      rw [← Real.rpow_natCast]
      rw [← Real.rpow_sub hMpos]
      congr 1
      norm_num

/-- The terminal correction in every positive layer is uniformly bounded. -/
theorem rootErrorRaw_div_succ_le (M : ℕ) (hM : 0 < M) :
    rootErrorRaw M / (M + 1 : ℕ) ≤ 1944 := by
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
  have hone : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hyone : (1 : ℝ) ≤ (M : ℝ) ^ (6 : ℝ)⁻¹ :=
    Real.one_le_rpow hone (by positivity)
  have hroot := cast_nthRoot_six_le_rpow M
  have hadd : ((Nat.nthRoot 6 M + 2 : ℕ) : ℝ) ≤
      3 * (M : ℝ) ^ (6 : ℝ)⁻¹ := by
    norm_num at hroot ⊢
    linarith
  have hpow : (((Nat.nthRoot 6 M + 2 : ℕ) : ℝ) ^ 5) ≤
      243 * ((M : ℝ) ^ (6 : ℝ)⁻¹) ^ 5 := by
    calc
      _ ≤ (3 * (M : ℝ) ^ (6 : ℝ)⁻¹) ^ 5 := by gcongr
      _ = 243 * ((M : ℝ) ^ (6 : ℝ)⁻¹) ^ 5 := by ring
  have hyrpow : ((M : ℝ) ^ (6 : ℝ)⁻¹) ^ 5 ≤ (M : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt hMpos)]
    apply Real.rpow_le_self_of_one_le hone
    norm_num
  unfold rootErrorRaw
  norm_num at hpow
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < (M + 1 : ℕ))).2
  norm_num
  nlinarith [hpow, hyrpow]

/-- The full sequence of sixth-root layer errors is summable. -/
theorem summable_rootErrorWeight : Summable rootErrorWeight := by
  have hs : Summable (fun M : ℕ => (M : ℝ) ^ (-(7 : ℝ) / 6)) :=
    Real.summable_nat_rpow.mpr (by norm_num)
  exact Summable.of_nonneg_of_le rootErrorWeight_nonneg
    rootErrorWeight_le_pseries (hs.mul_left 1944)

/-- Total finite sixth-root error in a cutoff layer objective. -/
noncomputable def rootErrorLayerMass (R : ℕ) : ℝ :=
  (∑ i : Fin R, rootErrorWeight (i.val + 1)) +
    rootErrorRaw R / (R + 1 : ℕ)

lemma FiberProfile.card_le_prime_add_rootErrorRaw {R : ℕ}
    (P : FiberProfile R) (i : Fin R) :
    ((P.fiber i).card : ℝ) ≤ Nat.primeCounting (i.val + 1) +
      rootErrorRaw (i.val + 1) := by
  have hsub : P.fiber i ⊆ Finset.Icc 1 (i.val + 1) := by
    intro d hd
    exact Finset.mem_Icc.mpr ⟨P.positive i d hd, P.bounded i d hd⟩
  simpa [rootErrorRaw] using
    selfCompatible_card_le_prime_add_root_error
      (P.fiber i) (i.val + 1) hsub (P.compatible i i)

/-- Layer-cake expression built from prime-counting values. -/
noncomputable def primeCountLayerMass (R : ℕ) : ℝ :=
  (∑ m ∈ Finset.range R,
      (Nat.primeCounting (m + 1) : ℝ) /
        (((m + 1 : ℕ) : ℝ) * ((m + 2 : ℕ) : ℝ))) +
    (Nat.primeCounting R : ℝ) / (R + 1)

lemma primeCounting_succ_cast (R : ℕ) :
    (Nat.primeCounting (R + 1) : ℝ) = Nat.primeCounting R +
      (if (R + 1).Prime then 1 else 0) := by
  rw [← Nat.primesLE_card_eq_primeCounting,
    ← Nat.primesLE_card_eq_primeCounting, Nat.primesLE_succ]
  by_cases hp : (R + 1).Prime
  · simp [hp, Nat.notMem_primesLE]
  · simp [hp]

lemma primeCountLayerMass_succ (R : ℕ) :
    primeCountLayerMass (R + 1) = primeCountLayerMass R +
      (if (R + 1).Prime then (1 : ℝ) / (R + 1) else 0) := by
  unfold primeCountLayerMass
  rw [Finset.sum_range_succ, primeCounting_succ_cast]
  by_cases hp : (R + 1).Prime <;> simp [hp]
  all_goals
    have h1 : (R : ℝ) + 1 ≠ 0 := by positivity
    have h2 : (R : ℝ) + 2 ≠ 0 := by positivity
    field_simp
    ring

/-- Reciprocal prime mass equals the prime-counting layer cake exactly. -/
theorem primeCountLayerMass_eq_primeMass (R : ℕ) :
    primeCountLayerMass R = primeMass R := by
  induction R with
  | zero => simp [primeCountLayerMass, primeMass]
  | succ R ih =>
      rw [primeCountLayerMass_succ, primeMass_succ, ih]

/-- Every compatible profile is bounded by the prime layer cake plus the
summable sixth-root error layer. -/
theorem FiberProfile.beta_le_prime_add_rootError {R : ℕ}
    (P : FiberProfile R) :
    P.beta ≤ primeCountLayerMass R + rootErrorLayerMass R := by
  have hlast := P.card_le_prime_add_rootErrorRaw
    ⟨R - 1, by have hR := P.posR; omega⟩
  unfold FiberProfile.beta primeCountLayerMass rootErrorLayerMass
  rw [← Fin.sum_univ_eq_sum_range (fun m =>
    (Nat.primeCounting (m + 1) : ℝ) /
      (((m + 1 : ℕ) : ℝ) * ((m + 2 : ℕ) : ℝ))) R]
  calc
    (∑ i : Fin R, ((P.fiber i).card : ℝ) /
        (((i.val + 1 : ℕ) : ℝ) * ((i.val + 2 : ℕ) : ℝ))) +
        ((P.fiber ⟨R - 1, by have hR := P.posR; omega⟩).card : ℝ) /
          (R + 1) ≤
      (∑ i : Fin R, ((Nat.primeCounting (i.val + 1) : ℝ) +
          rootErrorRaw (i.val + 1)) /
        (((i.val + 1 : ℕ) : ℝ) * ((i.val + 2 : ℕ) : ℝ))) +
        ((Nat.primeCounting R : ℝ) + rootErrorRaw R) / (R + 1) := by
      apply add_le_add
      · apply Finset.sum_le_sum
        intro i hi
        exact div_le_div_of_nonneg_right
          (P.card_le_prime_add_rootErrorRaw i) (by positivity)
      · exact div_le_div_of_nonneg_right (by
          simpa [Nat.sub_add_cancel (show 1 ≤ R by have hR := P.posR; omega)]
            using hlast) (by positivity)
    _ = ((∑ i : Fin R, (Nat.primeCounting (i.val + 1) : ℝ) /
          (((i.val + 1 : ℕ) : ℝ) * ((i.val + 2 : ℕ) : ℝ))) +
        (Nat.primeCounting R : ℝ) / (R + 1)) +
      ((∑ i : Fin R, rootErrorWeight (i.val + 1)) +
        rootErrorRaw R / (R + 1)) := by
      have herr (i : Fin R) :
          rootErrorRaw (i.val + 1) /
              (((i.val + 1 : ℕ) : ℝ) * ((i.val + 2 : ℕ) : ℝ)) =
            rootErrorWeight (i.val + 1) := by
        rw [rootErrorWeight, if_neg (by omega)]
      simp_rw [add_div, herr]
      rw [Finset.sum_add_distrib]
      norm_num
      ring
    _ = ((∑ i : Fin R, (Nat.primeCounting (i.val + 1) : ℝ) /
          (((i.val + 1 : ℕ) : ℝ) * ((i.val + 2 : ℕ) : ℝ))) +
        (Nat.primeCounting R : ℝ) / (R + 1)) +
      ((∑ i : Fin R, rootErrorWeight (i.val + 1)) +
        rootErrorRaw R / ((R + 1 : ℕ) : ℝ)) := by norm_num

/-- One absolute finite constant bounding all variational gains. -/
noncomputable def universalVariationalBound : ℝ :=
  ∑' M : ℕ, rootErrorWeight M + 1944

/-- Every finite error layer is bounded by the same convergent-series
constant. -/
theorem rootErrorLayerMass_le_universal (R : ℕ) (hR : 0 < R) :
    rootErrorLayerMass R ≤ universalVariationalBound := by
  have hshift : Summable (fun m : ℕ => rootErrorWeight (m + 1)) :=
    (summable_nat_add_iff 1).mpr summable_rootErrorWeight
  have hpartial :
      (∑ m ∈ Finset.range R, rootErrorWeight (m + 1)) ≤
        ∑' m : ℕ, rootErrorWeight (m + 1) :=
    hshift.sum_le_tsum (Finset.range R)
      (fun i hi => rootErrorWeight_nonneg (i + 1))
  have htail : (∑' m : ℕ, rootErrorWeight (m + 1)) =
      ∑' m : ℕ, rootErrorWeight m := by
    have h := summable_rootErrorWeight.sum_add_tsum_nat_add 1
    simpa [rootErrorWeight] using h
  have hterminal := rootErrorRaw_div_succ_le R hR
  unfold rootErrorLayerMass universalVariationalBound
  rw [Fin.sum_univ_eq_sum_range (fun m => rootErrorWeight (m + 1)) R]
  rw [htail] at hpartial
  linarith

/-- Uniform boundedness of the renormalized objective for every finite
compatible profile. -/
theorem FiberProfile.gamma_le_universal {R : ℕ} (P : FiberProfile R) :
    P.gamma ≤ universalVariationalBound := by
  have hb := P.beta_le_prime_add_rootError
  have he := rootErrorLayerMass_le_universal R P.posR
  rw [primeCountLayerMass_eq_primeMass] at hb
  unfold FiberProfile.gamma
  linarith

end Erdos796
