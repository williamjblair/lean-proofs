import Research.ParameterSupply
import Research.Padding

noncomputable section
namespace Erdos959

def parameterBlockCount (m : ℕ) : ℕ :=
  ((parameterUniverse m).powersetCard (parameterH m)).card

def parameterSize (m : ℕ) : ℕ :=
  5 * (parameterBlockCount m * parameterQ m)

def parameterSignal (m : ℕ) : ℕ :=
  parameterBlockCount m * parameterQ m * 2 ^ parameterH m

lemma exists_parameter_dominant_set {m : ℕ} (hh15 : 15 ≤ parameterH m) :
    ∃ Y : Finset Point,
      parameterBlockCount m * parameterQ m ≤ 1152 * Y.card ∧
      Y.card ≤ parameterSize m ∧
      parameterSignal m ≤ 1152 * (orderedRealDistancePairs Y 1).card ∧
      (∀ d : ℝ, d ≠ 1 →
        2304 * (orderedRealDistancePairs Y d).card ≤ parameterSignal m) := by
  let U := parameterUniverse m
  let h := parameterH m
  let Q := parameterQ m
  have hhU : h ≤ U.card := parameterH_le_card m
  apply exists_finite_scaled_lattice_gap U h Q (m ^ 2) hhU
      (fun p hp => parameter_prime hp)
      (fun p hp => parameter_mod_four hp)
      (fun p hp => parameter_prime_le hp)
      chosenSplitGaussian
      (fun p hp => chosenSplitGaussian_norm (parameter_prime hp) (parameter_mod_four hp))
  · intro K hK
    have hcard : K.card = h := Finset.mem_powersetCard.mp hK |>.2
    have hsubset : K ⊆ U := Finset.mem_powersetCard.mp hK |>.1
    calc
      2049 ≤ 5 ^ h := by
        calc
          2049 ≤ 5 ^ 15 := by norm_num
          _ ≤ 5 ^ h := Nat.pow_le_pow_right (by omega) hh15
      _ = 5 ^ K.card := by rw [hcard]
      _ ≤ ∏ p ∈ K, p := parameter_product_lower hsubset
  · intro K hK
    have hcard : K.card = h := Finset.mem_powersetCard.mp hK |>.2
    have hsubset : K ⊆ U := Finset.mem_powersetCard.mp hK |>.1
    calc
      (∏ p ∈ K, p) ≤ (m ^ 2) ^ K.card := parameter_product_upper hsubset
      _ = Q := by simp [Q, parameterQ, hcard, h]
  · exact parameter_numeric_base m
  · have hnonempty : 1 ≤ (U.powersetCard h).card :=
      Finset.card_pos.mpr (Finset.powersetCard_nonempty.mpr hhU)
    calc
      23040 ≤ 2 ^ h := by
        calc
          23040 ≤ 2 ^ 15 := by norm_num
          _ ≤ 2 ^ h := Nat.pow_le_pow_right (by omega) hh15
      _ ≤ (U.powersetCard h).card * 2 ^ h := Nat.le_mul_of_pos_left _ hnonempty

lemma parameterSignal_large {m : ℕ} (hh15 : 15 ≤ parameterH m) :
    23040 ≤ parameterSignal m := by
  have hhU := parameterH_le_card m
  have hB : 1 ≤ parameterBlockCount m := by
    exact Finset.card_pos.mpr (Finset.powersetCard_nonempty.mpr hhU)
  have hmpos : 0 < m := by
    by_contra hm
    have : m = 0 := by omega
    subst m
    norm_num [parameterH, parameterUniverse, splitPrimesLE] at hh15
  have hQ : 1 ≤ parameterQ m := by
    exact Nat.one_le_pow _ _ (by positivity)
  calc
    23040 ≤ parameterBlockCount m * 2 ^ parameterH m := by
      calc
        23040 ≤ 2 ^ parameterH m := by
          calc
            23040 ≤ 2 ^ 15 := by norm_num
            _ ≤ 2 ^ parameterH m := Nat.pow_le_pow_right (by omega) hh15
        _ ≤ parameterBlockCount m * 2 ^ parameterH m :=
          Nat.le_mul_of_pos_left _ hB
    _ ≤ (parameterBlockCount m * 2 ^ parameterH m) * parameterQ m :=
      Nat.le_mul_of_pos_right _ hQ
    _ = parameterSignal m := by simp [parameterSignal]; ring

/-- At the explicit canonical cardinality `5 binom(|U_m|,h_m) Q_m`, generic
padding preserves the large gap. -/
theorem eventually_parameterSize_gap :
    ∃ M : ℕ, ∀ m ≥ M,
      parameterSize m * 2 ^ parameterH m ≤
        23040 * extremalGap (parameterSize m) := by
  obtain ⟨M, hM⟩ := parameterH_eventually_ge 15
  refine ⟨M, fun m hm => ?_⟩
  have hh15 := hM m hm
  obtain ⟨Y, hYlower, hYupper, htarget, hcomp⟩ :=
    exists_parameter_dominant_set hh15
  have hSlarge : 4608 ≤ parameterSignal m :=
    (by omega : 4608 ≤ 23040).trans (parameterSignal_large hh15)
  obtain ⟨Z, hZcard, hZtarget, hZcomp⟩ :=
    pad_dominant_set_to_exact_card Y (parameterSignal m) (parameterSize m)
      hYupper hSlarge htarget hcomp
  have hTfive : 5 ≤ parameterSize m := by
    have hhU := parameterH_le_card m
    have hB : 1 ≤ parameterBlockCount m :=
      Finset.card_pos.mpr (Finset.powersetCard_nonempty.mpr hhU)
    have hmpos : 0 < m := by
      by_contra hm0
      have : m = 0 := by omega
      subst m
      norm_num [parameterH, parameterUniverse, splitPrimesLE] at hh15
    have hQ : 1 ≤ parameterQ m := by
      exact Nat.one_le_pow _ _ (by positivity)
    simp only [parameterSize]
    nlinarith
  have hspectrum : 2 ≤ (pointDistanceSpectrum Z).card := by
    rw [← distanceValues_enumerateFinset]
    apply distanceValues_card_ge_two_of_four_le
    · rw [hZcard]
      omega
    · exact enumerateFinset_injective Z
  have hext : parameterSignal m ≤ 4608 * extremalGap (parameterSize m) := by
    rw [← hZcard]
    exact extremalGap_lower_of_ordered_dominance Z (parameterSignal m)
      (by omega) hspectrum hZtarget hZcomp
  calc
    parameterSize m * 2 ^ parameterH m = 5 * parameterSignal m := by
      simp [parameterSize, parameterSignal]
      ring
    _ ≤ 5 * (4608 * extremalGap (parameterSize m)) :=
      Nat.mul_le_mul_left 5 hext
    _ = 23040 * extremalGap (parameterSize m) := by ring

end Erdos959
