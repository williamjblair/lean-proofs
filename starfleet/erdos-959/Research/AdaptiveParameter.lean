import Research.ExactParameter

noncomputable section
namespace Erdos959

lemma exists_parameter_dominant_set_Q {m Q : ℕ}
    (hh15 : 15 ≤ parameterH m) (hQmin : parameterQ m ≤ Q) :
    ∃ Y : Finset Point,
      parameterBlockCount m * Q ≤ 1152 * Y.card ∧
      Y.card ≤ 5 * (parameterBlockCount m * Q) ∧
      parameterBlockCount m * Q * 2 ^ parameterH m ≤
        1152 * (orderedRealDistancePairs Y 1).card ∧
      (∀ d : ℝ, d ≠ 1 →
        2304 * (orderedRealDistancePairs Y d).card ≤
          parameterBlockCount m * Q * 2 ^ parameterH m) := by
  let U := parameterUniverse m
  let h := parameterH m
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
      _ = parameterQ m := by simp [parameterQ, hcard, h]
      _ ≤ Q := hQmin
  · exact parameter_numeric_base m
  · have hnonempty : 1 ≤ (U.powersetCard h).card :=
      Finset.card_pos.mpr (Finset.powersetCard_nonempty.mpr hhU)
    calc
      23040 ≤ 2 ^ h := by
        calc
          23040 ≤ 2 ^ 15 := by norm_num
          _ ≤ 2 ^ h := Nat.pow_le_pow_right (by omega) hh15
      _ ≤ (U.powersetCard h).card * 2 ^ h := Nat.le_mul_of_pos_left _ hnonempty

/-- Once the minimum construction fits inside `n` with factor ten of slack,
choose the replication parameter by division and pad generically to exactly
`n`. This eliminates any subsequence/interpolation issue. -/
theorem adaptive_parameter_gap {m n : ℕ}
    (hh15 : 15 ≤ parameterH m)
    (hfit : 10 * parameterBlockCount m * parameterQ m ≤ n) :
    n * 2 ^ parameterH m ≤ 46080 * extremalGap n := by
  let B := parameterBlockCount m
  let h := parameterH m
  let d := 5 * B
  let Q := n / d
  have hhU : h ≤ (parameterUniverse m).card := parameterH_le_card m
  have hB : 1 ≤ B := by
    exact Finset.card_pos.mpr (Finset.powersetCard_nonempty.mpr hhU)
  have hdpos : 0 < d := by simp [d]; positivity
  have hmpos : 0 < m := by
    by_contra hm0
    have : m = 0 := by omega
    subst m
    norm_num [h, parameterH, parameterUniverse, splitPrimesLE] at hh15
  have hQ0pos : 1 ≤ parameterQ m := Nat.one_le_pow _ _ (by positivity)
  have hQmin : parameterQ m ≤ Q := by
    apply (Nat.le_div_iff_mul_le hdpos).2
    dsimp [d, B]
    have hhalf : 5 * parameterBlockCount m * parameterQ m ≤ n := by
      calc
        5 * parameterBlockCount m * parameterQ m ≤
            10 * parameterBlockCount m * parameterQ m := by
          exact Nat.mul_le_mul_right (parameterQ m)
            (Nat.mul_le_mul_right (parameterBlockCount m) (by omega))
        _ ≤ n := hfit
    simpa [mul_comm, mul_left_comm, mul_assoc] using hhalf
  have hQpos : 1 ≤ Q := hQ0pos.trans hQmin
  obtain ⟨Y, hYlower, hYupper, htarget, hcomp⟩ :=
    exists_parameter_dominant_set_Q hh15 hQmin
  have hdQle : d * Q ≤ n := by
    simpa [Q, mul_comm] using (Nat.div_mul_le_self n d)
  have hYle : Y.card ≤ n := hYupper.trans (by
    dsimp [d, B] at hdQle ⊢
    simpa [mul_assoc] using hdQle)
  let S := B * Q * 2 ^ h
  have hSlarge : 4608 ≤ S := by
    have hpow : 23040 ≤ B * 2 ^ h := by
      calc
        23040 ≤ 2 ^ h := by
          calc
            23040 ≤ 2 ^ 15 := by norm_num
            _ ≤ 2 ^ h := Nat.pow_le_pow_right (by omega) hh15
        _ ≤ B * 2 ^ h := Nat.le_mul_of_pos_left _ hB
    have : B * 2 ^ h ≤ (B * 2 ^ h) * Q := Nat.le_mul_of_pos_right _ hQpos
    dsimp [S]
    have : 23040 ≤ B * Q * 2 ^ h := by nlinarith
    omega
  obtain ⟨Z, hZcard, hZtarget, hZcomp⟩ :=
    pad_dominant_set_to_exact_card Y S n hYle hSlarge
      (by simpa [S, B, Q, h] using htarget)
      (by simpa [S, B, Q, h] using hcomp)
  have hnlarge : 5 ≤ n := by
    have hprod : 1 ≤ B * parameterQ m := Nat.mul_pos hB hQ0pos
    have hten : 10 ≤ 10 * B * parameterQ m := by
      simpa [mul_assoc] using Nat.mul_le_mul_left 10 hprod
    exact (by omega : 5 ≤ 10).trans (hten.trans (by simpa [B] using hfit))
  have hspectrum : 2 ≤ (pointDistanceSpectrum Z).card := by
    rw [← distanceValues_enumerateFinset]
    apply distanceValues_card_ge_two_of_four_le
    · rw [hZcard]
      omega
    · exact enumerateFinset_injective Z
  have hext : S ≤ 4608 * extremalGap n := by
    rw [← hZcard]
    exact extremalGap_lower_of_ordered_dominance Z S (by omega)
      hspectrum hZtarget hZcomp
  have hdleDQ : d ≤ d * Q := Nat.le_mul_of_pos_right d hQpos
  have hmodlt : n % d < d := Nat.mod_lt n hdpos
  have hdecomp : n % d + d * Q = n := by
    simpa [Q, Nat.mul_comm] using (Nat.mod_add_div n d)
  have hnle : n ≤ 2 * (d * Q) := by omega
  calc
    n * 2 ^ h ≤ (2 * (d * Q)) * 2 ^ h := Nat.mul_le_mul_right _ hnle
    _ = 10 * S := by simp [d, S]; ring
    _ ≤ 10 * (4608 * extremalGap n) := Nat.mul_le_mul_left 10 hext
    _ = 46080 * extremalGap n := by ring

end Erdos959
