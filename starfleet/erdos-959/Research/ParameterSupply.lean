import Research.SplitPrimeDensity

noncomputable section
open Filter Asymptotics
namespace Erdos959

/-- The deliberately generous absolute constant in the denominator of `h`.
It makes the finite construction's numerical suppression hypothesis automatic. -/
def parameterScale : ℕ := 128 * 11520 ^ 2

def parameterUniverse (m : ℕ) : Finset ℕ := splitPrimesLE (m ^ 2)

def parameterH (m : ℕ) : ℕ :=
  (parameterUniverse m).card / (parameterScale * m)

def parameterQ (m : ℕ) : ℕ := (m ^ 2) ^ parameterH m

lemma parameterScale_pos : 0 < parameterScale := by
  norm_num [parameterScale]

lemma parameterH_le_card (m : ℕ) :
    parameterH m ≤ (parameterUniverse m).card := by
  simp only [parameterH]
  exact Nat.div_le_self _ _

/-- Although the numerical constant is huge, the selected subset size tends to
infinity. This is the only growth fact needed to trigger the finite theorem. -/
theorem parameterH_eventually_ge (H : ℕ) :
    ∃ M : ℕ, ∀ m ≥ M, H ≤ parameterH m := by
  obtain ⟨Nden, hNden⟩ := eventually_splitPrimes_card_mul_log_lower
  let C : ℕ := 8 * H * parameterScale + 1
  have hlittle : ∀ᶠ x : ℝ in atTop,
      (C : ℝ) * ‖Real.log x‖ ≤ ‖(id x : ℝ)‖ :=
    (isLittleO_iff_nat_mul_le.mp Real.isLittleO_log_id_atTop) C
  obtain ⟨X, hX⟩ := eventually_atTop.1 hlittle
  let M : ℕ := max (max 2 Nden) ⌈X⌉₊
  refine ⟨M, fun m hm => ?_⟩
  have hm2 : 2 ≤ m := le_trans (le_trans (le_max_left 2 Nden) (le_max_left _ ⌈X⌉₊)) hm
  have hmN : Nden ≤ m ^ 2 := by
    have : Nden ≤ m := le_trans (le_trans (le_max_right 2 Nden) (le_max_left _ ⌈X⌉₊)) hm
    have hmSq : m ≤ m ^ 2 := by nlinarith [Nat.zero_le m]
    exact this.trans hmSq
  have hdensity := hNden (m ^ 2) hmN
  have hmX : X ≤ (m : ℝ) := by
    have hc : X ≤ (⌈X⌉₊ : ℝ) := Nat.le_ceil X
    exact hc.trans (by exact_mod_cast (le_trans (le_max_right (max 2 Nden) ⌈X⌉₊) hm))
  have hlogNorm := hX m hmX
  have hmlog : 0 < Real.log (m : ℝ) := Real.log_pos (by exact_mod_cast hm2)
  have hmreal : 0 ≤ (m : ℝ) := by positivity
  have hlog : (C : ℝ) * Real.log m ≤ m := by
    simpa [Real.norm_eq_abs, abs_of_pos hmlog, abs_of_nonneg hmreal, id] using hlogNorm
  have hmul : H * (parameterScale * m) ≤ (parameterUniverse m).card := by
    by_contra hnot
    have hklt : ((parameterUniverse m).card : ℝ) <
        (H : ℝ) * parameterScale * m := by
      have hkNat := Nat.lt_of_not_ge hnot
      have hkNat' : (parameterUniverse m).card < H * parameterScale * m := by
        simpa [mul_assoc] using hkNat
      exact_mod_cast hkNat'
    have hlogpow : Real.log ((m ^ 2 : ℕ) : ℝ) = 2 * Real.log m := by
      push_cast
      rw [Real.log_pow]
      norm_num
    have hdensity' : ((m : ℝ) ^ 2) / 4 ≤
        ((parameterUniverse m).card : ℝ) * (2 * Real.log m) := by
      simpa [parameterUniverse, Nat.cast_pow, hlogpow] using hdensity
    have hC : (C : ℝ) = 8 * H * parameterScale + 1 := by
      simp [C]
    have hstrict : (8 : ℝ) * H * parameterScale * Real.log m < m := by
      rw [hC] at hlog
      nlinarith
    nlinarith
  have hdenpos : 0 < parameterScale * m :=
    Nat.mul_pos parameterScale_pos (by omega)
  exact (Nat.le_div_iff_mul_le hdenpos).2 hmul

noncomputable def chosenSplitGaussian (p : ℕ) : GaussianInt :=
  if hp : p.Prime ∧ p % 4 = 1 then
    Classical.choose (exists_gaussian_factor_of_prime_mod_four_one hp.1 hp.2)
  else 0

lemma chosenSplitGaussian_norm {p : ℕ} (hp : p.Prime) (hmod : p % 4 = 1) :
    (chosenSplitGaussian p).norm.natAbs = p := by
  rw [chosenSplitGaussian, dif_pos ⟨hp, hmod⟩]
  exact (Classical.choose_spec
    (exists_gaussian_factor_of_prime_mod_four_one hp hmod)).1

lemma parameter_prime {m p : ℕ} (hp : p ∈ parameterUniverse m) : p.Prime :=
  (mem_splitPrimesLE.mp hp).2.1

lemma parameter_mod_four {m p : ℕ} (hp : p ∈ parameterUniverse m) : p % 4 = 1 :=
  (mem_splitPrimesLE.mp hp).2.2

lemma parameter_prime_le {m p : ℕ} (hp : p ∈ parameterUniverse m) : p ≤ m ^ 2 :=
  (mem_splitPrimesLE.mp hp).1

lemma five_le_parameter_prime {m p : ℕ} (hp : p ∈ parameterUniverse m) : 5 ≤ p := by
  have hprime := parameter_prime hp
  have hmod := parameter_mod_four hp
  have hp2 := hprime.two_le
  omega

lemma parameter_product_lower {m : ℕ} {K : Finset ℕ}
    (hK : K ⊆ parameterUniverse m) :
    5 ^ K.card ≤ ∏ p ∈ K, p := by
  calc
    5 ^ K.card = ∏ _p ∈ K, 5 := by simp
    _ ≤ ∏ p ∈ K, p := by
      apply Finset.prod_le_prod'
      intro p hp
      exact five_le_parameter_prime (hK hp)

lemma parameter_product_upper {m : ℕ} {K : Finset ℕ}
    (hK : K ⊆ parameterUniverse m) :
    (∏ p ∈ K, p) ≤ (m ^ 2) ^ K.card := by
  exact finset_product_le_card_pow K id (m ^ 2)
    (fun p hp => parameter_prime_le (hK hp))

lemma parameter_numeric_base (m : ℕ) :
    (128 * 11520 ^ 2) * (m ^ 2) * (parameterH m) ^ 2 ≤
      4 * (parameterUniverse m).card ^ 2 := by
  have hdiv : parameterScale * m * parameterH m ≤ (parameterUniverse m).card := by
    simpa [parameterH, mul_comm, mul_left_comm, mul_assoc] using
      (Nat.div_mul_le_self (parameterUniverse m).card (parameterScale * m))
  have hs : 128 * 11520 ^ 2 = parameterScale := rfl
  rw [hs]
  have hscale : parameterScale ≤ 4 * parameterScale ^ 2 := by
    have := parameterScale_pos
    nlinarith
  calc
    parameterScale * m ^ 2 * parameterH m ^ 2
        ≤ (4 * parameterScale ^ 2) * m ^ 2 * parameterH m ^ 2 := by
      have := Nat.mul_le_mul_right (m ^ 2 * parameterH m ^ 2) hscale
      nlinarith
    _ = 4 * (parameterScale * m * parameterH m) ^ 2 := by ring
    _ ≤ 4 * (parameterUniverse m).card ^ 2 :=
      Nat.mul_le_mul_left 4 (Nat.pow_le_pow_left hdiv 2)

/-- The split-prime parameters satisfy every hypothesis of the finite extremal
construction for all sufficiently large `m`. -/
theorem eventually_exists_parameter_gap :
    ∃ M : ℕ, ∀ m ≥ M, ∃ N : ℕ,
      ((parameterUniverse m).powersetCard (parameterH m)).card * parameterQ m ≤ 1152 * N ∧
      N ≤ 5 * (((parameterUniverse m).powersetCard (parameterH m)).card * parameterQ m) ∧
      N * 2 ^ parameterH m ≤ 23040 * extremalGap N := by
  obtain ⟨M, hM⟩ := parameterH_eventually_ge 15
  refine ⟨M, fun m hm => ?_⟩
  let U := parameterUniverse m
  let h := parameterH m
  let Q := parameterQ m
  have hh15 : 15 ≤ h := hM m hm
  have hhU : h ≤ U.card := parameterH_le_card m
  apply finite_parameters_imply_extremal_gap U h Q (m ^ 2) hhU
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

end Erdos959
