import Research.ParameterBounds

noncomputable section
open Filter Asymptotics
namespace Erdos959

lemma parameterH_upper_of_card_log
    {m : ℕ} (hm : 1 ≤ m)
    (hcard : ((parameterUniverse m).card : ℝ) * Real.log m ≤ 2 * (m : ℝ) ^ 2) :
    (parameterScale : ℝ) * parameterH m * Real.log m ≤ 2 * m := by
  have hdiv : parameterScale * m * parameterH m ≤ (parameterUniverse m).card := by
    simpa [parameterH, mul_comm, mul_left_comm, mul_assoc] using
      (Nat.div_mul_le_self (parameterUniverse m).card (parameterScale * m))
  have hdivR : (parameterScale : ℝ) * m * parameterH m ≤
      (parameterUniverse m).card := by exact_mod_cast hdiv
  have hlognonneg : 0 ≤ Real.log (m : ℝ) := Real.log_nonneg (by exact_mod_cast hm)
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have := mul_le_mul_of_nonneg_right hdivR hlognonneg
  nlinarith

lemma parameterH_lower_of_density
    {m : ℕ} (hm : 2 ≤ m) (hh : 1 ≤ parameterH m)
    (hdensity : (m : ℝ) ^ 2 / 4 ≤
      ((parameterUniverse m).card : ℝ) * Real.log ((m ^ 2 : ℕ) : ℝ)) :
    (m : ℝ) ≤ 16 * parameterScale * parameterH m * Real.log m := by
  have hdpos : 0 < parameterScale * m :=
    Nat.mul_pos parameterScale_pos (by omega)
  have hklt0 := Nat.lt_div_mul_add (a := (parameterUniverse m).card) hdpos
  have hklt : (parameterUniverse m).card <
      (parameterH m + 1) * (parameterScale * m) := by
    rw [parameterH]
    calc
      (parameterUniverse m).card <
          (parameterUniverse m).card / (parameterScale * m) *
            (parameterScale * m) + parameterScale * m := hklt0
      _ = ((parameterUniverse m).card / (parameterScale * m) + 1) *
            (parameterScale * m) := by ring
  have hkltR : ((parameterUniverse m).card : ℝ) <
      (parameterH m + 1) * (parameterScale * m) := by exact_mod_cast hklt
  have hlogpow : Real.log ((m ^ 2 : ℕ) : ℝ) = 2 * Real.log m := by
    push_cast
    rw [Real.log_pow]
    norm_num
  rw [hlogpow] at hdensity
  have hmlog : 0 < Real.log (m : ℝ) := Real.log_pos (by exact_mod_cast hm)
  have hmpos : (0 : ℝ) < m := by positivity
  have hhR : (1 : ℝ) ≤ parameterH m := by exact_mod_cast hh
  have hklog := mul_lt_mul_of_pos_right hkltR (by positivity : 0 < 2 * Real.log (m : ℝ))
  have hchain : (m : ℝ) ^ 2 / 4 <
      ((parameterH m : ℝ) + 1) * (parameterScale * m) *
        (2 * Real.log m) := hdensity.trans_lt (by simpa using hklog)
  have hplus : (parameterH m : ℝ) + 1 ≤ 2 * parameterH m := by nlinarith
  have hchain' : (m : ℝ) ^ 2 / 4 <
      (2 * parameterH m) * (parameterScale * m) * (2 * Real.log m) :=
    hchain.trans_le (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hplus (by positivity)) (by positivity))
  nlinarith

lemma parameterBlockCount_le_m_pow {m : ℕ} (hm : 2 ≤ m) :
    parameterBlockCount m ≤ m ^ (3 * parameterH m) := by
  have hsubset : parameterUniverse m ⊆ Finset.Iic (m ^ 2) := by
    intro p hp
    exact Finset.mem_Iic.mpr (parameter_prime_le hp)
  have hcard0 : (parameterUniverse m).card ≤ m ^ 2 + 1 := by
    simpa using Finset.card_le_card hsubset
  have hcard : (parameterUniverse m).card ≤ m ^ 3 := by
    have : m ^ 2 + 1 ≤ m ^ 3 := by nlinarith [Nat.zero_le m]
    exact hcard0.trans this
  calc
    parameterBlockCount m = (parameterUniverse m).card.choose (parameterH m) := by
      simp [parameterBlockCount]
    _ ≤ (parameterUniverse m).card ^ parameterH m :=
      Nat.choose_le_pow _ _
    _ ≤ (m ^ 3) ^ parameterH m :=
      Nat.pow_le_pow_left hcard _
    _ = m ^ (3 * parameterH m) := by rw [← pow_mul]

lemma parameter_minimum_product_le_m_pow {m : ℕ} (hm : 2 ≤ m) :
    parameterBlockCount m * parameterQ m ≤ m ^ (5 * parameterH m) := by
  calc
    parameterBlockCount m * parameterQ m ≤
        m ^ (3 * parameterH m) * (m ^ 2) ^ parameterH m :=
      Nat.mul_le_mul (parameterBlockCount_le_m_pow hm) le_rfl
    _ = m ^ (5 * parameterH m) := by
      rw [← pow_mul, ← pow_add]
      congr 1
      omega

/-- A local analytic criterion ensuring that the minimum replicated
construction fits inside `n`. -/
lemma parameter_minimum_fits
    {m n : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n)
    (hupper : (parameterScale : ℝ) * parameterH m * Real.log m ≤ 2 * m)
    (hmn : (m : ℝ) ≤ (parameterScale : ℝ) * Real.log n / 40)
    (hlog10 : Real.log 10 ≤ Real.log n / 4) :
    10 * parameterBlockCount m * parameterQ m ≤ n := by
  have hprod := parameter_minimum_product_le_m_pow hm
  have hprod10 : 10 * parameterBlockCount m * parameterQ m ≤
      10 * m ^ (5 * parameterH m) := by
    simpa [mul_assoc] using Nat.mul_le_mul_left 10 hprod
  apply hprod10.trans
  have hmpos : (0 : ℝ) < m := by positivity
  have hnpos : (0 : ℝ) < n := by positivity
  have hscaleR : (0 : ℝ) < parameterScale := by exact_mod_cast parameterScale_pos
  have hexpBound : Real.log 10 + (5 * parameterH m : ℕ) * Real.log m ≤ Real.log n := by
    have hfive : (5 : ℝ) * parameterH m * Real.log m ≤
        10 * (m : ℝ) / parameterScale := by
      have := hupper
      field_simp
      nlinarith
    have hmterm : 10 * (m : ℝ) / parameterScale ≤ Real.log n / 4 := by
      field_simp
      nlinarith
    have hlogn : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n))
    norm_num only [Nat.cast_mul, Nat.cast_ofNat]
    nlinarith
  have hlogpow : Real.log ((m ^ (5 * parameterH m) : ℕ) : ℝ) =
      (5 * parameterH m : ℕ) * Real.log m := by
    push_cast
    rw [Real.log_pow]
    norm_num only [Nat.cast_mul, Nat.cast_ofNat]
  have hlogprod : Real.log ((10 * m ^ (5 * parameterH m) : ℕ) : ℝ) ≤
      Real.log n := by
    norm_num only [Nat.cast_mul, Nat.cast_ofNat]
    rw [Real.log_mul (by norm_num : (10 : ℝ) ≠ 0)
      (by positivity : ((m ^ (5 * parameterH m) : ℕ) : ℝ) ≠ 0), hlogpow]
    exact hexpBound
  have hposprod : (0 : ℝ) < (10 * m ^ (5 * parameterH m) : ℕ) := by positivity
  have hreal : ((10 * m ^ (5 * parameterH m) : ℕ) : ℝ) ≤ n := by
    calc
      ((10 * m ^ (5 * parameterH m) : ℕ) : ℝ) =
          Real.exp (Real.log ((10 * m ^ (5 * parameterH m) : ℕ) : ℝ)) :=
        (Real.exp_log hposprod).symm
      _ ≤ Real.exp (Real.log n) := (Real.exp_le_exp.mpr hlogprod)
      _ = n := Real.exp_log hnpos
  exact_mod_cast hreal

end Erdos959
