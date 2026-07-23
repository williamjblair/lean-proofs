import Research.SmoothCoreIncidence
import Research.RayCutoff
import Mathlib.NumberTheory.EulerProduct.Basic

namespace Erdos796

open Filter Topology

/-- Completely multiplicative Rankin weight, with value zero at zero. -/
noncomputable def rankinWeight (σ : ℝ) (n : ℕ) : ℝ :=
  if n = 0 then 0 else (n : ℝ) ^ (-σ)

@[simp] lemma rankinWeight_zero (σ : ℝ) : rankinWeight σ 0 = 0 := by
  simp [rankinWeight]

@[simp] lemma rankinWeight_one (σ : ℝ) : rankinWeight σ 1 = 1 := by
  simp [rankinWeight]

lemma rankinWeight_mul (σ : ℝ) (m n : ℕ) :
    rankinWeight σ (m * n) = rankinWeight σ m * rankinWeight σ n := by
  by_cases hm : m = 0
  · simp [hm]
  by_cases hn : n = 0
  · simp [hn]
  simp only [rankinWeight, hm, hn, mul_ne_zero hm hn, if_false, Nat.cast_mul]
  exact Real.mul_rpow (by positivity) (by positivity)

lemma rankinWeight_prime_pow (σ : ℝ) {p : ℕ} (hp : p.Prime) (e : ℕ) :
    rankinWeight σ (p ^ e) = ((p : ℝ) ^ (-σ)) ^ e := by
  simp only [rankinWeight, pow_ne_zero e hp.ne_zero, if_false, Nat.cast_pow]
  calc
    (((p : ℝ) ^ e) : ℝ) ^ (-σ) =
        (((p : ℝ) ^ (e : ℝ)) : ℝ) ^ (-σ) := by rw [Real.rpow_natCast]
    _ = (p : ℝ) ^ ((e : ℝ) * (-σ)) :=
      (Real.rpow_mul (by positivity) (e : ℝ) (-σ)).symm
    _ = (p : ℝ) ^ ((-σ) * (e : ℝ)) := by congr 1; ring
    _ = (((p : ℝ) ^ (-σ)) : ℝ) ^ (e : ℝ) :=
      Real.rpow_mul (by positivity) (-σ) (e : ℝ)
    _ = ((p : ℝ) ^ (-σ)) ^ e := Real.rpow_natCast _ _

lemma rankinPrimeRatio_lt_one {σ : ℝ} (hσ : 0 < σ)
    {p : ℕ} (hp : p.Prime) :
    (p : ℝ) ^ (-σ) < 1 := by
  rw [Real.rpow_neg (by positivity)]
  exact inv_lt_one_of_one_lt₀ (Real.one_lt_rpow (by exact_mod_cast hp.one_lt) hσ)

lemma summable_rankinWeight_prime_pow {σ : ℝ} (hσ : 0 < σ)
    {p : ℕ} (hp : p.Prime) :
    Summable (fun e : ℕ => ‖rankinWeight σ (p ^ e)‖) := by
  have hr0 : 0 ≤ (p : ℝ) ^ (-σ) := Real.rpow_nonneg (by positivity) _
  have hr1 := rankinPrimeRatio_lt_one hσ hp
  have hs := summable_geometric_of_lt_one hr0 hr1
  apply hs.congr
  intro e
  rw [rankinWeight_prime_pow σ hp e, Real.norm_eq_abs,
    abs_of_nonneg (pow_nonneg hr0 e)]

/-- Exact finite Euler product for the Rankin weight over smooth numbers. -/
theorem rankinWeight_smooth_hasSum {σ : ℝ} (hσ : 0 < σ) (y : ℕ) :
    HasSum (fun m : (y + 1).smoothNumbers => rankinWeight σ m.1)
      (∏ p ∈ Nat.primesLE y, (1 - (p : ℝ) ^ (-σ))⁻¹) := by
  have he := (EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_tsum
    (f := rankinWeight σ) (rankinWeight_one σ)
    (fun {_m _n} _hcop => rankinWeight_mul σ _m _n)
    (fun {_p} hp => summable_rankinWeight_prime_pow hσ hp)
    (y + 1)).2
  have hprimes : (y + 1).primesBelow = Nat.primesLE y := by
    ext p
    simp only [Nat.mem_primesBelow, Nat.mem_primesLE]
    constructor <;> rintro ⟨h, hp⟩ <;> exact ⟨by omega, hp⟩
  rw [hprimes] at he
  have hprod : (∏ p ∈ Nat.primesLE y,
      ∑' e : ℕ, rankinWeight σ (p ^ e)) =
      ∏ p ∈ Nat.primesLE y, (1 - (p : ℝ) ^ (-σ))⁻¹ := by
    apply Finset.prod_congr rfl
    intro p hp
    have hp' := (Nat.mem_primesLE.mp hp).2
    rw [show (∑' e : ℕ, rankinWeight σ (p ^ e)) =
        ∑' e : ℕ, ((p : ℝ) ^ (-σ)) ^ e by
      apply tsum_congr
      intro e
      exact rankinWeight_prime_pow σ hp' e]
    exact tsum_geometric_of_norm_lt_one (by
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (by positivity) _)]
      exact rankinPrimeRatio_lt_one hσ hp')
  rw [hprod] at he
  exact he

/-- Rankin's finite smooth-number bound before estimating its Euler product. -/
theorem smoothNumbersUpTo_card_le_rankin
    {σ : ℝ} (hσ : 0 < σ) (X y : ℕ) (hX : 0 < X) :
    ((Nat.smoothNumbersUpTo X (y + 1)).card : ℝ) ≤
      (X : ℝ) ^ σ *
        ∏ p ∈ Nat.primesLE y, (1 - (p : ℝ) ^ (-σ))⁻¹ := by
  classical
  let A := Nat.smoothNumbersUpTo X (y + 1)
  let emb : ↥A ↪ (y + 1).smoothNumbers :=
    ⟨fun m => ⟨m.1, (Nat.mem_smoothNumbersUpTo.mp m.2).2⟩,
      fun a b h => by
        apply Subtype.ext
        exact congrArg (fun z : (y + 1).smoothNumbers => z.1) h⟩
  let B : Finset ((y + 1).smoothNumbers) := Finset.univ.map emb
  have hBcard : B.card = A.card := by simp [B]
  have hsmooth := rankinWeight_smooth_hasSum hσ y
  have hsumm : Summable (fun m : (y + 1).smoothNumbers =>
      rankinWeight σ m.1) := hsmooth.summable
  have hterm : ∀ m ∈ B, (1 : ℝ) ≤
      (X : ℝ) ^ σ * rankinWeight σ m.1 := by
    intro m hm
    rcases Finset.mem_map.mp hm with ⟨a, ha, rfl⟩
    have haX := (Nat.mem_smoothNumbersUpTo.mp a.2).1
    have ha0 := (Nat.mem_smoothNumbersUpTo.mp a.2).2.1
    have hapos : (0 : ℝ) < a.1 := by exact_mod_cast Nat.pos_of_ne_zero ha0
    have haXR : (a.1 : ℝ) ≤ (X : ℝ) := by exact_mod_cast haX
    have hpow := Real.rpow_le_rpow
      (by positivity : (0 : ℝ) ≤ (a.1 : ℝ)) haXR hσ.le
    change (1 : ℝ) ≤ (X : ℝ) ^ σ * rankinWeight σ a.1
    rw [rankinWeight, if_neg ha0, Real.rpow_neg (by positivity)]
    change (1 : ℝ) ≤ (X : ℝ) ^ σ / (a.1 : ℝ) ^ σ
    apply (le_div_iff₀ (Real.rpow_pos_of_pos hapos σ)).2
    simpa using hpow
  calc
    (A.card : ℝ) = ∑ _m ∈ B, (1 : ℝ) := by simp [hBcard]
    _ ≤ ∑ m ∈ B, (X : ℝ) ^ σ * rankinWeight σ m.1 :=
      Finset.sum_le_sum hterm
    _ = (X : ℝ) ^ σ * ∑ m ∈ B, rankinWeight σ m.1 := by
      rw [Finset.mul_sum]
    _ ≤ (X : ℝ) ^ σ * ∑' m : (y + 1).smoothNumbers,
        rankinWeight σ m.1 := by
      gcongr
      exact hsumm.sum_le_tsum B (by
        intro m hm
        unfold rankinWeight
        split_ifs <;> positivity)
    _ = _ := by rw [hsmooth.tsum_eq]

/-- Rankin exponent chosen just below one. -/
noncomputable def rankinSigma (y : ℕ) : ℝ :=
  1 - 1 / (2 * Real.log (y : ℝ))

/-- Reciprocal-prime mass is eventually at most twice `log log`. -/
theorem eventually_primeMass_le_two_loglog :
    ∀ᶠ y : ℕ in atTop,
      primeMass y ≤ 2 * Real.log (Real.log (y : ℝ)) := by
  have hres : Tendsto (fun y : ℕ => primeReciprocalResidual (y : ℝ))
      atTop (nhds Mertens.M) :=
    tendsto_primeReciprocalResidual.comp tendsto_natCast_atTop_atTop
  have hlog : Tendsto (fun y : ℕ => Real.log (y : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hll : Tendsto (fun y : ℕ => Real.log (Real.log (y : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp hlog
  have hresBound : ∀ᶠ y : ℕ in atTop,
      primeReciprocalResidual (y : ℝ) < Mertens.M + 1 :=
    hres.eventually (gt_mem_nhds (by linarith : Mertens.M < Mertens.M + 1))
  have hllBound : ∀ᶠ y : ℕ in atTop,
      Mertens.M + 1 ≤ Real.log (Real.log (y : ℝ)) :=
    hll.eventually (eventually_ge_atTop (Mertens.M + 1))
  filter_upwards [hresBound, hllBound] with y hr hl
  rw [primeMass_eq_residual]
  linarith

lemma rankinEulerFactor_le_exp {σ : ℝ} (hσ : (1 : ℝ) / 2 ≤ σ)
    {p : ℕ} (hp : p.Prime) :
    (1 - (p : ℝ) ^ (-σ))⁻¹ ≤
      Real.exp (4 * (p : ℝ) ^ (-σ)) := by
  let x : ℝ := (p : ℝ) ^ (-σ)
  have hpR : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hx0 : 0 ≤ x := by dsimp [x]; positivity
  have hxpos : 0 < x := by dsimp [x]; positivity
  have hx34 : x ≤ (3 : ℝ) / 4 := by
    have hinv : (0 : ℝ) < ((p : ℝ)⁻¹) := by positivity
    have hinv1 : (p : ℝ)⁻¹ ≤ 1 := (inv_le_one₀ (by positivity)).2 hpR.le
    have he1 : ((p : ℝ)⁻¹) ^ σ ≤ ((p : ℝ)⁻¹) ^ ((1 : ℝ) / 2) :=
      Real.rpow_le_rpow_of_exponent_ge hinv hinv1 hσ
    have hpInv : (p : ℝ)⁻¹ ≤ (2 : ℝ)⁻¹ := by
      exact inv_anti₀ (by norm_num) (by exact_mod_cast hp.two_le)
    have he2 : ((p : ℝ)⁻¹) ^ ((1 : ℝ) / 2) ≤
        ((2 : ℝ)⁻¹) ^ ((1 : ℝ) / 2) :=
      Real.rpow_le_rpow (by positivity) hpInv (by norm_num)
    have hs : ((2 : ℝ)⁻¹) ^ ((1 : ℝ) / 2) ≤ (3 : ℝ) / 4 := by
      rw [← Real.sqrt_eq_rpow]
      have hsq := Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ)⁻¹ by positivity)
      have hs0 := Real.sqrt_nonneg ((2 : ℝ)⁻¹)
      nlinarith
    dsimp [x]
    rw [Real.rpow_neg (by positivity), ← Real.inv_rpow (by positivity)]
    exact he1.trans (he2.trans hs)
  have hone : 0 < 1 - x := by linarith
  have hratio : (1 - x)⁻¹ - 1 ≤ 4 * x := by
    rw [show (1 - x)⁻¹ - 1 = x / (1 - x) by
      field_simp [ne_of_gt hone]
      <;> ring]
    apply (div_le_iff₀ hone).2
    nlinarith
  have hlog : Real.log ((1 - x)⁻¹) ≤ 4 * x :=
    (Real.log_le_sub_one_of_pos (by positivity)).trans hratio
  have hexp := (Real.exp_le_exp.mpr hlog)
  rw [Real.exp_log (by positivity)] at hexp
  exact hexp

lemma rankinPrimeWeight_le_three_div {y p : ℕ}
    (hylog : 0 < Real.log (y : ℝ)) (hp : p.Prime) (hpy : p ≤ y) :
    (p : ℝ) ^ (-rankinSigma y) ≤ 3 / (p : ℝ) := by
  let δ : ℝ := 1 / (2 * Real.log (y : ℝ))
  have hδ : 0 ≤ δ := by dsimp [δ]; positivity
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hyR : (0 : ℝ) < y := by
    have hyNat : 0 < y := by
      by_contra h
      have : y = 0 := Nat.eq_zero_of_not_pos h
      subst y
      norm_num at hylog
    exact_mod_cast hyNat
  have hpyR : (p : ℝ) ≤ (y : ℝ) := by exact_mod_cast hpy
  have hbase : (p : ℝ) ^ δ ≤ (y : ℝ) ^ δ :=
    Real.rpow_le_rpow (by positivity) hpyR hδ
  have hyδ : (y : ℝ) ^ δ < 3 := by
    rw [Real.rpow_def_of_pos hyR]
    have hexponent : Real.log (y : ℝ) * δ = (1 : ℝ) / 2 := by
      dsimp [δ]
      field_simp [ne_of_gt hylog]
      <;> ring
    rw [hexponent]
    exact (Real.exp_lt_exp.mpr (by norm_num : (1 : ℝ) / 2 < 1)).trans
      Real.exp_one_lt_three
  have hpδ : (p : ℝ) ^ δ ≤ 3 := hbase.trans hyδ.le
  have hexp : -rankinSigma y = (-1 : ℝ) + δ := by
    unfold rankinSigma
    dsimp [δ]
    ring
  rw [hexp, Real.rpow_add hpR, Real.rpow_neg hpR.le, Real.rpow_one,
    div_eq_mul_inv]
  have hinv0 : (0 : ℝ) ≤ (p : ℝ)⁻¹ := by positivity
  simpa [mul_comm] using mul_le_mul_of_nonneg_right hpδ hinv0

theorem rankinEulerProduct_le_exp_primeMass {y : ℕ}
    (hylog : 0 < Real.log (y : ℝ))
    (hhalf : (1 : ℝ) / 2 ≤ rankinSigma y) :
    (∏ p ∈ Nat.primesLE y,
        (1 - (p : ℝ) ^ (-rankinSigma y))⁻¹) ≤
      Real.exp (12 * primeMass y) := by
  calc
    (∏ p ∈ Nat.primesLE y,
        (1 - (p : ℝ) ^ (-rankinSigma y))⁻¹) ≤
        ∏ p ∈ Nat.primesLE y,
          Real.exp (4 * (p : ℝ) ^ (-rankinSigma y)) := by
      apply Finset.prod_le_prod
      · intro p hp
        have hp' := (Nat.mem_primesLE.mp hp).2
        have hspos : 0 < rankinSigma y := lt_of_lt_of_le (by norm_num) hhalf
        have hx := (rankinPrimeRatio_lt_one hspos hp').le
        exact inv_nonneg.mpr (sub_nonneg.mpr hx)
      · intro p hp
        exact rankinEulerFactor_le_exp hhalf (Nat.mem_primesLE.mp hp).2
    _ = Real.exp (∑ p ∈ Nat.primesLE y,
          4 * (p : ℝ) ^ (-rankinSigma y)) := by
      rw [Real.exp_sum]
    _ ≤ Real.exp (12 * primeMass y) := by
      apply Real.exp_le_exp.mpr
      unfold primeMass
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro p hp
      have hpMem := Nat.mem_primesLE.mp hp
      have hw := rankinPrimeWeight_le_three_div hylog hpMem.2 hpMem.1
      calc
        4 * (p : ℝ) ^ (-rankinSigma y) ≤ 4 * (3 / (p : ℝ)) :=
          mul_le_mul_of_nonneg_left hw (by norm_num)
        _ = 12 * (1 / (p : ℝ)) := by ring

lemma eventually_rankinSigma_half :
    ∀ᶠ y : ℕ in atTop, (1 : ℝ) / 2 ≤ rankinSigma y ∧
      0 < Real.log (y : ℝ) := by
  have hlog : Tendsto (fun y : ℕ => Real.log (y : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hlog.eventually (eventually_ge_atTop 2)] with y hy
  constructor
  · unfold rankinSigma
    have : 0 < Real.log (y : ℝ) := lt_of_lt_of_le (by norm_num) hy
    apply (le_sub_iff_add_le).2
    have hden : (0 : ℝ) < 2 * Real.log (y : ℝ) := by positivity
    have hfrac : 1 / (2 * Real.log (y : ℝ)) ≤ 1 / 2 := by
      apply one_div_le_one_div_of_le (by norm_num)
      linarith
    linarith
  · linarith

/-- The Euler factor in Rankin's bound grows only polynomially in `log y`. -/
theorem eventually_rankinEulerProduct_le_log_pow :
    ∀ᶠ y : ℕ in atTop,
      (∏ p ∈ Nat.primesLE y,
          (1 - (p : ℝ) ^ (-rankinSigma y))⁻¹) ≤
        (Real.log (y : ℝ)) ^ 24 := by
  filter_upwards [eventually_rankinSigma_half,
    eventually_primeMass_le_two_loglog] with y hy hmass
  have he := rankinEulerProduct_le_exp_primeMass hy.2 hy.1
  calc
    (∏ p ∈ Nat.primesLE y,
        (1 - (p : ℝ) ^ (-rankinSigma y))⁻¹) ≤
        Real.exp (12 * primeMass y) := he
    _ ≤ Real.exp (24 * Real.log (Real.log (y : ℝ))) := by
      apply Real.exp_le_exp.mpr
      linarith
    _ = (Real.log (y : ℝ)) ^ 24 := by
      have heq := Real.exp_nat_mul (Real.log (Real.log (y : ℝ))) 24
      rw [Real.exp_log hy.2] at heq
      simpa using heq

/-- Uniform Rankin estimate for smooth-number counts, with a fully explicit
polylogarithmic Euler-product loss. -/
theorem eventually_smoothNumbersUpTo_card_le_rankin_log_pow :
    ∀ᶠ y : ℕ in atTop, ∀ X : ℕ, 0 < X →
      ((Nat.smoothNumbersUpTo X (y + 1)).card : ℝ) ≤
        (X : ℝ) ^ rankinSigma y * (Real.log (y : ℝ)) ^ 24 := by
  filter_upwards [eventually_rankinSigma_half,
    eventually_rankinEulerProduct_le_log_pow] with y hy hprod
  intro X hX
  exact (smoothNumbersUpTo_card_le_rankin
      (lt_of_lt_of_le (by norm_num) hy.1) (X := X) (y := y) hX).trans
    (mul_le_mul_of_nonneg_left hprod (Real.rpow_nonneg (by positivity) _))

end Erdos796
