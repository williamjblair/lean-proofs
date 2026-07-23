import Research.Profile40
import PrimeNumberTheoremAnd.Consequences
import PrimeNumberTheoremAnd.IEANTN.Mertens
import PrimeNumberTheoremAnd.IEANTN.RosserSchoenfeld.RosserSchoenfeldPrime

open Filter Asymptotics MeasureTheory intervalIntegral

namespace Erdos796

/-- Prime reciprocal sum through a real cutoff, minus `log log`. -/
noncomputable def primeReciprocalResidual (x : ℝ) : ℝ :=
  (∑ p ∈ Finset.Ioc 0 ⌊x⌋₊ with p.Prime, (1 : ℝ) / p) -
    Real.log (Real.log x)

/-- The prime reciprocal residual tends to the formal Meissel--Mertens
value supplied by PrimeNumberTheoremAnd. -/
theorem tendsto_primeReciprocalResidual :
    Tendsto primeReciprocalResidual atTop (nhds Mertens.M) := by
  have hE : Tendsto Mertens.E₂p atTop (nhds 0) :=
    (Asymptotics.isLittleO_one_iff ℝ).mp Mertens.E₂p.bound'
  have h := hE.const_add Mertens.M
  have heq : primeReciprocalResidual = fun x => Mertens.M + Mertens.E₂p x := by
    funext x
    unfold primeReciprocalResidual
    rw [Mertens.sum_prime_div_eq]
    ring
  rw [heq]
  simpa using h

/-- Pointwise bound for the integral error produced by the medium PNT. -/
lemma theta_error_integrand_bound {C t : ℝ} (hC : 0 ≤ C) (ht : 2 ≤ t)
    (hθ : |Chebyshev.theta t - t| ≤ C * t / Real.log t ^ 2) :
    |(Chebyshev.theta t - t) / (t * Real.log t ^ 2)| ≤
      (C / Real.log 2 ^ 2) * (1 / Real.log t ^ 2) := by
  have htpos : 0 < t := by linarith
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog : 0 < Real.log t := Real.log_pos (by linarith)
  have hlogle : Real.log 2 ≤ Real.log t := Real.log_le_log (by norm_num) ht
  rw [abs_div, abs_of_pos (mul_pos htpos (sq_pos_of_pos hlog))]
  calc
    |Chebyshev.theta t - t| / (t * Real.log t ^ 2)
        ≤ (C * t / Real.log t ^ 2) / (t * Real.log t ^ 2) :=
      div_le_div_of_nonneg_right hθ (by positivity)
    _ = (C / Real.log t ^ 2) * (1 / Real.log t ^ 2) := by field_simp
    _ ≤ (C / Real.log t ^ 2) * (1 / Real.log 2 ^ 2) := by gcongr
    _ = _ := by ring

/-- Pointwise endpoint bound for the medium-PNT error. -/
lemma theta_error_endpoint_bound {C x : ℝ} (hC : 0 ≤ C) (hx : 2 ≤ x)
    (hθ : |Chebyshev.theta x - x| ≤ C * x / Real.log x ^ 2) :
    |(Chebyshev.theta x - x) / Real.log x| ≤
      (C / Real.log 2) * |x / Real.log x ^ 2| := by
  have hxpos : 0 < x := by linarith
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog : 0 < Real.log x := Real.log_pos (by linarith)
  have hlogle : Real.log 2 ≤ Real.log x := Real.log_le_log (by norm_num) hx
  rw [abs_div, abs_of_pos hlog, abs_of_pos (div_pos hxpos (sq_pos_of_pos hlog))]
  calc
    |Chebyshev.theta x - x| / Real.log x
        ≤ (C * x / Real.log x ^ 2) / Real.log x :=
      div_le_div_of_nonneg_right hθ hlog.le
    _ = (C / Real.log x) * (x / Real.log x ^ 2) := by field_simp
    _ ≤ (C / Real.log 2) * (x / Real.log x ^ 2) := by gcongr

set_option maxHeartbeats 1000000 in
/-- Uniform PNT estimate strong enough to sum over all complementary prime
factors through `sqrt n`. -/
theorem primeCounting_sub_main_isBigO :
    (fun x : ℝ => (Nat.primeCounting ⌊x⌋₊ : ℝ) - x / Real.log x) =O[atTop]
      (fun x : ℝ => x / Real.log x ^ 2) := by
  obtain ⟨C, hC, htheta⟩ := RS_prime.pnt
  obtain ⟨D, hDpos, hD⟩ :=
    (isBigO_iff'.mp Chebyshev.integral_one_div_log_sq_isBigO)
  rw [isBigO_iff']
  let K : ℝ := C / Real.log 2
  let F : ℝ := C / Real.log 2 ^ 2
  refine ⟨K + (1 + F) * D, ?_, ?_⟩
  · have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
    dsimp [K, F]
    positivity
  filter_upwards [hD, eventually_ge_atTop 2] with x hIx hx
  have hxpos : 0 < x := by linarith
  have hlog : 0 < Real.log x := Real.log_pos (by linarith)
  have hbase : IntervalIntegrable (fun t : ℝ => 1 / Real.log t ^ 2) volume 2 x := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hx]
    fun_prop (disch := simp_all; grind)
  have hthetaInt : IntervalIntegrable
      (fun t : ℝ => Chebyshev.theta t / (t * Real.log t ^ 2)) volume 2 x := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hx]
    exact Chebyshev.integrableOn_theta_div_id_mul_log_sq x
  have herr : IntervalIntegrable
      (fun t : ℝ => (Chebyshev.theta t - t) / (t * Real.log t ^ 2)) volume 2 x := by
    apply (hthetaInt.sub hbase).congr
    intro t ht
    have ht' : 2 < t ∧ t ≤ x := by simpa [Set.uIoc_of_le hx] using ht
    have ht0 : t ≠ 0 := by linarith
    have hlt : Real.log t ≠ 0 := by
      exact Real.log_ne_zero_of_pos_of_ne_one (by linarith) (by linarith)
    field_simp
  have hdecomp :
      (Nat.primeCounting ⌊x⌋₊ : ℝ) - x / Real.log x =
        (Chebyshev.theta x - x) / Real.log x +
          (∫ t : ℝ in 2..x, 1 / Real.log t ^ 2) +
          ∫ t : ℝ in 2..x,
            (Chebyshev.theta t - t) / (t * Real.log t ^ 2) := by
    change pi x - x / Real.log x = _
    rw [RS_prime.eq_417 hx]
    have hsplit : (∫ t : ℝ in 2..x,
        Chebyshev.theta t / (t * Real.log t ^ 2)) =
        (∫ t : ℝ in 2..x, 1 / Real.log t ^ 2) +
        ∫ t : ℝ in 2..x,
          (Chebyshev.theta t - t) / (t * Real.log t ^ 2) := by
      rw [← intervalIntegral.integral_add hbase herr]
      apply intervalIntegral.integral_congr
      intro t ht
      have ht' : t ∈ Set.Icc 2 x := by simpa [Set.uIcc_of_le hx] using ht
      have ht0 : t ≠ 0 := by linarith [ht'.1]
      have hlt : Real.log t ≠ 0 :=
        Real.log_ne_zero_of_pos_of_ne_one (by linarith [ht'.1]) (by linarith [ht'.1])
      field_simp
      ring
    rw [hsplit]
    field_simp
    ring
  have hI_nonneg : 0 ≤ ∫ t : ℝ in 2..x, 1 / Real.log t ^ 2 := by
    apply intervalIntegral.integral_nonneg hx
    intro t ht
    positivity
  have hF : 0 ≤ F := by dsimp [F]; positivity
  have hgbound : IntervalIntegrable
      (fun t : ℝ => F * (1 / Real.log t ^ 2)) volume 2 x := hbase.const_mul F
  have hJ : |∫ t : ℝ in 2..x,
      (Chebyshev.theta t - t) / (t * Real.log t ^ 2)| ≤
      F * (∫ t : ℝ in 2..x, 1 / Real.log t ^ 2) := by
    rw [← Real.norm_eq_abs]
    calc
      _ ≤ ∫ t : ℝ in 2..x, F * (1 / Real.log t ^ 2) := by
        apply intervalIntegral.norm_integral_le_of_norm_le hx
        · filter_upwards with t ht
          have ht2 : 2 ≤ t := le_of_lt ht.1
          rw [Real.norm_eq_abs]
          change |(Chebyshev.theta t - t) / (t * Real.log t ^ 2)| ≤
            (C / Real.log 2 ^ 2) * (1 / Real.log t ^ 2)
          exact theta_error_integrand_bound hC ht2 (htheta t ht2)
        · exact hgbound
      _ = _ := intervalIntegral.integral_const_mul F _
  rw [hdecomp]
  calc
    |(Chebyshev.theta x - x) / Real.log x +
          (∫ t : ℝ in 2..x, 1 / Real.log t ^ 2) +
          ∫ t : ℝ in 2..x,
            (Chebyshev.theta t - t) / (t * Real.log t ^ 2)|
      ≤ |(Chebyshev.theta x - x) / Real.log x| +
          |∫ t : ℝ in 2..x, 1 / Real.log t ^ 2| +
          |∫ t : ℝ in 2..x,
            (Chebyshev.theta t - t) / (t * Real.log t ^ 2)| := abs_add_three _ _ _
    _ ≤ K * |x / Real.log x ^ 2| +
          (1 + F) * |∫ t : ℝ in 2..x, 1 / Real.log t ^ 2| := by
      rw [abs_of_nonneg hI_nonneg]
      have he := theta_error_endpoint_bound hC hx (htheta x hx)
      dsimp [K]
      linarith
    _ ≤ (K + (1 + F) * D) * |x / Real.log x ^ 2| := by
      have h1F : 0 ≤ 1 + F := by positivity
      rw [abs_of_nonneg hI_nonneg]
      have hIx' : (∫ t : ℝ in 2..x, 1 / Real.log t ^ 2) ≤
          D * |x / Real.log x ^ 2| := by
        simpa only [Real.norm_eq_abs, abs_of_nonneg hI_nonneg] using hIx
      calc
        K * |x / Real.log x ^ 2| +
            (1 + F) * (∫ t : ℝ in 2..x, 1 / Real.log t ^ 2)
          ≤ K * |x / Real.log x ^ 2| +
            (1 + F) * (D * |x / Real.log x ^ 2|) := by
          gcongr
        _ = _ := by ring

/-- Prime counts at every fixed reciprocal dilation, normalized at the
original scale. -/
theorem tendsto_primeCounting_div_normalization (j : ℕ) (hj : 0 < j) :
    Tendsto (fun n : ℕ =>
      (Nat.primeCounting (n / j) : ℝ) /
        ((n : ℝ) / Real.log (n : ℝ))) atTop
      (nhds ((1 : ℝ) / j)) := by
  have hjR : (0 : ℝ) < (j : ℝ) := by exact_mod_cast hj
  have hscale : Tendsto (fun n : ℕ => (n : ℝ) / (j : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_div_const hjR
  have hpi0 := pi_alt'.comp_tendsto hscale
  have hleft : ((fun x : ℝ => (Nat.primeCounting ⌊x⌋₊ : ℝ)) ∘
      fun n : ℕ => (n : ℝ) / (j : ℝ)) =
      fun n : ℕ => (Nat.primeCounting (n / j) : ℝ) := by
    funext n
    rw [Function.comp_apply, Nat.floor_div_natCast]
    simp
  have hpi : (fun n : ℕ => (Nat.primeCounting (n / j) : ℝ)) ~[atTop]
      (fun n : ℕ => ((n : ℝ) / (j : ℝ)) /
        Real.log ((n : ℝ) / (j : ℝ))) := by
    rw [← hleft]
    exact hpi0
  have hden_ne : ∀ᶠ n : ℕ in atTop,
      ((n : ℝ) / (j : ℝ)) / Real.log ((n : ℝ) / (j : ℝ)) ≠ 0 := by
    filter_upwards [eventually_gt_atTop j] with n hn
    have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (lt_trans hj hn)
    have hx : (1 : ℝ) < (n : ℝ) / (j : ℝ) := by
      rw [one_lt_div hjR]
      exact_mod_cast hn
    exact div_ne_zero (div_ne_zero (ne_of_gt hnR) (ne_of_gt hjR))
      (Real.log_ne_zero_of_pos_of_ne_one (by positivity) (ne_of_gt hx))
  rw [isEquivalent_iff_tendsto_one hden_ne] at hpi
  have hpi' : Tendsto (fun n : ℕ =>
      (Nat.primeCounting (n / j) : ℝ) /
        (((n : ℝ) / (j : ℝ)) / Real.log ((n : ℝ) / (j : ℝ))))
      atTop (nhds 1) := by
    exact hpi
  have hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hsmall : Tendsto (fun n : ℕ => Real.log (j : ℝ) / Real.log (n : ℝ))
      atTop (nhds 0) := hlog.const_div_atTop _
  have hratio : Tendsto (fun n : ℕ =>
      Real.log (n : ℝ) / Real.log ((n : ℝ) / (j : ℝ))) atTop (nhds 1) := by
    have hone : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1) := tendsto_const_nhds
    have haux := (hone.sub hsmall).inv₀ (by norm_num : (1 : ℝ) - 0 ≠ 0)
    have heq : (fun n : ℕ => (1 - Real.log (j : ℝ) /
        Real.log (n : ℝ))⁻¹) =ᶠ[atTop]
        (fun n : ℕ => Real.log (n : ℝ) /
          Real.log ((n : ℝ) / (j : ℝ))) := by
      filter_upwards [eventually_gt_atTop j] with n hn
      have hn1 : 1 < n := by omega
      have hn0 : (n : ℝ) ≠ 0 := by
        exact_mod_cast (ne_of_gt (lt_trans Nat.zero_lt_one hn1))
      have hln : Real.log (n : ℝ) ≠ 0 := by
        apply Real.log_ne_zero_of_pos_of_ne_one (by positivity)
        exact_mod_cast (ne_of_gt hn1)
      rw [Real.log_div hn0 (ne_of_gt hjR)]
      field_simp
    simpa using haux.congr' heq
  have hmiddle : Tendsto (fun n : ℕ =>
      (((n : ℝ) / (j : ℝ)) / Real.log ((n : ℝ) / (j : ℝ))) /
        ((n : ℝ) / Real.log (n : ℝ))) atTop (nhds ((1 : ℝ) / j)) := by
    have h := hratio.const_mul ((1 : ℝ) / j)
    have h' : Tendsto (fun n : ℕ => ((1 : ℝ) / j) *
        (Real.log (n : ℝ) / Real.log ((n : ℝ) / (j : ℝ))))
        atTop (nhds ((1 : ℝ) / j)) := by simpa using h
    apply h'.congr'
    filter_upwards [eventually_gt_atTop j] with n hn
    have hn1 : 1 < n := by omega
    have hn0 : (n : ℝ) ≠ 0 := by
      exact_mod_cast (ne_of_gt (lt_trans Nat.zero_lt_one hn1))
    have hln : Real.log (n : ℝ) ≠ 0 := by
      apply Real.log_ne_zero_of_pos_of_ne_one (by positivity)
      exact_mod_cast (ne_of_gt hn1)
    have hx : (1 : ℝ) < (n : ℝ) / (j : ℝ) := by
      rw [one_lt_div hjR]
      exact_mod_cast hn
    have hld : Real.log ((n : ℝ) / (j : ℝ)) ≠ 0 :=
      Real.log_ne_zero_of_pos_of_ne_one (by positivity) (ne_of_gt hx)
    field_simp
  have hmul := hpi'.mul hmiddle
  have hmul' : Tendsto
      (fun n =>
        ((Nat.primeCounting (n / j) : ℝ) /
          (((n : ℝ) / (j : ℝ)) / Real.log ((n : ℝ) / (j : ℝ)))) *
        ((((n : ℝ) / (j : ℝ)) / Real.log ((n : ℝ) / (j : ℝ))) /
          ((n : ℝ) / Real.log (n : ℝ))))
      atTop (nhds ((1 : ℝ) / j)) := by simpa using hmul
  apply hmul'.congr'
  filter_upwards [hden_ne, eventually_gt_atTop j] with n ha hn
  have hn1 : 1 < n := by omega
  have hn0 : (n : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (lt_trans Nat.zero_lt_one hn1))
  have hln : Real.log (n : ℝ) ≠ 0 := by
    apply Real.log_ne_zero_of_pos_of_ne_one (by positivity)
    exact_mod_cast (ne_of_gt hn1)
  have hld : Real.log ((n : ℝ) / (j : ℝ)) ≠ 0 := by
    intro h
    apply ha
    rw [h]
    simp
  field_simp

/-- Prime counts only through `sqrt n` are negligible at the `n / log n`
scale. -/
theorem tendsto_primeCounting_sqrt_div_normalization :
    Tendsto (fun n : ℕ =>
      (Nat.primeCounting n.sqrt : ℝ) /
        ((n : ℝ) / Real.log (n : ℝ))) atTop (nhds 0) := by
  have h1 : Tendsto (fun x : ℝ => Real.log x / Real.sqrt x) atTop (nhds 0) := by
    simpa [Real.sqrt_eq_rpow] using
      (Real.tendsto_pow_log_div_pow_atTop ((1 : ℝ) / 2) 1 (by norm_num))
  have h2 : Tendsto (fun x : ℝ => Real.log x / x) atTop (nhds 0) := by
    simpa using (Real.tendsto_pow_log_div_pow_atTop 1 1 (by norm_num))
  have hreal : Tendsto (fun x : ℝ =>
      (Real.sqrt x + 1) * Real.log x / x) atTop (nhds 0) := by
    have h := h1.add h2
    have heq : (fun x : ℝ => Real.log x / Real.sqrt x + Real.log x / x) =ᶠ[atTop]
        (fun x : ℝ => (Real.sqrt x + 1) * Real.log x / x) := by
      filter_upwards [eventually_gt_atTop 0] with x hx
      field_simp [Real.sqrt_ne_zero'.mpr hx]
      ring_nf
      rw [Real.sq_sqrt hx.le]
      ring
    simpa using h.congr' heq
  have hbound : Tendsto (fun n : ℕ =>
      ((n.sqrt : ℝ) + 1) * Real.log (n : ℝ) / (n : ℝ)) atTop (nhds 0) := by
    apply squeeze_zero' (g := fun n : ℕ =>
      (Real.sqrt (n : ℝ) + 1) * Real.log (n : ℝ) / (n : ℝ))
    · filter_upwards [eventually_gt_atTop 1] with n hn
      positivity
    · filter_upwards [eventually_gt_atTop 1] with n hn
      have hs := Real.nat_sqrt_le_real_sqrt (a := n)
      apply div_le_div_of_nonneg_right _ (by positivity)
      apply mul_le_mul_of_nonneg_right _
        (Real.log_nonneg (by exact_mod_cast (le_of_lt hn)))
      linarith
    · exact hreal.comp tendsto_natCast_atTop_atTop
  apply squeeze_zero' (g := fun n : ℕ =>
    ((n.sqrt : ℝ) + 1) * Real.log (n : ℝ) / (n : ℝ))
  · filter_upwards [eventually_gt_atTop 1] with n hn
    positivity
  · filter_upwards [eventually_gt_atTop 1] with n hn
    have hnR : (0 : ℝ) < (n : ℝ) := by positivity
    have hlog : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn)
    have hpi : Nat.primeCounting n.sqrt ≤ n.sqrt + 1 := by
      unfold Nat.primeCounting
      exact Nat.count_le Nat.Prime
    rw [div_div_eq_mul_div]
    apply div_le_div_of_nonneg_right _ hnR.le
    apply mul_le_mul_of_nonneg_right _ hlog.le
    exact_mod_cast hpi
  · exact hbound

/-- Labels above `sqrt n` whose available core capacity is at least `c`. -/
def capacityLabels (n c : ℕ) : Finset ℕ :=
  (sqrtPrimeLabels n).filter fun q => c ≤ n / q

/-- Capacity-at-least-`c` labels are exactly primes at most `n/c`, with all
primes through `sqrt n` removed. -/
theorem capacityLabels_eq (n c : ℕ) (hc : 0 < c) :
    capacityLabels n c = Nat.primesLE (n / c) \ Nat.primesLE n.sqrt := by
  ext q
  simp only [capacityLabels, Finset.mem_filter, sqrtPrimeLabels,
    Finset.mem_Icc, Nat.mem_primesLE, Finset.mem_sdiff]
  constructor
  · rintro ⟨⟨⟨hqlower, hqn⟩, hqprime⟩, hcap⟩
    have hmul : q * c ≤ n := by
      simpa [Nat.mul_comm] using (Nat.le_div_iff_mul_le hqprime.pos).mp hcap
    have hqupper : q ≤ n / c := (Nat.le_div_iff_mul_le hc).mpr hmul
    exact ⟨⟨hqupper, hqprime⟩, by omega⟩
  · rintro ⟨⟨hqupper, hqprime⟩, hnot⟩
    have hqn : q ≤ n := le_trans hqupper (Nat.div_le_self n c)
    have hqlower : n.sqrt + 1 ≤ q := by
      simp only [not_and_or, not_le] at hnot
      rcases hnot with h | h
      · omega
      · exact (h hqprime).elim
    have hmul : q * c ≤ n := (Nat.le_div_iff_mul_le hc).mp hqupper
    have hcap : c ≤ n / q := by
      apply (Nat.le_div_iff_mul_le hqprime.pos).mpr
      simpa [Nat.mul_comm] using hmul
    exact ⟨⟨⟨hqlower, hqn⟩, hqprime⟩, hcap⟩

/-- Exact cardinality of the capacity-at-least label set once its upper cutoff
lies above `sqrt n`. -/
theorem capacityLabels_card (n c : ℕ) (hc : 0 < c) (hs : n.sqrt ≤ n / c) :
    (capacityLabels n c).card =
      Nat.primeCounting (n / c) - Nat.primeCounting n.sqrt := by
  rw [capacityLabels_eq n c hc]
  rw [Finset.card_sdiff_of_subset (Nat.primesLE_mono hs)]
  simp

/-- For every fixed positive capacity, its label layer has normalized mass
`1/c`. -/
theorem tendsto_capacityLabels_card_div_normalization (c : ℕ) (hc : 0 < c) :
    Tendsto (fun n : ℕ =>
      ((capacityLabels n c).card : ℝ) /
        ((n : ℝ) / Real.log (n : ℝ))) atTop
      (nhds ((1 : ℝ) / c)) := by
  have hs : ∀ᶠ n : ℕ in atTop, n.sqrt ≤ n / c := by
    filter_upwards [eventually_ge_atTop (c * c)] with n hn
    have hcs : c ≤ n.sqrt := Nat.le_sqrt.mpr hn
    apply (Nat.le_div_iff_mul_le hc).mpr
    calc
      n.sqrt * c ≤ n.sqrt * n.sqrt := Nat.mul_le_mul_left _ hcs
      _ ≤ n := Nat.sqrt_le n
  have hmain := (tendsto_primeCounting_div_normalization c hc).sub
    tendsto_primeCounting_sqrt_div_normalization
  have hmain' : Tendsto (fun n : ℕ =>
      (Nat.primeCounting (n / c) : ℝ) /
          ((n : ℝ) / Real.log (n : ℝ)) -
        (Nat.primeCounting n.sqrt : ℝ) /
          ((n : ℝ) / Real.log (n : ℝ))) atTop
      (nhds ((1 : ℝ) / c)) := by simpa using hmain
  apply hmain'.congr'
  filter_upwards [hs, eventually_gt_atTop 1] with n hsn hn
  rw [capacityLabels_card n c hc hsn, Nat.cast_sub
    (Nat.monotone_primeCounting hsn)]
  ring

/-- Successive cardinal increment in the certified cutoff-40 profile. -/
def fiberDelta40 (i : Fin 40) : ℕ :=
  if h : i.val = 0 then (fiberType40 i).card
  else (fiberType40 i).card -
    (fiberType40 ⟨i.val - 1, by omega⟩).card

/-- Every cutoff-40 fiber cardinality is the sum of its successive
increments. -/
theorem fiberType40_card_telescope (k : Fin 40) :
    (fiberType40 k).card =
      ∑ i : Fin 40, if i.val ≤ k.val then fiberDelta40 i else 0 := by
  fin_cases k <;> native_decide

/-- The base cardinality at capacity `J` is the sum of precisely the first
`J` profile increments, capped at 40. -/
theorem fiberType40_base_card_telescope (J : ℕ) (hJ : 0 < J) :
    (certifiedProfile40.base J).card =
      ∑ i : Fin 40, if i.val + 1 ≤ J then fiberDelta40 i else 0 := by
  rw [show (certifiedProfile40.base J).card =
      (fiberType40 ⟨min (J - 1) 39, by omega⟩).card from rfl]
  rw [fiberType40_card_telescope]
  apply Finset.sum_congr rfl
  intro i hi
  have heq : i.val ≤ min (J - 1) 39 ↔ i.val + 1 ≤ J := by
    simp only [Nat.le_min]
    constructor
    · omega
    · exact fun h => ⟨by omega, by omega⟩
  simp only [heq]

/-- Total incidence count from the finite base part of profile 40. -/
def profile40BaseCount (n : ℕ) : ℕ :=
  ∑ q ∈ sqrtPrimeLabels n, (certifiedProfile40.base (n / q)).card

/-- Exact layer-cake expression for the profile-40 base incidence count. -/
theorem profile40BaseCount_eq (n : ℕ) :
    profile40BaseCount n =
      ∑ i : Fin 40, fiberDelta40 i *
        (capacityLabels n (i.val + 1)).card := by
  unfold profile40BaseCount
  have hJ : ∀ q ∈ sqrtPrimeLabels n, 0 < n / q := by
    intro q hq
    have hq' := Finset.mem_filter.mp hq
    exact Nat.div_pos (Finset.mem_Icc.mp hq'.1).2 hq'.2.pos
  calc
    _ = ∑ q ∈ sqrtPrimeLabels n,
        ∑ i : Fin 40, if i.val + 1 ≤ n / q then fiberDelta40 i else 0 := by
      apply Finset.sum_congr rfl
      intro q hq
      have hJq : 0 < n / q := hJ q hq
      exact fiberType40_base_card_telescope (n / q) hJq
    _ = ∑ i : Fin 40,
        ∑ q ∈ sqrtPrimeLabels n,
          if i.val + 1 ≤ n / q then fiberDelta40 i else 0 := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i hi
      simp only [capacityLabels, Finset.card_filter, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q hq
      split_ifs <;> simp

/-- The incremental layer-cake objective equals the original weighted profile
objective exactly. -/
theorem fiberDelta40_beta_value :
    (∑ i : Fin 40, (fiberDelta40 i : ℚ) / (i.val + 1 : ℕ)) =
      ∑ i : Fin 40, fiberWeight40 i * (fiberType40 i).card := by
  native_decide

/-- The profile-40 base incidence count has normalized limit equal to its
finite layer objective. -/
theorem tendsto_profile40BaseCount_div_normalization :
    Tendsto (fun n : ℕ =>
      (profile40BaseCount n : ℝ) /
        ((n : ℝ) / Real.log (n : ℝ))) atTop
      (nhds (∑ i : Fin 40, (fiberDelta40 i : ℝ) /
        (i.val + 1 : ℕ))) := by
  have hi : ∀ i : Fin 40, Tendsto (fun n : ℕ =>
      (fiberDelta40 i : ℝ) *
        (((capacityLabels n (i.val + 1)).card : ℝ) /
          ((n : ℝ) / Real.log (n : ℝ)))) atTop
      (nhds ((fiberDelta40 i : ℝ) * ((1 : ℝ) / (i.val + 1 : ℕ)))) := by
    intro i
    exact (tendsto_capacityLabels_card_div_normalization
      (i.val + 1) (by omega)).const_mul _
  have hsum := tendsto_finsetSum Finset.univ (fun i _ => hi i)
  have hsum' : Tendsto (fun n : ℕ =>
      ∑ i : Fin 40, (fiberDelta40 i : ℝ) *
        (((capacityLabels n (i.val + 1)).card : ℝ) /
          ((n : ℝ) / Real.log (n : ℝ)))) atTop
      (nhds (∑ i : Fin 40, (fiberDelta40 i : ℝ) /
        (i.val + 1 : ℕ))) := by
    simpa [div_eq_mul_inv] using hsum
  apply hsum'.congr'
  filter_upwards with n
  rw [profile40BaseCount_eq]
  push_cast
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i hi
  ring

end Erdos796

