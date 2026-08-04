import ResearchPNT.ParameterChoice
import Research.LowerRecurrence

/-! # Lower prime counts for the compatible-prime recurrence -/

open Filter Asymptotics Real Chebyshev

namespace ResearchPNT

/-- A prime-interval lower bound from endpoint errors for theta. -/
theorem sub_theta_error_div_log_le_card_prime_Ioc
    (u v : ℕ) (Eu Ev : ℝ) (huv : u ≤ v) (hv : 2 ≤ v)
    (hEu : |Chebyshev.theta u - u| ≤ Eu)
    (hEv : |Chebyshev.theta v - v| ≤ Ev) :
    ((v : ℝ) - u - Eu - Ev) / Real.log v ≤
      (((Finset.Ioc u v).filter Nat.Prime).card : ℝ) := by
  have hvpos : (0 : ℝ) < v := by positivity
  have hlogpos : 0 < Real.log (v : ℝ) :=
    Real.log_pos (by exact_mod_cast hv)
  rw [div_le_iff₀ hlogpos]
  calc
    (v : ℝ) - u - Eu - Ev ≤ Chebyshev.theta v - Chebyshev.theta u := by
      rw [abs_le] at hEu hEv
      linarith
    _ = ∑ p ∈ (Finset.Ioc u v).filter Nat.Prime, Real.log p :=
      theta_sub_theta_eq_sum_Ioc u v huv
    _ ≤ ∑ _p ∈ (Finset.Ioc u v).filter Nat.Prime, Real.log v := by
      apply Finset.sum_le_sum
      intro p hp
      rw [Finset.mem_filter, Finset.mem_Ioc] at hp
      exact Real.log_le_log (by exact_mod_cast hp.2.pos)
        (by exact_mod_cast hp.1.2)
    _ = (((Finset.Ioc u v).filter Nat.Prime).card : ℝ) * Real.log v := by
      simp

/-- The logarithmic gain from dividing the prime-search endpoint by
`m≥2` absorbs a theta-PNT error and the floor loss.  This lemma isolates the
exact elementary budget needed for a unit-coefficient lower recurrence. -/
theorem primeCounting_floor_div_ge_main_term
    (C : ℝ) (N m : ℕ) (hm : 0 < m) (hq : 2 ≤ N / m)
    (hN : 1 < N) (hlogm : 0 < Real.log (m : ℝ))
    (htheta : |Chebyshev.theta ((N / m : ℕ) : ℝ) - (N / m : ℕ)| ≤
      C * ((N / m : ℕ) / Real.log (N / m : ℕ) ^ 2))
    (hbudget : 1 + C * ((N / m : ℕ) /
        Real.log (N / m : ℕ) ^ 2) ≤
      ((N : ℝ) / m) * Real.log m / Real.log N) :
    (N : ℝ) / ((m : ℝ) * Real.log N) ≤
      (Nat.primeCounting (N / m) : ℝ) := by
  let q := N / m
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hqR : (0 : ℝ) < q := by positivity
  have hlogN : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast hN)
  have hlogq : 0 < Real.log (q : ℝ) :=
    Real.log_pos (by exact_mod_cast hq)
  have hqm : q * m ≤ N := Nat.div_mul_le_self N m
  have hlogqm : Real.log (q : ℝ) + Real.log (m : ℝ) ≤ Real.log N := by
    rw [← Real.log_mul (ne_of_gt hqR) (ne_of_gt hmR)]
    exact Real.log_le_log (by positivity) (by exact_mod_cast hqm)
  have hfloor : (N : ℝ) / m - 1 < q := by
    have hlt := Nat.lt_mul_div_succ N hm
    have hltR : (N : ℝ) < (m : ℝ) * (q + 1 : ℕ) := by exact_mod_cast hlt
    norm_num only [Nat.cast_add, Nat.cast_one] at hltR
    apply (sub_lt_iff_lt_add).mpr
    apply (div_lt_iff₀ hmR).mpr
    nlinarith
  rw [abs_le] at htheta
  have hthetaLower : (q : ℝ) -
      C * ((q : ℝ) / Real.log q ^ 2) ≤ Chebyshev.theta q := by
    linarith [htheta.1]
  have htargetTheta :
      ((N : ℝ) / (m * Real.log N)) * Real.log q ≤
        Chebyshev.theta q := by
    calc
      ((N : ℝ) / (m * Real.log N)) * Real.log q ≤
          (N : ℝ) / m - ((N : ℝ) / m) * Real.log m / Real.log N := by
        apply (le_sub_iff_add_le).mpr
        rw [div_mul_eq_mul_div, div_mul_eq_mul_div]
        field_simp [ne_of_gt hmR, ne_of_gt hlogN]
        nlinarith
      _ ≤ (q : ℝ) - C * ((q : ℝ) / Real.log q ^ 2) := by
        dsimp [q] at hbudget ⊢
        linarith
      _ ≤ Chebyshev.theta q := hthetaLower
  have hthetaCount : Chebyshev.theta (q : ℝ) ≤
      (Nat.primeCounting q : ℝ) * Real.log q :=
    (Chebyshev.theta_le_psi (q : ℝ)).trans
      (Chebyshev.psi_le_primeCounting_mul_log q)
  apply le_of_mul_le_mul_right _ hlogq
  simpa [q] using (le_trans htargetTheta hthetaCount)

/-- A conservative logarithmic cutoff for the lower recurrence. -/
def lowerY (N : ℕ) : ℕ := Nat.log (65536 ^ 2) N

/-- Uniformly for `2≤m≤lowerY N`, the gain from `log(N/m)<log N`
eventually absorbs both the floor and clean theta-PNT errors.  Crucially, the
coefficient of the main term is exactly one. -/
theorem eventually_primeCounting_floor_div_ge_main :
    ∀ᶠ N : ℕ in atTop, ∀ m : ℕ, 2 ≤ m → m ≤ lowerY N →
      (N : ℝ) / ((m : ℝ) * Real.log N) ≤
        (Nat.primeCounting (N / m) : ℝ) := by
  obtain ⟨C, hC, X, hX, htheta⟩ := exists_theta_error_bound
  have hlogTend : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlogSq : (fun N : ℕ => Real.log (N : ℝ) ^ 2) =o[atTop]
      (fun N : ℕ => (N : ℝ)) :=
    Real.isLittleO_pow_log_id_atTop.comp_tendsto
      (tendsto_natCast_atTop_atTop (R := ℝ))
  have hlog2Pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hsquareSmall := hlogSq.bound
    (show 0 < Real.log 2 / 4 by positivity)
  have hClog : ∀ᶠ N : ℕ in atTop,
      4 * C / Real.log (N : ℝ) ≤ Real.log 2 / 2 := by
    have hthreshold : ∀ᶠ t : ℝ in atTop,
        8 * C / Real.log 2 ≤ t := eventually_ge_atTop _
    filter_upwards [hlogTend.eventually hthreshold,
      hlogTend.eventually (eventually_gt_atTop 0)] with N hlarge hlogPos
    rw [div_le_iff₀ hlogPos]
    have hC0 : 0 ≤ C := hC.le
    have := mul_le_mul_of_nonneg_left hlarge (show 0 ≤ Real.log 2 / 2 by positivity)
    field_simp [ne_of_gt hlog2Pos] at this ⊢
    nlinarith
  let NX : ℕ := max 16 ((Nat.ceil X + 1) ^ 2)
  have hNlarge : ∀ᶠ N : ℕ in atTop, NX ≤ N := eventually_ge_atTop NX
  filter_upwards [eventually_two_chosenY_le_sqrt, hsquareSmall, hClog,
    hNlarge, hlogTend.eventually (eventually_ge_atTop 1)] with
      N hsqrt hsqSmall hClogSmall hNX hlogOne
  intro m hm2 hmY
  have hYle : lowerY N ≤ chosenY N := by
    exact Nat.log_anti_left (by norm_num : 1 < 3)
      (by norm_num : 3 ≤ 65536 ^ 2)
  have hmChosen : m ≤ chosenY N := le_trans hmY hYle
  have hmSqrt : 2 * m ≤ N.sqrt :=
    le_trans (Nat.mul_le_mul_left 2 hmChosen) hsqrt
  have hmPos : 0 < m := by omega
  have hsqrt2 : 2 ≤ N.sqrt := by omega
  have hsm : (N.sqrt + 1) * m ≤ N := by
    calc
      (N.sqrt + 1) * m ≤ (2 * N.sqrt) * m := by nlinarith
      _ = N.sqrt * (2 * m) := by ring
      _ ≤ N.sqrt * N.sqrt := Nat.mul_le_mul_left _ hmSqrt
      _ ≤ N := Nat.sqrt_le N
  have hqSqrt : N.sqrt + 1 ≤ N / m :=
    (Nat.le_div_iff_mul_le hmPos).mpr hsm
  have hq2 : 2 ≤ N / m := by omega
  have hqLeN : N / m ≤ N := Nat.div_le_self N m
  have hNpos : 0 < N := by omega
  have hNR : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hmR : (0 : ℝ) < m := by exact_mod_cast hmPos
  have hlogN : 0 < Real.log (N : ℝ) := lt_of_lt_of_le zero_lt_one hlogOne
  have hlogq : 0 < Real.log ((N / m : ℕ) : ℝ) :=
    Real.log_pos (by exact_mod_cast hq2)
  have hlogHalf : Real.log (N : ℝ) / 2 <
      Real.log ((N / m : ℕ) : ℝ) := by
    rw [← Real.log_sqrt (show (0 : ℝ) ≤ N by positivity)]
    apply Real.log_lt_log (by positivity)
    exact lt_of_lt_of_le (Real.real_sqrt_lt_nat_sqrt_succ (a := N))
      (by exact_mod_cast hqSqrt)
  have hqX : X ≤ ((N / m : ℕ) : ℝ) := by
    have hNX' : max 16 ((Nat.ceil X + 1) ^ 2) ≤ N := by
      simpa [NX] using hNX
    have hsquare : (Nat.ceil X + 1) ^ 2 ≤ N :=
      le_trans (le_max_right 16 ((Nat.ceil X + 1) ^ 2)) hNX'
    have hsqrtCeil : Nat.ceil X + 1 ≤ N.sqrt :=
      Nat.le_sqrt'.mpr hsquare
    calc
      X ≤ Nat.ceil X := Nat.le_ceil X
      _ ≤ (N.sqrt + 1 : ℕ) := by exact_mod_cast (show Nat.ceil X ≤ N.sqrt + 1 by omega)
      _ ≤ (N / m : ℕ) := by exact_mod_cast hqSqrt
  have hthetaQ := htheta (((N / m : ℕ) : ℝ)) hqX
  have hqUpper : ((N / m : ℕ) : ℝ) ≤ (N : ℝ) / m := Nat.cast_div_le
  have hden : Real.log (N : ℝ) ^ 2 ≤
      4 * Real.log ((N / m : ℕ) : ℝ) ^ 2 := by nlinarith
  have herror : C * (((N / m : ℕ) : ℝ) /
      Real.log (N / m : ℕ) ^ 2) ≤
      4 * C * ((N : ℝ) / m) / Real.log N ^ 2 := by
    have hC0 : 0 ≤ C := hC.le
    have hnum : C * ((N / m : ℕ) : ℝ) ≤ C * ((N : ℝ) / m) :=
      mul_le_mul_of_nonneg_left hqUpper hC0
    calc
      C * (((N / m : ℕ) : ℝ) / Real.log (N / m : ℕ) ^ 2) =
          (C * ((N / m : ℕ) : ℝ)) / Real.log (N / m : ℕ) ^ 2 := by ring
      _ ≤ (C * ((N : ℝ) / m)) / Real.log (N / m : ℕ) ^ 2 :=
        div_le_div_of_nonneg_right hnum (sq_nonneg _)
      _ ≤ (4 * C * ((N : ℝ) / m)) / Real.log N ^ 2 := by
        rw [div_le_div_iff₀ (sq_pos_of_pos hlogq) (sq_pos_of_pos hlogN)]
        have hmul := mul_le_mul_of_nonneg_left hden
          (mul_nonneg hC0 (by positivity : (0 : ℝ) ≤ (N : ℝ) / m))
        nlinarith
      _ = 4 * C * ((N : ℝ) / m) / Real.log N ^ 2 := rfl
  have hmLog : (m : ℝ) ≤ Real.log (N : ℝ) := by
    have hmYReal : (m : ℝ) ≤ lowerY N := by exact_mod_cast hmY
    have hnat := Real.natLog_le_logb N (65536 ^ 2)
    have hbase : 1 ≤ Real.log (((65536 ^ 2 : ℕ) : ℝ)) := by
      have := Real.log_le_log (by norm_num : (0 : ℝ) < 3)
        (by norm_num : (3 : ℝ) ≤ ((65536 ^ 2 : ℕ) : ℝ))
      exact le_trans one_lt_log_three.le this
    have hlogb : Real.logb (((65536 ^ 2 : ℕ) : ℝ)) (N : ℝ) ≤
        Real.log N := by
      rw [Real.logb]
      exact div_le_self hlogN.le hbase
    exact le_trans hmYReal (le_trans hnat hlogb)
  have hbudgetCoarse :
      1 + 4 * C * ((N : ℝ) / m) / Real.log N ^ 2 ≤
        ((N : ℝ) / m) * Real.log 2 / Real.log N := by
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _),
      Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (N : ℝ))]
      at hsqSmall
    norm_num at hsqSmall
    have hsqDiv : Real.log N ^ 2 / (N : ℝ) ≤ Real.log 2 / 4 := by
      apply (div_le_iff₀ hNR).mpr
      simpa [div_mul_eq_mul_div] using hsqSmall
    have hscalar : Real.log N ^ 2 / N + 4 * C / Real.log N ≤
        Real.log 2 := by linarith
    have hmL : (m : ℝ) * Real.log N ≤ Real.log N ^ 2 := by
      simpa [pow_two] using mul_le_mul_of_nonneg_right hmLog hlogN.le
    field_simp [ne_of_gt hNR, ne_of_gt hmR, ne_of_gt hlogN] at hscalar ⊢
    nlinarith
  have hlogm2 : Real.log 2 ≤ Real.log (m : ℝ) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hm2)
  have hbudget : 1 + C * (((N / m : ℕ) : ℝ) /
      Real.log (N / m : ℕ) ^ 2) ≤
      ((N : ℝ) / m) * Real.log m / Real.log N := by
    exact le_trans (by simpa [add_comm] using add_le_add_left herror 1)
      (le_trans hbudgetCoarse (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hlogm2 (by positivity)) hlogN.le))
  exact primeCounting_floor_div_ge_main_term C N m hmPos hq2
    (by have := Nat.div_le_self N m; omega) (Real.log_pos (by exact_mod_cast hm2)) hthetaQ hbudget

/-- The endpoint main term eventually dominates the exponential cost at
our conservative cutoff. -/
theorem eventually_lowerY_endpoint_nonnegative :
    ∀ᶠ N : ℕ in atTop,
      2 ≤ lowerY N ∧
      0 ≤ ((N : ℝ) / Real.log N) / lowerY N -
        (65536 ^ lowerY N + 1 : ℕ) := by
  have hquarter : Real.log =o[atTop]
      (fun x : ℝ => x ^ (1 / 4 : ℝ)) :=
    isLittleO_log_rpow_atTop (by norm_num)
  have hmul := hquarter.mul hquarter
  have hrpow : ∀ᶠ x : ℝ in atTop,
      x ^ (1 / 4 : ℝ) * x ^ (1 / 4 : ℝ) = Real.sqrt x := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    rw [← Real.rpow_add hx]
    norm_num [Real.sqrt_eq_rpow]
  have hlogSqReal : (fun x : ℝ => Real.log x ^ 2) =o[atTop]
      (fun x : ℝ => Real.sqrt x) :=
    hmul.congr' (Eventually.of_forall (fun x => by ring)) hrpow
  have hlogSqNat : (fun N : ℕ => Real.log (N : ℝ) ^ 2) =o[atTop]
      (fun N : ℕ => Real.sqrt (N : ℝ)) :=
    hlogSqReal.comp_tendsto (tendsto_natCast_atTop_atTop (R := ℝ))
  have hsmall := hlogSqNat.bound (by norm_num : (0 : ℝ) < 1 / 2)
  have hlogTend : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hNlarge : ∀ᶠ N : ℕ in atTop, (65536 ^ 2) ^ 2 ≤ N :=
    eventually_ge_atTop _
  filter_upwards [hsmall, hNlarge,
    hlogTend.eventually (eventually_ge_atTop 1)] with N hsmallN hbaseN hlogOne
  have hY2 : 2 ≤ lowerY N := by
    apply Nat.le_log_of_pow_le (by norm_num : 1 < 65536 ^ 2)
    exact hbaseN
  have hNpos : 0 < N := by omega
  have hlogPos : 0 < Real.log (N : ℝ) := lt_of_lt_of_le zero_lt_one hlogOne
  have hyPos : (0 : ℝ) < lowerY N := by positivity
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _),
    Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)] at hsmallN
  norm_num at hsmallN
  have hsqrtBig : 1 ≤ Real.sqrt (N : ℝ) := by
    rw [Real.one_le_sqrt]
    exact_mod_cast (show 1 ≤ N by omega)
  have hpowLog : (65536 ^ 2) ^ lowerY N ≤ N :=
    Nat.pow_log_le_self (65536 ^ 2) (by omega)
  have hpowSq : (65536 ^ lowerY N) ^ 2 ≤ N := by
    calc
      (65536 ^ lowerY N) ^ 2 = 65536 ^ (lowerY N * 2) :=
        (pow_mul 65536 (lowerY N) 2).symm
      _ = 65536 ^ (2 * lowerY N) := by rw [Nat.mul_comm]
      _ = (65536 ^ 2) ^ lowerY N := pow_mul 65536 2 (lowerY N)
      _ ≤ N := hpowLog
  have hpowSqrt : 65536 ^ lowerY N ≤ N.sqrt := Nat.le_sqrt'.mpr hpowSq
  have hcost : ((65536 ^ lowerY N + 1 : ℕ) : ℝ) ≤
      2 * Real.sqrt N := by
    have hnatSqrt : ((N.sqrt : ℕ) : ℝ) ≤ Real.sqrt N :=
      Real.nat_sqrt_le_real_sqrt
    have hpowCast : ((65536 ^ lowerY N : ℕ) : ℝ) ≤ ((N.sqrt : ℕ) : ℝ) := by
      exact_mod_cast hpowSqrt
    have hpowReal := le_trans hpowCast hnatSqrt
    norm_num only [Nat.cast_add, Nat.cast_one] at hpowReal ⊢
    nlinarith
  have hyLog : (lowerY N : ℝ) ≤ Real.log N := by
    have hnat := Real.natLog_le_logb N (65536 ^ 2)
    have hbase : 1 ≤ Real.log (((65536 ^ 2 : ℕ) : ℝ)) := by
      have h := Real.log_le_log (by norm_num : (0 : ℝ) < 3)
        (by norm_num : (3 : ℝ) ≤ ((65536 ^ 2 : ℕ) : ℝ))
      exact le_trans one_lt_log_three.le h
    exact le_trans hnat (by
      rw [Real.logb]
      exact div_le_self hlogPos.le hbase)
  have hyLogMul : (lowerY N : ℝ) * Real.log N ≤ Real.log N ^ 2 := by
    simpa [pow_two] using mul_le_mul_of_nonneg_right hyLog hlogPos.le
  have hprod1 : ((65536 ^ lowerY N + 1 : ℕ) : ℝ) *
      ((lowerY N : ℝ) * Real.log N) ≤
        (2 * Real.sqrt N) * Real.log N ^ 2 :=
    mul_le_mul hcost hyLogMul (by positivity) (by positivity)
  have hprod2 : (2 * Real.sqrt N) * Real.log N ^ 2 ≤ N := by
    calc
      (2 * Real.sqrt N) * Real.log N ^ 2 ≤
          Real.sqrt N * Real.sqrt N := by nlinarith [Real.sqrt_nonneg (N : ℝ)]
      _ = N := by rw [Real.mul_self_sqrt (by positivity)]
  refine ⟨hY2, ?_⟩
  rw [sub_nonneg, div_div]
  apply (le_div_iff₀ (mul_pos hlogPos hyPos)).mpr
  nlinarith [le_trans hprod1 hprod2]

/-- The exact compatible-prime interval therefore has a unit main term,
minus only a monotone exponential cost. -/
theorem eventually_compatiblePrimeSet_card_ge :
    ∀ᶠ N : ℕ in atTop, ∀ m : ℕ, 2 ≤ m → m ≤ lowerY N →
      (N : ℝ) / ((m : ℝ) * Real.log N) - (65536 ^ m + 1 : ℕ) ≤
        ((Research.compatiblePrimeSet N m).card : ℝ) := by
  filter_upwards [eventually_primeCounting_floor_div_ge_main,
    eventually_two_chosenY_le_sqrt,
    (eventually_ge_atTop 1 : ∀ᶠ N : ℕ in atTop, 1 ≤ N)] with
      N hprime hsqrt hN
  intro m hm2 hmY
  have hYle : lowerY N ≤ chosenY N :=
    Nat.log_anti_left (by norm_num : 1 < 3)
      (by norm_num : 3 ≤ 65536 ^ 2)
  have hmChosen : m ≤ chosenY N := le_trans hmY hYle
  have hmSqrt : 2 * m ≤ N.sqrt :=
    le_trans (Nat.mul_le_mul_left 2 hmChosen) hsqrt
  have hmPos : 0 < m := by omega
  have hsqrt2 : 2 ≤ N.sqrt := by omega
  have hsm : (N.sqrt + 1) * m ≤ N := by
    calc
      (N.sqrt + 1) * m ≤ (2 * N.sqrt) * m := by nlinarith
      _ = N.sqrt * (2 * m) := by ring
      _ ≤ N.sqrt * N.sqrt := Nat.mul_le_mul_left _ hmSqrt
      _ ≤ N := Nat.sqrt_le N
  have hqSqrt : N.sqrt + 1 ≤ N / m :=
    (Nat.le_div_iff_mul_le hmPos).mpr hsm
  have hpowLog : (65536 ^ 2) ^ lowerY N ≤ N := by
    exact Nat.pow_log_le_self (65536 ^ 2) (by omega)
  have hpowSq : (65536 ^ lowerY N) ^ 2 ≤ N := by
    calc
      (65536 ^ lowerY N) ^ 2 = 65536 ^ (lowerY N * 2) :=
        (pow_mul 65536 (lowerY N) 2).symm
      _ = 65536 ^ (2 * lowerY N) := by rw [Nat.mul_comm]
      _ = (65536 ^ 2) ^ lowerY N := pow_mul 65536 2 (lowerY N)
      _ ≤ N := hpowLog
  have hpowSqrt : 65536 ^ lowerY N ≤ N.sqrt := Nat.le_sqrt'.mpr hpowSq
  have hpowm : 65536 ^ m ≤ 65536 ^ lowerY N :=
    Nat.pow_le_pow_right (by omega) hmY
  have hthreshold : Research.compatibilityThreshold m ≤ N / m := by
    exact le_trans (Research.compatibilityThreshold_le_pow hmPos)
      (le_trans hpowm (le_trans hpowSqrt (by omega)))
  have hpcMono : Nat.primeCounting (Research.compatibilityThreshold m) ≤
      Nat.primeCounting (N / m) := Nat.monotone_primeCounting hthreshold
  have hpcCost : Nat.primeCounting (Research.compatibilityThreshold m) ≤
      65536 ^ m + 1 := by
    calc
      Nat.primeCounting (Research.compatibilityThreshold m) ≤
          Research.compatibilityThreshold m + 1 :=
        Nat.count_le (p := Nat.Prime)
      _ ≤ 65536 ^ m + 1 := Nat.add_le_add_right
        (Research.compatibilityThreshold_le_pow hmPos) 1
  have hcard := card_prime_Ioc (Research.compatibilityThreshold m) (N / m)
    hthreshold
  have hcastCard : ((Research.compatiblePrimeSet N m).card : ℝ) =
      (Nat.primeCounting (N / m) : ℝ) -
        Nat.primeCounting (Research.compatibilityThreshold m) := by
    rw [Research.compatiblePrimeSet, hcard, Nat.cast_sub hpcMono]
  rw [hcastCard]
  have hp := hprime m hm2 hmY
  exact sub_le_sub hp (by exact_mod_cast hpcCost)

/-- Uniform lower count for arbitrary sufficiently large natural intervals. -/
theorem exists_prime_interval_lower :
    ∃ C : ℝ, 0 < C ∧ ∃ X : ℝ, 2 ≤ X ∧
      ∀ u v : ℕ, X ≤ u → u ≤ v →
        ((v : ℝ) - u -
          C * ((u : ℝ) / Real.log u ^ 2) -
          C * ((v : ℝ) / Real.log v ^ 2)) / Real.log v ≤
            (((Finset.Ioc u v).filter Nat.Prime).card : ℝ) := by
  obtain ⟨C, hC, X, hX, htheta⟩ := exists_theta_error_bound
  refine ⟨C, hC, X, hX, ?_⟩
  intro u v hu huv
  have hvX : X ≤ (v : ℝ) := le_trans hu (by exact_mod_cast huv)
  have hv2 : 2 ≤ v := by exact_mod_cast (le_trans hX hvX)
  exact sub_theta_error_div_log_le_card_prime_Ioc u v
    (C * ((u : ℝ) / Real.log u ^ 2))
    (C * ((v : ℝ) / Real.log v ^ 2)) huv hv2
    (htheta u hu) (htheta v hvX)

#print axioms exists_prime_interval_lower

end ResearchPNT
