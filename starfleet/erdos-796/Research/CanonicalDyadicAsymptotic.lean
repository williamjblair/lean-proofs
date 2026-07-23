import Research.CanonicalDyadic
import Research.SmoothAsymptotic

namespace Erdos796

open Filter Topology

section RotateThird

variable {T Q P : Type*} [Fintype T] [Fintype Q] [Fintype P]
  [DecidableEq T] [DecidableEq Q] [DecidableEq P]

/-- Move the third coordinate of a tripartite incidence system to the front. -/
def rotateThirdEquiv : T × (Q × P) ≃ P × (Q × T) where
  toFun e := (e.2.2, (e.2.1, e.1))
  invFun e := (e.2.2, (e.2.1, e.1))
  left_inv e := by rcases e with ⟨t, q, p⟩; rfl
  right_inv e := by rcases e with ⟨p, q, t⟩; rfl

/-- Rotated incidence finset. -/
def rotateThird (H : Finset (T × (Q × P))) : Finset (P × (Q × T)) :=
  H.map rotateThirdEquiv.toEmbedding

@[simp] lemma mem_rotateThird_iff (H : Finset (T × (Q × P)))
    (p : P) (q : Q) (t : T) :
    (p, (q, t)) ∈ rotateThird H ↔ (t, (q, p)) ∈ H := by
  constructor
  · intro h
    rcases Finset.mem_map.mp h with ⟨e, he, hev⟩
    rcases e with ⟨t', q', p'⟩
    simp [rotateThirdEquiv] at hev
    rcases hev with ⟨rfl, rfl, rfl⟩
    exact he
  · intro h
    apply Finset.mem_map.mpr
    exact ⟨(t, (q, p)), h, rfl⟩

@[simp] lemma rotateThird_card (H : Finset (T × (Q × P))) :
    (rotateThird H).card = H.card := by
  simp [rotateThird]

lemma rotateThird_cubeFree (H : Finset (T × (Q × P)))
    (hfree : CubeFree H) : CubeFree (rotateThird H) := by
  intro p v q r t u hpv hqr htu
    hpqt hpqu hprt hpru hvqt hvqu hvrt hvru
  apply hfree htu hqr hpv
  · exact (mem_rotateThird_iff H p q t).mp hpqt
  · exact (mem_rotateThird_iff H v q t).mp hvqt
  · exact (mem_rotateThird_iff H p r t).mp hprt
  · exact (mem_rotateThird_iff H v r t).mp hvrt
  · exact (mem_rotateThird_iff H p q u).mp hpqu
  · exact (mem_rotateThird_iff H v q u).mp hvqu
  · exact (mem_rotateThird_iff H p r u).mp hpru
  · exact (mem_rotateThird_iff H v r u).mp hvru

/-- Cube-free bound with the third coordinate placed first. -/
theorem cubeFree_card_le_rotateThird (H : Finset (T × (Q × P)))
    (hfree : CubeFree H) :
    (H.card : ℝ) ≤
      (Fintype.card Q : ℝ) * Fintype.card T +
      (Fintype.card P : ℝ) *
        Real.sqrt ((Fintype.card Q : ℝ) * Fintype.card T *
          (Fintype.card Q +
            Fintype.card T * Real.sqrt (Fintype.card Q))) := by
  have h := cubeFree_card_le_explicit (rotateThird H)
    (rotateThird_cubeFree H hfree)
  simpa using h

end RotateThird

/-- A dyadic Rankin exponent with simple exact dependence on the prime index. -/
noncomputable def dyadicRankinSigma (k : ℕ) : ℝ :=
  1 - 1 / (4 * ((k : ℝ) + 1))

/-- Geometric loss in the coefficient scale supplied by the dyadic Rankin
exponent. -/
noncomputable def dyadicRankinDecay (j k : ℕ) : ℝ :=
  (2 : ℝ) ^ (-((j : ℝ) + 1) / (4 * ((k : ℝ) + 1)))

lemma dyadicRankinSigma_pos (k : ℕ) : 0 < dyadicRankinSigma k := by
  unfold dyadicRankinSigma
  have hk : (1 : ℝ) ≤ (k : ℝ) + 1 := by
    have : (0 : ℝ) ≤ (k : ℝ) := by positivity
    linarith
  have : 1 / (4 * ((k : ℝ) + 1)) ≤ 1 / 4 := by
    apply one_div_le_one_div_of_le (by norm_num)
    nlinarith
  linarith

lemma log_two_pow_sub_one_le (k : ℕ) :
    Real.log (((2 ^ (k + 1) - 1 : ℕ) : ℝ)) ≤ (k + 1 : ℕ) := by
  by_cases hk : k = 0
  · subst k
    norm_num
  have hyNat : 0 < 2 ^ (k + 1) - 1 := by
    have : 1 < 2 ^ (k + 1) := one_lt_pow₀ (by omega) (by norm_num)
    omega
  have hypos : (0 : ℝ) < ((2 ^ (k + 1) - 1 : ℕ) : ℝ) := by
    exact_mod_cast hyNat
  have hleNat : 2 ^ (k + 1) - 1 ≤ 2 ^ (k + 1) := Nat.sub_le _ _
  have hleR : (((2 ^ (k + 1) - 1 : ℕ) : ℝ)) ≤
      ((2 ^ (k + 1) : ℕ) : ℝ) := by exact_mod_cast hleNat
  calc
    Real.log (((2 ^ (k + 1) - 1 : ℕ) : ℝ)) ≤
        Real.log (((2 ^ (k + 1) : ℕ) : ℝ)) :=
      Real.log_le_log hypos hleR
    _ = ((k + 1 : ℕ) : ℝ) * Real.log 2 := by
      rw [Nat.cast_pow, Real.log_pow]
      norm_num
    _ ≤ ((k + 1 : ℕ) : ℝ) := by
      have hlog2 : Real.log 2 ≤ 1 := (Real.log_le_sub_one_of_pos (by norm_num)).trans_eq (by norm_num)
      nlinarith [show (0 : ℝ) ≤ (k + 1 : ℕ) by positivity]

lemma dyadicSigma_ge_rankinSigma (k : ℕ) (hk : 0 < k) :
    rankinSigma (2 ^ (k + 1) - 1) ≤ dyadicRankinSigma k := by
  have hylog : 0 < Real.log (((2 ^ (k + 1) - 1 : ℕ) : ℝ)) := by
    apply Real.log_pos
    have : 1 < 2 ^ (k + 1) - 1 := by
      have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hk)
      have : 4 ≤ 2 ^ (k + 1) := by
        calc 4 = 2 ^ 2 := by norm_num
             _ ≤ 2 ^ (k + 1) := Nat.pow_le_pow_right (by omega) (by omega)
      omega
    exact_mod_cast this
  have hlog := log_two_pow_sub_one_le k
  unfold rankinSigma dyadicRankinSigma
  have hden1 : (0 : ℝ) < 2 * Real.log (((2 ^ (k + 1) - 1 : ℕ) : ℝ)) := by positivity
  have hden2 : (0 : ℝ) < 4 * ((k : ℝ) + 1) := by positivity
  have hcompare : 2 * Real.log (((2 ^ (k + 1) - 1 : ℕ) : ℝ)) ≤
      4 * ((k : ℝ) + 1) := by
    push_cast at hlog
    nlinarith
  have hinv : 1 / (4 * ((k : ℝ) + 1)) ≤
      1 / (2 * Real.log (((2 ^ (k + 1) - 1 : ℕ) : ℝ))) :=
    one_div_le_one_div_of_le hden1 hcompare
  linarith

lemma rankinEulerFactor_mono_sigma {a b : ℝ} (hab : a ≤ b)
    {p : ℕ} (hp : p.Prime) (ha : 0 < a) :
    (1 - (p : ℝ) ^ (-b))⁻¹ ≤ (1 - (p : ℝ) ^ (-a))⁻¹ := by
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_le
  have hpow : (p : ℝ) ^ (-b) ≤ (p : ℝ) ^ (-a) :=
    Real.rpow_le_rpow_of_exponent_le hp1 (by linarith)
  have hapos : 0 < 1 - (p : ℝ) ^ (-a) :=
    sub_pos.mpr (rankinPrimeRatio_lt_one ha hp)
  exact inv_anti₀ hapos (by linarith)

/-- Eventually, the dyadic Rankin Euler product is bounded by the same
`(log y)^24` majorant as the canonical Rankin exponent. -/
theorem eventually_dyadicRankinEulerProduct_le_log_pow :
    ∀ᶠ k : ℕ in atTop,
      (∏ p ∈ Nat.primesLE (2 ^ (k + 1) - 1),
          (1 - (p : ℝ) ^ (-dyadicRankinSigma k))⁻¹) ≤
        (Real.log (((2 ^ (k + 1) - 1 : ℕ) : ℝ))) ^ 24 := by
  have hy : Tendsto (fun k : ℕ => 2 ^ (k + 1) - 1) atTop atTop := by
    rw [tendsto_atTop]
    intro B
    filter_upwards [eventually_ge_atTop (Nat.log2 (B + 1) + 1)] with k hk
    have hpow : B + 1 < 2 ^ (k + 1) := by
      calc
        B + 1 < 2 ^ (Nat.log2 (B + 1) + 1) := by
          rw [Nat.log2_eq_log_two]
          exact Nat.lt_pow_succ_log_self Nat.one_lt_two (B + 1)
        _ ≤ 2 ^ (k + 1) := Nat.pow_le_pow_right (by omega) (by omega)
    omega
  filter_upwards [hy.eventually eventually_rankinEulerProduct_le_log_pow,
    eventually_ge_atTop 1] with k hk hklow
  apply (Finset.prod_le_prod (fun p hp => by
      have hs := dyadicRankinSigma_pos k
      have hx := rankinPrimeRatio_lt_one hs (Nat.mem_primesLE.mp hp).2
      exact inv_nonneg.mpr (sub_nonneg.mpr hx.le)) (fun p hp =>
        rankinEulerFactor_mono_sigma (dyadicSigma_ge_rankinSigma k (by omega))
          (Nat.mem_primesLE.mp hp).2
          (by
            have hy2 : (2 : ℕ) ≤ 2 ^ (k + 1) - 1 := by
              have : 4 ≤ 2 ^ (k + 1) := by
                calc 4 = 2 ^ 2 := by norm_num
                     _ ≤ 2 ^ (k + 1) := Nat.pow_le_pow_right (by omega) (by omega)
              omega
            have hlog2 : (1 : ℝ) / 2 < Real.log 2 := by
              linarith [Real.log_two_gt_d9]
            have hlogmono : Real.log 2 ≤
                Real.log (((2 ^ (k + 1) - 1 : ℕ) : ℝ)) := by
              apply Real.log_le_log (by norm_num)
              exact_mod_cast hy2
            unfold rankinSigma
            have hlog : (1 : ℝ) / 2 <
                Real.log (((2 ^ (k + 1) - 1 : ℕ) : ℝ)) :=
              hlog2.trans_le hlogmono
            have hinv : 1 / (2 * Real.log (((2 ^ (k + 1) - 1 : ℕ) : ℝ))) < 1 := by
              apply (div_lt_one (by positivity)).2
              linarith
            linarith))).trans
  exact hk

lemma dyadicPower_rpow_sigma_eq (j k : ℕ) :
    (((2 ^ (j + 1) : ℕ) : ℝ)) ^ dyadicRankinSigma k =
      (((2 ^ (j + 1) : ℕ) : ℝ)) * dyadicRankinDecay j k := by
  have hx : (0 : ℝ) < ((2 ^ (j + 1) : ℕ) : ℝ) := by positivity
  rw [show dyadicRankinSigma k = 1 +
      (-1 / (4 * ((k : ℝ) + 1))) by
    unfold dyadicRankinSigma
    ring, Real.rpow_add hx, Real.rpow_one]
  unfold dyadicRankinDecay
  rw [Real.rpow_def_of_pos hx, Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
  congr 2
  rw [Nat.cast_pow, Real.log_pow]
  push_cast
  ring

lemma canonicalCoefficientRange_subset_smoothCores (j k : ℕ) :
    canonicalCoefficientRange j k ⊆
      smoothCoresUpTo (2 ^ (k + 1) - 1) (2 ^ (j + 1)) := by
  intro d hd
  have hd' := Nat.mem_smoothNumbersUpTo.mp hd
  apply mem_smoothCoresUpTo.mpr
  refine ⟨Nat.one_le_iff_ne_zero.mpr hd'.2.1, hd'.1, ?_⟩
  intro p hpprime hpd
  have hplist : p ∈ d.primeFactorsList :=
    (Nat.mem_primeFactorsList hd'.2.1).mpr ⟨hpprime, hpd⟩
  have hplt := hd'.2.2 p hplist
  omega

lemma canonicalCoefficientRange_card_le_polynomial (j k : ℕ) :
    (canonicalCoefficientRange j k).card ≤
      (j + 2) ^ (Nat.primeCounting (2 ^ (k + 1) - 1)) := by
  exact (Finset.card_le_card (canonicalCoefficientRange_subset_smoothCores j k)).trans
    (by simpa using (smoothCoresUpTo_two_pow_card_le
      (2 ^ (k + 1) - 1) (j + 1)))

/-- Uniform geometric coefficient-census bound for all sufficiently high
prime dyadic scales. -/
theorem eventually_canonicalCoefficientRange_card_le :
    ∀ᶠ k : ℕ in atTop, ∀ j : ℕ,
      ((canonicalCoefficientRange j k).card : ℝ) ≤
        2 * (((2 ^ j : ℕ) : ℝ)) *
          dyadicRankinDecay j k * (((k + 1 : ℕ) : ℝ) ^ 24) := by
  filter_upwards [eventually_dyadicRankinEulerProduct_le_log_pow,
    eventually_ge_atTop 1] with k hprod hk
  intro j
  have hX : 0 < 2 ^ (j + 1) := by positivity
  have hbase := smoothNumbersUpTo_card_le_rankin
    (dyadicRankinSigma_pos k) (2 ^ (j + 1)) (2 ^ (k + 1) - 1) hX
  have hlog := log_two_pow_sub_one_le k
  have hlog0 : 0 ≤ Real.log (((2 ^ (k + 1) - 1 : ℕ) : ℝ)) := by
    have hnat : 1 ≤ 2 ^ (k + 1) - 1 := by
      have : 2 ≤ 2 ^ (k + 1) := by
        calc
          2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ (k + 1) := Nat.pow_le_pow_right (by omega) (by omega)
      omega
    apply Real.log_nonneg
    exact_mod_cast hnat
  have hpowlog : (Real.log (((2 ^ (k + 1) - 1 : ℕ) : ℝ))) ^ 24 ≤
      (((k + 1 : ℕ) : ℝ)) ^ 24 := by gcongr
  have hyEq : 2 ^ (k + 1) - 1 + 1 = 2 ^ (k + 1) := by
    exact Nat.sub_add_cancel (by
      exact pow_pos (by norm_num : 0 < (2 : ℕ)) (k + 1))
  rw [hyEq] at hbase
  unfold canonicalCoefficientRange
  apply hbase.trans
  rw [dyadicPower_rpow_sigma_eq]
  have hdec0 : 0 ≤ dyadicRankinDecay j k := by
    unfold dyadicRankinDecay
    positivity
  have hfront0 : 0 ≤ (((2 ^ (j + 1) : ℕ) : ℝ)) *
      dyadicRankinDecay j k := mul_nonneg (by positivity) hdec0
  calc
    (((2 ^ (j + 1) : ℕ) : ℝ)) * dyadicRankinDecay j k *
        (∏ p ∈ Nat.primesLE (2 ^ (k + 1) - 1),
          (1 - (p : ℝ) ^ (-dyadicRankinSigma k))⁻¹) ≤
        (((2 ^ (j + 1) : ℕ) : ℝ)) * dyadicRankinDecay j k *
          (Real.log (((2 ^ (k + 1) - 1 : ℕ) : ℝ))) ^ 24 := by
      exact mul_le_mul_of_nonneg_left hprod hfront0
    _ ≤ (((2 ^ (j + 1) : ℕ) : ℝ)) * dyadicRankinDecay j k *
        (((k + 1 : ℕ) : ℝ) ^ 24) := by
      exact mul_le_mul_of_nonneg_left hpowlog hfront0
    _ = 2 * (((2 ^ j : ℕ) : ℝ)) * dyadicRankinDecay j k *
        (((k + 1 : ℕ) : ℝ) ^ 24) := by
      have hpowcast : (((2 ^ (j + 1) : ℕ) : ℝ)) =
          2 * (((2 ^ j : ℕ) : ℝ)) := by
        norm_cast
        rw [pow_succ]
        ring
      rw [hpowcast]

/-- Persistent part of the normalized cube-projection error. -/
noncomputable def canonicalMainWeight (j k : ℕ) : ℝ :=
  dyadicRankinDecay j k * (((k + 1 : ℕ) : ℝ) ^ 24) /
    Real.sqrt (((2 ^ k : ℕ) : ℝ))

lemma canonicalMainWeight_nonneg (j k : ℕ) :
    0 ≤ canonicalMainWeight j k := by
  unfold canonicalMainWeight dyadicRankinDecay
  positivity

lemma dyadicRankinDecay_eq_pow (j k : ℕ) :
    dyadicRankinDecay j k =
      (((2 : ℝ) ^ (-1 / (4 * ((k : ℝ) + 1)))) ^ (j + 1)) := by
  unfold dyadicRankinDecay
  rw [← Real.rpow_natCast]
  rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
  congr 1
  push_cast
  field_simp

lemma dyadicRankinRatio_pos_lt_one (k : ℕ) :
    0 < (2 : ℝ) ^ (-1 / (4 * ((k : ℝ) + 1))) ∧
      (2 : ℝ) ^ (-1 / (4 * ((k : ℝ) + 1))) < 1 := by
  constructor
  · positivity
  · have h := rankinPrimeRatio_lt_one (p := 2)
      (show 0 < 1 / (4 * ((k : ℝ) + 1)) by positivity) Nat.prime_two
    have he : (-1 : ℝ) / (4 * ((k : ℝ) + 1)) =
        -(1 / (4 * ((k : ℝ) + 1))) := by ring
    rw [he]
    simpa only [Nat.cast_ofNat] using h

lemma summable_dyadicRankinDecay (k : ℕ) :
    Summable (fun j : ℕ => dyadicRankinDecay j k) := by
  rw [show (fun j : ℕ => dyadicRankinDecay j k) =
      fun j => ((2 : ℝ) ^ (-1 / (4 * ((k : ℝ) + 1)))) ^ (j + 1) by
    funext j
    exact dyadicRankinDecay_eq_pow j k]
  apply (summable_nat_add_iff 1).2
  exact summable_geometric_of_norm_lt_one (by
    rw [Real.norm_eq_abs, abs_of_pos (dyadicRankinRatio_pos_lt_one k).1]
    exact (dyadicRankinRatio_pos_lt_one k).2)

lemma tsum_dyadicRankinDecay_le (k : ℕ) :
    ∑' j : ℕ, dyadicRankinDecay j k ≤
      4 * ((k : ℝ) + 1) / Real.log 2 := by
  let r : ℝ := (2 : ℝ) ^ (-1 / (4 * ((k : ℝ) + 1)))
  let x : ℝ := Real.log 2 / (4 * ((k : ℝ) + 1))
  have hx : 0 < x := by dsimp [x]; positivity
  have hr : r = Real.exp (-x) := by
    dsimp [r, x]
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
    congr 1
    field_simp
  have hr01 := dyadicRankinRatio_pos_lt_one k
  have hsum : (∑' j : ℕ, dyadicRankinDecay j k) = r / (1 - r) := by
    rw [show (fun j : ℕ => dyadicRankinDecay j k) = fun j => r ^ (j + 1) by
      funext j
      exact dyadicRankinDecay_eq_pow j k]
    rw [show (∑' j : ℕ, r ^ (j + 1)) = r * ∑' j : ℕ, r ^ j by
      rw [← tsum_mul_left]
      apply tsum_congr
      intro j
      rw [pow_succ']]
    rw [tsum_geometric_of_norm_lt_one (by
      rw [Real.norm_eq_abs, abs_of_pos hr01.1]
      exact hr01.2)]
    ring
  rw [hsum, hr, Real.exp_neg]
  have hexp : 1 + x ≤ Real.exp x := by
    simpa [add_comm] using Real.add_one_le_exp x
  have hexppos : 0 < Real.exp x := Real.exp_pos x
  have hden : 0 < 1 - (Real.exp x)⁻¹ := by
    rw [sub_pos, inv_lt_one₀ hexppos]
    exact lt_of_lt_of_le (by linarith) hexp
  have heq : (Real.exp x)⁻¹ / (1 - (Real.exp x)⁻¹) =
      1 / (Real.exp x - 1) := by
    field_simp [ne_of_gt hexppos, ne_of_gt hden]
  rw [heq]
  have hsub : x ≤ Real.exp x - 1 := by linarith
  have hsubpos : 0 < Real.exp x - 1 := lt_of_lt_of_le hx hsub
  calc
    1 / (Real.exp x - 1) ≤ 1 / x :=
      one_div_le_one_div_of_le hx hsub
    _ = 4 * ((k : ℝ) + 1) / Real.log 2 := by
      dsimp [x]
      field_simp [ne_of_gt (Real.log_pos (by norm_num : (1 : ℝ) < 2))]

lemma sqrt_two_pow_eq (k : ℕ) :
    Real.sqrt (((2 ^ k : ℕ) : ℝ)) = (Real.sqrt 2) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ, Nat.cast_mul, Real.sqrt_mul (by positivity), ih]
      norm_num
      rw [pow_succ]

lemma four_thirds_le_sqrt_two : (4 : ℝ) / 3 ≤ Real.sqrt 2 := by
  have hs0 := Real.sqrt_nonneg 2
  have hsq := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  nlinarith

lemma summable_poly_div_sqrt_two_pow (m : ℕ) :
    Summable (fun k : ℕ => (((k + 1 : ℕ) : ℝ) ^ m) /
      Real.sqrt (((2 ^ k : ℕ) : ℝ))) := by
  have hr : ‖(3 / 4 : ℝ)‖ < 1 := by norm_num
  have hgeom := summable_pow_mul_geometric_of_norm_lt_one m hr
  have hshift := hgeom.comp_injective (i := fun k : ℕ => k + 1)
    (fun a b h => Nat.add_right_cancel h)
  have hmodelShift : Summable (fun k : ℕ => (((k + 1 : ℕ) : ℝ) ^ m) *
      (3 / 4 : ℝ) ^ (k + 1)) := by
    simpa [Function.comp_def] using hshift
  have hmodel : Summable (fun k : ℕ => (4 / 3 : ℝ) *
      ((((k + 1 : ℕ) : ℝ) ^ m) * (3 / 4 : ℝ) ^ (k + 1))) :=
    Summable.mul_left (4 / 3) hmodelShift
  apply Summable.of_nonneg_of_le
    (fun k => by positivity) (fun k => ?_) hmodel
  rw [sqrt_two_pow_eq]
  have hsqrtPos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hpow : ((4 : ℝ) / 3) ^ k ≤ (Real.sqrt 2) ^ k := by
    gcongr
    exact four_thirds_le_sqrt_two
  have hInv : ((Real.sqrt 2) ^ k)⁻¹ ≤ (((4 : ℝ) / 3) ^ k)⁻¹ :=
    inv_anti₀ (by positivity) hpow
  have hpowEq : ((((4 : ℝ) / 3) ^ k)⁻¹) = (3 / 4 : ℝ) ^ k := by
    rw [← inv_pow]
    congr 1
    norm_num
  rw [div_eq_mul_inv]
  have hpoly : 0 ≤ (((k + 1 : ℕ) : ℝ) ^ m) := by positivity
  calc
    (((k + 1 : ℕ) : ℝ) ^ m) * ((Real.sqrt 2) ^ k)⁻¹ ≤
        (((k + 1 : ℕ) : ℝ) ^ m) * (3 / 4 : ℝ) ^ k :=
      mul_le_mul_of_nonneg_left (hInv.trans_eq hpowEq) hpoly
    _ = (4 / 3 : ℝ) * ((((k + 1 : ℕ) : ℝ) ^ m) *
        (3 / 4 : ℝ) ^ (k + 1)) := by
      rw [pow_succ]
      ring

lemma sum_range_two_pow_real (m : ℕ) :
    ∑ i ∈ Finset.range m, (2 : ℝ) ^ i = (2 : ℝ) ^ m - 1 := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Finset.sum_range_succ, ih, pow_succ]
      ring

lemma hyperbolic_two_pow_sum_le (L a : ℕ) :
    (∑ i ∈ Finset.range (L + 1),
        if i + a ≤ L then (2 : ℝ) ^ (i + a) else 0) ≤
      (2 : ℝ) ^ (L + 1) := by
  let s := (Finset.range (L + 1)).filter fun i => i + a ≤ L
  have hinj : Set.InjOn (fun i : ℕ => i + a) s := by
    intro x hx y hy hxy
    exact Nat.add_right_cancel hxy
  have himage : s.image (fun i : ℕ => i + a) ⊆ Finset.range (L + 1) := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨i, hi, rfl⟩
    have hi' := (Finset.mem_filter.mp hi).2
    exact Finset.mem_range.mpr (by omega)
  calc
    (∑ i ∈ Finset.range (L + 1),
        if i + a ≤ L then (2 : ℝ) ^ (i + a) else 0) =
        ∑ i ∈ s, (2 : ℝ) ^ (i + a) := by
      unfold s
      rw [Finset.sum_filter]
    _ = ∑ x ∈ s.image (fun i : ℕ => i + a), (2 : ℝ) ^ x := by
      exact (Finset.sum_image hinj).symm
    _ ≤ ∑ x ∈ Finset.range (L + 1), (2 : ℝ) ^ x :=
      Finset.sum_le_sum_of_subset_of_nonneg himage (fun _ _ _ => by positivity)
    _ = (2 : ℝ) ^ (L + 1) - 1 := sum_range_two_pow_real (L + 1)
    _ ≤ (2 : ℝ) ^ (L + 1) := by linarith

lemma projectionSqrt_le_split {A Q P : ℝ}
    (hA : 0 ≤ A) (hQ : 0 ≤ Q) (hP : 0 ≤ P)
    (hactive : A ≤ Q * P) :
    Real.sqrt (A * (Q + P * Real.sqrt Q)) ≤
      Q * Real.sqrt P + P * Real.sqrt (Q * Real.sqrt Q) := by
  have hsQ : 0 ≤ Real.sqrt Q := Real.sqrt_nonneg _
  have hinside : A * (Q + P * Real.sqrt Q) ≤
      Q ^ 2 * P + P ^ 2 * (Q * Real.sqrt Q) := by
    calc
      A * (Q + P * Real.sqrt Q) ≤
          (Q * P) * (Q + P * Real.sqrt Q) := by gcongr
      _ = Q ^ 2 * P + P ^ 2 * (Q * Real.sqrt Q) := by ring
  calc
    Real.sqrt (A * (Q + P * Real.sqrt Q)) ≤
        Real.sqrt (Q ^ 2 * P + P ^ 2 * (Q * Real.sqrt Q)) :=
      Real.sqrt_le_sqrt hinside
    _ ≤ Real.sqrt (Q ^ 2 * P) +
        Real.sqrt (P ^ 2 * (Q * Real.sqrt Q)) := by
      have hx : 0 ≤ Q ^ 2 * P := mul_nonneg (sq_nonneg Q) hP
      have hy : 0 ≤ P ^ 2 * (Q * Real.sqrt Q) :=
        mul_nonneg (sq_nonneg P) (mul_nonneg hQ hsQ)
      rw [Real.sqrt_le_iff]
      constructor
      · positivity
      · have hsx := Real.sq_sqrt hx
        have hsy := Real.sq_sqrt hy
        have hcross : 0 ≤ Real.sqrt (Q ^ 2 * P) *
            Real.sqrt (P ^ 2 * (Q * Real.sqrt Q)) := by positivity
        nlinarith
    _ = Q * Real.sqrt P + P * Real.sqrt (Q * Real.sqrt Q) := by
      rw [show Q ^ 2 * P = Q ^ 2 * P by rfl,
        Real.sqrt_mul (sq_nonneg Q), Real.sqrt_sq_eq_abs,
        abs_of_nonneg hQ,
        Real.sqrt_mul (sq_nonneg P), Real.sqrt_sq_eq_abs,
        abs_of_nonneg hP]

/-- The block projection error splits into a persistent summable term and a
power-saving transient term. -/
theorem canonicalDyadicBlock_error_le_split
    (A : Finset ℕ) (n R i j k : ℕ) :
    ((canonicalCoefficientRange j k).card : ℝ) *
        Real.sqrt (((canonicalDyadicActiveCells A n R i j k).card : ℝ) *
          (((canonicalLabelRange n i).card : ℝ) +
            (dyadicPrimes k).card *
              Real.sqrt ((canonicalLabelRange n i).card : ℝ))) ≤
      ((canonicalCoefficientRange j k).card : ℝ) *
        ((canonicalLabelRange n i).card : ℝ) *
          Real.sqrt ((dyadicPrimes k).card : ℝ) +
      ((canonicalCoefficientRange j k).card : ℝ) *
        ((dyadicPrimes k).card : ℝ) *
          Real.sqrt (((canonicalLabelRange n i).card : ℝ) *
            Real.sqrt ((canonicalLabelRange n i).card : ℝ)) := by
  have hsplit := projectionSqrt_le_split
    (A := ((canonicalDyadicActiveCells A n R i j k).card : ℝ))
    (Q := ((canonicalLabelRange n i).card : ℝ))
    (P := ((dyadicPrimes k).card : ℝ))
    (by positivity) (by positivity) (by positivity)
    (by exact_mod_cast canonicalDyadicActiveCells_card_le A n R i j k)
  have hT : (0 : ℝ) ≤ (canonicalCoefficientRange j k).card := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hsplit hT]

/-- Actual normalized coefficient factor in the persistent block error. -/
noncomputable def canonicalActualMainWeight (j k : ℕ) : ℝ :=
  ((canonicalCoefficientRange j k).card : ℝ) /
    ((((2 ^ j : ℕ) : ℝ)) * Real.sqrt (((2 ^ k : ℕ) : ℝ)))

/-- Fixed-prime-scale polynomial majorant for the actual coefficient factor. -/
noncomputable def canonicalLowMainMajorant (j k : ℕ) : ℝ :=
  (((j + 2) ^ (Nat.primeCounting (2 ^ (k + 1) - 1)) : ℕ) : ℝ) /
    ((((2 ^ j : ℕ) : ℝ)) * Real.sqrt (((2 ^ k : ℕ) : ℝ)))

lemma canonicalActualMainWeight_nonneg (j k : ℕ) :
    0 ≤ canonicalActualMainWeight j k := by
  unfold canonicalActualMainWeight
  positivity

lemma canonicalCoefficientRange_card_le_pow (j k : ℕ) :
    (canonicalCoefficientRange j k).card ≤ 2 ^ (j + 2) := by
  unfold canonicalCoefficientRange Nat.smoothNumbersUpTo
  calc
    ({n ∈ Finset.range (2 ^ (j + 1) + 1) |
      n ∈ (2 ^ (k + 1)).smoothNumbers}).card ≤
        (Finset.range (2 ^ (j + 1) + 1)).card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    _ = 2 ^ (j + 1) + 1 := by simp
    _ ≤ 2 ^ (j + 2) := by
      rw [show j + 2 = (j + 1) + 1 by omega, pow_succ]
      have hpos : 0 < 2 ^ (j + 1) := pow_pos (by omega) _
      omega

lemma sqrt_two_pow_le (i : ℕ) :
    Real.sqrt (((2 ^ i : ℕ) : ℝ)) ≤
      (((2 ^ (i / 2 + 1) : ℕ) : ℝ)) := by
  rw [Real.sqrt_le_iff]
  constructor
  · positivity
  · norm_num
    rw [sq, ← pow_add]
    norm_cast
    apply Nat.pow_le_pow_right (by omega)
    omega

lemma sqrt_two_pow_mul_sqrt_le (i : ℕ) :
    Real.sqrt ((((2 ^ i : ℕ) : ℝ)) *
      Real.sqrt (((2 ^ i : ℕ) : ℝ))) ≤
      (((2 ^ (i - i / 4 + 2) : ℕ) : ℝ)) := by
  have hs := sqrt_two_pow_le i
  have hins : (((2 ^ i : ℕ) : ℝ)) *
      Real.sqrt (((2 ^ i : ℕ) : ℝ)) ≤
      (((2 ^ (i + i / 2 + 1) : ℕ) : ℝ)) := by
    calc
      (((2 ^ i : ℕ) : ℝ)) * Real.sqrt (((2 ^ i : ℕ) : ℝ)) ≤
          (((2 ^ i : ℕ) : ℝ)) * (((2 ^ (i / 2 + 1) : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_left hs (by positivity)
      _ = (((2 ^ (i + i / 2 + 1) : ℕ) : ℝ)) := by
        norm_cast
        rw [← pow_add]
        congr 1
  rw [Real.sqrt_le_iff]
  constructor
  · positivity
  · apply hins.trans
    norm_num
    rw [sq, ← pow_add]
    norm_cast
    apply Nat.pow_le_pow_right (by omega)
    omega

/-- Persistent piece of one occupied block's projection error. -/
noncomputable def canonicalPersistentTerm
    (A : Finset ℕ) (n R i j k : ℕ) : ℝ :=
  if (canonicalDyadicBlock A n R i j k).Nonempty then
    ((canonicalCoefficientRange j k).card : ℝ) *
      ((canonicalLabelRange n i).card : ℝ) *
        Real.sqrt ((dyadicPrimes k).card : ℝ)
  else 0

lemma canonicalPersistentTerm_nonneg
    (A : Finset ℕ) (n R i j k : ℕ) :
    0 ≤ canonicalPersistentTerm A n R i j k := by
  unfold canonicalPersistentTerm
  split_ifs <;> positivity

/-- Pointwise hyperbolic majorant for the persistent term. -/
theorem canonicalPersistentTerm_le
    {A : Finset ℕ} {n R i j k : ℕ}
    (hn : 0 < n) (hR : 0 < R) (hAint : A ⊆ Finset.Icc 1 n)
    (hprime : ((dyadicPrimes i).card : ℝ) ≤
      dyadicPrimeConstant * (((2 ^ i : ℕ) : ℝ)) / (i + 1)) :
    canonicalPersistentTerm A n R i j k ≤
      (2 * dyadicPrimeConstant / ((Nat.log2 n + 1 : ℕ) : ℝ)) *
        canonicalActualMainWeight j k *
          (((2 ^ (i + j + k) : ℕ) : ℝ)) := by
  classical
  unfold canonicalPersistentTerm
  split_ifs with hne
  · have hprod := canonicalDyadicBlock_nonempty_product_le hR hAint hne
    have hlabel := canonicalDyadicBlock_nonempty_log2_lt_two_mul hne
    have hsum : i + j + k ≤ Nat.log2 n := by
      have hnPow : 2 ^ (i + j + k) ≤ n := by
        simpa [pow_add, mul_assoc] using hprod
      have hlog := log2_mono_of_le (by positivity : 2 ^ (i + j + k) ≠ 0) hnPow
      simpa using hlog
    have hL : Nat.log2 n + 1 ≤ 2 * (i + 1) := by omega
    have hq0 : (0 : ℝ) ≤ (canonicalLabelRange n i).card := by positivity
    have hqlePrime : ((canonicalLabelRange n i).card : ℝ) ≤
        ((dyadicPrimes i).card : ℝ) := by
      exact_mod_cast canonicalLabelRange_card_le n i
    have hLpos : (0 : ℝ) < ((Nat.log2 n + 1 : ℕ) : ℝ) := by positivity
    have hipos : (0 : ℝ) < ((i + 1 : ℕ) : ℝ) := by positivity
    have hqbound : ((canonicalLabelRange n i).card : ℝ) ≤
        2 * dyadicPrimeConstant * (((2 ^ i : ℕ) : ℝ)) /
          ((Nat.log2 n + 1 : ℕ) : ℝ) := by
      apply hqlePrime.trans (hprime.trans ?_)
      have hC := dyadicPrimeConstant_pos.le
      have hpow0 : (0 : ℝ) ≤ ((2 ^ i : ℕ) : ℝ) := by positivity
      push_cast at hL ⊢
      have hiR : (0 : ℝ) < (i : ℝ) + 1 := by positivity
      have hLR : (0 : ℝ) < (Nat.log2 n : ℝ) + 1 := by positivity
      apply (div_le_iff₀ hiR).2
      rw [div_mul_eq_mul_div]
      apply (le_div_iff₀ hLR).2
      have hLcast : (Nat.log2 n : ℝ) + 1 ≤ 2 * ((i : ℝ) + 1) := by
        exact_mod_cast hL
      have hmul := mul_le_mul_of_nonneg_left hLcast
        (mul_nonneg hC hpow0)
      norm_num at hmul ⊢
      convert hmul using 1 <;> ring
    have hpbound : ((dyadicPrimes k).card : ℝ) ≤
        ((2 ^ k : ℕ) : ℝ) := by
      exact_mod_cast (show (dyadicPrimes k).card ≤ 2 ^ k by
        exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq
          (dyadicInterval_card k))
    have hsqrt := Real.sqrt_le_sqrt hpbound
    have hT : (0 : ℝ) ≤ (canonicalCoefficientRange j k).card := by positivity
    have hfirst := mul_le_mul_of_nonneg_left hqbound hT
    have hqbound0 : 0 ≤ 2 * dyadicPrimeConstant *
        (((2 ^ i : ℕ) : ℝ)) / ((Nat.log2 n + 1 : ℕ) : ℝ) := by
      exact div_nonneg
        (mul_nonneg (mul_nonneg (by norm_num) dyadicPrimeConstant_pos.le)
          (by positivity)) (by positivity)
    have hsecond := mul_le_mul hfirst hsqrt (Real.sqrt_nonneg _)
      (mul_nonneg hT hqbound0)
    apply hsecond.trans_eq
    unfold canonicalActualMainWeight
    have hjpow : (0 : ℝ) < ((2 ^ j : ℕ) : ℝ) := by positivity
    have hkroot : (0 : ℝ) < Real.sqrt (((2 ^ k : ℕ) : ℝ)) := by positivity
    have hLne : (((Nat.log2 n + 1 : ℕ) : ℝ)) ≠ 0 := ne_of_gt hLpos
    have hrootSq := Real.sq_sqrt
      (show (0 : ℝ) ≤ ((2 ^ k : ℕ) : ℝ) by positivity)
    field_simp [hLne, ne_of_gt hjpow, ne_of_gt hkroot]
    norm_num [pow_add]
    ring
  · simp
    have hC : 0 ≤ dyadicPrimeConstant := dyadicPrimeConstant_pos.le
    have hW := canonicalActualMainWeight_nonneg j k
    positivity

lemma canonicalPersistent_iSum_le
    {A : Finset ℕ} {n K j k I₀ : ℕ}
    (hn : 0 < n) (hAint : A ⊆ Finset.Icc 1 n)
    (hprime : ∀ i ≥ I₀, ((dyadicPrimes i).card : ℝ) ≤
      dyadicPrimeConstant * (((2 ^ i : ℕ) : ℝ)) / (i + 1))
    (hlogLarge : 2 * I₀ ≤ Nat.log2 n) :
    (∑ i ∈ Finset.range (Nat.log2 n + 1),
      canonicalPersistentTerm A n (2 ^ (K + 2)) i j k) ≤
      (2 * dyadicPrimeConstant / ((Nat.log2 n + 1 : ℕ) : ℝ)) *
        canonicalActualMainWeight j k *
          (if K < j + k then ((2 ^ (Nat.log2 n + 1) : ℕ) : ℝ) else 0) := by
  let c : ℝ := 2 * dyadicPrimeConstant /
    ((Nat.log2 n + 1 : ℕ) : ℝ) * canonicalActualMainWeight j k
  have hc : 0 ≤ c := by
    unfold c
    have hC := dyadicPrimeConstant_pos.le
    have hW := canonicalActualMainWeight_nonneg j k
    positivity
  by_cases hdegree : K < j + k
  · calc
      (∑ i ∈ Finset.range (Nat.log2 n + 1),
        canonicalPersistentTerm A n (2 ^ (K + 2)) i j k) ≤
          ∑ i ∈ Finset.range (Nat.log2 n + 1),
            c * (if i + (j + k) ≤ Nat.log2 n then
              ((2 ^ (i + (j + k)) : ℕ) : ℝ) else 0) := by
        apply Finset.sum_le_sum
        intro i hi
        by_cases hne : (canonicalDyadicBlock A n (2 ^ (K + 2)) i j k).Nonempty
        · have hilog := canonicalDyadicBlock_nonempty_log2_lt_two_mul hne
          have hi0 : I₀ ≤ i := by omega
          have hpoint := canonicalPersistentTerm_le
            (R := 2 ^ (K + 2)) (i := i) (j := j) (k := k)
            hn (by positivity) hAint (hprime i hi0)
          have hprod := canonicalDyadicBlock_nonempty_product_le
            (by positivity : 0 < 2 ^ (K + 2)) hAint hne
          have hsum : i + (j + k) ≤ Nat.log2 n := by
            have hp : 2 ^ (i + (j + k)) ≤ n := by
              simpa [pow_add, mul_assoc] using hprod
            have hl := log2_mono_of_le (by positivity : 2 ^ (i + (j + k)) ≠ 0) hp
            simpa using hl
          rw [if_pos hsum]
          simpa [c, add_assoc] using hpoint
        · rw [canonicalPersistentTerm, if_neg hne]
          positivity
      _ = c * (∑ i ∈ Finset.range (Nat.log2 n + 1),
          if i + (j + k) ≤ Nat.log2 n then
            ((2 ^ (i + (j + k)) : ℕ) : ℝ) else 0) := by
        rw [Finset.mul_sum]
      _ ≤ c * (((2 ^ (Nat.log2 n + 1) : ℕ) : ℝ)) := by
        gcongr
        norm_num
        exact hyperbolic_two_pow_sum_le (Nat.log2 n) (j + k)
      _ = _ := by rw [if_pos hdegree]
  · have hempty : ∀ i ∈ Finset.range (Nat.log2 n + 1),
        ¬(canonicalDyadicBlock A n (2 ^ (K + 2)) i j k).Nonempty := by
      intro i hi hne
      exact hdegree (canonicalDyadicBlock_nonempty_degree_gt hne)
    rw [if_neg hdegree, mul_zero]
    have hz : (∑ i ∈ Finset.range (Nat.log2 n + 1),
        canonicalPersistentTerm A n (2 ^ (K + 2)) i j k) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      rw [canonicalPersistentTerm, if_neg (hempty i hi)]
    rw [hz]

noncomputable def canonicalPersistentSum
    (A : Finset ℕ) (n R : ℕ) : ℝ :=
  ∑ e ∈ dyadicIndexCube n,
    canonicalPersistentTerm A n R e.1 e.2.1 e.2.2

/-- Normalized coefficient factor for the linear rotated term. -/
noncomputable def canonicalActualLinearWeight (j k : ℕ) : ℝ :=
  ((canonicalCoefficientRange j k).card : ℝ) /
    ((((2 ^ j : ℕ) : ℝ)) * (((2 ^ k : ℕ) : ℝ)))

lemma canonicalActualLinearWeight_nonneg (j k : ℕ) :
    0 ≤ canonicalActualLinearWeight j k := by
  unfold canonicalActualLinearWeight
  positivity

lemma sqrt_two_pow_le_two_pow (k : ℕ) :
    Real.sqrt (((2 ^ k : ℕ) : ℝ)) ≤ (((2 ^ k : ℕ) : ℝ)) := by
  rw [Real.sqrt_le_iff]
  constructor
  · positivity
  · have h1 : (1 : ℝ) ≤ ((2 ^ k : ℕ) : ℝ) := by
      exact_mod_cast (show 1 ≤ 2 ^ k by
        have := pow_pos (by omega : 0 < (2 : ℕ)) k
        omega)
    nlinarith

lemma canonicalActualLinearWeight_le_main (j k : ℕ) :
    canonicalActualLinearWeight j k ≤ canonicalActualMainWeight j k := by
  unfold canonicalActualLinearWeight canonicalActualMainWeight
  have hnum : (0 : ℝ) ≤ (canonicalCoefficientRange j k).card := by positivity
  have hj : (0 : ℝ) < ((2 ^ j : ℕ) : ℝ) := by positivity
  have hs : (0 : ℝ) < Real.sqrt (((2 ^ k : ℕ) : ℝ)) := by positivity
  exact div_le_div_of_nonneg_left hnum (mul_pos hj hs)
    (mul_le_mul_of_nonneg_left (sqrt_two_pow_le_two_pow k) hj.le)

/-- Linear term in the third-coordinate-rotated cube bound. -/
noncomputable def canonicalLowLinearTerm
    (A : Finset ℕ) (n R i j k : ℕ) : ℝ :=
  if (canonicalDyadicBlock A n R i j k).Nonempty then
    ((canonicalLabelRange n i).card : ℝ) *
      ((canonicalCoefficientRange j k).card : ℝ)
  else 0

/-- Pointwise hyperbolic majorant for the rotated linear term. -/
theorem canonicalLowLinearTerm_le
    {A : Finset ℕ} {n R i j k : ℕ}
    (hn : 0 < n) (hR : 0 < R) (hAint : A ⊆ Finset.Icc 1 n)
    (hprime : ((dyadicPrimes i).card : ℝ) ≤
      dyadicPrimeConstant * (((2 ^ i : ℕ) : ℝ)) / (i + 1)) :
    canonicalLowLinearTerm A n R i j k ≤
      (2 * dyadicPrimeConstant / ((Nat.log2 n + 1 : ℕ) : ℝ)) *
        canonicalActualLinearWeight j k *
          (((2 ^ (i + j + k) : ℕ) : ℝ)) := by
  classical
  unfold canonicalLowLinearTerm
  split_ifs with hne
  · have hprod := canonicalDyadicBlock_nonempty_product_le hR hAint hne
    have hlabel := canonicalDyadicBlock_nonempty_log2_lt_two_mul hne
    have hL : Nat.log2 n + 1 ≤ 2 * (i + 1) := by omega
    have hqlePrime : ((canonicalLabelRange n i).card : ℝ) ≤
        ((dyadicPrimes i).card : ℝ) := by
      exact_mod_cast canonicalLabelRange_card_le n i
    have hLpos : (0 : ℝ) < ((Nat.log2 n + 1 : ℕ) : ℝ) := by positivity
    have hqbound : ((canonicalLabelRange n i).card : ℝ) ≤
        2 * dyadicPrimeConstant * (((2 ^ i : ℕ) : ℝ)) /
          ((Nat.log2 n + 1 : ℕ) : ℝ) := by
      apply hqlePrime.trans (hprime.trans ?_)
      have hC := dyadicPrimeConstant_pos.le
      have hpow0 : (0 : ℝ) ≤ ((2 ^ i : ℕ) : ℝ) := by positivity
      push_cast at hL ⊢
      have hiR : (0 : ℝ) < (i : ℝ) + 1 := by positivity
      have hLR : (0 : ℝ) < (Nat.log2 n : ℝ) + 1 := by positivity
      apply (div_le_iff₀ hiR).2
      rw [div_mul_eq_mul_div]
      apply (le_div_iff₀ hLR).2
      have hLcast : (Nat.log2 n : ℝ) + 1 ≤ 2 * ((i : ℝ) + 1) := by
        exact_mod_cast hL
      have hmul := mul_le_mul_of_nonneg_left hLcast
        (mul_nonneg hC hpow0)
      norm_num at hmul ⊢
      convert hmul using 1 <;> ring
    have hT : (0 : ℝ) ≤ (canonicalCoefficientRange j k).card := by positivity
    have hmain := mul_le_mul_of_nonneg_right hqbound hT
    apply hmain.trans_eq
    unfold canonicalActualLinearWeight
    have hLne : (((Nat.log2 n + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
    have hj : (((2 ^ j : ℕ) : ℝ)) ≠ 0 := by positivity
    have hk : (((2 ^ k : ℕ) : ℝ)) ≠ 0 := by positivity
    field_simp [hLne, hj, hk]
    norm_num [pow_add]
    ring
  · simp
    have hC := dyadicPrimeConstant_pos.le
    have hW := canonicalActualLinearWeight_nonneg j k
    positivity

lemma canonicalLowLinear_iSum_le
    {A : Finset ℕ} {n K j k I₀ : ℕ}
    (hn : 0 < n) (hAint : A ⊆ Finset.Icc 1 n)
    (hprime : ∀ i ≥ I₀, ((dyadicPrimes i).card : ℝ) ≤
      dyadicPrimeConstant * (((2 ^ i : ℕ) : ℝ)) / (i + 1))
    (hlogLarge : 2 * I₀ ≤ Nat.log2 n) :
    (∑ i ∈ Finset.range (Nat.log2 n + 1),
      canonicalLowLinearTerm A n (2 ^ (K + 2)) i j k) ≤
      (2 * dyadicPrimeConstant / ((Nat.log2 n + 1 : ℕ) : ℝ)) *
        canonicalActualLinearWeight j k *
          (if K < j + k then ((2 ^ (Nat.log2 n + 1) : ℕ) : ℝ) else 0) := by
  let c : ℝ := 2 * dyadicPrimeConstant /
    ((Nat.log2 n + 1 : ℕ) : ℝ) * canonicalActualLinearWeight j k
  have hc : 0 ≤ c := by
    unfold c
    have hC := dyadicPrimeConstant_pos.le
    have hW := canonicalActualLinearWeight_nonneg j k
    positivity
  by_cases hdegree : K < j + k
  · calc
      (∑ i ∈ Finset.range (Nat.log2 n + 1),
        canonicalLowLinearTerm A n (2 ^ (K + 2)) i j k) ≤
          ∑ i ∈ Finset.range (Nat.log2 n + 1),
            c * (if i + (j + k) ≤ Nat.log2 n then
              ((2 ^ (i + (j + k)) : ℕ) : ℝ) else 0) := by
        apply Finset.sum_le_sum
        intro i hi
        by_cases hne : (canonicalDyadicBlock A n (2 ^ (K + 2)) i j k).Nonempty
        · have hilog := canonicalDyadicBlock_nonempty_log2_lt_two_mul hne
          have hi0 : I₀ ≤ i := by omega
          have hpoint := canonicalLowLinearTerm_le
            (R := 2 ^ (K + 2)) (i := i) (j := j) (k := k)
            hn (by positivity) hAint (hprime i hi0)
          have hprod := canonicalDyadicBlock_nonempty_product_le
            (by positivity : 0 < 2 ^ (K + 2)) hAint hne
          have hsum : i + (j + k) ≤ Nat.log2 n := by
            have hp : 2 ^ (i + (j + k)) ≤ n := by
              simpa [pow_add, mul_assoc] using hprod
            have hl := log2_mono_of_le (by positivity : 2 ^ (i + (j + k)) ≠ 0) hp
            simpa using hl
          rw [if_pos hsum]
          simpa [c, add_assoc] using hpoint
        · rw [canonicalLowLinearTerm, if_neg hne]
          positivity
      _ = c * (∑ i ∈ Finset.range (Nat.log2 n + 1),
          if i + (j + k) ≤ Nat.log2 n then
            ((2 ^ (i + (j + k)) : ℕ) : ℝ) else 0) := by
        rw [Finset.mul_sum]
      _ ≤ c * (((2 ^ (Nat.log2 n + 1) : ℕ) : ℝ)) := by
        gcongr
        norm_num
        exact hyperbolic_two_pow_sum_le (Nat.log2 n) (j + k)
      _ = _ := by rw [if_pos hdegree]
  · have hempty : ∀ i ∈ Finset.range (Nat.log2 n + 1),
        ¬(canonicalDyadicBlock A n (2 ^ (K + 2)) i j k).Nonempty := by
      intro i hi hne
      exact hdegree (canonicalDyadicBlock_nonempty_degree_gt hne)
    rw [if_neg hdegree, mul_zero]
    have hz : (∑ i ∈ Finset.range (Nat.log2 n + 1),
        canonicalLowLinearTerm A n (2 ^ (K + 2)) i j k) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      rw [canonicalLowLinearTerm, if_neg (hempty i hi)]
    rw [hz]

noncomputable def canonicalLowLinearSum
    (A : Finset ℕ) (n R : ℕ) : ℝ :=
  ∑ e ∈ dyadicIndexCube n,
    canonicalLowLinearTerm A n R e.1 e.2.1 e.2.2

/-- Normalized arithmetic weight for the rotated square-root term. -/
noncomputable def canonicalActualRootWeight (j k : ℕ) : ℝ :=
  (((dyadicPrimes k).card : ℝ) /
      (((2 ^ k : ℕ) : ℝ))) *
    (Real.sqrt ((canonicalCoefficientRange j k).card : ℝ) /
      (((2 ^ j : ℕ) : ℝ)))

lemma canonicalActualRootWeight_nonneg (j k : ℕ) :
    0 ≤ canonicalActualRootWeight j k := by
  unfold canonicalActualRootWeight
  positivity

noncomputable def rootGeometricWeight (j : ℕ) : ℝ :=
  1 / Real.sqrt (((2 ^ j : ℕ) : ℝ))

lemma rootGeometricWeight_eq_pow (j : ℕ) :
    rootGeometricWeight j = ((Real.sqrt 2)⁻¹) ^ j := by
  unfold rootGeometricWeight
  rw [sqrt_two_pow_eq, one_div, inv_pow]

lemma summable_rootGeometricWeight : Summable rootGeometricWeight := by
  apply (summable_geometric_of_norm_lt_one ?_).congr
  · intro j
    exact rootGeometricWeight_eq_pow j |>.symm
  · rw [Real.norm_eq_abs, abs_of_pos (by positivity : 0 < (Real.sqrt 2)⁻¹)]
    exact (inv_lt_one₀ (show 0 < Real.sqrt 2 by positivity)).2
      (by
        have hs0 := Real.sqrt_nonneg 2
        have hs2 := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
        nlinarith)

lemma canonicalActualRootWeight_le_geometric (j k : ℕ) :
    canonicalActualRootWeight j k ≤
      2 * rootGeometricWeight j := by
  have hP : ((dyadicPrimes k).card : ℝ) ≤ ((2 ^ k : ℕ) : ℝ) := by
    exact_mod_cast (show (dyadicPrimes k).card ≤ 2 ^ k by
      exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq
        (dyadicInterval_card k))
  have hPratio : ((dyadicPrimes k).card : ℝ) /
      ((2 ^ k : ℕ) : ℝ) ≤ 1 := by
    exact (div_le_one (by positivity)).2 hP
  have hT : ((canonicalCoefficientRange j k).card : ℝ) ≤
      ((2 ^ (j + 2) : ℕ) : ℝ) := by
    exact_mod_cast canonicalCoefficientRange_card_le_pow j k
  have hsqrtT := Real.sqrt_le_sqrt hT
  have hsqrtEq : Real.sqrt (((2 ^ (j + 2) : ℕ) : ℝ)) =
      2 * Real.sqrt (((2 ^ j : ℕ) : ℝ)) := by
    rw [sqrt_two_pow_eq, sqrt_two_pow_eq]
    rw [show j + 2 = j + 2 by rfl, pow_add]
    norm_num
    ring
  have hjpow : (0 : ℝ) < ((2 ^ j : ℕ) : ℝ) := by positivity
  have hsqrtj : (0 : ℝ) < Real.sqrt (((2 ^ j : ℕ) : ℝ)) := by positivity
  have hratio : Real.sqrt ((canonicalCoefficientRange j k).card : ℝ) /
      ((2 ^ j : ℕ) : ℝ) ≤ 2 * rootGeometricWeight j := by
    apply (div_le_iff₀ hjpow).2
    unfold rootGeometricWeight
    rw [show (2 * (1 / Real.sqrt (((2 ^ j : ℕ) : ℝ)))) *
        (((2 ^ j : ℕ) : ℝ)) =
        2 * Real.sqrt (((2 ^ j : ℕ) : ℝ)) by
      have hs := Real.sq_sqrt (show (0 : ℝ) ≤ ((2 ^ j : ℕ) : ℝ) by positivity)
      field_simp [ne_of_gt hsqrtj]
      nlinarith]
    rw [← hsqrtEq]
    exact hsqrtT
  unfold canonicalActualRootWeight
  have hsecond : 0 ≤ Real.sqrt ((canonicalCoefficientRange j k).card : ℝ) /
      ((2 ^ j : ℕ) : ℝ) := by positivity
  calc
    ((dyadicPrimes k).card : ℝ) / ((2 ^ k : ℕ) : ℝ) *
        (Real.sqrt ((canonicalCoefficientRange j k).card : ℝ) /
          ((2 ^ j : ℕ) : ℝ)) ≤
      1 * (Real.sqrt ((canonicalCoefficientRange j k).card : ℝ) /
          ((2 ^ j : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_right hPratio hsecond
    _ ≤ 2 * rootGeometricWeight j := by simpa using hratio

lemma summable_canonicalActualRootWeight (k : ℕ) :
    Summable (fun j : ℕ => canonicalActualRootWeight j k) :=
  Summable.of_nonneg_of_le (fun j => canonicalActualRootWeight_nonneg j k)
    (fun j => canonicalActualRootWeight_le_geometric j k)
    (Summable.mul_left 2 summable_rootGeometricWeight)

/-- Square-root term in the third-coordinate-rotated cube bound. -/
noncomputable def canonicalLowRootTerm
    (A : Finset ℕ) (n R i j k : ℕ) : ℝ :=
  if (canonicalDyadicBlock A n R i j k).Nonempty then
    ((dyadicPrimes k).card : ℝ) *
      ((canonicalLabelRange n i).card : ℝ) *
        Real.sqrt ((canonicalCoefficientRange j k).card : ℝ)
  else 0

lemma canonicalLowLinearTerm_nonneg
    (A : Finset ℕ) (n R i j k : ℕ) :
    0 ≤ canonicalLowLinearTerm A n R i j k := by
  unfold canonicalLowLinearTerm
  split_ifs <;> positivity

lemma canonicalLowRootTerm_nonneg
    (A : Finset ℕ) (n R i j k : ℕ) :
    0 ≤ canonicalLowRootTerm A n R i j k := by
  unfold canonicalLowRootTerm
  split_ifs <;> positivity

/-- Pointwise hyperbolic majorant for the rotated square-root term. -/
theorem canonicalLowRootTerm_le
    {A : Finset ℕ} {n R i j k : ℕ}
    (hn : 0 < n) (hR : 0 < R) (hAint : A ⊆ Finset.Icc 1 n)
    (hprime : ((dyadicPrimes i).card : ℝ) ≤
      dyadicPrimeConstant * (((2 ^ i : ℕ) : ℝ)) / (i + 1)) :
    canonicalLowRootTerm A n R i j k ≤
      (2 * dyadicPrimeConstant / ((Nat.log2 n + 1 : ℕ) : ℝ)) *
        canonicalActualRootWeight j k *
          (((2 ^ (i + j + k) : ℕ) : ℝ)) := by
  classical
  unfold canonicalLowRootTerm
  split_ifs with hne
  · have hlabel := canonicalDyadicBlock_nonempty_log2_lt_two_mul hne
    have hL : Nat.log2 n + 1 ≤ 2 * (i + 1) := by omega
    have hqlePrime : ((canonicalLabelRange n i).card : ℝ) ≤
        ((dyadicPrimes i).card : ℝ) := by
      exact_mod_cast canonicalLabelRange_card_le n i
    have hqbound : ((canonicalLabelRange n i).card : ℝ) ≤
        2 * dyadicPrimeConstant * (((2 ^ i : ℕ) : ℝ)) /
          ((Nat.log2 n + 1 : ℕ) : ℝ) := by
      apply hqlePrime.trans (hprime.trans ?_)
      have hC := dyadicPrimeConstant_pos.le
      have hpow0 : (0 : ℝ) ≤ ((2 ^ i : ℕ) : ℝ) := by positivity
      push_cast at hL ⊢
      have hiR : (0 : ℝ) < (i : ℝ) + 1 := by positivity
      have hLR : (0 : ℝ) < (Nat.log2 n : ℝ) + 1 := by positivity
      apply (div_le_iff₀ hiR).2
      rw [div_mul_eq_mul_div]
      apply (le_div_iff₀ hLR).2
      have hLcast : (Nat.log2 n : ℝ) + 1 ≤ 2 * ((i : ℝ) + 1) := by
        exact_mod_cast hL
      have hmul := mul_le_mul_of_nonneg_left hLcast
        (mul_nonneg hC hpow0)
      norm_num at hmul ⊢
      convert hmul using 1 <;> ring
    have hP : (0 : ℝ) ≤ (dyadicPrimes k).card := by positivity
    have hroot : 0 ≤ Real.sqrt ((canonicalCoefficientRange j k).card : ℝ) :=
      Real.sqrt_nonneg _
    have hmain := mul_le_mul_of_nonneg_left hqbound hP
    have hmain' := mul_le_mul_of_nonneg_right hmain hroot
    apply hmain'.trans_eq
    unfold canonicalActualRootWeight
    have hLne : (((Nat.log2 n + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
    have hj : (((2 ^ j : ℕ) : ℝ)) ≠ 0 := by positivity
    have hk : (((2 ^ k : ℕ) : ℝ)) ≠ 0 := by positivity
    field_simp [hLne, hj, hk]
    norm_num [pow_add]
    ring
  · simp
    have hC := dyadicPrimeConstant_pos.le
    have hW := canonicalActualRootWeight_nonneg j k
    positivity

lemma canonicalLowRoot_iSum_le
    {A : Finset ℕ} {n K j k I₀ : ℕ}
    (hn : 0 < n) (hAint : A ⊆ Finset.Icc 1 n)
    (hprime : ∀ i ≥ I₀, ((dyadicPrimes i).card : ℝ) ≤
      dyadicPrimeConstant * (((2 ^ i : ℕ) : ℝ)) / (i + 1))
    (hlogLarge : 2 * I₀ ≤ Nat.log2 n) :
    (∑ i ∈ Finset.range (Nat.log2 n + 1),
      canonicalLowRootTerm A n (2 ^ (K + 2)) i j k) ≤
      (2 * dyadicPrimeConstant / ((Nat.log2 n + 1 : ℕ) : ℝ)) *
        canonicalActualRootWeight j k *
          (if K < j + k then ((2 ^ (Nat.log2 n + 1) : ℕ) : ℝ) else 0) := by
  let c : ℝ := 2 * dyadicPrimeConstant /
    ((Nat.log2 n + 1 : ℕ) : ℝ) * canonicalActualRootWeight j k
  have hc : 0 ≤ c := by
    unfold c
    have hC := dyadicPrimeConstant_pos.le
    have hW := canonicalActualRootWeight_nonneg j k
    positivity
  by_cases hdegree : K < j + k
  · calc
      (∑ i ∈ Finset.range (Nat.log2 n + 1),
        canonicalLowRootTerm A n (2 ^ (K + 2)) i j k) ≤
          ∑ i ∈ Finset.range (Nat.log2 n + 1),
            c * (if i + (j + k) ≤ Nat.log2 n then
              ((2 ^ (i + (j + k)) : ℕ) : ℝ) else 0) := by
        apply Finset.sum_le_sum
        intro i hi
        by_cases hne : (canonicalDyadicBlock A n (2 ^ (K + 2)) i j k).Nonempty
        · have hilog := canonicalDyadicBlock_nonempty_log2_lt_two_mul hne
          have hi0 : I₀ ≤ i := by omega
          have hpoint := canonicalLowRootTerm_le
            (R := 2 ^ (K + 2)) (i := i) (j := j) (k := k)
            hn (by positivity) hAint (hprime i hi0)
          have hprod := canonicalDyadicBlock_nonempty_product_le
            (by positivity : 0 < 2 ^ (K + 2)) hAint hne
          have hsum : i + (j + k) ≤ Nat.log2 n := by
            have hp : 2 ^ (i + (j + k)) ≤ n := by
              simpa [pow_add, mul_assoc] using hprod
            have hl := log2_mono_of_le (by positivity : 2 ^ (i + (j + k)) ≠ 0) hp
            simpa using hl
          rw [if_pos hsum]
          simpa [c, add_assoc] using hpoint
        · rw [canonicalLowRootTerm, if_neg hne]
          positivity
      _ = c * (∑ i ∈ Finset.range (Nat.log2 n + 1),
          if i + (j + k) ≤ Nat.log2 n then
            ((2 ^ (i + (j + k)) : ℕ) : ℝ) else 0) := by
        rw [Finset.mul_sum]
      _ ≤ c * (((2 ^ (Nat.log2 n + 1) : ℕ) : ℝ)) := by
        gcongr
        norm_num
        exact hyperbolic_two_pow_sum_le (Nat.log2 n) (j + k)
      _ = _ := by rw [if_pos hdegree]
  · have hempty : ∀ i ∈ Finset.range (Nat.log2 n + 1),
        ¬(canonicalDyadicBlock A n (2 ^ (K + 2)) i j k).Nonempty := by
      intro i hi hne
      exact hdegree (canonicalDyadicBlock_nonempty_degree_gt hne)
    rw [if_neg hdegree, mul_zero]
    have hz : (∑ i ∈ Finset.range (Nat.log2 n + 1),
        canonicalLowRootTerm A n (2 ^ (K + 2)) i j k) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      rw [canonicalLowRootTerm, if_neg (hempty i hi)]
    rw [hz]

/-- Transient piece of one occupied block's projection error. -/
noncomputable def canonicalTransientTerm
    (A : Finset ℕ) (n R i j k : ℕ) : ℝ :=
  if (canonicalDyadicBlock A n R i j k).Nonempty then
    ((canonicalCoefficientRange j k).card : ℝ) *
      ((dyadicPrimes k).card : ℝ) *
        Real.sqrt (((canonicalLabelRange n i).card : ℝ) *
          Real.sqrt ((canonicalLabelRange n i).card : ℝ))
  else 0

lemma canonicalTransientTerm_nonneg
    (A : Finset ℕ) (n R i j k : ℕ) :
    0 ≤ canonicalTransientTerm A n R i j k := by
  unfold canonicalTransientTerm
  split_ifs <;> positivity

/-- Every occupied transient block has a uniform dyadic power saving coming
from its large-prime label coordinate. -/
theorem canonicalTransientTerm_le
    {A : Finset ℕ} {n R i j k : ℕ}
    (hR : 0 < R) (hAint : A ⊆ Finset.Icc 1 n) :
    canonicalTransientTerm A n R i j k ≤
      (((2 ^ (Nat.log2 n - Nat.log2 n / 8 + 4) : ℕ) : ℝ)) := by
  classical
  unfold canonicalTransientTerm
  split_ifs with hne
  · have hprod := canonicalDyadicBlock_nonempty_product_le hR hAint hne
    have hlabel := canonicalDyadicBlock_nonempty_log2_lt_two_mul hne
    have hsum : i + j + k ≤ Nat.log2 n := by
      have hp : 2 ^ (i + j + k) ≤ n := by
        simpa [pow_add, mul_assoc] using hprod
      have hl := log2_mono_of_le (by positivity : 2 ^ (i + j + k) ≠ 0) hp
      simpa using hl
    have hquarter : Nat.log2 n / 8 ≤ i / 4 := by omega
    have hT : ((canonicalCoefficientRange j k).card : ℝ) ≤
        ((2 ^ (j + 2) : ℕ) : ℝ) := by
      exact_mod_cast canonicalCoefficientRange_card_le_pow j k
    have hP : ((dyadicPrimes k).card : ℝ) ≤ ((2 ^ k : ℕ) : ℝ) := by
      exact_mod_cast (show (dyadicPrimes k).card ≤ 2 ^ k by
        exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq
          (dyadicInterval_card k))
    have hQ : ((canonicalLabelRange n i).card : ℝ) ≤
        ((2 ^ i : ℕ) : ℝ) := by
      exact_mod_cast (canonicalLabelRange_card_le n i |>.trans
        (show (dyadicPrimes i).card ≤ 2 ^ i by
          exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq
            (dyadicInterval_card i)))
    have hrootInner := Real.sqrt_le_sqrt hQ
    have hinside : ((canonicalLabelRange n i).card : ℝ) *
        Real.sqrt ((canonicalLabelRange n i).card : ℝ) ≤
        (((2 ^ i : ℕ) : ℝ)) * Real.sqrt (((2 ^ i : ℕ) : ℝ)) :=
      mul_le_mul hQ hrootInner (Real.sqrt_nonneg _) (by positivity)
    have hroot : Real.sqrt (((canonicalLabelRange n i).card : ℝ) *
        Real.sqrt ((canonicalLabelRange n i).card : ℝ)) ≤
        (((2 ^ (i - i / 4 + 2) : ℕ) : ℝ)) :=
      (Real.sqrt_le_sqrt hinside).trans (sqrt_two_pow_mul_sqrt_le i)
    have hmul := mul_le_mul (mul_le_mul hT hP (by positivity) (by positivity))
      hroot (Real.sqrt_nonneg _) (mul_nonneg (by positivity) (by positivity))
    apply hmul.trans
    exact_mod_cast (show
      2 ^ (j + 2) * 2 ^ k * 2 ^ (i - i / 4 + 2) ≤
        2 ^ (Nat.log2 n - Nat.log2 n / 8 + 4) by
      rw [← pow_add, ← pow_add]
      apply Nat.pow_le_pow_right (by omega)
      omega)
  · positivity

noncomputable def canonicalLowRootSum
    (A : Finset ℕ) (n R K : ℕ) : ℝ :=
  ∑ e ∈ dyadicIndexCube n,
    if e.2.2 < K + 2 then
      canonicalLowRootTerm A n R e.1 e.2.1 e.2.2 else 0

noncomputable def canonicalRootTriangle (K : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (K + 2), ∑' j : ℕ,
    if K < j + k then canonicalActualRootWeight j k else 0

noncomputable def canonicalTransientSum
    (A : Finset ℕ) (n R : ℕ) : ℝ :=
  ∑ e ∈ dyadicIndexCube n,
    canonicalTransientTerm A n R e.1 e.2.1 e.2.2

noncomputable def canonicalTransientMajorant (n : ℕ) : ℝ :=
  (((Nat.log2 n + 1) ^ 3 : ℕ) : ℝ) *
    (((2 ^ (Nat.log2 n - Nat.log2 n / 8 + 4) : ℕ) : ℝ))

theorem canonicalTransientSum_le
    {A : Finset ℕ} {n R : ℕ} (hR : 0 < R)
    (hAint : A ⊆ Finset.Icc 1 n) :
    canonicalTransientSum A n R ≤ canonicalTransientMajorant n := by
  unfold canonicalTransientSum canonicalTransientMajorant
  calc
    (∑ e ∈ dyadicIndexCube n,
      canonicalTransientTerm A n R e.1 e.2.1 e.2.2) ≤
        ∑ _e ∈ dyadicIndexCube n,
          (((2 ^ (Nat.log2 n - Nat.log2 n / 8 + 4) : ℕ) : ℝ)) := by
      apply Finset.sum_le_sum
      intro e he
      exact canonicalTransientTerm_le hR hAint
    _ = (((dyadicIndexCube n).card : ℕ) : ℝ) *
        (((2 ^ (Nat.log2 n - Nat.log2 n / 8 + 4) : ℕ) : ℝ)) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ = _ := by rw [dyadicIndexCube_card]

noncomputable def canonicalTransientComparison (n : ℕ) : ℝ :=
  (16 * 8 ^ 4 * Real.log 2) *
    ((((Nat.log2 n / 8 + 1 : ℕ) : ℝ) ^ 4) /
      (((2 ^ (Nat.log2 n / 8) : ℕ) : ℝ)))

lemma tendsto_log2_div_eight_atTop :
    Tendsto (fun n : ℕ => Nat.log2 n / 8) atTop atTop :=
  (Nat.tendsto_div_const_atTop (by norm_num : (8 : ℕ) ≠ 0)).comp
    tendsto_nat_log2_atTop

lemma tendsto_canonicalTransientComparison_zero :
    Tendsto canonicalTransientComparison atTop (nhds 0) := by
  have h := (tendsto_succ_pow_div_two_pow 4).comp tendsto_log2_div_eight_atTop
  unfold canonicalTransientComparison
  simpa using h.const_mul (16 * 8 ^ 4 * Real.log 2)

/-- The explicit transient majorant is negligible on the second-order scale. -/
theorem tendsto_canonicalTransientMajorant_normalized_zero :
    Tendsto (fun n : ℕ => canonicalTransientMajorant n /
      ((n : ℝ) / Real.log (n : ℝ))) atTop (nhds 0) := by
  apply squeeze_zero' (g := canonicalTransientComparison)
  · filter_upwards [eventually_gt_atTop 1] with n hn
    have hnum : 0 ≤ canonicalTransientMajorant n := by
      unfold canonicalTransientMajorant
      positivity
    have hden : 0 < (n : ℝ) / Real.log (n : ℝ) := by
      exact div_pos (by positivity) (Real.log_pos (by exact_mod_cast hn))
    exact div_nonneg hnum hden.le
  · filter_upwards [eventually_gt_atTop 1] with n hn
    let L := Nat.log2 n
    let r := L / 8
    have hn0 : n ≠ 0 := by omega
    have hnR : (0 : ℝ) < n := by positivity
    have hlogpos : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn)
    have hden : 0 < (n : ℝ) / Real.log (n : ℝ) := div_pos hnR hlogpos
    have hlogBound := real_log_le_log2_add_one_mul_log_two (by omega : 0 < n)
    have hpowLow : 2 ^ L ≤ n := two_pow_log2_le hn0
    have hpolyNat : (L + 1) ^ 4 ≤ 8 ^ 4 * (r + 1) ^ 4 := by
      have hLr : L + 1 ≤ 8 * (r + 1) := by
        dsimp [r]
        omega
      calc
        (L + 1) ^ 4 ≤ (8 * (r + 1)) ^ 4 := Nat.pow_le_pow_left hLr 4
        _ = 8 ^ 4 * (r + 1) ^ 4 := by ring
    have hpowSplit : 2 ^ (L - r + 4) * 2 ^ r = 16 * 2 ^ L := by
      rw [← pow_add]
      have hrL : r ≤ L := by dsimp [r]; omega
      rw [show L - r + 4 + r = L + 4 by omega, pow_add]
      norm_num
      ring
    unfold canonicalTransientMajorant canonicalTransientComparison
    rw [div_secondOrder_eq_mul_log_div hn]
    have htarget :
        ((((L + 1) ^ 3 : ℕ) : ℝ) * (((2 ^ (L - r + 4) : ℕ) : ℝ))) *
            Real.log (n : ℝ) / (n : ℝ) ≤
          (16 * 8 ^ 4 * Real.log 2) *
            ((((r + 1 : ℕ) : ℝ) ^ 4) / (((2 ^ r : ℕ) : ℝ))) := by
      have hL1 : (0 : ℝ) ≤ ((L + 1 : ℕ) : ℝ) := by positivity
      have hrawLog :
          (((L + 1 : ℕ) : ℝ) ^ 3) * (((2 ^ (L - r + 4) : ℕ) : ℝ)) *
              Real.log (n : ℝ) ≤
            (((L + 1 : ℕ) : ℝ) ^ 4) *
              (((2 ^ (L - r + 4) : ℕ) : ℝ)) * Real.log 2 := by
        change Real.log (n : ℝ) ≤
          ((L + 1 : ℕ) : ℝ) * Real.log 2 at hlogBound
        have hcoeff : 0 ≤ (((L + 1 : ℕ) : ℝ) ^ 3) *
            (((2 ^ (L - r + 4) : ℕ) : ℝ)) := by positivity
        have hm := mul_le_mul_of_nonneg_left hlogBound hcoeff
        calc
          (((L + 1 : ℕ) : ℝ) ^ 3) *
              (((2 ^ (L - r + 4) : ℕ) : ℝ)) * Real.log (n : ℝ) ≤
            (((L + 1 : ℕ) : ℝ) ^ 3) *
              (((2 ^ (L - r + 4) : ℕ) : ℝ)) *
                (((L + 1 : ℕ) : ℝ) * Real.log 2) := hm
          _ = (((L + 1 : ℕ) : ℝ) ^ 4) *
              (((2 ^ (L - r + 4) : ℕ) : ℝ)) * Real.log 2 := by ring
      have hpolyR : (((L + 1 : ℕ) : ℝ) ^ 4) ≤
          (8 : ℝ) ^ 4 * (((r + 1 : ℕ) : ℝ) ^ 4) := by
        exact_mod_cast hpolyNat
      have hrawLogNat : ((((L + 1) ^ 3 : ℕ) : ℝ) *
          (((2 ^ (L - r + 4) : ℕ) : ℝ)) * Real.log (n : ℝ)) ≤
          ((((L + 1) ^ 4 : ℕ) : ℝ) *
            (((2 ^ (L - r + 4) : ℕ) : ℝ)) * Real.log 2) := by
        simpa only [Nat.cast_pow, Nat.cast_add, Nat.cast_one] using hrawLog
      have hpolyNatR : ((((L + 1) ^ 4 : ℕ) : ℝ)) ≤
          (((8 ^ 4 * (r + 1) ^ 4 : ℕ) : ℝ)) := by
        exact_mod_cast hpolyNat
      have hpowLowR : (((2 ^ L : ℕ) : ℝ)) ≤ (n : ℝ) := by exact_mod_cast hpowLow
      have hpowSplitR : (((2 ^ (L - r + 4) : ℕ) : ℝ)) *
          (((2 ^ r : ℕ) : ℝ)) = 16 * (((2 ^ L : ℕ) : ℝ)) := by
        exact_mod_cast hpowSplit
      apply (div_le_iff₀ hnR).2
      have hrpow : (0 : ℝ) < ((2 ^ r : ℕ) : ℝ) := by positivity
      rw [show
        16 * 8 ^ 4 * Real.log 2 *
            ((((r + 1 : ℕ) : ℝ) ^ 4) / (((2 ^ r : ℕ) : ℝ))) * (n : ℝ) =
          (16 * 8 ^ 4 * Real.log 2 * (((r + 1 : ℕ) : ℝ) ^ 4) *
            (n : ℝ)) / (((2 ^ r : ℕ) : ℝ)) by ring]
      apply (le_div_iff₀ hrpow).2
      calc
        _ ≤ ((((L + 1) ^ 4 : ℕ) : ℝ) *
            (((2 ^ (L - r + 4) : ℕ) : ℝ)) * Real.log 2) *
            (((2 ^ r : ℕ) : ℝ)) :=
          mul_le_mul_of_nonneg_right hrawLogNat (by positivity)
        _ = ((((L + 1) ^ 4 : ℕ) : ℝ)) *
            (16 * (((2 ^ L : ℕ) : ℝ))) * Real.log 2 := by
          rw [← hpowSplitR]
          ring
        _ ≤ (((8 ^ 4 * (r + 1) ^ 4 : ℕ) : ℝ)) *
            (16 * (n : ℝ)) * Real.log 2 := by
          gcongr
        _ = 16 * 8 ^ 4 * Real.log 2 *
            (((r + 1 : ℕ) : ℝ) ^ 4) * (n : ℝ) := by
          norm_num
          ring
    simpa [L, r] using htarget
  · exact tendsto_canonicalTransientComparison_zero

/-- A canonical block is bounded by its two rotated persistent pieces and the
same power-saving transient piece. -/
theorem canonicalDyadicBlock_card_le_rotated_split
    {A : Finset ℕ} {n R i j k : ℕ} (hA : HasRepBound 3 A) :
    ((canonicalDyadicBlock A n R i j k).card : ℝ) ≤
      canonicalLowLinearTerm A n R i j k +
      canonicalLowRootTerm A n R i j k +
      canonicalTransientTerm A n R i j k := by
  classical
  by_cases hne : (canonicalDyadicBlock A n R i j k).Nonempty
  · have hbase := cubeFree_card_le_rotateThird
      (canonicalDyadicBlock A n R i j k)
      (canonicalDyadicBlock_cubeFree hA)
    simp only [Fintype.card_coe] at hbase
    have hsplit := projectionSqrt_le_split
      (A := ((canonicalLabelRange n i).card : ℝ) *
        (canonicalCoefficientRange j k).card)
      (Q := ((canonicalLabelRange n i).card : ℝ))
      (P := ((canonicalCoefficientRange j k).card : ℝ))
      (by positivity) (by positivity) (by positivity) (le_rfl)
    have hP : (0 : ℝ) ≤ (dyadicPrimes k).card := by positivity
    have herr := mul_le_mul_of_nonneg_left hsplit hP
    unfold canonicalLowLinearTerm canonicalLowRootTerm canonicalTransientTerm
    rw [if_pos hne, if_pos hne, if_pos hne]
    calc
      ((canonicalDyadicBlock A n R i j k).card : ℝ) ≤
          ((canonicalLabelRange n i).card : ℝ) *
            (canonicalCoefficientRange j k).card +
          ((dyadicPrimes k).card : ℝ) *
            Real.sqrt (((canonicalLabelRange n i).card : ℝ) *
              (canonicalCoefficientRange j k).card *
              (((canonicalLabelRange n i).card : ℝ) +
                (canonicalCoefficientRange j k).card *
                  Real.sqrt ((canonicalLabelRange n i).card : ℝ))) := hbase
      _ ≤ ((canonicalLabelRange n i).card : ℝ) *
            (canonicalCoefficientRange j k).card +
          ((dyadicPrimes k).card : ℝ) *
            (((canonicalLabelRange n i).card : ℝ) *
                Real.sqrt ((canonicalCoefficientRange j k).card : ℝ) +
              ((canonicalCoefficientRange j k).card : ℝ) *
                Real.sqrt (((canonicalLabelRange n i).card : ℝ) *
                  Real.sqrt ((canonicalLabelRange n i).card : ℝ))) :=
        add_le_add_right herr _
      _ = _ := by ring
  · have hz := Finset.not_nonempty_iff_eq_empty.mp hne
    rw [hz]
    norm_num
    exact add_nonneg
      (add_nonneg (canonicalLowLinearTerm_nonneg A n R i j k)
        (canonicalLowRootTerm_nonneg A n R i j k))
      (canonicalTransientTerm_nonneg A n R i j k)

lemma canonicalActualMainWeight_le_low (j k : ℕ) :
    canonicalActualMainWeight j k ≤ canonicalLowMainMajorant j k := by
  unfold canonicalActualMainWeight canonicalLowMainMajorant
  gcongr
  exact_mod_cast canonicalCoefficientRange_card_le_polynomial j k

lemma summable_canonicalLowMainMajorant (k : ℕ) :
    Summable (fun j : ℕ => canonicalLowMainMajorant j k) := by
  have hs := summable_smoothDyadicMajorant (2 ^ (k + 1) - 1)
  have hs' := Summable.mul_right
    (1 / Real.sqrt (((2 ^ k : ℕ) : ℝ))) hs
  apply hs'.congr
  intro j
  unfold canonicalLowMainMajorant
  push_cast
  have hsqrt : Real.sqrt ((2 : ℝ) ^ k) ≠ 0 := by positivity
  field_simp [hsqrt]
  <;> ring

lemma canonicalActualMainWeight_le_two_main_of_coefficient_bound
    {j k : ℕ}
    (h : ((canonicalCoefficientRange j k).card : ℝ) ≤
      2 * (((2 ^ j : ℕ) : ℝ)) * dyadicRankinDecay j k *
        (((k + 1 : ℕ) : ℝ) ^ 24)) :
    canonicalActualMainWeight j k ≤ 2 * canonicalMainWeight j k := by
  unfold canonicalActualMainWeight canonicalMainWeight
  have hden : 0 < (((2 ^ j : ℕ) : ℝ)) *
      Real.sqrt (((2 ^ k : ℕ) : ℝ)) := by positivity
  apply (div_le_iff₀ hden).2
  calc
    ((canonicalCoefficientRange j k).card : ℝ) ≤
        2 * (((2 ^ j : ℕ) : ℝ)) * dyadicRankinDecay j k *
          (((k + 1 : ℕ) : ℝ) ^ 24) := h
    _ = (2 * (dyadicRankinDecay j k * (((k + 1 : ℕ) : ℝ) ^ 24) /
          Real.sqrt (((2 ^ k : ℕ) : ℝ)))) *
        ((((2 ^ j : ℕ) : ℝ)) * Real.sqrt (((2 ^ k : ℕ) : ℝ))) := by
      have hs : Real.sqrt (((2 ^ k : ℕ) : ℝ)) ≠ 0 := by positivity
      field_simp [hs]

 theorem summable_canonicalMainWeight :
    Summable (fun z : ℕ × ℕ => canonicalMainWeight z.2 z.1) := by
  rw [summable_prod_of_nonneg (fun z => by
    unfold canonicalMainWeight dyadicRankinDecay
    positivity)]
  constructor
  · intro k
    have hs := Summable.mul_left
      ((((k + 1 : ℕ) : ℝ) ^ 24) /
        Real.sqrt (((2 ^ k : ℕ) : ℝ)))
      (summable_dyadicRankinDecay k)
    apply hs.congr
    intro j
    unfold canonicalMainWeight
    ring
  · apply Summable.of_nonneg_of_le
      (fun k => by
        exact tsum_nonneg fun j => by
          unfold canonicalMainWeight dyadicRankinDecay
          positivity)
      (fun k => ?_)
      (Summable.mul_left (4 / Real.log 2)
        (summable_poly_div_sqrt_two_pow 25))
    have hconst : 0 ≤ (((k + 1 : ℕ) : ℝ) ^ 24) /
        Real.sqrt (((2 ^ k : ℕ) : ℝ)) := by positivity
    have heq : (∑' j : ℕ, canonicalMainWeight j k) =
        ((((k + 1 : ℕ) : ℝ) ^ 24) /
          Real.sqrt (((2 ^ k : ℕ) : ℝ))) *
          ∑' j : ℕ, dyadicRankinDecay j k := by
      rw [← tsum_mul_left]
      apply tsum_congr
      intro j
      unfold canonicalMainWeight
      ring
    rw [heq]
    calc
      ((((k + 1 : ℕ) : ℝ) ^ 24) /
          Real.sqrt (((2 ^ k : ℕ) : ℝ))) *
          ∑' j : ℕ, dyadicRankinDecay j k ≤
        ((((k + 1 : ℕ) : ℝ) ^ 24) /
          Real.sqrt (((2 ^ k : ℕ) : ℝ))) *
          (4 * ((k : ℝ) + 1) / Real.log 2) :=
        mul_le_mul_of_nonneg_left (tsum_dyadicRankinDecay_le k) hconst
      _ = (4 / Real.log 2) *
          ((((k + 1 : ℕ) : ℝ) ^ 25) /
            Real.sqrt (((2 ^ k : ℕ) : ℝ))) := by
        push_cast
        ring

noncomputable def canonicalLowCutoffMajorant (K₀ : ℕ)
    (z : ℕ × ℕ) : ℝ :=
  if z.1 < K₀ then canonicalLowMainMajorant z.2 z.1 else 0

lemma canonicalLowCutoffMajorant_nonneg (K₀ : ℕ) (z : ℕ × ℕ) :
    0 ≤ canonicalLowCutoffMajorant K₀ z := by
  unfold canonicalLowCutoffMajorant
  split_ifs
  · unfold canonicalLowMainMajorant
    positivity
  · rfl

lemma summable_canonicalLowCutoffMajorant (K₀ : ℕ) :
    Summable (canonicalLowCutoffMajorant K₀) := by
  rw [summable_prod_of_nonneg (canonicalLowCutoffMajorant_nonneg K₀)]
  constructor
  · intro k
    by_cases hk : k < K₀
    · simpa [canonicalLowCutoffMajorant, hk] using
        summable_canonicalLowMainMajorant k
    · simp [canonicalLowCutoffMajorant, hk]
  · apply summable_of_ne_finset_zero (s := Finset.range K₀)
    intro k hk
    have hnot : ¬k < K₀ := by simpa using hk
    simp [canonicalLowCutoffMajorant, hnot]

lemma summable_canonicalCombinedMajorant (K₀ : ℕ) :
    Summable (fun z : ℕ × ℕ =>
      canonicalLowCutoffMajorant K₀ z +
        2 * canonicalMainWeight z.2 z.1) :=
  (summable_canonicalLowCutoffMajorant K₀).add
    (Summable.mul_left 2 summable_canonicalMainWeight)

lemma canonicalActualMainWeight_le_combined
    (K₀ : ℕ)
    (hK₀ : ∀ k ≥ K₀, ∀ j,
      ((canonicalCoefficientRange j k).card : ℝ) ≤
        2 * (((2 ^ j : ℕ) : ℝ)) * dyadicRankinDecay j k *
          (((k + 1 : ℕ) : ℝ) ^ 24))
    (z : ℕ × ℕ) :
    canonicalActualMainWeight z.2 z.1 ≤
      canonicalLowCutoffMajorant K₀ z +
        2 * canonicalMainWeight z.2 z.1 := by
  by_cases hk : z.1 < K₀
  · have hlo := canonicalActualMainWeight_le_low z.2 z.1
    rw [canonicalLowCutoffMajorant, if_pos hk]
    exact hlo.trans (le_add_of_nonneg_right (by
      exact mul_nonneg (by norm_num) (canonicalMainWeight_nonneg z.2 z.1)))
  · have hcoef := hK₀ z.1 (by omega) z.2
    have hhi := canonicalActualMainWeight_le_two_main_of_coefficient_bound hcoef
    rw [canonicalLowCutoffMajorant, if_neg hk, zero_add]
    exact hhi

theorem summable_canonicalActualMainWeight :
    Summable (fun z : ℕ × ℕ => canonicalActualMainWeight z.2 z.1) := by
  rcases (eventually_atTop.1 eventually_canonicalCoefficientRange_card_le) with
    ⟨K₀, hK₀⟩
  exact Summable.of_nonneg_of_le
    (fun z => canonicalActualMainWeight_nonneg z.2 z.1)
    (canonicalActualMainWeight_le_combined K₀ hK₀)
    (summable_canonicalCombinedMajorant K₀)

lemma canonicalActualLinearWeight_pair_nonneg (z : ℕ × ℕ) :
    0 ≤ canonicalActualLinearWeight z.2 z.1 :=
  canonicalActualLinearWeight_nonneg z.2 z.1

lemma canonicalActualLinearWeight_pair_le (z : ℕ × ℕ) :
    canonicalActualLinearWeight z.2 z.1 ≤ canonicalActualMainWeight z.2 z.1 :=
  canonicalActualLinearWeight_le_main z.2 z.1

theorem summable_canonicalActualLinearWeight :
    Summable (fun z : ℕ × ℕ => canonicalActualLinearWeight z.2 z.1) :=
  Summable.of_nonneg_of_le canonicalActualLinearWeight_pair_nonneg
    canonicalActualLinearWeight_pair_le summable_canonicalActualMainWeight

theorem tendsto_canonicalActualLinearWeight_degreeTail_zero :
    Tendsto (fun K : ℕ => ∑' z : ℕ × ℕ,
      if K < z.1 + z.2 then canonicalActualLinearWeight z.1 z.2 else 0)
      atTop (nhds 0) := by
  have hsOrient : Summable (fun z : ℕ × ℕ =>
      canonicalActualLinearWeight z.1 z.2) := by
    simpa [Function.comp_def] using
      summable_canonicalActualLinearWeight.comp_injective
        (i := Prod.swap) Prod.swap_injective
  have h := tendsto_tsum_of_dominated_convergence
    (𝓕 := atTop)
    (f := fun K (z : ℕ × ℕ) =>
      if K < z.1 + z.2 then canonicalActualLinearWeight z.1 z.2 else 0)
    (g := fun _z : ℕ × ℕ => (0 : ℝ)) hsOrient
    (fun z => by
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_ge_atTop (z.1 + z.2)] with K hK
      simp [show ¬K < z.1 + z.2 by omega])
    (by
      filter_upwards [eventually_ge_atTop 0] with K hK
      intro z
      by_cases hz : K < z.1 + z.2
      · simp [hz, abs_of_nonneg (canonicalActualLinearWeight_nonneg z.1 z.2)]
      · simp [hz, canonicalActualLinearWeight_nonneg z.1 z.2])
  simpa using h

/-- Global rotated linear error at cutoff `2^(K+2)`. -/
theorem canonicalLowLinearSum_le
    {A : Finset ℕ} {n K I₀ : ℕ}
    (hn : 0 < n) (hAint : A ⊆ Finset.Icc 1 n)
    (hprime : ∀ i ≥ I₀, ((dyadicPrimes i).card : ℝ) ≤
      dyadicPrimeConstant * (((2 ^ i : ℕ) : ℝ)) / (i + 1))
    (hlogLarge : 2 * I₀ ≤ Nat.log2 n) :
    canonicalLowLinearSum A n (2 ^ (K + 2)) ≤
      (2 * dyadicPrimeConstant / ((Nat.log2 n + 1 : ℕ) : ℝ)) *
        (((2 ^ (Nat.log2 n + 1) : ℕ) : ℝ)) *
          (∑' z : ℕ × ℕ, if K < z.1 + z.2 then
            canonicalActualLinearWeight z.1 z.2 else 0) := by
  classical
  let I := Finset.range (Nat.log2 n + 1)
  have hreorder : canonicalLowLinearSum A n (2 ^ (K + 2)) =
      ∑ jk ∈ I.product I, ∑ i ∈ I,
        canonicalLowLinearTerm A n (2 ^ (K + 2)) i jk.1 jk.2 := by
    dsimp [canonicalLowLinearSum, dyadicIndexCube, I]
    rw [Finset.sum_product, Finset.sum_comm]
  rw [hreorder]
  calc
    (∑ jk ∈ I.product I, ∑ i ∈ I,
        canonicalLowLinearTerm A n (2 ^ (K + 2)) i jk.1 jk.2) ≤
      ∑ jk ∈ I.product I,
        (2 * dyadicPrimeConstant / ((Nat.log2 n + 1 : ℕ) : ℝ)) *
          canonicalActualLinearWeight jk.1 jk.2 *
            (if K < jk.1 + jk.2 then
              ((2 ^ (Nat.log2 n + 1) : ℕ) : ℝ) else 0) := by
        apply Finset.sum_le_sum
        intro jk hjk
        exact canonicalLowLinear_iSum_le hn hAint hprime hlogLarge
    _ = (2 * dyadicPrimeConstant / ((Nat.log2 n + 1 : ℕ) : ℝ)) *
        (((2 ^ (Nat.log2 n + 1) : ℕ) : ℝ)) *
          ∑ jk ∈ I.product I, (if K < jk.1 + jk.2 then
            canonicalActualLinearWeight jk.1 jk.2 else 0) := by
      symm
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro jk hjk
      by_cases hdeg : K < jk.1 + jk.2 <;> simp [hdeg] <;> ring
    _ ≤ (2 * dyadicPrimeConstant / ((Nat.log2 n + 1 : ℕ) : ℝ)) *
        (((2 ^ (Nat.log2 n + 1) : ℕ) : ℝ)) *
          (∑' z : ℕ × ℕ, if K < z.1 + z.2 then
            canonicalActualLinearWeight z.1 z.2 else 0) := by
      have hsOrient : Summable (fun z : ℕ × ℕ =>
          canonicalActualLinearWeight z.1 z.2) := by
        simpa [Function.comp_def] using
          summable_canonicalActualLinearWeight.comp_injective
            (i := Prod.swap) Prod.swap_injective
      have hsum := (hsOrient.indicator
        {z : ℕ × ℕ | K < z.1 + z.2}).sum_le_tsum (I.product I)
        (fun z hz => by
          by_cases hdeg : K < z.1 + z.2
          · simp [hdeg, canonicalActualLinearWeight_nonneg]
          · simp [hdeg])
      have hsum' : (∑ jk ∈ I.product I,
          if K < jk.1 + jk.2 then canonicalActualLinearWeight jk.1 jk.2 else 0) ≤
          (∑' z : ℕ × ℕ, if K < z.1 + z.2 then
            canonicalActualLinearWeight z.1 z.2 else 0) := by
        simpa [Set.indicator] using hsum
      have hpref : 0 ≤
          (2 * dyadicPrimeConstant / ((Nat.log2 n + 1 : ℕ) : ℝ)) *
            (((2 ^ (Nat.log2 n + 1) : ℕ) : ℝ)) := by
        exact mul_nonneg
          (div_nonneg (mul_nonneg (by norm_num) dyadicPrimeConstant_pos.le)
            (by positivity)) (by positivity)
      exact mul_le_mul_of_nonneg_left hsum' hpref

/-- Global low-prime rotated square-root error, bounded by the triangular
root-weight majorant. -/
theorem canonicalLowRootSum_le
    {A : Finset ℕ} {n K I₀ : ℕ}
    (hn : 0 < n) (hAint : A ⊆ Finset.Icc 1 n)
    (hprime : ∀ i ≥ I₀, ((dyadicPrimes i).card : ℝ) ≤
      dyadicPrimeConstant * (((2 ^ i : ℕ) : ℝ)) / (i + 1))
    (hlogLarge : 2 * I₀ ≤ Nat.log2 n) :
    canonicalLowRootSum A n (2 ^ (K + 2)) K ≤
      (2 * dyadicPrimeConstant / ((Nat.log2 n + 1 : ℕ) : ℝ)) *
        (((2 ^ (Nat.log2 n + 1) : ℕ) : ℝ)) * canonicalRootTriangle K := by
  classical
  let I := Finset.range (Nat.log2 n + 1)
  have hreorder : canonicalLowRootSum A n (2 ^ (K + 2)) K =
      ∑ jk ∈ I.product I, ∑ i ∈ I,
        if jk.2 < K + 2 then
          canonicalLowRootTerm A n (2 ^ (K + 2)) i jk.1 jk.2 else 0 := by
    dsimp [canonicalLowRootSum, dyadicIndexCube, I]
    rw [Finset.sum_product, Finset.sum_comm]
  rw [hreorder]
  calc
    (∑ jk ∈ I.product I, ∑ i ∈ I,
        if jk.2 < K + 2 then
          canonicalLowRootTerm A n (2 ^ (K + 2)) i jk.1 jk.2 else 0) ≤
      ∑ jk ∈ I.product I,
        (2 * dyadicPrimeConstant / ((Nat.log2 n + 1 : ℕ) : ℝ)) *
          canonicalActualRootWeight jk.1 jk.2 *
            (if jk.2 < K + 2 ∧ K < jk.1 + jk.2 then
              ((2 ^ (Nat.log2 n + 1) : ℕ) : ℝ) else 0) := by
        apply Finset.sum_le_sum
        intro jk hjk
        by_cases hk : jk.2 < K + 2
        · simp only [if_pos hk, Finset.sum_const]
          have hbase := canonicalLowRoot_iSum_le (A := A) (n := n)
            (K := K) (j := jk.1) (k := jk.2) (I₀ := I₀)
            hn hAint hprime hlogLarge
          by_cases hd : K < jk.1 + jk.2
          · simpa [hk, hd] using hbase
          · simpa [hk, hd] using hbase
        · simp [hk]
    _ = (2 * dyadicPrimeConstant / ((Nat.log2 n + 1 : ℕ) : ℝ)) *
        (((2 ^ (Nat.log2 n + 1) : ℕ) : ℝ)) *
          ∑ jk ∈ I.product I,
            (if jk.2 < K + 2 ∧ K < jk.1 + jk.2 then
              canonicalActualRootWeight jk.1 jk.2 else 0) := by
      symm
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro jk hjk
      by_cases h : jk.2 < K + 2 ∧ K < jk.1 + jk.2 <;> simp [h] <;> ring
    _ ≤ (2 * dyadicPrimeConstant / ((Nat.log2 n + 1 : ℕ) : ℝ)) *
        (((2 ^ (Nat.log2 n + 1) : ℕ) : ℝ)) * canonicalRootTriangle K := by
      have hfinite : (∑ jk ∈ I.product I,
          (if jk.2 < K + 2 ∧ K < jk.1 + jk.2 then
            canonicalActualRootWeight jk.1 jk.2 else 0)) ≤
          canonicalRootTriangle K := by
        unfold canonicalRootTriangle
        have hreorder' : (∑ jk ∈ I.product I,
            (if jk.2 < K + 2 ∧ K < jk.1 + jk.2 then
              canonicalActualRootWeight jk.1 jk.2 else 0)) =
            ∑ k ∈ I, ∑ j ∈ I,
              (if k < K + 2 ∧ K < j + k then
                canonicalActualRootWeight j k else 0) :=
          Finset.sum_product_right _ _ _
        rw [hreorder']
        have hsplit : (∑ k ∈ I, ∑ j ∈ I,
              (if k < K + 2 ∧ K < j + k then
                canonicalActualRootWeight j k else 0)) =
            ∑ k ∈ I, if k < K + 2 then
              (∑ j ∈ I, if K < j + k then
                canonicalActualRootWeight j k else 0) else 0 := by
          apply Finset.sum_congr rfl
          intro k hk
          by_cases hkt : k < K + 2
          · simp [hkt]
          · simp [hkt]
        rw [hsplit, ← Finset.sum_filter]
        calc
          (∑ k ∈ I.filter (fun k => k < K + 2),
              ∑ j ∈ I, if K < j + k then
                canonicalActualRootWeight j k else 0) ≤
            ∑ k ∈ I.filter (fun k => k < K + 2),
              ∑' j : ℕ, if K < j + k then
                canonicalActualRootWeight j k else 0 := by
              apply Finset.sum_le_sum
              intro k hk
              have hsIndicator :=
                (summable_canonicalActualRootWeight k).indicator
                  {j : ℕ | K < j + k}
              have hs : Summable (fun j : ℕ =>
                  if K < j + k then canonicalActualRootWeight j k else 0) :=
                hsIndicator.congr (fun j => by
                  rw [Set.indicator_apply]
                  rfl)
              exact hs.sum_le_tsum I (fun j hj => by
                by_cases hd : K < j + k
                · simp [hd, canonicalActualRootWeight_nonneg]
                · simp [hd])
          _ ≤ ∑ k ∈ Finset.range (K + 2),
              ∑' j : ℕ, if K < j + k then
                canonicalActualRootWeight j k else 0 := by
              apply Finset.sum_le_sum_of_subset_of_nonneg
              · intro k hk
                exact Finset.mem_range.mpr (Finset.mem_filter.mp hk).2
              · intro k hkRange hkNot
                exact tsum_nonneg fun j => by
                  split_ifs
                  · exact canonicalActualRootWeight_nonneg j k
                  · rfl
      have hpref : 0 ≤
          (2 * dyadicPrimeConstant / ((Nat.log2 n + 1 : ℕ) : ℝ)) *
            (((2 ^ (Nat.log2 n + 1) : ℕ) : ℝ)) := by
        exact mul_nonneg
          (div_nonneg (mul_nonneg (by norm_num) dyadicPrimeConstant_pos.le)
            (by positivity)) (by positivity)
      exact mul_le_mul_of_nonneg_left hfinite hpref

lemma dyadicProjectionCoefficient_normalized_le
    {n : ℕ} (hn : 1 < n) :
    ((2 * dyadicPrimeConstant / ((Nat.log2 n + 1 : ℕ) : ℝ)) *
        (((2 ^ (Nat.log2 n + 1) : ℕ) : ℝ))) /
        ((n : ℝ) / Real.log (n : ℝ)) ≤
      4 * dyadicPrimeConstant * Real.log 2 := by
  have hnR : (0 : ℝ) < n := by positivity
  have hlogBound := real_log_le_log2_add_one_mul_log_two (by omega : 0 < n)
  have hpowNat : 2 ^ (Nat.log2 n + 1) ≤ 2 * n := by
    rw [pow_succ]
    simpa [mul_comm] using
      Nat.mul_le_mul_left 2 (two_pow_log2_le (by omega : n ≠ 0))
  have hpowBound : (((2 ^ (Nat.log2 n + 1) : ℕ) : ℝ)) ≤ 2 * (n : ℝ) := by
    exact_mod_cast hpowNat
  have hLpos : (0 : ℝ) < ((Nat.log2 n + 1 : ℕ) : ℝ) := by positivity
  rw [div_secondOrder_eq_mul_log_div hn]
  have heq :
      (2 * dyadicPrimeConstant / ((Nat.log2 n + 1 : ℕ) : ℝ) *
          (((2 ^ (Nat.log2 n + 1) : ℕ) : ℝ))) * Real.log (n : ℝ) /
          (n : ℝ) =
        (2 * dyadicPrimeConstant *
          (((2 ^ (Nat.log2 n + 1) : ℕ) : ℝ)) * Real.log (n : ℝ)) /
          (((Nat.log2 n + 1 : ℕ) : ℝ) * (n : ℝ)) := by
    field_simp [ne_of_gt hLpos, ne_of_gt hnR]
  rw [heq]
  apply (div_le_iff₀ (mul_pos hLpos hnR)).2
  calc
    2 * dyadicPrimeConstant *
        (((2 ^ (Nat.log2 n + 1) : ℕ) : ℝ)) * Real.log (n : ℝ) ≤
      2 * dyadicPrimeConstant *
        (((2 ^ (Nat.log2 n + 1) : ℕ) : ℝ)) *
          (((Nat.log2 n + 1 : ℕ) : ℝ) * Real.log 2) := by
        exact mul_le_mul_of_nonneg_left hlogBound
          (mul_nonneg
            (mul_nonneg (by norm_num) dyadicPrimeConstant_pos.le)
            (by positivity))
    _ ≤ 2 * dyadicPrimeConstant * (2 * (n : ℝ)) *
          (((Nat.log2 n + 1 : ℕ) : ℝ) * Real.log 2) := by
        have htwoC : (0 : ℝ) ≤ 2 * dyadicPrimeConstant :=
          mul_nonneg (by norm_num) dyadicPrimeConstant_pos.le
        have hp := mul_le_mul_of_nonneg_left hpowBound htwoC
        exact mul_le_mul_of_nonneg_right hp (mul_nonneg (by positivity)
          (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le)
    _ = (4 * dyadicPrimeConstant * Real.log 2) *
        (((Nat.log2 n + 1 : ℕ) : ℝ) * (n : ℝ)) := by ring

lemma normalized_le_of_dyadicProjection_bound
    {n : ℕ} (hn : 1 < n) {raw tail : ℝ} (htail : 0 ≤ tail)
    (hraw : raw ≤
      (2 * dyadicPrimeConstant / ((Nat.log2 n + 1 : ℕ) : ℝ)) *
        (((2 ^ (Nat.log2 n + 1) : ℕ) : ℝ)) * tail) :
    raw / ((n : ℝ) / Real.log (n : ℝ)) ≤
      (4 * dyadicPrimeConstant * Real.log 2) * tail := by
  have hden : 0 < (n : ℝ) / Real.log (n : ℝ) :=
    div_pos (by positivity) (Real.log_pos (by exact_mod_cast hn))
  have hdiv := div_le_div_of_nonneg_right hraw hden.le
  apply hdiv.trans
  rw [show
    ((2 * dyadicPrimeConstant / ((Nat.log2 n + 1 : ℕ) : ℝ)) *
      (((2 ^ (Nat.log2 n + 1) : ℕ) : ℝ)) * tail) /
      ((n : ℝ) / Real.log (n : ℝ)) =
    (((2 * dyadicPrimeConstant / ((Nat.log2 n + 1 : ℕ) : ℝ)) *
      (((2 ^ (Nat.log2 n + 1) : ℕ) : ℝ))) /
      ((n : ℝ) / Real.log (n : ℝ))) * tail by ring]
  exact mul_le_mul_of_nonneg_right
    (dyadicProjectionCoefficient_normalized_le hn) htail

/-- Normalized rotated linear error is bounded by its summable degree tail. -/
theorem eventually_canonicalLowLinearSum_normalized_le (K : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ A : Finset ℕ, A ⊆ Finset.Icc 1 n →
      canonicalLowLinearSum A n (2 ^ (K + 2)) /
          ((n : ℝ) / Real.log (n : ℝ)) ≤
        (4 * dyadicPrimeConstant * Real.log 2) *
          (∑' z : ℕ × ℕ, if K < z.1 + z.2 then
            canonicalActualLinearWeight z.1 z.2 else 0) := by
  rcases (eventually_atTop.1 eventually_dyadicPrimes_card_le) with ⟨I₀, hI₀⟩
  have hlog2 := tendsto_nat_log2_atTop.eventually_ge_atTop (2 * I₀)
  filter_upwards [eventually_gt_atTop 1, hlog2] with n hn hL
  intro A hAint
  have hraw := canonicalLowLinearSum_le (K := K) (I₀ := I₀)
    (by omega : 0 < n) hAint hI₀ hL
  let tail : ℝ := ∑' z : ℕ × ℕ, if K < z.1 + z.2 then
    canonicalActualLinearWeight z.1 z.2 else 0
  have htail : 0 ≤ tail := by
    apply tsum_nonneg
    intro z
    split_ifs
    · exact canonicalActualLinearWeight_nonneg z.1 z.2
    · rfl
  exact normalized_le_of_dyadicProjection_bound hn htail hraw

/-- Global persistent error at cutoff `2^(K+2)`, bounded by the summable
coefficient/prime-degree tail. -/
theorem canonicalPersistentSum_le
    {A : Finset ℕ} {n K I₀ : ℕ}
    (hn : 0 < n) (hAint : A ⊆ Finset.Icc 1 n)
    (hprime : ∀ i ≥ I₀, ((dyadicPrimes i).card : ℝ) ≤
      dyadicPrimeConstant * (((2 ^ i : ℕ) : ℝ)) / (i + 1))
    (hlogLarge : 2 * I₀ ≤ Nat.log2 n) :
    canonicalPersistentSum A n (2 ^ (K + 2)) ≤
      (2 * dyadicPrimeConstant / ((Nat.log2 n + 1 : ℕ) : ℝ)) *
        (((2 ^ (Nat.log2 n + 1) : ℕ) : ℝ)) *
          (∑' z : ℕ × ℕ, if K < z.1 + z.2 then
            canonicalActualMainWeight z.1 z.2 else 0) := by
  classical
  let I := Finset.range (Nat.log2 n + 1)
  have hreorder : canonicalPersistentSum A n (2 ^ (K + 2)) =
      ∑ jk ∈ I.product I, ∑ i ∈ I,
        canonicalPersistentTerm A n (2 ^ (K + 2)) i jk.1 jk.2 := by
    dsimp [canonicalPersistentSum, dyadicIndexCube, I]
    rw [Finset.sum_product, Finset.sum_comm]
  rw [hreorder]
  calc
    (∑ jk ∈ I.product I, ∑ i ∈ I,
        canonicalPersistentTerm A n (2 ^ (K + 2)) i jk.1 jk.2) ≤
      ∑ jk ∈ I.product I,
        (2 * dyadicPrimeConstant / ((Nat.log2 n + 1 : ℕ) : ℝ)) *
          canonicalActualMainWeight jk.1 jk.2 *
            (if K < jk.1 + jk.2 then
              ((2 ^ (Nat.log2 n + 1) : ℕ) : ℝ) else 0) := by
        apply Finset.sum_le_sum
        intro jk hjk
        exact canonicalPersistent_iSum_le hn hAint hprime hlogLarge
    _ = (2 * dyadicPrimeConstant / ((Nat.log2 n + 1 : ℕ) : ℝ)) *
        (((2 ^ (Nat.log2 n + 1) : ℕ) : ℝ)) *
          ∑ jk ∈ I.product I, (if K < jk.1 + jk.2 then
            canonicalActualMainWeight jk.1 jk.2 else 0) := by
      symm
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro jk hjk
      by_cases hdeg : K < jk.1 + jk.2 <;> simp [hdeg] <;> ring
    _ ≤ (2 * dyadicPrimeConstant / ((Nat.log2 n + 1 : ℕ) : ℝ)) *
        (((2 ^ (Nat.log2 n + 1) : ℕ) : ℝ)) *
          (∑' z : ℕ × ℕ, if K < z.1 + z.2 then
            canonicalActualMainWeight z.1 z.2 else 0) := by
      have hsOrient : Summable (fun z : ℕ × ℕ =>
          canonicalActualMainWeight z.1 z.2) := by
        simpa [Function.comp_def] using
          summable_canonicalActualMainWeight.comp_injective
            (i := Prod.swap) Prod.swap_injective
      have hsum := (hsOrient.indicator
        {z : ℕ × ℕ | K < z.1 + z.2}).sum_le_tsum (I.product I)
        (fun z hz => by
          by_cases hdeg : K < z.1 + z.2
          · simp [hdeg, canonicalActualMainWeight_nonneg]
          · simp [hdeg])
      have hsum' : (∑ jk ∈ I.product I,
          if K < jk.1 + jk.2 then canonicalActualMainWeight jk.1 jk.2 else 0) ≤
          (∑' z : ℕ × ℕ, if K < z.1 + z.2 then
            canonicalActualMainWeight z.1 z.2 else 0) := by
        simpa [Set.indicator] using hsum
      have hpref : 0 ≤
          (2 * dyadicPrimeConstant / ((Nat.log2 n + 1 : ℕ) : ℝ)) *
            (((2 ^ (Nat.log2 n + 1) : ℕ) : ℝ)) := by
        exact mul_nonneg
          (div_nonneg (mul_nonneg (by norm_num) dyadicPrimeConstant_pos.le)
            (by positivity)) (by positivity)
      exact mul_le_mul_of_nonneg_left hsum' hpref

/-- After second-order normalization, the global persistent error is bounded
by a universal constant times its summable degree tail. -/
theorem eventually_canonicalPersistentSum_normalized_le (K : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ A : Finset ℕ, A ⊆ Finset.Icc 1 n →
      canonicalPersistentSum A n (2 ^ (K + 2)) /
          ((n : ℝ) / Real.log (n : ℝ)) ≤
        (4 * dyadicPrimeConstant * Real.log 2) *
          (∑' z : ℕ × ℕ, if K < z.1 + z.2 then
            canonicalActualMainWeight z.1 z.2 else 0) := by
  rcases (eventually_atTop.1 eventually_dyadicPrimes_card_le) with ⟨I₀, hI₀⟩
  have hlog2 := tendsto_nat_log2_atTop.eventually_ge_atTop (2 * I₀)
  filter_upwards [eventually_gt_atTop 1, hlog2] with n hn hL
  intro A hAint
  have hnpos : 0 < n := by omega
  have hraw := canonicalPersistentSum_le (K := K) (I₀ := I₀)
    hnpos hAint hI₀ hL
  let tail : ℝ := ∑' z : ℕ × ℕ, if K < z.1 + z.2 then
    canonicalActualMainWeight z.1 z.2 else 0
  have htail : 0 ≤ tail := by
    apply tsum_nonneg
    intro z
    split_ifs
    · exact canonicalActualMainWeight_nonneg z.1 z.2
    · rfl
  have hnR : (0 : ℝ) < n := by positivity
  have hlogpos : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn)
  have hden : 0 < (n : ℝ) / Real.log (n : ℝ) := div_pos hnR hlogpos
  have hlogBound := real_log_le_log2_add_one_mul_log_two (by omega : 0 < n)
  have hpowNat : 2 ^ (Nat.log2 n + 1) ≤ 2 * n := by
    rw [pow_succ]
    simpa [mul_comm] using
      Nat.mul_le_mul_left 2 (two_pow_log2_le (by omega : n ≠ 0))
  have hpowBound : (((2 ^ (Nat.log2 n + 1) : ℕ) : ℝ)) ≤ 2 * (n : ℝ) := by
    exact_mod_cast hpowNat
  have hLpos : (0 : ℝ) < ((Nat.log2 n + 1 : ℕ) : ℝ) := by positivity
  have hcoef :
      ((2 * dyadicPrimeConstant / ((Nat.log2 n + 1 : ℕ) : ℝ)) *
          (((2 ^ (Nat.log2 n + 1) : ℕ) : ℝ))) /
          ((n : ℝ) / Real.log (n : ℝ)) ≤
        4 * dyadicPrimeConstant * Real.log 2 := by
    rw [div_secondOrder_eq_mul_log_div hn]
    have heq :
        (2 * dyadicPrimeConstant / ((Nat.log2 n + 1 : ℕ) : ℝ) *
            (((2 ^ (Nat.log2 n + 1) : ℕ) : ℝ))) * Real.log (n : ℝ) /
            (n : ℝ) =
          (2 * dyadicPrimeConstant *
            (((2 ^ (Nat.log2 n + 1) : ℕ) : ℝ)) * Real.log (n : ℝ)) /
            (((Nat.log2 n + 1 : ℕ) : ℝ) * (n : ℝ)) := by
      field_simp [ne_of_gt hLpos, ne_of_gt hnR]
    rw [heq]
    apply (div_le_iff₀ (mul_pos hLpos hnR)).2
    calc
      2 * dyadicPrimeConstant *
          (((2 ^ (Nat.log2 n + 1) : ℕ) : ℝ)) * Real.log (n : ℝ) ≤
        2 * dyadicPrimeConstant *
          (((2 ^ (Nat.log2 n + 1) : ℕ) : ℝ)) *
            (((Nat.log2 n + 1 : ℕ) : ℝ) * Real.log 2) := by
          exact mul_le_mul_of_nonneg_left hlogBound
            (mul_nonneg
              (mul_nonneg (by norm_num) dyadicPrimeConstant_pos.le)
              (by positivity))
      _ ≤ 2 * dyadicPrimeConstant * (2 * (n : ℝ)) *
            (((Nat.log2 n + 1 : ℕ) : ℝ) * Real.log 2) := by
          have htwoC : (0 : ℝ) ≤ 2 * dyadicPrimeConstant :=
            mul_nonneg (by norm_num) dyadicPrimeConstant_pos.le
          have hp : 2 * dyadicPrimeConstant *
              (((2 ^ (Nat.log2 n + 1) : ℕ) : ℝ)) ≤
              2 * dyadicPrimeConstant * (2 * (n : ℝ)) :=
            mul_le_mul_of_nonneg_left hpowBound htwoC
          have hBlog : (0 : ℝ) ≤
              (((Nat.log2 n + 1 : ℕ) : ℝ) * Real.log 2) :=
            mul_nonneg (by positivity)
              (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le
          exact mul_le_mul_of_nonneg_right hp hBlog
      _ = (4 * dyadicPrimeConstant * Real.log 2) *
          (((Nat.log2 n + 1 : ℕ) : ℝ) * (n : ℝ)) := by ring
  have hdiv := div_le_div_of_nonneg_right hraw hden.le
  change canonicalPersistentSum A n (2 ^ (K + 2)) /
      ((n : ℝ) / Real.log (n : ℝ)) ≤ _
  apply hdiv.trans
  change ((2 * dyadicPrimeConstant / ((Nat.log2 n + 1 : ℕ) : ℝ)) *
      (((2 ^ (Nat.log2 n + 1) : ℕ) : ℝ)) * tail) /
      ((n : ℝ) / Real.log (n : ℝ)) ≤
        (4 * dyadicPrimeConstant * Real.log 2) * tail
  rw [show
    ((2 * dyadicPrimeConstant / ((Nat.log2 n + 1 : ℕ) : ℝ)) *
      (((2 ^ (Nat.log2 n + 1) : ℕ) : ℝ)) * tail) /
      ((n : ℝ) / Real.log (n : ℝ)) =
    (((2 * dyadicPrimeConstant / ((Nat.log2 n + 1 : ℕ) : ℝ)) *
      (((2 ^ (Nat.log2 n + 1) : ℕ) : ℝ))) /
      ((n : ℝ) / Real.log (n : ℝ))) * tail by ring]
  exact mul_le_mul_of_nonneg_right hcoef htail

/-- The actual persistent block weights also have vanishing total-degree
tails (coefficient index first). -/
theorem tendsto_canonicalActualMainWeight_degreeTail_zero' :
    Tendsto (fun K : ℕ => ∑' z : ℕ × ℕ,
      if K < z.1 + z.2 then canonicalActualMainWeight z.1 z.2 else 0)
      atTop (nhds 0) := by
  have hsOrient : Summable (fun z : ℕ × ℕ =>
      canonicalActualMainWeight z.1 z.2) := by
    simpa [Function.comp_def] using
      summable_canonicalActualMainWeight.comp_injective
        (i := Prod.swap) Prod.swap_injective
  have h := tendsto_tsum_of_dominated_convergence
    (𝓕 := atTop)
    (f := fun K (z : ℕ × ℕ) =>
      if K < z.1 + z.2 then canonicalActualMainWeight z.1 z.2 else 0)
    (g := fun _z : ℕ × ℕ => (0 : ℝ))
    hsOrient
    (fun z => by
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_ge_atTop (z.1 + z.2)] with K hK
      simp [show ¬K < z.1 + z.2 by omega])
    (by
      filter_upwards [eventually_ge_atTop 0] with K hK
      intro z
      by_cases hz : K < z.1 + z.2
      · simp [hz, abs_of_nonneg (canonicalActualMainWeight_nonneg z.1 z.2)]
      · simp [hz, canonicalActualMainWeight_nonneg z.1 z.2])
  simpa using h

/-- The same tail theorem with the two dyadic coordinates reversed. -/
theorem tendsto_canonicalActualMainWeight_degreeTail_zero :
    Tendsto (fun K : ℕ => ∑' z : ℕ × ℕ,
      if K < z.1 + z.2 then canonicalActualMainWeight z.2 z.1 else 0)
      atTop (nhds 0) := by
  have h := tendsto_tsum_of_dominated_convergence
    (𝓕 := atTop)
    (f := fun K (z : ℕ × ℕ) =>
      if K < z.1 + z.2 then canonicalActualMainWeight z.2 z.1 else 0)
    (g := fun _z : ℕ × ℕ => (0 : ℝ))
    summable_canonicalActualMainWeight
    (fun z => by
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_ge_atTop (z.1 + z.2)] with K hK
      simp [show ¬K < z.1 + z.2 by omega])
    (by
      filter_upwards [eventually_ge_atTop 0] with K hK
      intro z
      by_cases hz : K < z.1 + z.2
      · simp [hz, abs_of_nonneg (canonicalActualMainWeight_nonneg z.2 z.1)]
      · simp [hz, canonicalActualMainWeight_nonneg z.2 z.1])
  simpa using h

/-- The summable persistent error has vanishing tails in total dyadic degree. -/
theorem tendsto_canonicalMainWeight_degreeTail_zero :
    Tendsto (fun K : ℕ => ∑' z : ℕ × ℕ,
      if K < z.1 + z.2 then canonicalMainWeight z.2 z.1 else 0)
      atTop (nhds 0) := by
  have hdom := summable_canonicalMainWeight
  have h := tendsto_tsum_of_dominated_convergence
    (𝓕 := atTop)
    (f := fun K (z : ℕ × ℕ) =>
      if K < z.1 + z.2 then canonicalMainWeight z.2 z.1 else 0)
    (g := fun _z : ℕ × ℕ => (0 : ℝ))
    hdom
    (fun z => by
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_ge_atTop (z.1 + z.2)] with K hK
      simp [show ¬K < z.1 + z.2 by omega])
    (by
      filter_upwards [eventually_ge_atTop 0] with K hK
      intro z
      by_cases hz : K < z.1 + z.2
      · simp [hz, abs_of_nonneg (canonicalMainWeight_nonneg z.2 z.1)]
      · simp [hz, canonicalMainWeight_nonneg z.2 z.1])
  simpa using h

end Erdos796
