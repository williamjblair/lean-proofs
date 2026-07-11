/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import ErdosProblems.Erdos686GlobalSquareLift

/-!
# Erdős 686: valuation concentration in the global residual progression

The global square lift puts `d^2` into the product of the positive residuals

`X_i = 3 * (n+i) - d`.

For a prime `p != 3`, all `p`-adic valuation outside a maximum residual costs
at most `v_p((k-1)!)`.  Since the input is a square, a clean local square
therefore loses only half that exponent.  At `p=3`, every residual has one
common factor.  Dividing the whole progression by three leaves the consecutive
block `n-d/3+i`; its exact common-factor cost is tracked rather than hidden in
a coarse constant.
-/

namespace Erdos686
namespace Erdos686Variant

open scoped BigOperators

/-- The residual-cleaning exponent lost from a prime-power component.  For
`p != 3` this is `ceil(v_p((k-1)!)/2)`.  At `p=3` it is
`ceil((k+v_3((k-1)!)-1)/2)`. -/
def globalResidualLossExponent (p k : ℕ) : ℕ :=
  if p = 3 then
    (k + (k - 1).factorial.factorization 3) / 2
  else
    ((k - 1).factorial.factorization p + 1) / 2

/-- The prime-power exponent retained after global residual cleaning. -/
def globalResidualCleanExponent (p e k : ℕ) : ℕ :=
  e - globalResidualLossExponent p k

private lemma prime_not_dvd_three_of_ne_three
    {p : ℕ} (hp : p.Prime) (hp3 : p ≠ 3) : ¬p ∣ 3 := by
  intro hdiv
  rcases (Nat.dvd_prime (by norm_num : Nat.Prime 3)).mp hdiv with hp1 | hp3'
  · exact hp.ne_one hp1
  · exact hp3 hp3'

private lemma globalLocalResidualNat_dist
    {n d i j : ℕ}
    (hi : d ≤ 3 * (n + i))
    (hj : d ≤ 3 * (n + j)) :
    Nat.dist (globalLocalResidualNat n d i)
        (globalLocalResidualNat n d j) =
      3 * Nat.dist i j := by
  unfold globalLocalResidualNat
  rcases le_total i j with hij | hji
  · rw [Nat.dist_eq_sub_of_le, Nat.dist_eq_sub_of_le hij]
    · omega
    · omega
  · rw [Nat.dist_eq_sub_of_le_right, Nat.dist_eq_sub_of_le_right hji]
    · omega
    · omega

/-- Valuation concentration in the residual arithmetic progression for
`p != 3`.  Multiplication by the step `3` is harmless because it is a unit
modulo every such prime. -/
theorem exists_globalResidual_factorization_concentration_of_ne_three
    {p k n d : ℕ}
    (hp : p.Prime)
    (hp3 : p ≠ 3)
    (hk : 1 ≤ k)
    (hpos : ∀ i ∈ Finset.Icc 1 k, d < 3 * (n + i)) :
    ∃ i, i ∈ Finset.Icc 1 k ∧
      (∏ j ∈ Finset.Icc 1 k,
          globalLocalResidualNat n d j).factorization p ≤
        (globalLocalResidualNat n d i).factorization p +
          (k - 1).factorial.factorization p := by
  let s : Finset ℕ := Finset.Icc 1 k
  have hs : s.Nonempty := by
    refine ⟨1, ?_⟩
    exact Finset.mem_Icc.mpr ⟨le_rfl, hk⟩
  obtain ⟨i, hi, hmax⟩ :=
    Finset.exists_max_image s
      (fun j => (globalLocalResidualNat n d j).factorization p) hs
  have hiIcc : i ∈ Finset.Icc 1 k := by simpa [s] using hi
  have hpowDist : ∀ j ∈ s.erase i,
      p ^ (globalLocalResidualNat n d j).factorization p ∣ Nat.dist i j := by
    intro j hjErase
    have hj : j ∈ s := (Finset.mem_erase.mp hjErase).2
    have hjIcc : j ∈ Finset.Icc 1 k := by simpa [s] using hj
    have hji : j ≠ i := (Finset.mem_erase.mp hjErase).1
    have hXi0 : globalLocalResidualNat n d i ≠ 0 := by
      unfold globalLocalResidualNat
      have := hpos i hiIcc
      omega
    have hXj0 : globalLocalResidualNat n d j ≠ 0 := by
      unfold globalLocalResidualNat
      have := hpos j hjIcc
      omega
    have hpowj : p ^ (globalLocalResidualNat n d j).factorization p ∣
        globalLocalResidualNat n d j :=
      (hp.pow_dvd_iff_le_factorization hXj0).mpr le_rfl
    have hpowi : p ^ (globalLocalResidualNat n d j).factorization p ∣
        globalLocalResidualNat n d i :=
      (hp.pow_dvd_iff_le_factorization hXi0).mpr (hmax j hj)
    have hdistX : p ^ (globalLocalResidualNat n d j).factorization p ∣
        Nat.dist (globalLocalResidualNat n d i)
          (globalLocalResidualNat n d j) := by
      rcases le_total (globalLocalResidualNat n d i)
          (globalLocalResidualNat n d j) with hle | hge
      · rw [Nat.dist_eq_sub_of_le hle]
        exact Nat.dvd_sub hpowj hpowi
      · rw [Nat.dist_eq_sub_of_le_right hge]
        exact Nat.dvd_sub hpowi hpowj
    have hstep : p ^ (globalLocalResidualNat n d j).factorization p ∣
        3 * Nat.dist i j := by
      rw [← globalLocalResidualNat_dist
        (Nat.le_of_lt (hpos i hiIcc)) (Nat.le_of_lt (hpos j hjIcc))]
      exact hdistX
    exact
      (hp.coprime_pow_of_not_dvd
          (m := (globalLocalResidualNat n d j).factorization p)
          (prime_not_dvd_three_of_ne_three hp hp3)).symm.dvd_of_dvd_mul_left
        hstep
  have hprodDvd :
      (∏ j ∈ s.erase i,
          p ^ (globalLocalResidualNat n d j).factorization p) ∣
        ∏ j ∈ s.erase i, Nat.dist i j := by
    exact Finset.prod_dvd_prod_of_dvd _ _ hpowDist
  have hpowCoeff :
      p ^ (∑ j ∈ s.erase i,
          (globalLocalResidualNat n d j).factorization p) ∣
        localBlockCoefficientNat k i := by
    calc
      p ^ (∑ j ∈ s.erase i,
          (globalLocalResidualNat n d j).factorization p) =
          ∏ j ∈ s.erase i,
            p ^ (globalLocalResidualNat n d j).factorization p := by
              rw [Finset.prod_pow_eq_pow_sum]
      _ ∣ ∏ j ∈ s.erase i, Nat.dist i j := hprodDvd
      _ = localBlockCoefficientNat k i :=
        prod_dist_erase_eq_localBlockCoefficientNat hiIcc
  have hcoeff0 : localBlockCoefficientNat k i ≠ 0 := by
    unfold localBlockCoefficientNat
    exact mul_ne_zero (Nat.factorial_ne_zero _) (Nat.factorial_ne_zero _)
  have hsumCoeff :
      (∑ j ∈ s.erase i,
          (globalLocalResidualNat n d j).factorization p) ≤
        (localBlockCoefficientNat k i).factorization p :=
    (hp.pow_dvd_iff_le_factorization hcoeff0).mp hpowCoeff
  have hcoeffDvd : localBlockCoefficientNat k i ∣ (k - 1).factorial :=
    localBlockCoefficientNat_dvd_factorial_pred hiIcc
  have hcoeffVal :
      (localBlockCoefficientNat k i).factorization p ≤
        (k - 1).factorial.factorization p :=
    ((Nat.factorization_le_iff_dvd hcoeff0 (Nat.factorial_ne_zero _)).mpr
      hcoeffDvd) p
  have hterms0 : ∀ j ∈ s, globalLocalResidualNat n d j ≠ 0 := by
    intro j hj
    unfold globalLocalResidualNat
    have hjIcc : j ∈ Finset.Icc 1 k := by simpa [s] using hj
    have := hpos j hjIcc
    omega
  have hprodVal :
      (∏ j ∈ s, globalLocalResidualNat n d j).factorization p =
        ∑ j ∈ s, (globalLocalResidualNat n d j).factorization p :=
    Nat.factorization_prod_apply (p := p) hterms0
  have hsumSplit :
      (∑ j ∈ s, (globalLocalResidualNat n d j).factorization p) =
        (globalLocalResidualNat n d i).factorization p +
          ∑ j ∈ s.erase i,
            (globalLocalResidualNat n d j).factorization p :=
    (Finset.add_sum_erase s
      (fun j => (globalLocalResidualNat n d j).factorization p) hi).symm
  refine ⟨i, hiIcc, ?_⟩
  rw [show Finset.Icc 1 k = s by rfl, hprodVal, hsumSplit]
  omega

private lemma residual_three_reduction
    {k n d : ℕ}
    (hk : 1 ≤ k)
    (hthree : 3 ∣ d)
    (hpos : ∀ i ∈ Finset.Icc 1 k, d < 3 * (n + i)) :
    d / 3 ≤ n ∧
      ∀ i ∈ Finset.Icc 1 k,
        globalLocalResidualNat n d i = 3 * (n - d / 3 + i) := by
  have hqeq : 3 * (d / 3) = d := Nat.mul_div_cancel' hthree
  have hqle : d / 3 ≤ n := by
    have h1 : (1 : ℕ) ∈ Finset.Icc 1 k :=
      Finset.mem_Icc.mpr ⟨le_rfl, hk⟩
    have hp := hpos 1 h1
    omega
  refine ⟨hqle, ?_⟩
  intro i hi
  unfold globalLocalResidualNat
  have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
  omega

/-- Exact `p=3` accounting.  After removing the common factor three from
each residual, the remaining factors are one consecutive block. -/
theorem three_factorization_globalResidual_product
    {k n d : ℕ}
    (hk : 1 ≤ k)
    (hthree : 3 ∣ d)
    (hpos : ∀ i ∈ Finset.Icc 1 k, d < 3 * (n + i)) :
    (∏ i ∈ Finset.Icc 1 k,
        globalLocalResidualNat n d i).factorization 3 =
      k + (blockProduct k (n - d / 3)).factorization 3 := by
  obtain ⟨hqle, hres⟩ := residual_three_reduction hk hthree hpos
  have hcard : (Finset.Icc 1 k).card = k := by simp [Nat.card_Icc]
  have hprodEq :
      (∏ i ∈ Finset.Icc 1 k, globalLocalResidualNat n d i) =
        3 ^ k * blockProduct k (n - d / 3) := by
    unfold blockProduct
    calc
      (∏ i ∈ Finset.Icc 1 k, globalLocalResidualNat n d i) =
          ∏ i ∈ Finset.Icc 1 k, (3 * (n - d / 3 + i)) := by
            apply Finset.prod_congr rfl
            intro i hi
            exact hres i hi
      _ = (∏ _i ∈ Finset.Icc 1 k, 3) *
          ∏ i ∈ Finset.Icc 1 k, (n - d / 3 + i) := by
            rw [← Finset.prod_mul_distrib]
      _ = 3 ^ k * ∏ i ∈ Finset.Icc 1 k, (n - d / 3 + i) := by
            simp [Finset.prod_const, hcard]
  have hblock0 : blockProduct k (n - d / 3) ≠ 0 :=
    ne_of_gt (blockProduct_pos k (n - d / 3))
  rw [hprodEq, Nat.factorization_mul (pow_ne_zero _ (by norm_num)) hblock0,
    Nat.factorization_pow]
  norm_num

/-- A prime power `p^e | d`, `p != 3`, has a cleaned divisor concentrated in
one residual.  It divides the gap and the corresponding lower factor, while
its square divides the residual. -/
theorem primePower_component_exists_globalResidual_clean_of_ne_three
    {p e k n d : ℕ}
    (hp : p.Prime)
    (hp3 : p ≠ 3)
    (hk5 : 5 ≤ k)
    (hkd : k ≤ d)
    (hd : p ^ e ∣ d)
    (heq : blockProduct k (n + d) = 4 * blockProduct k n) :
    ∃ i, i ∈ Finset.Icc 1 k ∧
      p ^ globalResidualCleanExponent p e k ∣ d ∧
      p ^ globalResidualCleanExponent p e k ∣ n + i ∧
      (p ^ globalResidualCleanExponent p e k) ^ 2 ∣
        globalLocalResidualNat n d i ∧
      p ^ e ≤ p ^ globalResidualLossExponent p k *
        p ^ globalResidualCleanExponent p e k := by
  have hgap := twice_gap_lt_n_of_four_solution hk5 hkd heq
  have hpos : ∀ i ∈ Finset.Icc 1 k, d < 3 * (n + i) := by
    intro i hi
    have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
    omega
  have hprod0 :
      (∏ i ∈ Finset.Icc 1 k, globalLocalResidualNat n d i) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro i hi
    unfold globalLocalResidualNat
    have := hpos i hi
    omega
  have hsquare := gap_sq_dvd_globalLocalResidualNat_product hk5 hkd heq
  have hpTwoE : p ^ (2 * e) ∣
      ∏ i ∈ Finset.Icc 1 k, globalLocalResidualNat n d i := by
    have hpowSq : (p ^ e) * (p ^ e) ∣ d * d := Nat.mul_dvd_mul hd hd
    have hsquare' : d * d ∣
        ∏ i ∈ Finset.Icc 1 k, globalLocalResidualNat n d i := by
      simpa [pow_two] using hsquare
    have htrans := dvd_trans hpowSq hsquare'
    simpa [← pow_add, two_mul] using htrans
  have htotal : 2 * e ≤
      (∏ i ∈ Finset.Icc 1 k,
        globalLocalResidualNat n d i).factorization p :=
    (hp.pow_dvd_iff_le_factorization hprod0).mp hpTwoE
  obtain ⟨i, hi, hconcentration⟩ :=
    exists_globalResidual_factorization_concentration_of_ne_three
      hp hp3 (by omega : 1 ≤ k) hpos
  let V : ℕ := (k - 1).factorial.factorization p
  let c : ℕ := (V + 1) / 2
  let t : ℕ := e - c
  have hc : c = globalResidualLossExponent p k := by
    simp [c, V, globalResidualLossExponent, hp3]
  have ht : t = globalResidualCleanExponent p e k := by
    simp [t, globalResidualCleanExponent, ← hc]
  have hlocalVal : 2 * t ≤
      (globalLocalResidualNat n d i).factorization p := by
    dsimp [V, c, t]
    omega
  have hXi0 : globalLocalResidualNat n d i ≠ 0 := by
    unfold globalLocalResidualNat
    have := hpos i hi
    omega
  have htE : t ≤ e := by dsimp [t]; omega
  have htDvdD : p ^ t ∣ d := dvd_trans (pow_dvd_pow p htE) hd
  have htSqDvdX : (p ^ t) ^ 2 ∣ globalLocalResidualNat n d i := by
    have : p ^ (2 * t) ∣ globalLocalResidualNat n d i :=
      (hp.pow_dvd_iff_le_factorization hXi0).mpr hlocalVal
    simpa [pow_two, ← pow_add, two_mul] using this
  have htDvdX : p ^ t ∣ globalLocalResidualNat n d i := by
    exact dvd_trans (by
      refine ⟨p ^ t, ?_⟩
      ring) htSqDvdX
  have hXadd : globalLocalResidualNat n d i + d = 3 * (n + i) := by
    unfold globalLocalResidualNat
    have := hpos i hi
    omega
  have htDvdThree : p ^ t ∣ 3 * (n + i) := by
    rw [← hXadd]
    exact dvd_add htDvdX htDvdD
  have htFactor : p ^ t ∣ n + i :=
    (hp.coprime_pow_of_not_dvd (m := t)
      (prime_not_dvd_three_of_ne_three hp hp3)).symm.dvd_of_dvd_mul_left
        htDvdThree
  have heBound : p ^ e ≤ p ^ c * p ^ t := by
    rw [← pow_add]
    apply Nat.pow_le_pow_right hp.pos
    dsimp [t]
    omega
  refine ⟨i, hi, ?_, ?_, ?_, ?_⟩
  · simpa [ht] using htDvdD
  · simpa [ht] using htFactor
  · simpa [ht] using htSqDvdX
  · simpa [hc, ht] using heBound

/-- The exact `p=3` counterpart.  The common `3` in every residual and the
loss in the reduced consecutive block are both visible in the exponent. -/
theorem threePower_component_exists_globalResidual_clean
    {e k n d : ℕ}
    (he : 0 < e)
    (hk5 : 5 ≤ k)
    (hkd : k ≤ d)
    (hd : 3 ^ e ∣ d)
    (heq : blockProduct k (n + d) = 4 * blockProduct k n) :
    ∃ i, i ∈ Finset.Icc 1 k ∧
      3 ^ globalResidualCleanExponent 3 e k ∣ d ∧
      3 ^ globalResidualCleanExponent 3 e k ∣ n + i ∧
      (3 ^ globalResidualCleanExponent 3 e k) ^ 2 ∣
        globalLocalResidualNat n d i ∧
      3 ^ e ≤ 3 ^ globalResidualLossExponent 3 k *
        3 ^ globalResidualCleanExponent 3 e k := by
  have hthreePow : 3 ^ 1 ∣ 3 ^ e := pow_dvd_pow 3 he
  have hthree : 3 ∣ d := by
    exact dvd_trans (by simpa using hthreePow) hd
  have hgap := twice_gap_lt_n_of_four_solution hk5 hkd heq
  have hpos : ∀ i ∈ Finset.Icc 1 k, d < 3 * (n + i) := by
    intro i hi
    have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
    omega
  obtain ⟨hqle, hres⟩ :=
    residual_three_reduction (by omega : 1 ≤ k) hthree hpos
  have hprod0 :
      (∏ i ∈ Finset.Icc 1 k, globalLocalResidualNat n d i) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro i hi
    unfold globalLocalResidualNat
    have := hpos i hi
    omega
  have hsquare := gap_sq_dvd_globalLocalResidualNat_product hk5 hkd heq
  have hpTwoE : 3 ^ (2 * e) ∣
      ∏ i ∈ Finset.Icc 1 k, globalLocalResidualNat n d i := by
    have hpowSq : (3 ^ e) * (3 ^ e) ∣ d * d := Nat.mul_dvd_mul hd hd
    have hsquare' : d * d ∣
        ∏ i ∈ Finset.Icc 1 k, globalLocalResidualNat n d i := by
      simpa [pow_two] using hsquare
    have htrans := dvd_trans hpowSq hsquare'
    simpa [← pow_add, two_mul] using htrans
  have htotal : 2 * e ≤
      (∏ i ∈ Finset.Icc 1 k,
        globalLocalResidualNat n d i).factorization 3 :=
    ((by norm_num : Nat.Prime 3).pow_dvd_iff_le_factorization hprod0).mp hpTwoE
  have hprodVal :
      (∏ i ∈ Finset.Icc 1 k,
        globalLocalResidualNat n d i).factorization 3 =
      k + (blockProduct k (n - d / 3)).factorization 3 :=
    three_factorization_globalResidual_product
      (by omega : 1 ≤ k) hthree hpos
  obtain ⟨i, hi, hconcentration⟩ :=
    exists_blockProduct_factorization_concentration
      (by norm_num : Nat.Prime 3) (by omega : 1 ≤ k) (n := n - d / 3)
  let V : ℕ := (k - 1).factorial.factorization 3
  let c : ℕ := (k + V) / 2
  let t : ℕ := e - c
  have hc : c = globalResidualLossExponent 3 k := by
    simp [c, V, globalResidualLossExponent]
  have ht : t = globalResidualCleanExponent 3 e k := by
    simp [t, globalResidualCleanExponent, ← hc]
  have hYVal : 2 * t ≤
      1 + (n - d / 3 + i).factorization 3 := by
    rw [hprodVal] at htotal
    dsimp [V, c, t]
    omega
  have hY0 : n - d / 3 + i ≠ 0 := by
    have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
    omega
  have hXi0 : globalLocalResidualNat n d i ≠ 0 := by
    rw [hres i hi]
    exact mul_ne_zero (by norm_num) hY0
  have hXiVal :
      (globalLocalResidualNat n d i).factorization 3 =
        1 + (n - d / 3 + i).factorization 3 := by
    rw [hres i hi, Nat.factorization_mul (by norm_num) hY0]
    norm_num
  have htSqDvdX : (3 ^ t) ^ 2 ∣ globalLocalResidualNat n d i := by
    have : 3 ^ (2 * t) ∣ globalLocalResidualNat n d i :=
      ((by norm_num : Nat.Prime 3).pow_dvd_iff_le_factorization hXi0).mpr (by
        rw [hXiVal]
        exact hYVal)
    simpa [pow_two, ← pow_add, two_mul] using this
  have hcpos : 0 < c := by
    dsimp [c]
    have : 2 ≤ k + V := by omega
    omega
  have htPredE : t ≤ e - 1 := by
    dsimp [t]
    omega
  have htDvdD : 3 ^ t ∣ d :=
    dvd_trans (pow_dvd_pow 3 (by omega : t ≤ e)) hd
  have htDvdDThird : 3 ^ t ∣ d / 3 := by
    apply (Nat.dvd_div_iff_mul_dvd hthree).2
    have hpow : 3 ^ (t + 1) ∣ d :=
      dvd_trans (pow_dvd_pow 3 (by omega : t + 1 ≤ e)) hd
    simpa [pow_succ, mul_comm] using hpow
  have htDvdY : 3 ^ t ∣ n - d / 3 + i := by
    by_cases ht0 : t = 0
    · rw [ht0]
      exact one_dvd _
    · have htVal : t ≤ (n - d / 3 + i).factorization 3 := by omega
      exact ((by norm_num : Nat.Prime 3).pow_dvd_iff_le_factorization hY0).mpr htVal
  have hYadd : n - d / 3 + i + d / 3 = n + i := by omega
  have htFactor : 3 ^ t ∣ n + i := by
    rw [← hYadd]
    exact dvd_add htDvdY htDvdDThird
  have heBound : 3 ^ e ≤ 3 ^ c * 3 ^ t := by
    rw [← pow_add]
    apply Nat.pow_le_pow_right (by norm_num)
    dsimp [t]
    omega
  refine ⟨i, hi, ?_, ?_, ?_, ?_⟩
  · simpa [ht] using htDvdD
  · simpa [ht] using htFactor
  · simpa [ht] using htSqDvdX
  · simpa [hc, ht] using heBound

/-- Unified clean-component theorem for every prime base in the six odd
target rows. -/
theorem primePower_component_exists_globalResidual_clean
    {p e k n d : ℕ}
    (hp : p.Prime)
    (he : 0 < e)
    (hk5 : 5 ≤ k)
    (hkd : k ≤ d)
    (hd : p ^ e ∣ d)
    (heq : blockProduct k (n + d) = 4 * blockProduct k n) :
    ∃ i, i ∈ Finset.Icc 1 k ∧
      p ^ globalResidualCleanExponent p e k ∣ d ∧
      p ^ globalResidualCleanExponent p e k ∣ n + i ∧
      (p ^ globalResidualCleanExponent p e k) ^ 2 ∣
        globalLocalResidualNat n d i ∧
      p ^ e ≤ p ^ globalResidualLossExponent p k *
      p ^ globalResidualCleanExponent p e k := by
  by_cases hp3 : p = 3
  · subst p
    exact threePower_component_exists_globalResidual_clean he hk5 hkd hd heq
  · exact primePower_component_exists_globalResidual_clean_of_ne_three
      hp hp3 hk5 hkd hd heq

/-- In the full small odd-row range, the loss for any one prime-power
component is at most `3^10 = 59049`.  For primes other than three the sharper
uniform bound is `64`. -/
theorem globalResidual_prime_loss_factor_le
    {p k : ℕ}
    (hp : p.Prime)
    (hk5 : 5 ≤ k)
    (hk15 : k ≤ 15) :
    p ^ globalResidualLossExponent p k ≤
      if p = 3 then 59049 else 64 := by
  have hkPred14 : k - 1 ≤ 14 := by omega
  have hfacDvd : (k - 1).factorial ∣ (14 : ℕ).factorial :=
    Nat.factorial_dvd_factorial hkPred14
  have hfacLe : (k - 1).factorial.factorization p ≤
      (14 : ℕ).factorial.factorization p :=
    ((Nat.factorization_le_iff_dvd
      (Nat.factorial_ne_zero _) (Nat.factorial_ne_zero _)).mpr hfacDvd) p
  by_cases hp3 : p = 3
  · subst p
    have hval : ((14 : ℕ).factorial).factorization 3 = 5 := by
      rw [Nat.factorization_factorial (by norm_num : Nat.Prime 3)
        (show Nat.log 3 14 < 3 by norm_num)]
      norm_num [Finset.sum_Ico_succ_top]
    rw [hval] at hfacLe
    simp only [globalResidualLossExponent, if_pos]
    calc
      3 ^ ((k + (k - 1).factorial.factorization 3) / 2) ≤ 3 ^ 10 :=
        Nat.pow_le_pow_right (by norm_num) (by omega)
      _ = 59049 := by norm_num
  · simp only [hp3, if_false, globalResidualLossExponent]
    by_cases hpk : k ≤ p
    · have hpNotDvd : ¬p ∣ (k - 1).factorial := by
        rw [Nat.Prime.dvd_factorial hp]
        omega
      have hzero : (k - 1).factorial.factorization p = 0 :=
        Nat.factorization_eq_zero_of_not_dvd hpNotDvd
      simp [hzero]
    · have hpk' : p < k := by omega
      have hp14 : p ≤ 14 := by omega
      have hpCases : p = 2 ∨ p = 5 ∨ p = 7 ∨ p = 11 ∨ p = 13 := by
        interval_cases p <;> norm_num at hp
        all_goals simp_all
      rcases hpCases with rfl | rfl | rfl | rfl | rfl
      · have hval : ((14 : ℕ).factorial).factorization 2 = 11 := by
          rw [Nat.factorization_factorial (by norm_num : Nat.Prime 2)
            (show Nat.log 2 14 < 4 by norm_num)]
          norm_num [Finset.sum_Ico_succ_top]
        rw [hval] at hfacLe
        change 2 ^ (((k - 1).factorial.factorization 2 + 1) / 2) ≤ 2 ^ 6
        exact Nat.pow_le_pow_right (by norm_num) (by omega)
      · have hval : ((14 : ℕ).factorial).factorization 5 = 2 := by
          rw [Nat.factorization_factorial (by norm_num : Nat.Prime 5)
            (show Nat.log 5 14 < 2 by norm_num)]
          norm_num [Finset.sum_Ico_succ_top]
        rw [hval] at hfacLe
        have hpow : 5 ^ (((k - 1).factorial.factorization 5 + 1) / 2) ≤ 5 ^ 1 :=
          Nat.pow_le_pow_right (by norm_num) (by omega)
        norm_num at hpow ⊢
        omega
      · have hval : ((14 : ℕ).factorial).factorization 7 = 2 := by
          rw [Nat.factorization_factorial (by norm_num : Nat.Prime 7)
            (show Nat.log 7 14 < 2 by norm_num)]
          norm_num [Finset.sum_Ico_succ_top]
        rw [hval] at hfacLe
        have hpow : 7 ^ (((k - 1).factorial.factorization 7 + 1) / 2) ≤ 7 ^ 1 :=
          Nat.pow_le_pow_right (by norm_num) (by omega)
        norm_num at hpow ⊢
        omega
      · have hval : ((14 : ℕ).factorial).factorization 11 = 1 := by
          rw [Nat.factorization_factorial (by norm_num : Nat.Prime 11)
            (show Nat.log 11 14 < 2 by norm_num)]
          norm_num [Finset.sum_Ico_succ_top]
        rw [hval] at hfacLe
        have hpow : 11 ^ (((k - 1).factorial.factorization 11 + 1) / 2) ≤ 11 ^ 1 :=
          Nat.pow_le_pow_right (by norm_num) (by omega)
        norm_num at hpow ⊢
        omega
      · have hval : ((14 : ℕ).factorial).factorization 13 = 1 := by
          rw [Nat.factorization_factorial (by norm_num : Nat.Prime 13)
            (show Nat.log 13 14 < 2 by norm_num)]
          norm_num [Finset.sum_Ico_succ_top]
        rw [hval] at hfacLe
        have hpow : 13 ^ (((k - 1).factorial.factorization 13 + 1) / 2) ≤ 13 ^ 1 :=
          Nat.pow_le_pow_right (by norm_num) (by omega)
        norm_num at hpow ⊢
        omega

/-- The common-prime loss exponents in the six admissible odd rows are
exactly `3,4,5,7,9,10`. -/
theorem globalResidual_three_loss_table :
    globalResidualLossExponent 3 5 = 3 ∧
    globalResidualLossExponent 3 7 = 4 ∧
    globalResidualLossExponent 3 9 = 5 ∧
    globalResidualLossExponent 3 11 = 7 ∧
    globalResidualLossExponent 3 13 = 9 ∧
    globalResidualLossExponent 3 15 = 10 := by
  have h4 : ((4 : ℕ).factorial).factorization 3 = 1 := by
    rw [Nat.factorization_factorial (by norm_num : Nat.Prime 3)
      (show Nat.log 3 4 < 2 by norm_num)]
    norm_num [Finset.sum_Ico_succ_top]
  have h6 : ((6 : ℕ).factorial).factorization 3 = 2 := by
    rw [Nat.factorization_factorial (by norm_num : Nat.Prime 3)
      (show Nat.log 3 6 < 2 by norm_num)]
    norm_num [Finset.sum_Ico_succ_top]
  have h8 : ((8 : ℕ).factorial).factorization 3 = 2 := by
    rw [Nat.factorization_factorial (by norm_num : Nat.Prime 3)
      (show Nat.log 3 8 < 2 by norm_num)]
    norm_num [Finset.sum_Ico_succ_top]
  have h10 : ((10 : ℕ).factorial).factorization 3 = 4 := by
    rw [Nat.factorization_factorial (by norm_num : Nat.Prime 3)
      (show Nat.log 3 10 < 3 by norm_num)]
    norm_num [Finset.sum_Ico_succ_top]
  have h12 : ((12 : ℕ).factorial).factorization 3 = 5 := by
    rw [Nat.factorization_factorial (by norm_num : Nat.Prime 3)
      (show Nat.log 3 12 < 3 by norm_num)]
    norm_num [Finset.sum_Ico_succ_top]
  have h14 : ((14 : ℕ).factorial).factorization 3 = 5 := by
    rw [Nat.factorization_factorial (by norm_num : Nat.Prime 3)
      (show Nat.log 3 14 < 3 by norm_num)]
    norm_num [Finset.sum_Ico_succ_top]
  have h24 : (24 : ℕ).factorization 3 = 1 := by simpa using h4
  have h720 : (720 : ℕ).factorization 3 = 2 := by simpa using h6
  have h40320 : (40320 : ℕ).factorization 3 = 2 := by simpa using h8
  have h3628800 : (3628800 : ℕ).factorization 3 = 4 := by simpa using h10
  have h479001600 : (479001600 : ℕ).factorization 3 = 5 := by simpa using h12
  have h87178291200 : (87178291200 : ℕ).factorization 3 = 5 := by simpa using h14
  norm_num [globalResidualLossExponent, h24, h720, h40320, h3628800,
    h479001600, h87178291200]

end Erdos686Variant
end Erdos686
