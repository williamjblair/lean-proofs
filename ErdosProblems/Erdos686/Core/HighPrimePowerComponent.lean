/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import ErdosProblems.Erdos686.Core.LargePrimeGapComponent

/-!
# High prime-power components for Erdős 686

This module formalizes the exact valuation and normalized-unit machinery for
a canonical prime-power component `p^e` of the gap.  The final application is
the audited trichotomy at the maximum lower-block `p`-adic valuation, with
separate branches for `p ≥ 5`, `p = 2`, and `p = 3`.

No external greatest-prime-factor theorem is used here.
-/

namespace Erdos686
namespace Erdos686Variant

open scoped BigOperators

/-- The universal logarithmic loss for a length-`k` consecutive block. -/
def highComponentLambda (p k : ℕ) : ℕ := Nat.log p (k - 1)

/-- The loss in the singleton half-component branch at `p=3`. -/
def highComponentMuThree (k e : ℕ) : ℕ :=
  min (highComponentLambda 3 k) (e - 2)

/-- Adding a number of strictly larger `p`-adic valuation preserves the
smaller factorization exponent. -/
lemma factorization_add_eq_left_of_lt
    {p x d e : ℕ} (hp : p.Prime) (hx : x ≠ 0) (hd : d ≠ 0)
    (hexact : d.factorization p = e)
    (hlt : x.factorization p < e) :
    (x + d).factorization p = x.factorization p := by
  let s := x.factorization p
  have hsle : s ≤ e := by omega
  have hsx : p ^ s ∣ x :=
    (hp.pow_dvd_iff_le_factorization hx).mpr le_rfl
  have hsd : p ^ s ∣ d :=
    (hp.pow_dvd_iff_le_factorization hd).mpr (by simpa [hexact])
  have hssum : p ^ s ∣ x + d := dvd_add hsx hsd
  have hsum0 : x + d ≠ 0 := by omega
  have hlow : s ≤ (x + d).factorization p :=
    (hp.pow_dvd_iff_le_factorization hsum0).mp hssum
  have hs1d : p ^ (s + 1) ∣ d :=
    (hp.pow_dvd_iff_le_factorization hd).mpr (by simpa [hexact] using hlt)
  have hnotx : ¬ p ^ (s + 1) ∣ x := by
    intro hdiv
    have := (hp.pow_dvd_iff_le_factorization hx).mp hdiv
    omega
  have hnotsum : ¬ p ^ (s + 1) ∣ x + d := by
    intro hdiv
    apply hnotx
    have hsub := Nat.dvd_sub hdiv hs1d
    simpa using hsub
  have hupp : (x + d).factorization p ≤ s := by
    by_contra hnot
    have hs1le : s + 1 ≤ (x + d).factorization p := by omega
    exact hnotsum ((hp.pow_dvd_iff_le_factorization hsum0).mpr hs1le)
  exact Nat.le_antisymm hupp hlow

/-- Adding a number of strictly smaller `p`-adic valuation leaves exactly the
valuation of that summand. -/
lemma factorization_add_eq_right_of_gt
    {p x d e : ℕ} (hp : p.Prime) (hx : x ≠ 0) (hd : d ≠ 0)
    (hexact : d.factorization p = e)
    (hgt : e < x.factorization p) :
    (x + d).factorization p = e := by
  have hed : p ^ e ∣ d :=
    (hp.pow_dvd_iff_le_factorization hd).mpr (by simp [hexact])
  have hex : p ^ e ∣ x :=
    (hp.pow_dvd_iff_le_factorization hx).mpr (by omega)
  have hesum : p ^ e ∣ x + d := dvd_add hex hed
  have hsum0 : x + d ≠ 0 := by omega
  have hlow : e ≤ (x + d).factorization p :=
    (hp.pow_dvd_iff_le_factorization hsum0).mp hesum
  have he1x : p ^ (e + 1) ∣ x :=
    (hp.pow_dvd_iff_le_factorization hx).mpr (by omega)
  have hnotd : ¬ p ^ (e + 1) ∣ d := by
    intro hdiv
    have := (hp.pow_dvd_iff_le_factorization hd).mp hdiv
    omega
  have hnotsum : ¬ p ^ (e + 1) ∣ x + d := by
    intro hdiv
    apply hnotd
    have hsub := Nat.dvd_sub hdiv he1x
    simpa [add_comm] using hsub
  have hupp : (x + d).factorization p ≤ e := by
    by_contra hnot
    have he1le : e + 1 ≤ (x + d).factorization p := by omega
    exact hnotsum ((hp.pow_dvd_iff_le_factorization hsum0).mpr he1le)
  exact Nat.le_antisymm hupp hlow

/-- Canonical component decomposition from an exact factorization exponent. -/
lemma pow_factorization_mul_ordCompl_eq_of_factorization_eq
    {p d e : ℕ} (hexact : d.factorization p = e) :
    p ^ e * ordCompl[p] d = d := by
  simpa [hexact] using Nat.ordProj_mul_ordCompl_eq_self d p

/-- The product of the `p`-free parts of a consecutive block. -/
def pFreeBlockProduct (p k x : ℕ) : ℕ :=
  ∏ i ∈ Finset.Icc 1 k, ordCompl[p] (x + i)

lemma ordCompl_finset_prod
    {α : Type*} (p : ℕ) (s : Finset α) (f : α → ℕ) :
    ordCompl[p] (∏ x ∈ s, f x) = ∏ x ∈ s, ordCompl[p] (f x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      simp only [Finset.prod_insert ha]
      rw [Nat.ordCompl_mul, ih]

lemma pFreeBlockProduct_eq_ordCompl_blockProduct (p k x : ℕ) :
    pFreeBlockProduct p k x = ordCompl[p] (blockProduct k x) := by
  unfold pFreeBlockProduct blockProduct
  rw [ordCompl_finset_prod]

/-- Applying `ordCompl[p]` to the exact quotient-four equation. -/
lemma pFreeBlockProduct_eq_of_four_solution
    {p k n d : ℕ}
    (heq : blockProduct k (n + d) = 4 * blockProduct k n) :
    pFreeBlockProduct p k (n + d) =
      ordCompl[p] 4 * pFreeBlockProduct p k n := by
  rw [pFreeBlockProduct_eq_ordCompl_blockProduct,
    pFreeBlockProduct_eq_ordCompl_blockProduct, heq, Nat.ordCompl_mul]

lemma prime_not_dvd_prod_ordCompl
    {α : Type*} {p : ℕ} (hp : p.Prime)
    {s : Finset α} {f : α → ℕ} (hf : ∀ x ∈ s, f x ≠ 0) :
    ¬ p ∣ ∏ x ∈ s, ordCompl[p] (f x) := by
  classical
  intro hdiv
  obtain ⟨x, hx, hpx⟩ :=
    (hp.prime.dvd_finset_prod_iff
      (S := s) (g := fun x => ordCompl[p] (f x))).mp hdiv
  exact Nat.not_dvd_ordCompl hp (hf x hx) hpx

lemma pFreeBlockProduct_not_dvd
    {p k x : ℕ} (hp : p.Prime) :
    ¬ p ∣ pFreeBlockProduct p k x := by
  unfold pFreeBlockProduct
  apply prime_not_dvd_prod_ordCompl hp
  intro i hi
  have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
  omega

/-- Exact normalized-unit translation below the component valuation. -/
lemma ordCompl_add_eq_of_factorization_lt
    {p x d e : ℕ} (hp : p.Prime) (hx : x ≠ 0) (hd : d ≠ 0)
    (hexact : d.factorization p = e)
    (hlt : x.factorization p < e) :
    ordCompl[p] (x + d) =
      ordCompl[p] x +
        p ^ (e - x.factorization p) * ordCompl[p] d := by
  let s := x.factorization p
  have hfac : (x + d).factorization p = s := by
    simpa [s] using factorization_add_eq_left_of_lt hp hx hd hexact hlt
  have hxEq : p ^ s * ordCompl[p] x = x := by
    simpa [s] using Nat.ordProj_mul_ordCompl_eq_self x p
  have hdEq : p ^ e * ordCompl[p] d = d := by
    simpa [hexact] using Nat.ordProj_mul_ordCompl_eq_self d p
  have hxdEq : p ^ s * ordCompl[p] (x + d) = x + d := by
    simpa [hfac] using Nat.ordProj_mul_ordCompl_eq_self (x + d) p
  have hpow : p ^ e = p ^ s * p ^ (e - s) := by
    rw [← pow_add]
    congr 1
    dsimp [s]
    omega
  apply Nat.eq_of_mul_eq_mul_left (Nat.pow_pos hp.pos)
  calc
    p ^ s * ordCompl[p] (x + d) = x + d := hxdEq
    _ = p ^ s * ordCompl[p] x + p ^ e * ordCompl[p] d := by
      rw [hxEq, hdEq]
    _ = p ^ s *
        (ordCompl[p] x + p ^ (e - s) * ordCompl[p] d) := by
      rw [hpow]
      ring

/-- A uniform weakened congruence for every term whose lower valuation is at
most `L<e`. -/
lemma ordCompl_add_modEq_of_factorization_le
    {p x d e L : ℕ} (hp : p.Prime) (hx : x ≠ 0) (hd : d ≠ 0)
    (hexact : d.factorization p = e)
    (hval : x.factorization p ≤ L) (hL : L < e) :
    ordCompl[p] (x + d) ≡ ordCompl[p] x [MOD p ^ (e - L)] := by
  have hlt : x.factorization p < e := hval.trans_lt hL
  rw [ordCompl_add_eq_of_factorization_lt hp hx hd hexact hlt]
  apply Nat.add_modEq_left_iff.mpr
  apply dvd_mul_of_dvd_left
  apply pow_dvd_pow
  omega

/-- Product form of the normalized-unit translation congruence. -/
lemma prod_ordCompl_shift_modEq_of_factorization_le
    {p n d e L : ℕ} (hp : p.Prime) (hd : d ≠ 0)
    (hexact : d.factorization p = e)
    {s : Finset ℕ} (hi1 : ∀ i ∈ s, 1 ≤ i)
    (hval : ∀ i ∈ s, (n + i).factorization p ≤ L)
    (hL : L < e) :
    (∏ i ∈ s, ordCompl[p] (n + d + i)) ≡
      (∏ i ∈ s, ordCompl[p] (n + i)) [MOD p ^ (e - L)] := by
  apply Nat.ModEq.prod
  intro i hi
  have hx : n + i ≠ 0 := by
    have := hi1 i hi
    omega
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    ordCompl_add_modEq_of_factorization_le hp hx hd hexact
      (hval i hi) hL

/-- A lower-block index carrying the maximum `p`-adic valuation, with the
pointwise maximum property retained. -/
lemma exists_block_factorization_max
    {p k n : ℕ} (hk : 1 ≤ k) :
    ∃ i, i ∈ Finset.Icc 1 k ∧
      ∀ j ∈ Finset.Icc 1 k,
        (n + j).factorization p ≤ (n + i).factorization p := by
  let s := Finset.Icc 1 k
  have hs : s.Nonempty := by
    refine ⟨1, ?_⟩
    exact Finset.mem_Icc.mpr ⟨le_rfl, hk⟩
  obtain ⟨i, hi, hmax⟩ :=
    Finset.exists_max_image s (fun j => (n + j).factorization p) hs
  exact ⟨i, hi, fun j hj => hmax j hj⟩

lemma highComponentLambda_lt_exponent
    {p k e : ℕ} (hk : 2 ≤ k)
    (hcomponent : k ≤ p ^ e) :
    highComponentLambda p k < e := by
  unfold highComponentLambda
  apply Nat.log_lt_of_lt_pow
  · omega
  · omega

/-- Every nonowner next to an exact `p^e` owner loses at most
`log_p(k-1)` powers of `p`. -/
lemma nonowner_factorization_le_highComponentLambda
    {p e k n i j : ℕ} (hp : p.Prime)
    (hcomponent : k ≤ p ^ e)
    (hi : i ∈ Finset.Icc 1 k) (hj : j ∈ Finset.Icc 1 k)
    (hij : i ≠ j) (hiVal : (n + i).factorization p = e) :
    (n + j).factorization p ≤ highComponentLambda p k := by
  have hni0 : n + i ≠ 0 := by
    have := (Finset.mem_Icc.mp hi).1
    omega
  have hnj0 : n + j ≠ 0 := by
    have := (Finset.mem_Icc.mp hj).1
    omega
  have hjLt : (n + j).factorization p < e := by
    by_contra hnot
    have hqI : p ^ e ∣ n + i :=
      (hp.pow_dvd_iff_le_factorization hni0).mpr (by simp [hiVal])
    have hqJ : p ^ e ∣ n + j :=
      (hp.pow_dvd_iff_le_factorization hnj0).mpr (by omega)
    exact hij (unique_dvd_add_of_mem_Icc_of_le
      hcomponent hi hj hqI hqJ)
  let s := (n + j).factorization p
  have hsJ : p ^ s ∣ n + j :=
    (hp.pow_dvd_iff_le_factorization hnj0).mpr le_rfl
  have hsI : p ^ s ∣ n + i :=
    (hp.pow_dvd_iff_le_factorization hni0).mpr (by simp [s, hiVal]; omega)
  have hdistDvd : p ^ s ∣ Nat.dist i j := by
    rcases le_total i j with hijle | hjile
    · rw [Nat.dist_eq_sub_of_le hijle]
      have hsub := Nat.dvd_sub hsJ hsI
      have heq : (n + j) - (n + i) = j - i := by omega
      rwa [heq] at hsub
    · rw [Nat.dist_eq_sub_of_le_right hjile]
      have hsub := Nat.dvd_sub hsI hsJ
      have heq : (n + i) - (n + j) = i - j := by omega
      rwa [heq] at hsub
  have hdistPos : 0 < Nat.dist i j := Nat.dist_pos_of_ne hij
  have hdistLe : Nat.dist i j ≤ k - 1 := by
    rcases le_total i j with hijle | hjile
    · rw [Nat.dist_eq_sub_of_le hijle]
      have hi1 := (Finset.mem_Icc.mp hi).1
      have hjk := (Finset.mem_Icc.mp hj).2
      omega
    · rw [Nat.dist_eq_sub_of_le_right hjile]
      have hj1 := (Finset.mem_Icc.mp hj).1
      have hik := (Finset.mem_Icc.mp hi).2
      omega
  unfold highComponentLambda
  apply Nat.le_log_of_pow_le hp.one_lt
  exact (Nat.le_of_dvd hdistPos hdistDvd).trans hdistLe

lemma blockProduct_factorization_eq_sum
    {p k x : ℕ} :
    (blockProduct k x).factorization p =
      ∑ i ∈ Finset.Icc 1 k, (x + i).factorization p := by
  unfold blockProduct
  apply Nat.factorization_prod_apply
  intro i hi
  have hi1 := (Finset.mem_Icc.mp hi).1
  omega

lemma blockProduct_factorization_eq_four_add
    {p k n d : ℕ}
    (heq : blockProduct k (n + d) = 4 * blockProduct k n) :
    (blockProduct k (n + d)).factorization p =
      (4 : ℕ).factorization p + (blockProduct k n).factorization p := by
  have hblock0 : blockProduct k n ≠ 0 :=
    ne_of_gt (blockProduct_pos k n)
  rw [heq, Nat.factorization_mul (by norm_num : 4 ≠ 0) hblock0,
    Finsupp.add_apply]

/-- No lower valuation can exceed the exact component valuation: the unique
component owner would drop to `e`, all other valuations would be unchanged,
and the upper total would be strictly smaller than the lower one. -/
lemma max_factorization_not_gt_component
    {p e k n d i : ℕ} (hp : p.Prime) (hd : d ≠ 0)
    (hexact : d.factorization p = e)
    (hcomponent : k ≤ p ^ e)
    (hi : i ∈ Finset.Icc 1 k)
    (heq : blockProduct k (n + d) = 4 * blockProduct k n) :
    ¬ e < (n + i).factorization p := by
  intro hgt
  let s := Finset.Icc 1 k
  have hni0 : n + i ≠ 0 := by
    have := (Finset.mem_Icc.mp hi).1
    omega
  have hiUpper : (n + i + d).factorization p = e :=
    factorization_add_eq_right_of_gt hp hni0 hd hexact hgt
  have hiUpper' : (n + d + i).factorization p = e := by
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hiUpper
  have hrest : ∀ j ∈ s.erase i,
      (n + d + j).factorization p = (n + j).factorization p := by
    intro j hjErase
    have hj : j ∈ Finset.Icc 1 k := (Finset.mem_erase.mp hjErase).2
    have hji : j ≠ i := (Finset.mem_erase.mp hjErase).1
    have hnj0 : n + j ≠ 0 := by
      have := (Finset.mem_Icc.mp hj).1
      omega
    have hjLt : (n + j).factorization p < e := by
      by_contra hnot
      have hqI : p ^ e ∣ n + i :=
        (hp.pow_dvd_iff_le_factorization hni0).mpr (by omega)
      have hqJ : p ^ e ∣ n + j :=
        (hp.pow_dvd_iff_le_factorization hnj0).mpr (by omega)
      exact hji (unique_dvd_add_of_mem_Icc_of_le
        hcomponent hj hi hqJ hqI)
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      factorization_add_eq_left_of_lt hp hnj0 hd hexact hjLt
  have hrestSum :
      (∑ j ∈ s.erase i, (n + d + j).factorization p) =
        ∑ j ∈ s.erase i, (n + j).factorization p := by
    apply Finset.sum_congr rfl
    intro j hj
    exact hrest j hj
  have hupperSplit :
      (∑ j ∈ s, (n + d + j).factorization p) =
        (n + d + i).factorization p +
          ∑ j ∈ s.erase i, (n + d + j).factorization p :=
    (Finset.add_sum_erase s
      (fun j => (n + d + j).factorization p) hi).symm
  have hlowerSplit :
      (∑ j ∈ s, (n + j).factorization p) =
        (n + i).factorization p +
          ∑ j ∈ s.erase i, (n + j).factorization p :=
    (Finset.add_sum_erase s
      (fun j => (n + j).factorization p) hi).symm
  have htotalLt :
      (blockProduct k (n + d)).factorization p <
        (blockProduct k n).factorization p := by
    rw [blockProduct_factorization_eq_sum,
      blockProduct_factorization_eq_sum]
    change (∑ j ∈ s, (n + d + j).factorization p) <
      ∑ j ∈ s, (n + j).factorization p
    rw [hupperSplit, hlowerSplit, hiUpper', hrestSum]
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hgt
  have htotalEq := blockProduct_factorization_eq_four_add (p := p) heq
  rw [htotalEq] at htotalLt
  omega

/-- For `p≥5`, the maximum lower valuation cannot lie below the exact gap
component valuation: normalized units would be unchanged modulo `p`, while
the equation multiplies their product by four. -/
lemma max_factorization_not_lt_component_of_five_le
    {p e k n d i : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (he : 0 < e)
    (hd : d ≠ 0) (hexact : d.factorization p = e)
    (hmax : ∀ j ∈ Finset.Icc 1 k,
      (n + j).factorization p ≤ (n + i).factorization p)
    (heq : blockProduct k (n + d) = 4 * blockProduct k n) :
    ¬ (n + i).factorization p < e := by
  intro hlt
  let S := Finset.Icc 1 k
  have hval : ∀ j ∈ S, (n + j).factorization p ≤ e - 1 := by
    intro j hj
    have hjMax := hmax j hj
    omega
  have hpredLt : e - 1 < e := by omega
  have hprod := prod_ordCompl_shift_modEq_of_factorization_le
    hp hd hexact (s := S)
    (fun j hj => (Finset.mem_Icc.mp hj).1) hval hpredLt (n := n)
  have hexp : e - (e - 1) = 1 := by omega
  rw [hexp, pow_one] at hprod
  have hfreeEq := pFreeBlockProduct_eq_of_four_solution (p := p) heq
  have hpNotFour : ¬ p ∣ 4 := by
    intro hp4
    have hpLe : p ≤ 4 := Nat.le_of_dvd (by norm_num) hp4
    omega
  have hordFour : ordCompl[p] 4 = 4 :=
    (Nat.ordCompl_eq_self_iff_zero_or_not_dvd 4 hp).mpr (Or.inr hpNotFour)
  change pFreeBlockProduct p k (n + d) ≡
    pFreeBlockProduct p k n [MOD p] at hprod
  rw [hfreeEq, hordFour] at hprod
  let U := pFreeBlockProduct p k n
  have hplus : 3 * U + U ≡ 0 + U [MOD p] := by
    simpa [U, show 4 * U = 3 * U + U by omega] using hprod
  have hzero : 3 * U ≡ 0 [MOD p] :=
    Nat.ModEq.add_right_cancel' U hplus
  have hpDvd : p ∣ 3 * U := Nat.modEq_zero_iff_dvd.mp hzero
  rcases hp.dvd_mul.mp hpDvd with hp3 | hpU
  · have hpLe : p ≤ 3 := Nat.le_of_dvd (by norm_num) hp3
    omega
  · exact (pFreeBlockProduct_not_dvd hp) hpU

/-- The erased normalized-unit product at one owner. -/
def pFreeBlockCofactor (p k n i : ℕ) : ℕ :=
  ∏ j ∈ (Finset.Icc 1 k).erase i, ordCompl[p] (n + j)

lemma pFreeBlockProduct_eq_owner_mul_cofactor
    {p k n i : ℕ} (hi : i ∈ Finset.Icc 1 k) :
    pFreeBlockProduct p k n =
      ordCompl[p] (n + i) * pFreeBlockCofactor p k n i := by
  unfold pFreeBlockProduct pFreeBlockCofactor
  exact (Finset.mul_prod_erase (Finset.Icc 1 k)
    (fun j => ordCompl[p] (n + j)) hi).symm

lemma pFreeBlockCofactor_not_dvd
    {p k n i : ℕ} (hp : p.Prime) :
    ¬ p ∣ pFreeBlockCofactor p k n i := by
  unfold pFreeBlockCofactor
  apply prime_not_dvd_prod_ordCompl hp
  intro j hj
  have hjIcc := (Finset.mem_erase.mp hj).2
  have hj1 := (Finset.mem_Icc.mp hjIcc).1
  omega

/-- If a lower owner and its translate both have the exact component
valuation, their upper normalized unit is the sum of the two lower units. -/
lemma ordCompl_add_eq_of_both_factorization_eq
    {p x d e : ℕ} (hp : p.Prime)
    (hexactD : d.factorization p = e)
    (hexactX : x.factorization p = e)
    (hexactAdd : (x + d).factorization p = e) :
    ordCompl[p] (x + d) = ordCompl[p] x + ordCompl[p] d := by
  have hxEq : p ^ e * ordCompl[p] x = x := by
    simpa [hexactX] using Nat.ordProj_mul_ordCompl_eq_self x p
  have hdEq : p ^ e * ordCompl[p] d = d := by
    simpa [hexactD] using Nat.ordProj_mul_ordCompl_eq_self d p
  have haddEq : p ^ e * ordCompl[p] (x + d) = x + d := by
    simpa [hexactAdd] using Nat.ordProj_mul_ordCompl_eq_self (x + d) p
  apply Nat.eq_of_mul_eq_mul_left (Nat.pow_pos hp.pos)
  calc
    p ^ e * ordCompl[p] (x + d) = x + d := haddEq
    _ = p ^ e * ordCompl[p] x + p ^ e * ordCompl[p] d := by
      rw [hxEq, hdEq]
    _ = p ^ e * (ordCompl[p] x + ordCompl[p] d) := by ring

/-- At an exact component owner for a prime not dividing four, the translated
owner also has exact valuation `e`. -/
lemma owner_upper_factorization_eq_of_not_dvd_four
    {p e k n d i : ℕ} (hp : p.Prime) (hp4 : ¬ p ∣ 4)
    (hd : d ≠ 0) (hexact : d.factorization p = e)
    (hcomponent : k ≤ p ^ e)
    (hi : i ∈ Finset.Icc 1 k)
    (hiVal : (n + i).factorization p = e)
    (heq : blockProduct k (n + d) = 4 * blockProduct k n) :
    (n + d + i).factorization p = e := by
  let S := Finset.Icc 1 k
  have hrest : ∀ j ∈ S.erase i,
      (n + d + j).factorization p = (n + j).factorization p := by
    intro j hjErase
    have hj : j ∈ Finset.Icc 1 k := (Finset.mem_erase.mp hjErase).2
    have hji : j ≠ i := (Finset.mem_erase.mp hjErase).1
    have hnj0 : n + j ≠ 0 := by
      have := (Finset.mem_Icc.mp hj).1
      omega
    have hjLt : (n + j).factorization p < e := by
      have hni0 : n + i ≠ 0 := by
        have := (Finset.mem_Icc.mp hi).1
        omega
      by_contra hnot
      have hqI : p ^ e ∣ n + i :=
        (hp.pow_dvd_iff_le_factorization hni0).mpr (by simp [hiVal])
      have hqJ : p ^ e ∣ n + j :=
        (hp.pow_dvd_iff_le_factorization hnj0).mpr (by omega)
      exact hji (unique_dvd_add_of_mem_Icc_of_le
        hcomponent hj hi hqJ hqI)
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      factorization_add_eq_left_of_lt hp hnj0 hd hexact hjLt
  have hrestSum :
      (∑ j ∈ S.erase i, (n + d + j).factorization p) =
        ∑ j ∈ S.erase i, (n + j).factorization p := by
    apply Finset.sum_congr rfl
    intro j hj
    exact hrest j hj
  have hupperSplit :
      (∑ j ∈ S, (n + d + j).factorization p) =
        (n + d + i).factorization p +
          ∑ j ∈ S.erase i, (n + d + j).factorization p :=
    (Finset.add_sum_erase S
      (fun j => (n + d + j).factorization p) hi).symm
  have hlowerSplit :
      (∑ j ∈ S, (n + j).factorization p) =
        (n + i).factorization p +
          ∑ j ∈ S.erase i, (n + j).factorization p :=
    (Finset.add_sum_erase S
      (fun j => (n + j).factorization p) hi).symm
  have htotal := blockProduct_factorization_eq_four_add (p := p) heq
  rw [Nat.factorization_eq_zero_of_not_dvd hp4, zero_add,
    blockProduct_factorization_eq_sum,
    blockProduct_factorization_eq_sum] at htotal
  change (∑ j ∈ S, (n + d + j).factorization p) =
    ∑ j ∈ S, (n + j).factorization p at htotal
  rw [hupperSplit, hlowerSplit, hiVal, hrestSum] at htotal
  omega

/-- The audited logarithmic-loss residual lift for an exact component with
prime base at least five. -/
theorem highPrimePower_ge_five_exists_residual_lift
    {p e k n d : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (he : 0 < e) (hk : 2 ≤ k) (hd : 0 < d)
    (hexact : d.factorization p = e)
    (hcomponent : k ≤ p ^ e)
    (heq : blockProduct k (n + d) = 4 * blockProduct k n) :
    ∃ i, i ∈ Finset.Icc 1 k ∧
      (((p ^ (2 * e - highComponentLambda p k) : ℕ) : ℤ) ∣
        3 * ((n + i : ℕ) : ℤ) - (d : ℤ)) := by
  obtain ⟨i, hi, hmax⟩ :=
    exists_block_factorization_max (p := p) (n := n) (k := k) (by omega)
  have hnotLt := max_factorization_not_lt_component_of_five_le
    hp hp5 he hd.ne' hexact hmax heq
  have hnotGt := max_factorization_not_gt_component
    hp hd.ne' hexact hcomponent hi heq
  have hiVal : (n + i).factorization p = e := by omega
  have hlambdaLt : highComponentLambda p k < e :=
    highComponentLambda_lt_exponent hk hcomponent
  have hpNotFour : ¬ p ∣ 4 := by
    intro hp4
    have hpLe : p ≤ 4 := Nat.le_of_dvd (by norm_num) hp4
    omega
  have hUpperVal : (n + d + i).factorization p = e :=
    owner_upper_factorization_eq_of_not_dvd_four
      hp hpNotFour hd.ne' hexact hcomponent hi hiVal heq
  have hUpperVal' : (n + i + d).factorization p = e := by
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hUpperVal
  have hOwnerUnit :
      ordCompl[p] (n + d + i) =
        ordCompl[p] (n + i) + ordCompl[p] d := by
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      ordCompl_add_eq_of_both_factorization_eq hp hexact hiVal hUpperVal'
  have hnonowner : ∀ j ∈ (Finset.Icc 1 k).erase i,
      (n + j).factorization p ≤ highComponentLambda p k := by
    intro j hj
    exact nonowner_factorization_le_highComponentLambda hp hcomponent
      hi (Finset.mem_erase.mp hj).2 (Finset.mem_erase.mp hj).1.symm hiVal
  have hCmod :
      pFreeBlockCofactor p k (n + d) i ≡
        pFreeBlockCofactor p k n i
          [MOD p ^ (e - highComponentLambda p k)] := by
    unfold pFreeBlockCofactor
    exact prod_ordCompl_shift_modEq_of_factorization_le
      hp hd.ne' hexact
      (fun j hj => (Finset.mem_Icc.mp (Finset.mem_erase.mp hj).2).1)
      hnonowner hlambdaLt
  have hfreeEq := pFreeBlockProduct_eq_of_four_solution (p := p) heq
  have hordFour : ordCompl[p] 4 = 4 :=
    (Nat.ordCompl_eq_self_iff_zero_or_not_dvd 4 hp).mpr (Or.inr hpNotFour)
  have hupperSplit := pFreeBlockProduct_eq_owner_mul_cofactor
    (p := p) (n := n + d) hi
  have hlowerSplit := pFreeBlockProduct_eq_owner_mul_cofactor
    (p := p) (n := n) hi
  have hunitEq :
      (ordCompl[p] (n + i) + ordCompl[p] d) *
          pFreeBlockCofactor p k (n + d) i =
        4 * (ordCompl[p] (n + i) * pFreeBlockCofactor p k n i) := by
    rw [hupperSplit, hlowerSplit, hordFour] at hfreeEq
    rw [hOwnerUnit] at hfreeEq
    exact hfreeEq
  have hunitMod :
      (ordCompl[p] (n + i) + ordCompl[p] d) *
          pFreeBlockCofactor p k n i ≡
        (4 * ordCompl[p] (n + i)) *
          pFreeBlockCofactor p k n i
          [MOD p ^ (e - highComponentLambda p k)] := by
    have hleft := hCmod.mul_left
      (ordCompl[p] (n + i) + ordCompl[p] d)
    have heqMod :
        (ordCompl[p] (n + i) + ordCompl[p] d) *
            pFreeBlockCofactor p k (n + d) i ≡
          (4 * ordCompl[p] (n + i)) *
            pFreeBlockCofactor p k n i
            [MOD p ^ (e - highComponentLambda p k)] := by
      simp [Nat.ModEq, hunitEq, mul_assoc]
    exact hleft.symm.trans heqMod
  have hcoprime :
      Nat.gcd (p ^ (e - highComponentLambda p k))
        (pFreeBlockCofactor p k n i) = 1 := by
    exact (hp.coprime_pow_of_not_dvd
      (pFreeBlockCofactor_not_dvd hp)).symm
  have hownerMod :
      ordCompl[p] (n + i) + ordCompl[p] d ≡
        4 * ordCompl[p] (n + i)
          [MOD p ^ (e - highComponentLambda p k)] :=
    Nat.ModEq.cancel_right_of_coprime hcoprime hunitMod
  have hcoreDvd :
      ((p ^ (e - highComponentLambda p k) : ℕ) : ℤ) ∣
        3 * (ordCompl[p] (n + i) : ℤ) - (ordCompl[p] d : ℤ) := by
    have hdiv := hownerMod.dvd
    convert hdiv using 1
    push_cast
    ring
  have hownerDecomp : p ^ e * ordCompl[p] (n + i) = n + i := by
    simpa [hiVal] using Nat.ordProj_mul_ordCompl_eq_self (n + i) p
  have hgapDecomp : p ^ e * ordCompl[p] d = d :=
    pow_factorization_mul_ordCompl_eq_of_factorization_eq hexact
  have hownerDecompZ :
      ((n + i : ℕ) : ℤ) =
        ((p ^ e : ℕ) : ℤ) * (ordCompl[p] (n + i) : ℤ) := by
    exact_mod_cast hownerDecomp.symm
  have hgapDecompZ :
      (d : ℤ) = ((p ^ e : ℕ) : ℤ) * (ordCompl[p] d : ℤ) := by
    exact_mod_cast hgapDecomp.symm
  have hresEq :
      3 * ((n + i : ℕ) : ℤ) - (d : ℤ) =
        ((p ^ e : ℕ) : ℤ) *
          (3 * (ordCompl[p] (n + i) : ℤ) - (ordCompl[p] d : ℤ)) := by
    calc
      3 * ((n + i : ℕ) : ℤ) - (d : ℤ) =
          3 * (((p ^ e : ℕ) : ℤ) * (ordCompl[p] (n + i) : ℤ)) -
            ((p ^ e : ℕ) : ℤ) * (ordCompl[p] d : ℤ) := by
              apply congrArg₂ (· - ·)
              · exact congrArg (fun z : ℤ => 3 * z) hownerDecompZ
              · exact hgapDecompZ
      _ = ((p ^ e : ℕ) : ℤ) *
          (3 * (ordCompl[p] (n + i) : ℤ) - (ordCompl[p] d : ℤ)) := by
            ring
  have hprodDvd :
      (((p ^ e * p ^ (e - highComponentLambda p k) : ℕ) : ℤ)) ∣
        3 * ((n + i : ℕ) : ℤ) - (d : ℤ) := by
    rcases hcoreDvd with ⟨z, hz⟩
    refine ⟨z, ?_⟩
    rw [hresEq, hz]
    push_cast
    ring
  have hpow :
      p ^ (2 * e - highComponentLambda p k) =
        p ^ e * p ^ (e - highComponentLambda p k) := by
    calc
      p ^ (2 * e - highComponentLambda p k) =
          p ^ (e + (e - highComponentLambda p k)) := by
            congr 1
            omega
      _ = p ^ e * p ^ (e - highComponentLambda p k) := by rw [pow_add]
  refine ⟨i, hi, ?_⟩
  simpa [hpow] using hprodDvd

/-- A uniform archimedean closure for any equation-facing divisor of one
positive local residual. -/
lemma no_four_solution_of_residual_lift_dominance
    {M k n d : ℕ} (hk : 16 ≤ k) (hd : k ≤ d)
    (hdominant :
      (13 * k - 6) * d + 18 * (k - 1) ≤ 6 * M)
    (hlift : blockProduct k (n + d) = 4 * blockProduct k n →
      ∃ i, i ∈ Finset.Icc 1 k ∧
        ((M : ℕ) : ℤ) ∣ 3 * ((n + i : ℕ) : ℤ) - (d : ℤ)) :
    blockProduct k (n + d) ≠ 4 * blockProduct k n := by
  intro heq
  obtain ⟨i, hi, hdivZ⟩ := hlift heq
  have h9d : 9 * d < n := nine_mul_gap_lt_n_of_four_solution hk hd heq
  have hresPos : 0 < 3 * (n + i) - d := by
    have hi1 := (Finset.mem_Icc.mp hi).1
    omega
  have hresZ :
      3 * ((n + i : ℕ) : ℤ) - (d : ℤ) =
        ((3 * (n + i) - d : ℕ) : ℤ) := by
    rw [Nat.cast_sub (by omega : d ≤ 3 * (n + i))]
    norm_num
  have hdivNat : M ∣ 3 * (n + i) - d := by
    rw [hresZ] at hdivZ
    exact Int.natCast_dvd_natCast.mp hdivZ
  have hMle : M ≤ 3 * (n + i) - d := Nat.le_of_dvd hresPos hdivNat
  have hresAdd : (3 * (n + i) - d) + d = 3 * (n + i) :=
    Nat.sub_add_cancel (by omega)
  have hliftCeil : 6 * M + 6 * d ≤ 18 * (n + i) := by
    nlinarith
  have hik := (Finset.mem_Icc.mp hi).2
  have hindexCeil :
      18 * (n + i) ≤ 18 * (n + 1) + 18 * (k - 1) := by
    omega
  have hratio : 18 * (n + 1) < 13 * k * d :=
    eighteen_mul_n_add_one_lt_thirteen_mul_k_mul_gap_of_four_solution hk heq
  have hstrict :
      6 * M + 6 * d < 13 * k * d + 18 * (k - 1) :=
    lt_of_le_of_lt (hliftCeil.trans hindexCeil) (Nat.add_lt_add_right hratio _)
  have hreverse :
      13 * k * d + 18 * (k - 1) ≤ 6 * M + 6 * d := by
    have hadd := Nat.add_le_add_right hdominant (6 * d)
    let A := 13 * k - 6
    have hA : A + 6 = 13 * k := by dsimp [A]; omega
    calc
      13 * k * d + 18 * (k - 1) =
          (A * d + 18 * (k - 1)) + 6 * d := by
            rw [← hA]
            ring
      _ = ((13 * k - 6) * d + 18 * (k - 1)) + 6 * d := by rfl
      _ ≤ 6 * M + 6 * d := hadd
  exact (Nat.not_lt_of_ge hreverse) hstrict

/-- Exact high-component exclusion for prime bases at least five. -/
theorem no_four_solution_of_highPrimePower_ge_five_component
    {p e k n d : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hk : 16 ≤ k) (hd : k ≤ d)
    (hexact : d.factorization p = e)
    (hcomponent : k ≤ p ^ e)
    (hdominant :
      (13 * k - 6) * d + 18 * (k - 1) ≤
        6 * p ^ (2 * e - highComponentLambda p k)) :
    blockProduct k (n + d) ≠ 4 * blockProduct k n := by
  have he : 0 < e := by
    by_contra hnot
    have he0 : e = 0 := Nat.eq_zero_of_not_pos hnot
    rw [he0, pow_zero] at hcomponent
    omega
  apply no_four_solution_of_residual_lift_dominance hk hd hdominant
  intro heq
  exact highPrimePower_ge_five_exists_residual_lift
    hp hp5 he (by omega) (by omega) hexact hcomponent heq

/-- At `p=2`, a maximum below `e` would leave every valuation unchanged,
contradicting the exact two-power contribution of the multiplier four. -/
lemma max_factorization_not_lt_component_two
    {e k n d i : ℕ} (hd : d ≠ 0)
    (hexact : d.factorization 2 = e)
    (hmax : ∀ j ∈ Finset.Icc 1 k,
      (n + j).factorization 2 ≤ (n + i).factorization 2)
    (heq : blockProduct k (n + d) = 4 * blockProduct k n) :
    ¬ (n + i).factorization 2 < e := by
  intro hlt
  have hsumEq :
      (∑ j ∈ Finset.Icc 1 k, (n + d + j).factorization 2) =
        ∑ j ∈ Finset.Icc 1 k, (n + j).factorization 2 := by
    apply Finset.sum_congr rfl
    intro j hj
    have hnj0 : n + j ≠ 0 := by
      have := (Finset.mem_Icc.mp hj).1
      omega
    have hjLt : (n + j).factorization 2 < e :=
      (hmax j hj).trans_lt hlt
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      factorization_add_eq_left_of_lt (by norm_num) hnj0 hd hexact hjLt
  have htotal := blockProduct_factorization_eq_four_add (p := 2) heq
  have hfour : (4 : ℕ).factorization 2 = 2 := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num]
    exact Nat.factorization_pow_self (by norm_num)
  rw [hfour] at htotal
  rw [blockProduct_factorization_eq_sum,
    blockProduct_factorization_eq_sum] at htotal
  rw [hsumEq] at htotal
  omega

/-- At an exact lower two-power owner, the translated owner absorbs the
entire two-power contribution of four. -/
lemma owner_upper_factorization_eq_two_add_two
    {e k n d i : ℕ} (hd : d ≠ 0)
    (hexact : d.factorization 2 = e)
    (hcomponent : k ≤ 2 ^ e)
    (hi : i ∈ Finset.Icc 1 k)
    (hiVal : (n + i).factorization 2 = e)
    (heq : blockProduct k (n + d) = 4 * blockProduct k n) :
    (n + d + i).factorization 2 = e + 2 := by
  let S := Finset.Icc 1 k
  have hrest : ∀ j ∈ S.erase i,
      (n + d + j).factorization 2 = (n + j).factorization 2 := by
    intro j hjErase
    have hj : j ∈ Finset.Icc 1 k := (Finset.mem_erase.mp hjErase).2
    have hji : j ≠ i := (Finset.mem_erase.mp hjErase).1
    have hnj0 : n + j ≠ 0 := by
      have := (Finset.mem_Icc.mp hj).1
      omega
    have hjLt : (n + j).factorization 2 < e := by
      have hni0 : n + i ≠ 0 := by
        have := (Finset.mem_Icc.mp hi).1
        omega
      by_contra hnot
      have hqI : 2 ^ e ∣ n + i :=
        ((by norm_num : Nat.Prime 2).pow_dvd_iff_le_factorization hni0).mpr
          (by simp [hiVal])
      have hqJ : 2 ^ e ∣ n + j :=
        ((by norm_num : Nat.Prime 2).pow_dvd_iff_le_factorization hnj0).mpr
          (by omega)
      exact hji (unique_dvd_add_of_mem_Icc_of_le
        hcomponent hj hi hqJ hqI)
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      factorization_add_eq_left_of_lt (by norm_num) hnj0 hd hexact hjLt
  have hrestSum :
      (∑ j ∈ S.erase i, (n + d + j).factorization 2) =
        ∑ j ∈ S.erase i, (n + j).factorization 2 := by
    apply Finset.sum_congr rfl
    intro j hj
    exact hrest j hj
  have hupperSplit :
      (∑ j ∈ S, (n + d + j).factorization 2) =
        (n + d + i).factorization 2 +
          ∑ j ∈ S.erase i, (n + d + j).factorization 2 :=
    (Finset.add_sum_erase S
      (fun j => (n + d + j).factorization 2) hi).symm
  have hlowerSplit :
      (∑ j ∈ S, (n + j).factorization 2) =
        (n + i).factorization 2 +
          ∑ j ∈ S.erase i, (n + j).factorization 2 :=
    (Finset.add_sum_erase S
      (fun j => (n + j).factorization 2) hi).symm
  have htotal := blockProduct_factorization_eq_four_add (p := 2) heq
  have hfour : (4 : ℕ).factorization 2 = 2 := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num]
    exact Nat.factorization_pow_self (by norm_num)
  rw [hfour] at htotal
  rw [blockProduct_factorization_eq_sum,
    blockProduct_factorization_eq_sum] at htotal
  change (∑ j ∈ S, (n + d + j).factorization 2) =
    2 + ∑ j ∈ S, (n + j).factorization 2 at htotal
  rw [hupperSplit, hlowerSplit, hiVal, hrestSum] at htotal
  omega

/-- The audited logarithmic-loss residual lift for an exact two-power gap
component. -/
theorem highTwoPower_exists_residual_lift
    {e k n d : ℕ} (he : 0 < e) (hk : 2 ≤ k) (hd : 0 < d)
    (hexact : d.factorization 2 = e)
    (hcomponent : k ≤ 2 ^ e)
    (heq : blockProduct k (n + d) = 4 * blockProduct k n) :
    ∃ i, i ∈ Finset.Icc 1 k ∧
      (((2 ^ (2 * e - highComponentLambda 2 k + 2) : ℕ) : ℤ) ∣
        3 * ((n + i : ℕ) : ℤ) - (d : ℤ)) := by
  obtain ⟨i, hi, hmax⟩ :=
    exists_block_factorization_max (p := 2) (n := n) (k := k) (by omega)
  have hnotLt := max_factorization_not_lt_component_two
    hd.ne' hexact hmax heq
  have hnotGt := max_factorization_not_gt_component
    (by norm_num : Nat.Prime 2) hd.ne' hexact hcomponent hi heq
  have hiVal : (n + i).factorization 2 = e := by omega
  have hlambdaLt : highComponentLambda 2 k < e :=
    highComponentLambda_lt_exponent hk hcomponent
  have hUpperVal : (n + d + i).factorization 2 = e + 2 :=
    owner_upper_factorization_eq_two_add_two
      hd.ne' hexact hcomponent hi hiVal heq
  have hnonowner : ∀ j ∈ (Finset.Icc 1 k).erase i,
      (n + j).factorization 2 ≤ highComponentLambda 2 k := by
    intro j hj
    exact nonowner_factorization_le_highComponentLambda (by norm_num)
      hcomponent hi (Finset.mem_erase.mp hj).2
      (Finset.mem_erase.mp hj).1.symm hiVal
  have hCmod :
      pFreeBlockCofactor 2 k (n + d) i ≡
        pFreeBlockCofactor 2 k n i
          [MOD 2 ^ (e - highComponentLambda 2 k)] := by
    unfold pFreeBlockCofactor
    exact prod_ordCompl_shift_modEq_of_factorization_le
      (by norm_num) hd.ne' hexact
      (fun j hj => (Finset.mem_Icc.mp (Finset.mem_erase.mp hj).2).1)
      hnonowner hlambdaLt
  have hfreeEq := pFreeBlockProduct_eq_of_four_solution (p := 2) heq
  have hordFour : ordCompl[2] 4 = 1 := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num]
    exact Nat.ordCompl_self_pow (by norm_num)
  have hupperSplit := pFreeBlockProduct_eq_owner_mul_cofactor
    (p := 2) (n := n + d) hi
  have hlowerSplit := pFreeBlockProduct_eq_owner_mul_cofactor
    (p := 2) (n := n) hi
  have hunitEq :
      ordCompl[2] (n + d + i) * pFreeBlockCofactor 2 k (n + d) i =
        ordCompl[2] (n + i) * pFreeBlockCofactor 2 k n i := by
    rw [hupperSplit, hlowerSplit, hordFour, one_mul] at hfreeEq
    exact hfreeEq
  have hunitMod :
      ordCompl[2] (n + d + i) * pFreeBlockCofactor 2 k n i ≡
        ordCompl[2] (n + i) * pFreeBlockCofactor 2 k n i
          [MOD 2 ^ (e - highComponentLambda 2 k)] := by
    have hleft := hCmod.mul_left (ordCompl[2] (n + d + i))
    have heqMod :
        ordCompl[2] (n + d + i) * pFreeBlockCofactor 2 k (n + d) i ≡
          ordCompl[2] (n + i) * pFreeBlockCofactor 2 k n i
            [MOD 2 ^ (e - highComponentLambda 2 k)] := by
      simp [Nat.ModEq, hunitEq]
    exact hleft.symm.trans heqMod
  have hcoprime :
      Nat.gcd (2 ^ (e - highComponentLambda 2 k))
        (pFreeBlockCofactor 2 k n i) = 1 := by
    exact ((by norm_num : Nat.Prime 2).coprime_pow_of_not_dvd
      (pFreeBlockCofactor_not_dvd (by norm_num))).symm
  have hownerMod :
      ordCompl[2] (n + d + i) ≡ ordCompl[2] (n + i)
        [MOD 2 ^ (e - highComponentLambda 2 k)] :=
    Nat.ModEq.cancel_right_of_coprime hcoprime hunitMod
  have hdiffDvd :
      ((2 ^ (e - highComponentLambda 2 k) : ℕ) : ℤ) ∣
        (ordCompl[2] (n + i) : ℤ) - (ordCompl[2] (n + d + i) : ℤ) := by
    exact hownerMod.dvd
  have hownerDecomp : 2 ^ e * ordCompl[2] (n + i) = n + i := by
    simpa [hiVal] using Nat.ordProj_mul_ordCompl_eq_self (n + i) 2
  have hgapDecomp : 2 ^ e * ordCompl[2] d = d :=
    pow_factorization_mul_ordCompl_eq_of_factorization_eq hexact
  have hupperDecomp :
      2 ^ (e + 2) * ordCompl[2] (n + d + i) = n + d + i := by
    simpa [hUpperVal] using Nat.ordProj_mul_ordCompl_eq_self (n + d + i) 2
  have hpowFour : 2 ^ (e + 2) = 2 ^ e * 4 := by
    rw [pow_add]
    norm_num
  have hrelation :
      ordCompl[2] (n + i) + ordCompl[2] d =
        4 * ordCompl[2] (n + d + i) := by
    apply Nat.eq_of_mul_eq_mul_left (Nat.pow_pos (by norm_num : 0 < 2))
    calc
      2 ^ e * (ordCompl[2] (n + i) + ordCompl[2] d) =
          n + i + d := by rw [mul_add, hownerDecomp, hgapDecomp]
      _ = n + d + i := by omega
      _ = 2 ^ (e + 2) * ordCompl[2] (n + d + i) := hupperDecomp.symm
      _ = 2 ^ e * (4 * ordCompl[2] (n + d + i)) := by
        rw [hpowFour]
        ring
  have hrelationZ :
      (ordCompl[2] (n + i) : ℤ) + (ordCompl[2] d : ℤ) =
        4 * (ordCompl[2] (n + d + i) : ℤ) := by
    exact_mod_cast hrelation
  have hcoreEq :
      3 * (ordCompl[2] (n + i) : ℤ) - (ordCompl[2] d : ℤ) =
        4 * ((ordCompl[2] (n + i) : ℤ) -
          (ordCompl[2] (n + d + i) : ℤ)) := by
    linarith
  have hfourCoreDvd :
      (((4 * 2 ^ (e - highComponentLambda 2 k) : ℕ) : ℤ)) ∣
        3 * (ordCompl[2] (n + i) : ℤ) - (ordCompl[2] d : ℤ) := by
    rcases hdiffDvd with ⟨z, hz⟩
    refine ⟨z, ?_⟩
    rw [hcoreEq, hz]
    push_cast
    ring
  have hownerDecompZ :
      ((n + i : ℕ) : ℤ) =
        ((2 ^ e : ℕ) : ℤ) * (ordCompl[2] (n + i) : ℤ) := by
    exact_mod_cast hownerDecomp.symm
  have hgapDecompZ :
      (d : ℤ) = ((2 ^ e : ℕ) : ℤ) * (ordCompl[2] d : ℤ) := by
    exact_mod_cast hgapDecomp.symm
  have hresEq :
      3 * ((n + i : ℕ) : ℤ) - (d : ℤ) =
        ((2 ^ e : ℕ) : ℤ) *
          (3 * (ordCompl[2] (n + i) : ℤ) - (ordCompl[2] d : ℤ)) := by
    calc
      3 * ((n + i : ℕ) : ℤ) - (d : ℤ) =
          3 * (((2 ^ e : ℕ) : ℤ) * (ordCompl[2] (n + i) : ℤ)) -
            ((2 ^ e : ℕ) : ℤ) * (ordCompl[2] d : ℤ) := by
              apply congrArg₂ (· - ·)
              · exact congrArg (fun z : ℤ => 3 * z) hownerDecompZ
              · exact hgapDecompZ
      _ = ((2 ^ e : ℕ) : ℤ) *
          (3 * (ordCompl[2] (n + i) : ℤ) - (ordCompl[2] d : ℤ)) := by ring
  have hprodDvd :
      (((2 ^ e * (4 * 2 ^ (e - highComponentLambda 2 k)) : ℕ) : ℤ)) ∣
        3 * ((n + i : ℕ) : ℤ) - (d : ℤ) := by
    rcases hfourCoreDvd with ⟨z, hz⟩
    refine ⟨z, ?_⟩
    rw [hresEq, hz]
    push_cast
    ring
  have hpow :
      2 ^ (2 * e - highComponentLambda 2 k + 2) =
        2 ^ e * (4 * 2 ^ (e - highComponentLambda 2 k)) := by
    calc
      2 ^ (2 * e - highComponentLambda 2 k + 2) =
          2 ^ (e + (2 + (e - highComponentLambda 2 k))) := by
            congr 1
            omega
      _ = 2 ^ e * (2 ^ 2 * 2 ^ (e - highComponentLambda 2 k)) := by
        rw [pow_add, pow_add]
      _ = 2 ^ e * (4 * 2 ^ (e - highComponentLambda 2 k)) := by norm_num
  refine ⟨i, hi, ?_⟩
  simpa [hpow] using hprodDvd

/-- Exact high-component exclusion for the prime base two. -/
theorem no_four_solution_of_highTwoPower_component
    {e k n d : ℕ} (hk : 16 ≤ k) (hd : k ≤ d)
    (hexact : d.factorization 2 = e)
    (hcomponent : k ≤ 2 ^ e)
    (hdominant :
      (13 * k - 6) * d + 18 * (k - 1) ≤
        24 * 2 ^ (2 * e - highComponentLambda 2 k)) :
    blockProduct k (n + d) ≠ 4 * blockProduct k n := by
  have he : 0 < e := by
    by_contra hnot
    have he0 : e = 0 := Nat.eq_zero_of_not_pos hnot
    rw [he0, pow_zero] at hcomponent
    omega
  have hrewrite :
      24 * 2 ^ (2 * e - highComponentLambda 2 k) =
        6 * 2 ^ (2 * e - highComponentLambda 2 k + 2) := by
    rw [pow_add]
    norm_num
    ring
  rw [hrewrite] at hdominant
  apply no_four_solution_of_residual_lift_dominance hk hd hdominant
  intro heq
  exact highTwoPower_exists_residual_lift
    he (by omega) (by omega) hexact hcomponent heq

/-! ## The half-component branch at `p = 3` -/

/-- Indices whose lower factors have exact valuation `e-1` at three. -/
def p3HalfOwners (k n e : ℕ) : Finset ℕ :=
  (Finset.Icc 1 k).filter
    (fun i => (n + i).factorization 3 = e - 1)

/-- The complementary indices in the lower block. -/
def p3Nonowners (k n e : ℕ) : Finset ℕ :=
  (Finset.Icc 1 k).filter
    (fun i => (n + i).factorization 3 ≠ e - 1)

/-- The normalized three-free unit at a lower factor. -/
def p3OwnerUnit (n i : ℕ) : ℕ :=
  ordCompl[3] (n + i)

lemma mem_p3HalfOwners_iff {k n e i : ℕ} :
    i ∈ p3HalfOwners k n e ↔
      i ∈ Finset.Icc 1 k ∧ (n + i).factorization 3 = e - 1 := by
  simp [p3HalfOwners]

/-- Congruent indices in `Icc 1 k` are equal when the modulus is at least
`k`.  The non-strict boundary is safe because the interval has diameter
`k-1`. -/
lemma modEq_eq_of_mem_Icc_of_le
    {q k i j : ℕ}
    (hkq : k ≤ q)
    (hi : i ∈ Finset.Icc 1 k)
    (hj : j ∈ Finset.Icc 1 k)
    (hij : i ≡ j [MOD q]) :
    i = j := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hijlt | hjilt
  · have hdvd : q ∣ j - i :=
      (Nat.modEq_iff_dvd' (Nat.le_of_lt hijlt)).mp hij
    have hpos : 0 < j - i := Nat.sub_pos_of_lt hijlt
    have hqle : q ≤ j - i := Nat.le_of_dvd hpos hdvd
    have hi1 := (Finset.mem_Icc.mp hi).1
    have hjk := (Finset.mem_Icc.mp hj).2
    omega
  · have hdvd : q ∣ i - j :=
      (Nat.modEq_iff_dvd' (Nat.le_of_lt hjilt)).mp hij.symm
    have hpos : 0 < i - j := Nat.sub_pos_of_lt hjilt
    have hqle : q ≤ i - j := Nat.le_of_dvd hpos hdvd
    have hj1 := (Finset.mem_Icc.mp hj).1
    have hik := (Finset.mem_Icc.mp hi).2
    omega

lemma p3Owner_decomp
    {n i e : ℕ}
    (hval : (n + i).factorization 3 = e - 1) :
    3 ^ (e - 1) * p3OwnerUnit n i = n + i := by
  simpa [p3OwnerUnit, hval] using
    Nat.ordProj_mul_ordCompl_eq_self (n + i) 3

lemma p3OwnerUnit_not_dvd
    {n i : ℕ} (hi1 : 1 ≤ i) :
    ¬ 3 ∣ p3OwnerUnit n i := by
  exact Nat.not_dvd_ordCompl (by norm_num) (by omega)

/-- Distinct half-component owners have distinct normalized unit classes
modulo three. -/
lemma p3HalfOwnerResidue_injOn
    {k n e : ℕ} (he : 1 ≤ e) (hkq : k ≤ 3 ^ e) :
    Set.InjOn
      (fun i => p3OwnerUnit n i % 3)
      (p3HalfOwners k n e : Set ℕ) := by
  intro i hi j hj hres
  have hi' := (mem_p3HalfOwners_iff.mp hi)
  have hj' := (mem_p3HalfOwners_iff.mp hj)
  have hunit : p3OwnerUnit n i ≡ p3OwnerUnit n j [MOD 3] := by
    exact hres
  have hscaled := hunit.mul_left' (3 ^ (e - 1))
  have hpow : 3 ^ (e - 1) * 3 = 3 ^ e := by
    rw [← pow_succ]
    congr 1
    omega
  rw [p3Owner_decomp hi'.2, p3Owner_decomp hj'.2, hpow] at hscaled
  have hindices : i ≡ j [MOD 3 ^ e] :=
    Nat.ModEq.add_left_cancel' n hscaled
  exact modEq_eq_of_mem_Icc_of_le hkq hi'.1 hj'.1 hindices

/-- There are at most two exact `3^(e-1)` owners in a block of length at
most `3^e`. -/
theorem p3HalfOwners_card_le_two
    {k n e : ℕ} (he : 1 ≤ e) (hkq : k ≤ 3 ^ e) :
    (p3HalfOwners k n e).card ≤ 2 := by
  classical
  let f : ℕ → ℕ := fun i => p3OwnerUnit n i % 3
  have hmaps : Set.MapsTo f
      (p3HalfOwners k n e : Set ℕ) (Finset.Icc 1 2 : Set ℕ) := by
    intro i hi
    have hi' := (mem_p3HalfOwners_iff.mp hi).1
    have hnot : f i ≠ 0 := by
      rw [show f i = p3OwnerUnit n i % 3 by rfl]
      simpa [Nat.dvd_iff_mod_eq_zero] using
        p3OwnerUnit_not_dvd (Finset.mem_Icc.mp hi').1
    have hlt : f i < 3 := Nat.mod_lt _ (by norm_num)
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  calc
    (p3HalfOwners k n e).card ≤ (Finset.Icc 1 2).card :=
      Finset.card_le_card_of_injOn f hmaps
        (p3HalfOwnerResidue_injOn he hkq)
    _ = 2 := by norm_num [Nat.card_Icc]

/-- After splitting off the exact valuation-`e-1` owners, the quotient-four
equation gives their normalized-unit equation modulo nine. -/
lemma p3HalfOwner_product_modEq_nine
    {e k n d : ℕ} (he2 : 2 ≤ e) (hd : 0 < d)
    (hexact : d.factorization 3 = e)
    (hmax : ∀ j ∈ Finset.Icc 1 k,
      (n + j).factorization 3 ≤ e - 1)
    (heq : blockProduct k (n + d) = 4 * blockProduct k n) :
    (∏ i ∈ p3HalfOwners k n e,
        (p3OwnerUnit n i + 3 * ordCompl[3] d)) ≡
      4 * ∏ i ∈ p3HalfOwners k n e, p3OwnerUnit n i
        [MOD 9] := by
  classical
  let S := Finset.Icc 1 k
  let H := p3HalfOwners k n e
  let R := p3Nonowners k n e
  let Aup := ∏ i ∈ H, (p3OwnerUnit n i + 3 * ordCompl[3] d)
  let Alo := ∏ i ∈ H, p3OwnerUnit n i
  let Cup := ∏ i ∈ R, ordCompl[3] (n + d + i)
  let Clo := ∏ i ∈ R, ordCompl[3] (n + i)
  have hownerShift : ∀ i ∈ H,
      ordCompl[3] (n + d + i) =
        p3OwnerUnit n i + 3 * ordCompl[3] d := by
    intro i hi
    have hi' := mem_p3HalfOwners_iff.mp (by simpa [H] using hi)
    have hni0 : n + i ≠ 0 := by
      have := (Finset.mem_Icc.mp hi'.1).1
      omega
    have hlt : (n + i).factorization 3 < e := by
      rw [hi'.2]
      omega
    have hshift := ordCompl_add_eq_of_factorization_lt
      (by norm_num : Nat.Prime 3) hni0 hd.ne' hexact hlt
    have hpow : 3 ^ (e - (n + i).factorization 3) = 3 := by
      rw [hi'.2]
      have : e - (e - 1) = 1 := by omega
      rw [this, pow_one]
    simpa [p3OwnerUnit, hpow, Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm] using hshift
  have hnonownerVal : ∀ i ∈ R,
      (n + i).factorization 3 ≤ e - 2 := by
    intro i hi
    have hi' : i ∈ Finset.Icc 1 k ∧
        (n + i).factorization 3 ≠ e - 1 := by
      simpa [R, p3Nonowners] using (Finset.mem_filter.mp hi)
    have := hmax i hi'.1
    omega
  have hRmod : Cup ≡ Clo [MOD 9] := by
    have hraw := prod_ordCompl_shift_modEq_of_factorization_le
      (by norm_num : Nat.Prime 3) hd.ne' hexact
      (s := R)
      (fun i hi => by
        have hi' : i ∈ Finset.Icc 1 k ∧
            (n + i).factorization 3 ≠ e - 1 := by
          simpa [R, p3Nonowners] using hi
        exact (Finset.mem_Icc.mp hi'.1).1)
      hnonownerVal (by omega : e - 2 < e) (n := n)
    have hpow : 3 ^ (e - (e - 2)) = 9 := by
      have : e - (e - 2) = 2 := by omega
      rw [this]
      norm_num
    simpa [Cup, Clo, hpow] using hraw
  have hupperPartition :
      pFreeBlockProduct 3 k (n + d) =
        (∏ i ∈ H, ordCompl[3] (n + d + i)) * Cup := by
    have hsplit := Finset.prod_filter_mul_prod_filter_not
      S (fun i => (n + i).factorization 3 = e - 1)
      (fun i => ordCompl[3] (n + d + i))
    simpa [pFreeBlockProduct, S, H, R, p3HalfOwners,
      p3Nonowners, Cup] using hsplit.symm
  have hlowerPartition :
      pFreeBlockProduct 3 k n =
        (∏ i ∈ H, ordCompl[3] (n + i)) * Clo := by
    have hsplit := Finset.prod_filter_mul_prod_filter_not
      S (fun i => (n + i).factorization 3 = e - 1)
      (fun i => ordCompl[3] (n + i))
    simpa [pFreeBlockProduct, S, H, R, p3HalfOwners,
      p3Nonowners, Clo] using hsplit.symm
  have hupperOwners :
      (∏ i ∈ H, ordCompl[3] (n + d + i)) = Aup := by
    apply Finset.prod_congr rfl
    intro i hi
    exact hownerShift i hi
  have hlowerOwners :
      (∏ i ∈ H, ordCompl[3] (n + i)) = Alo := by
    apply Finset.prod_congr rfl
    intro i _hi
    rfl
  have hfreeEq := pFreeBlockProduct_eq_of_four_solution (p := 3) heq
  have hordFour : ordCompl[3] 4 = 4 :=
    (Nat.ordCompl_eq_self_iff_zero_or_not_dvd 4
      (by norm_num : Nat.Prime 3)).mpr (Or.inr (by norm_num))
  have hunitEq : Aup * Cup = (4 * Alo) * Clo := by
    rw [hupperPartition, hlowerPartition, hupperOwners,
      hlowerOwners, hordFour] at hfreeEq
    simpa [mul_assoc] using hfreeEq
  have heqMod : Aup * Cup ≡ (4 * Alo) * Clo [MOD 9] := by
    simp [Nat.ModEq, hunitEq]
  have hCupNot : ¬ 3 ∣ Cup := by
    dsimp [Cup]
    apply prime_not_dvd_prod_ordCompl (by norm_num : Nat.Prime 3)
    intro i hi
    have hi' : i ∈ Finset.Icc 1 k ∧
        (n + i).factorization 3 ≠ e - 1 := by
      simpa [R, p3Nonowners] using hi
    have hi1 := (Finset.mem_Icc.mp hi'.1).1
    omega
  have hcoprime : Nat.gcd 9 Cup = 1 := by
    have hcop : Nat.Coprime Cup (3 ^ 2) :=
      (by norm_num : Nat.Prime 3).coprime_pow_of_not_dvd hCupNot
    simpa using hcop.symm
  have hcancel := Nat.ModEq.cancel_right_div_gcd'
    (by norm_num : 0 < 9) hRmod heqMod
  have hownerMod : Aup ≡ 4 * Alo [MOD 9] := by
    simpa [hcoprime] using hcancel
  simpa [Aup, Alo, H] using hownerMod

lemma three_dvd_add_of_distinct_nonzero_mod_three
    {a b : ℕ} (ha : ¬ 3 ∣ a) (hb : ¬ 3 ∣ b)
    (hab : a % 3 ≠ b % 3) :
    3 ∣ a + b := by
  have ha0 : a % 3 ≠ 0 := by
    simpa [Nat.dvd_iff_mod_eq_zero] using ha
  have hb0 : b % 3 ≠ 0 := by
    simpa [Nat.dvd_iff_mod_eq_zero] using hb
  have haLt : a % 3 < 3 := Nat.mod_lt _ (by norm_num)
  have hbLt : b % 3 < 3 := Nat.mod_lt _ (by norm_num)
  have haCases : a % 3 = 1 ∨ a % 3 = 2 := by omega
  have hbCases : b % 3 = 1 ∨ b % 3 = 2 := by omega
  rcases haCases with ha1 | ha2 <;>
    rcases hbCases with hb1 | hb2
  · exact (hab (ha1.trans hb1.symm)).elim
  · rw [Nat.dvd_iff_mod_eq_zero, Nat.add_mod, ha1, hb2]
  · rw [Nat.dvd_iff_mod_eq_zero, Nat.add_mod, ha2, hb1]
  · exact (hab (ha2.trans hb2.symm)).elim

/-- The two-owner normalized-unit equation has no solution modulo nine. -/
lemma p3_two_owner_mod9_impossible
    {a b m : ℕ} (ha : ¬ 3 ∣ a) (hb : ¬ 3 ∣ b)
    (hab : a % 3 ≠ b % 3)
    (hunit :
      (a + 3 * m) * (b + 3 * m) ≡ 4 * (a * b) [MOD 9]) :
    False := by
  have habSum : 3 ∣ a + b :=
    three_dvd_add_of_distinct_nonzero_mod_three ha hb hab
  obtain ⟨c, hc⟩ := habSum
  have hmid : 3 * m * (a + b) ≡ 0 [MOD 9] := by
    apply Nat.modEq_zero_iff_dvd.mpr
    refine ⟨m * c, ?_⟩
    rw [hc]
    ring
  have hsq : 9 * (m * m) ≡ 0 [MOD 9] := by
    apply Nat.modEq_zero_iff_dvd.mpr
    exact dvd_mul_right 9 (m * m)
  have hleft :
      (a + 3 * m) * (b + 3 * m) ≡ a * b [MOD 9] := by
    calc
      (a + 3 * m) * (b + 3 * m) =
          a * b + 3 * m * (a + b) + 9 * (m * m) := by ring
      _ ≡ a * b + 0 + 0 [MOD 9] :=
        (Nat.ModEq.rfl.add hmid).add hsq
      _ = a * b := by omega
  have hab4 : a * b ≡ 4 * (a * b) [MOD 9] :=
    hleft.symm.trans hunit
  have hdvd : 9 ∣ 4 * (a * b) - a * b :=
    (Nat.modEq_iff_dvd' (by omega)).mp hab4
  have hdiff : 4 * (a * b) - a * b = 3 * (a * b) := by omega
  rw [hdiff] at hdvd
  have hthree : 3 ∣ a * b := by
    apply Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 3)
    simpa using hdvd
  rcases (by norm_num : Nat.Prime 3).dvd_mul.mp hthree with h3a | h3b
  · exact ha h3a
  · exact hb h3b

lemma p3HalfOwners_card_ne_two
    {e k n d : ℕ} (he2 : 2 ≤ e) (hd : 0 < d)
    (hexact : d.factorization 3 = e)
    (hkq : k ≤ 3 ^ e)
    (hmax : ∀ j ∈ Finset.Icc 1 k,
      (n + j).factorization 3 ≤ e - 1)
    (heq : blockProduct k (n + d) = 4 * blockProduct k n) :
    (p3HalfOwners k n e).card ≠ 2 := by
  classical
  intro hcard
  obtain ⟨i, j, hij, hH⟩ := Finset.card_eq_two.mp hcard
  have hiH : i ∈ p3HalfOwners k n e := by
    rw [hH]
    simp
  have hjH : j ∈ p3HalfOwners k n e := by
    rw [hH]
    simp
  have hi' := mem_p3HalfOwners_iff.mp hiH
  have hj' := mem_p3HalfOwners_iff.mp hjH
  have hres : p3OwnerUnit n i % 3 ≠ p3OwnerUnit n j % 3 := by
    intro heqRes
    exact hij (p3HalfOwnerResidue_injOn (by omega) hkq
      hiH hjH heqRes)
  have hiUnit : ¬ 3 ∣ p3OwnerUnit n i :=
    p3OwnerUnit_not_dvd (Finset.mem_Icc.mp hi'.1).1
  have hjUnit : ¬ 3 ∣ p3OwnerUnit n j :=
    p3OwnerUnit_not_dvd (Finset.mem_Icc.mp hj'.1).1
  have hunit := p3HalfOwner_product_modEq_nine
    he2 hd hexact hmax heq
  have hunit' :
      (p3OwnerUnit n i + 3 * ordCompl[3] d) *
          (p3OwnerUnit n j + 3 * ordCompl[3] d) ≡
        4 * (p3OwnerUnit n i * p3OwnerUnit n j) [MOD 9] := by
    simpa [hH, hij] using hunit
  exact p3_two_owner_mod9_impossible hiUnit hjUnit hres hunit'

/-- In the maximum-valuation `e-1` branch there is exactly one owner. -/
theorem p3HalfOwners_existsUnique
    {e k n d : ℕ} (he2 : 2 ≤ e) (hd : 0 < d)
    (hexact : d.factorization 3 = e)
    (hkq : k ≤ 3 ^ e)
    (hex : ∃ i, i ∈ Finset.Icc 1 k ∧
      (n + i).factorization 3 = e - 1)
    (hmax : ∀ j ∈ Finset.Icc 1 k,
      (n + j).factorization 3 ≤ e - 1)
    (heq : blockProduct k (n + d) = 4 * blockProduct k n) :
    ∃! i, i ∈ Finset.Icc 1 k ∧
      (n + i).factorization 3 = e - 1 := by
  classical
  have hnonempty : (p3HalfOwners k n e).Nonempty := by
    obtain ⟨i, hi, hval⟩ := hex
    exact ⟨i, mem_p3HalfOwners_iff.mpr ⟨hi, hval⟩⟩
  have hpos : 0 < (p3HalfOwners k n e).card :=
    Finset.card_pos.mpr hnonempty
  have hle : (p3HalfOwners k n e).card ≤ 2 :=
    p3HalfOwners_card_le_two (by omega) hkq
  have hne : (p3HalfOwners k n e).card ≠ 2 :=
    p3HalfOwners_card_ne_two he2 hd hexact hkq hmax heq
  have hcard : (p3HalfOwners k n e).card = 1 := by omega
  obtain ⟨i, hH⟩ := Finset.card_eq_one.mp hcard
  refine ⟨i, ?_, ?_⟩
  · exact mem_p3HalfOwners_iff.mp (by rw [hH]; simp)
  · intro j hj
    have hjH : j ∈ p3HalfOwners k n e :=
      mem_p3HalfOwners_iff.mpr hj
    rw [hH] at hjH
    simpa using hjH

/-- The maximum lower three-adic valuation cannot be at most `e-2`: all
normalized units would be fixed modulo nine, whereas the equation multiplies
their product by four. -/
lemma max_factorization_not_le_component_sub_two_three
    {e k n d i : ℕ} (he2 : 2 ≤ e) (hd : 0 < d)
    (hexact : d.factorization 3 = e)
    (hmax : ∀ j ∈ Finset.Icc 1 k,
      (n + j).factorization 3 ≤ (n + i).factorization 3)
    (heq : blockProduct k (n + d) = 4 * blockProduct k n) :
    ¬ (n + i).factorization 3 ≤ e - 2 := by
  intro hiLow
  have hval : ∀ j ∈ Finset.Icc 1 k,
      (n + j).factorization 3 ≤ e - 2 := by
    intro j hj
    exact (hmax j hj).trans hiLow
  have hprod := prod_ordCompl_shift_modEq_of_factorization_le
    (by norm_num : Nat.Prime 3) hd.ne' hexact
    (s := Finset.Icc 1 k)
    (fun j hj => (Finset.mem_Icc.mp hj).1)
    hval (by omega : e - 2 < e) (n := n)
  have hpow : 3 ^ (e - (e - 2)) = 9 := by
    have : e - (e - 2) = 2 := by omega
    rw [this]
    norm_num
  rw [hpow] at hprod
  have hfreeEq := pFreeBlockProduct_eq_of_four_solution (p := 3) heq
  have hordFour : ordCompl[3] 4 = 4 :=
    (Nat.ordCompl_eq_self_iff_zero_or_not_dvd 4
      (by norm_num : Nat.Prime 3)).mpr (Or.inr (by norm_num))
  change pFreeBlockProduct 3 k (n + d) ≡
    pFreeBlockProduct 3 k n [MOD 9] at hprod
  rw [hfreeEq, hordFour] at hprod
  let U := pFreeBlockProduct 3 k n
  have hplus : 3 * U + U ≡ 0 + U [MOD 9] := by
    simpa [U, show 4 * U = 3 * U + U by omega] using hprod
  have hzero : 3 * U ≡ 0 [MOD 9] :=
    Nat.ModEq.add_right_cancel' U hplus
  have hnine : 9 ∣ 3 * U := Nat.modEq_zero_iff_dvd.mp hzero
  have hthree : 3 ∣ U := by
    apply Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 3)
    simpa using hnine
  exact pFreeBlockProduct_not_dvd (by norm_num : Nat.Prime 3) hthree

/-- The maximum lower valuation cannot equal the full three-power component:
the owner equation modulo three would make the canonical gap cofactor
divisible by three. -/
lemma max_factorization_ne_component_three
    {e k n d i : ℕ} (he : 0 < e) (hd : 0 < d)
    (hexact : d.factorization 3 = e)
    (hcomponent : k ≤ 3 ^ e)
    (hi : i ∈ Finset.Icc 1 k)
    (hiVal : (n + i).factorization 3 = e)
    (heq : blockProduct k (n + d) = 4 * blockProduct k n) :
    False := by
  have hUpperVal : (n + d + i).factorization 3 = e :=
    owner_upper_factorization_eq_of_not_dvd_four
      (by norm_num : Nat.Prime 3) (by norm_num) hd.ne'
      hexact hcomponent hi hiVal heq
  have hUpperVal' : (n + i + d).factorization 3 = e := by
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hUpperVal
  have hOwnerUnit :
      ordCompl[3] (n + d + i) =
        ordCompl[3] (n + i) + ordCompl[3] d := by
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      ordCompl_add_eq_of_both_factorization_eq
        (by norm_num : Nat.Prime 3) hexact hiVal hUpperVal'
  have hnonowner : ∀ j ∈ (Finset.Icc 1 k).erase i,
      (n + j).factorization 3 ≤ e - 1 := by
    intro j hjErase
    have hj := (Finset.mem_erase.mp hjErase).2
    have hji := (Finset.mem_erase.mp hjErase).1
    have hni0 : n + i ≠ 0 := by
      have := (Finset.mem_Icc.mp hi).1
      omega
    have hnj0 : n + j ≠ 0 := by
      have := (Finset.mem_Icc.mp hj).1
      omega
    by_contra hnot
    have hqI : 3 ^ e ∣ n + i :=
      ((by norm_num : Nat.Prime 3).pow_dvd_iff_le_factorization hni0).mpr
        (by simp [hiVal])
    have hqJ : 3 ^ e ∣ n + j :=
      ((by norm_num : Nat.Prime 3).pow_dvd_iff_le_factorization hnj0).mpr
        (by omega)
    exact hji (unique_dvd_add_of_mem_Icc_of_le
      hcomponent hj hi hqJ hqI)
  have hCmod :
      pFreeBlockCofactor 3 k (n + d) i ≡
        pFreeBlockCofactor 3 k n i [MOD 3] := by
    unfold pFreeBlockCofactor
    have hraw := prod_ordCompl_shift_modEq_of_factorization_le
      (by norm_num : Nat.Prime 3) hd.ne' hexact
      (fun j hj =>
        (Finset.mem_Icc.mp (Finset.mem_erase.mp hj).2).1)
      hnonowner (by omega : e - 1 < e)
    have hpow : 3 ^ (e - (e - 1)) = 3 := by
      have : e - (e - 1) = 1 := by omega
      rw [this, pow_one]
    simpa [hpow] using hraw
  have hfreeEq := pFreeBlockProduct_eq_of_four_solution (p := 3) heq
  have hordFour : ordCompl[3] 4 = 4 :=
    (Nat.ordCompl_eq_self_iff_zero_or_not_dvd 4
      (by norm_num : Nat.Prime 3)).mpr (Or.inr (by norm_num))
  have hupperSplit := pFreeBlockProduct_eq_owner_mul_cofactor
    (p := 3) (n := n + d) hi
  have hlowerSplit := pFreeBlockProduct_eq_owner_mul_cofactor
    (p := 3) (n := n) hi
  have hunitEq :
      (ordCompl[3] (n + i) + ordCompl[3] d) *
          pFreeBlockCofactor 3 k (n + d) i =
        4 * (ordCompl[3] (n + i) * pFreeBlockCofactor 3 k n i) := by
    rw [hupperSplit, hlowerSplit, hordFour] at hfreeEq
    rw [hOwnerUnit] at hfreeEq
    exact hfreeEq
  have hunitMod :
      (ordCompl[3] (n + i) + ordCompl[3] d) *
          pFreeBlockCofactor 3 k n i ≡
        (4 * ordCompl[3] (n + i)) *
          pFreeBlockCofactor 3 k n i [MOD 3] := by
    have hleft := hCmod.mul_left
      (ordCompl[3] (n + i) + ordCompl[3] d)
    have heqMod :
        (ordCompl[3] (n + i) + ordCompl[3] d) *
            pFreeBlockCofactor 3 k (n + d) i ≡
          (4 * ordCompl[3] (n + i)) *
            pFreeBlockCofactor 3 k n i [MOD 3] := by
      simp [Nat.ModEq, hunitEq, mul_assoc]
    exact hleft.symm.trans heqMod
  have hcoprime : Nat.gcd 3 (pFreeBlockCofactor 3 k n i) = 1 := by
    exact (by norm_num : Nat.Prime 3).coprime_iff_not_dvd.mpr
      (pFreeBlockCofactor_not_dvd (by norm_num))
  have hownerMod :
      ordCompl[3] (n + i) + ordCompl[3] d ≡
        4 * ordCompl[3] (n + i) [MOD 3] :=
    Nat.ModEq.cancel_right_of_coprime hcoprime hunitMod
  have hfour :
      4 * ordCompl[3] (n + i) =
        ordCompl[3] (n + i) + 3 * ordCompl[3] (n + i) := by omega
  rw [hfour] at hownerMod
  have hmMod : ordCompl[3] d ≡ 3 * ordCompl[3] (n + i) [MOD 3] :=
    Nat.ModEq.add_left_cancel' (ordCompl[3] (n + i)) hownerMod
  have hrightZero : 3 * ordCompl[3] (n + i) ≡ 0 [MOD 3] :=
    Nat.modEq_zero_iff_dvd.mpr (dvd_mul_right 3 _)
  have hmZero : ordCompl[3] d ≡ 0 [MOD 3] := hmMod.trans hrightZero
  exact Nat.not_dvd_ordCompl (by norm_num : Nat.Prime 3) hd.ne'
    (Nat.modEq_zero_iff_dvd.mp hmZero)

/-- Complete maximum-valuation classification at three. -/
lemma max_factorization_eq_component_sub_one_three
    {e k n d i : ℕ} (he2 : 2 ≤ e) (hd : 0 < d)
    (hexact : d.factorization 3 = e)
    (hcomponent : k ≤ 3 ^ e)
    (hi : i ∈ Finset.Icc 1 k)
    (hmax : ∀ j ∈ Finset.Icc 1 k,
      (n + j).factorization 3 ≤ (n + i).factorization 3)
    (heq : blockProduct k (n + d) = 4 * blockProduct k n) :
    (n + i).factorization 3 = e - 1 := by
  have hnotGt := max_factorization_not_gt_component
    (by norm_num : Nat.Prime 3) hd.ne' hexact hcomponent hi heq
  have hnotLow := max_factorization_not_le_component_sub_two_three
    he2 hd hexact hmax heq
  have hne : (n + i).factorization 3 ≠ e := by
    intro hiVal
    exact max_factorization_ne_component_three (by omega) hd hexact
      hcomponent hi hiVal heq
  omega

/-- If one factor has strictly smaller valuation than another factor in the
same consecutive block, the smaller valuation is bounded by
`log_p(k-1)`. -/
lemma factorization_le_highComponentLambda_of_lt_owner
    {p k n i j : ℕ} (hp : p.Prime)
    (hi : i ∈ Finset.Icc 1 k) (hj : j ∈ Finset.Icc 1 k)
    (hij : i ≠ j)
    (hlt : (n + j).factorization p < (n + i).factorization p) :
    (n + j).factorization p ≤ highComponentLambda p k := by
  let s := (n + j).factorization p
  have hni0 : n + i ≠ 0 := by
    have := (Finset.mem_Icc.mp hi).1
    omega
  have hnj0 : n + j ≠ 0 := by
    have := (Finset.mem_Icc.mp hj).1
    omega
  have hsJ : p ^ s ∣ n + j :=
    (hp.pow_dvd_iff_le_factorization hnj0).mpr le_rfl
  have hsI : p ^ s ∣ n + i :=
    (hp.pow_dvd_iff_le_factorization hni0).mpr (by
      dsimp [s]
      omega)
  have hdistDvd : p ^ s ∣ Nat.dist i j := by
    rcases le_total i j with hijle | hjile
    · rw [Nat.dist_eq_sub_of_le hijle]
      have hsub := Nat.dvd_sub hsJ hsI
      have heq : (n + j) - (n + i) = j - i := by omega
      rwa [heq] at hsub
    · rw [Nat.dist_eq_sub_of_le_right hjile]
      have hsub := Nat.dvd_sub hsI hsJ
      have heq : (n + i) - (n + j) = i - j := by omega
      rwa [heq] at hsub
  have hdistPos : 0 < Nat.dist i j := Nat.dist_pos_of_ne hij
  have hdistLe : Nat.dist i j ≤ k - 1 := by
    rcases le_total i j with hijle | hjile
    · rw [Nat.dist_eq_sub_of_le hijle]
      have hi1 := (Finset.mem_Icc.mp hi).1
      have hjk := (Finset.mem_Icc.mp hj).2
      omega
    · rw [Nat.dist_eq_sub_of_le_right hjile]
      have hj1 := (Finset.mem_Icc.mp hj).1
      have hik := (Finset.mem_Icc.mp hi).2
      omega
  unfold highComponentLambda
  apply Nat.le_log_of_pow_le hp.one_lt
  exact (Nat.le_of_dvd hdistPos hdistDvd).trans hdistLe

lemma p3Nonowner_factorization_le_mu
    {e k n i j : ℕ} (he2 : 2 ≤ e)
    (hi : i ∈ Finset.Icc 1 k)
    (hj : j ∈ Finset.Icc 1 k)
    (hij : i ≠ j)
    (hiVal : (n + i).factorization 3 = e - 1)
    (hjMax : (n + j).factorization 3 ≤ e - 1)
    (hjNot : (n + j).factorization 3 ≠ e - 1) :
    (n + j).factorization 3 ≤ highComponentMuThree k e := by
  have hjPred : (n + j).factorization 3 ≤ e - 2 := by omega
  have hjLt : (n + j).factorization 3 < (n + i).factorization 3 := by
    rw [hiVal]
    omega
  have hjLambda :
      (n + j).factorization 3 ≤ highComponentLambda 3 k :=
    factorization_le_highComponentLambda_of_lt_owner
      (by norm_num : Nat.Prime 3) hi hj hij hjLt
  exact le_min hjLambda hjPred

/-- The audited singleton half-component residual lift at `p=3`. -/
theorem highThreePower_exists_residual_lift
    {e k n d : ℕ} (he2 : 2 ≤ e) (hk : 2 ≤ k) (hd : 0 < d)
    (hexact : d.factorization 3 = e)
    (hcomponent : k ≤ 3 ^ e)
    (heq : blockProduct k (n + d) = 4 * blockProduct k n) :
    ∃ i, i ∈ Finset.Icc 1 k ∧
      (((3 ^ (2 * e - highComponentMuThree k e - 1) : ℕ) : ℤ) ∣
        3 * ((n + i : ℕ) : ℤ) - (d : ℤ)) := by
  obtain ⟨i, hi, hmax⟩ :=
    exists_block_factorization_max (p := 3) (n := n) (k := k) (by omega)
  have hiVal : (n + i).factorization 3 = e - 1 :=
    max_factorization_eq_component_sub_one_three
      he2 hd hexact hcomponent hi hmax heq
  have hmaxPred : ∀ j ∈ Finset.Icc 1 k,
      (n + j).factorization 3 ≤ e - 1 := by
    intro j hj
    simpa [hiVal] using hmax j hj
  have hexOwner : ∃ j, j ∈ Finset.Icc 1 k ∧
      (n + j).factorization 3 = e - 1 := ⟨i, hi, hiVal⟩
  obtain ⟨u, hu, huniq⟩ := p3HalfOwners_existsUnique
    he2 hd hexact hcomponent hexOwner hmaxPred heq
  have hiu : i = u := huniq i ⟨hi, hiVal⟩
  have hunique : ∀ j, j ∈ Finset.Icc 1 k →
      (n + j).factorization 3 = e - 1 → j = i := by
    intro j hj hjVal
    exact (huniq j ⟨hj, hjVal⟩).trans hiu.symm
  have hmuLe : highComponentMuThree k e ≤ e - 2 := by
    exact min_le_right _ _
  have hmuLt : highComponentMuThree k e < e := by omega
  have hnonowner : ∀ j ∈ (Finset.Icc 1 k).erase i,
      (n + j).factorization 3 ≤ highComponentMuThree k e := by
    intro j hjErase
    have hj := (Finset.mem_erase.mp hjErase).2
    have hji := (Finset.mem_erase.mp hjErase).1
    have hjNot : (n + j).factorization 3 ≠ e - 1 := by
      intro hjVal
      exact hji (hunique j hj hjVal)
    exact p3Nonowner_factorization_le_mu he2 hi hj hji.symm
      hiVal (hmaxPred j hj) hjNot
  have hCmod :
      pFreeBlockCofactor 3 k (n + d) i ≡
        pFreeBlockCofactor 3 k n i
          [MOD 3 ^ (e - highComponentMuThree k e)] := by
    unfold pFreeBlockCofactor
    exact prod_ordCompl_shift_modEq_of_factorization_le
      (by norm_num : Nat.Prime 3) hd.ne' hexact
      (fun j hj =>
        (Finset.mem_Icc.mp (Finset.mem_erase.mp hj).2).1)
      hnonowner hmuLt
  have hni0 : n + i ≠ 0 := by
    have := (Finset.mem_Icc.mp hi).1
    omega
  have hownerLt : (n + i).factorization 3 < e := by
    rw [hiVal]
    omega
  have hOwnerUnit :
      ordCompl[3] (n + d + i) =
        ordCompl[3] (n + i) + 3 * ordCompl[3] d := by
    have hraw := ordCompl_add_eq_of_factorization_lt
      (by norm_num : Nat.Prime 3) hni0 hd.ne' hexact hownerLt
    have hpow : 3 ^ (e - (n + i).factorization 3) = 3 := by
      rw [hiVal]
      have : e - (e - 1) = 1 := by omega
      rw [this, pow_one]
    simpa [hpow, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hraw
  have hfreeEq := pFreeBlockProduct_eq_of_four_solution (p := 3) heq
  have hordFour : ordCompl[3] 4 = 4 :=
    (Nat.ordCompl_eq_self_iff_zero_or_not_dvd 4
      (by norm_num : Nat.Prime 3)).mpr (Or.inr (by norm_num))
  have hupperSplit := pFreeBlockProduct_eq_owner_mul_cofactor
    (p := 3) (n := n + d) hi
  have hlowerSplit := pFreeBlockProduct_eq_owner_mul_cofactor
    (p := 3) (n := n) hi
  have hunitEq :
      (ordCompl[3] (n + i) + 3 * ordCompl[3] d) *
          pFreeBlockCofactor 3 k (n + d) i =
        4 * (ordCompl[3] (n + i) * pFreeBlockCofactor 3 k n i) := by
    rw [hupperSplit, hlowerSplit, hordFour] at hfreeEq
    rw [hOwnerUnit] at hfreeEq
    exact hfreeEq
  have hunitMod :
      (ordCompl[3] (n + i) + 3 * ordCompl[3] d) *
          pFreeBlockCofactor 3 k n i ≡
        (4 * ordCompl[3] (n + i)) *
          pFreeBlockCofactor 3 k n i
          [MOD 3 ^ (e - highComponentMuThree k e)] := by
    have hleft := hCmod.mul_left
      (ordCompl[3] (n + i) + 3 * ordCompl[3] d)
    have heqMod :
        (ordCompl[3] (n + i) + 3 * ordCompl[3] d) *
            pFreeBlockCofactor 3 k (n + d) i ≡
          (4 * ordCompl[3] (n + i)) *
            pFreeBlockCofactor 3 k n i
            [MOD 3 ^ (e - highComponentMuThree k e)] := by
      simp [Nat.ModEq, hunitEq, mul_assoc]
    exact hleft.symm.trans heqMod
  have hcoprime :
      Nat.gcd (3 ^ (e - highComponentMuThree k e))
        (pFreeBlockCofactor 3 k n i) = 1 := by
    exact ((by norm_num : Nat.Prime 3).coprime_pow_of_not_dvd
      (pFreeBlockCofactor_not_dvd (by norm_num))).symm
  have hownerMod :
      ordCompl[3] (n + i) + 3 * ordCompl[3] d ≡
        4 * ordCompl[3] (n + i)
          [MOD 3 ^ (e - highComponentMuThree k e)] :=
    Nat.ModEq.cancel_right_of_coprime hcoprime hunitMod
  have hfour :
      4 * ordCompl[3] (n + i) =
        ordCompl[3] (n + i) + 3 * ordCompl[3] (n + i) := by omega
  rw [hfour] at hownerMod
  have hthreeMod :
      3 * ordCompl[3] d ≡ 3 * ordCompl[3] (n + i)
        [MOD 3 ^ (e - highComponentMuThree k e)] :=
    Nat.ModEq.add_left_cancel' (ordCompl[3] (n + i)) hownerMod
  let M := 3 ^ (e - highComponentMuThree k e - 1)
  have hmodulus : 3 ^ (e - highComponentMuThree k e) = 3 * M := by
    dsimp [M]
    calc
      3 ^ (e - highComponentMuThree k e) =
          3 ^ (1 + (e - highComponentMuThree k e - 1)) := by
            congr 1
            omega
      _ = 3 ^ 1 * 3 ^ (e - highComponentMuThree k e - 1) := by
        rw [pow_add]
      _ = 3 * 3 ^ (e - highComponentMuThree k e - 1) := by norm_num
  have hthreeMod' :
      3 * ordCompl[3] d ≡ 3 * ordCompl[3] (n + i) [MOD 3 * M] := by
    simpa [hmodulus] using hthreeMod
  have hcoreMod : ordCompl[3] d ≡ ordCompl[3] (n + i) [MOD M] :=
    Nat.ModEq.mul_left_cancel' (by norm_num : (3 : ℕ) ≠ 0) hthreeMod'
  have hcoreDvd : (M : ℤ) ∣
      (ordCompl[3] (n + i) : ℤ) - (ordCompl[3] d : ℤ) :=
    hcoreMod.dvd
  have hownerDecomp :
      3 ^ (e - 1) * ordCompl[3] (n + i) = n + i := by
    simpa [hiVal] using Nat.ordProj_mul_ordCompl_eq_self (n + i) 3
  have hgapDecomp : 3 ^ e * ordCompl[3] d = d :=
    pow_factorization_mul_ordCompl_eq_of_factorization_eq hexact
  have hpowOwner : 3 * 3 ^ (e - 1) = 3 ^ e := by
    calc
      3 * 3 ^ (e - 1) = 3 ^ 1 * 3 ^ (e - 1) := by norm_num
      _ = 3 ^ (1 + (e - 1)) := by rw [pow_add]
      _ = 3 ^ e := by congr 1; omega
  have hownerDecompZ :
      ((n + i : ℕ) : ℤ) =
        ((3 ^ (e - 1) : ℕ) : ℤ) * (ordCompl[3] (n + i) : ℤ) := by
    exact_mod_cast hownerDecomp.symm
  have hgapDecompZ :
      (d : ℤ) = ((3 ^ e : ℕ) : ℤ) * (ordCompl[3] d : ℤ) := by
    exact_mod_cast hgapDecomp.symm
  have hresEq :
      3 * ((n + i : ℕ) : ℤ) - (d : ℤ) =
        ((3 ^ e : ℕ) : ℤ) *
          ((ordCompl[3] (n + i) : ℤ) - (ordCompl[3] d : ℤ)) := by
    calc
      3 * ((n + i : ℕ) : ℤ) - (d : ℤ) =
          3 * (((3 ^ (e - 1) : ℕ) : ℤ) *
            (ordCompl[3] (n + i) : ℤ)) -
          ((3 ^ e : ℕ) : ℤ) * (ordCompl[3] d : ℤ) := by
            apply congrArg₂ (· - ·)
            · exact congrArg (fun z : ℤ => 3 * z) hownerDecompZ
            · exact hgapDecompZ
      _ = ((3 ^ e : ℕ) : ℤ) *
          ((ordCompl[3] (n + i) : ℤ) - (ordCompl[3] d : ℤ)) := by
            have hpowOwnerZ :
                (3 : ℤ) * ((3 ^ (e - 1) : ℕ) : ℤ) =
                  ((3 ^ e : ℕ) : ℤ) := by
              exact_mod_cast hpowOwner
            rw [← hpowOwnerZ]
            ring
  have hprodDvd : (((3 ^ e * M : ℕ) : ℤ)) ∣
      3 * ((n + i : ℕ) : ℤ) - (d : ℤ) := by
    rcases hcoreDvd with ⟨z, hz⟩
    refine ⟨z, ?_⟩
    rw [hresEq, hz]
    push_cast
    ring
  have hpowFinal :
      3 ^ (2 * e - highComponentMuThree k e - 1) = 3 ^ e * M := by
    dsimp [M]
    calc
      3 ^ (2 * e - highComponentMuThree k e - 1) =
          3 ^ (e + (e - highComponentMuThree k e - 1)) := by
            congr 1
            omega
      _ = 3 ^ e * 3 ^ (e - highComponentMuThree k e - 1) := by
        rw [pow_add]
  refine ⟨i, hi, ?_⟩
  simpa [hpowFinal] using hprodDvd

/-- Exact high-component exclusion for the prime base three. -/
theorem no_four_solution_of_highThreePower_component
    {e k n d : ℕ} (hk : 16 ≤ k) (hd : k ≤ d)
    (hexact : d.factorization 3 = e)
    (hcomponent : k ≤ 3 ^ e)
    (hdominant :
      (13 * k - 6) * d + 18 * (k - 1) ≤
        6 * 3 ^ (2 * e - highComponentMuThree k e - 1)) :
    blockProduct k (n + d) ≠ 4 * blockProduct k n := by
  have he3 : 3 ≤ e := by
    by_contra hnot
    have he2 : e ≤ 2 := by omega
    interval_cases e <;> norm_num at hcomponent <;> omega
  apply no_four_solution_of_residual_lift_dominance hk hd hdominant
  intro heq
  exact highThreePower_exists_residual_lift
    (by omega) (by omega) (by omega) hexact hcomponent heq

/-- Dispatcher for all three branches of the audited high prime-power
component theorem. -/
theorem no_four_solution_of_highPrimePower_component
    {p e k n d : ℕ} (hp : p.Prime)
    (hk : 16 ≤ k) (hd : k ≤ d)
    (hexact : d.factorization p = e)
    (hcomponent : k ≤ p ^ e)
    (hcase :
      (p = 2 ∧
        (13 * k - 6) * d + 18 * (k - 1) ≤
          24 * 2 ^ (2 * e - highComponentLambda 2 k)) ∨
      (p = 3 ∧
        (13 * k - 6) * d + 18 * (k - 1) ≤
          6 * 3 ^ (2 * e - highComponentMuThree k e - 1)) ∨
      (5 ≤ p ∧
        (13 * k - 6) * d + 18 * (k - 1) ≤
          6 * p ^ (2 * e - highComponentLambda p k))) :
    blockProduct k (n + d) ≠ 4 * blockProduct k n := by
  rcases hcase with ⟨hp2, hdom⟩ | ⟨hp3, hdom⟩ | ⟨hp5, hdom⟩
  · subst p
    exact no_four_solution_of_highTwoPower_component
      hk hd hexact hcomponent hdom
  · subst p
    exact no_four_solution_of_highThreePower_component
      hk hd hexact hcomponent hdom
  · exact no_four_solution_of_highPrimePower_ge_five_component
      hp hp5 hk hd hexact hcomponent hdom

/-! ## Cleaner component-square conditions and a uniform prime-power family -/

/-- The square of a component is at most the logarithmic-loss power times the
block length. -/
lemma componentSquare_le_k_mul_highPower
    {p e k : ℕ} (hk : 2 ≤ k)
    (hcomponent : k ≤ p ^ e) :
    p ^ (2 * e) ≤ k * p ^ (2 * e - highComponentLambda p k) := by
  have hlambdaLt : highComponentLambda p k < e :=
    highComponentLambda_lt_exponent hk hcomponent
  have hk1ne : k - 1 ≠ 0 := by omega
  have hlog : p ^ highComponentLambda p k ≤ k - 1 := by
    exact Nat.pow_log_le_self p hk1ne
  have hpow :
      p ^ (2 * e) =
        p ^ (2 * e - highComponentLambda p k) *
          p ^ highComponentLambda p k := by
    rw [← pow_add]
    congr 1
    have hle : highComponentLambda p k ≤ 2 * e := by omega
    exact (Nat.sub_add_cancel hle).symm
  rw [hpow]
  simpa [mul_comm] using
    Nat.mul_le_mul_left (p ^ (2 * e - highComponentLambda p k))
      (hlog.trans (Nat.sub_le k 1))

lemma highComponent_dominance_of_square_ge_five
    {p e k d : ℕ} (hk : 16 ≤ k) (hd : k ≤ d)
    (hcomponent : k ≤ p ^ e)
    (hsquare : 2 * p ^ (2 * e) ≥ 5 * k ^ 2 * d) :
    (13 * k - 6) * d + 18 * (k - 1) ≤
      6 * p ^ (2 * e - highComponentLambda p k) := by
  have hRlt : (13 * k - 6) * d + 18 * (k - 1) < 15 * k * d := by
    have hfirst : (13 * k - 6) * d ≤ 13 * k * d := by
      exact Nat.mul_le_mul_right d (Nat.sub_le (13 * k) 6)
    have hsecond : 18 * (k - 1) < 2 * k * d := by
      have hkpred : k - 1 + 1 = k := Nat.sub_add_cancel (by omega)
      have hsq : 18 * (k - 1) < 2 * k * k := by nlinarith
      exact hsq.trans_le (Nat.mul_le_mul_left (2 * k) hd)
    calc
      (13 * k - 6) * d + 18 * (k - 1) ≤
          13 * k * d + 18 * (k - 1) := Nat.add_le_add_right hfirst _
      _ < 13 * k * d + 2 * k * d := Nat.add_lt_add_left hsecond _
      _ = 15 * k * d := by ring
  have hcomp := componentSquare_le_k_mul_highPower (by omega) hcomponent
  have hkpos : 0 < k := by omega
  have hscaled : 5 * k ^ 2 * d ≤
      2 * k * p ^ (2 * e - highComponentLambda p k) := by
    calc
      5 * k ^ 2 * d ≤ 2 * p ^ (2 * e) := hsquare
      _ ≤ 2 * (k * p ^ (2 * e - highComponentLambda p k)) :=
        Nat.mul_le_mul_left 2 hcomp
      _ = 2 * k * p ^ (2 * e - highComponentLambda p k) := by ring
  have hmain : 15 * k * d ≤
      6 * p ^ (2 * e - highComponentLambda p k) := by
    nlinarith
  exact (Nat.le_of_lt hRlt).trans hmain

lemma highComponent_dominance_two_of_square
    {e k d : ℕ} (hk : 16 ≤ k) (hd : k ≤ d)
    (hcomponent : k ≤ 2 ^ e)
    (hsquare : 8 * 2 ^ (2 * e) ≥ 5 * k ^ 2 * d) :
    (13 * k - 6) * d + 18 * (k - 1) ≤
      24 * 2 ^ (2 * e - highComponentLambda 2 k) := by
  have hRlt : (13 * k - 6) * d + 18 * (k - 1) < 15 * k * d := by
    have hfirst : (13 * k - 6) * d ≤ 13 * k * d := by
      exact Nat.mul_le_mul_right d (Nat.sub_le (13 * k) 6)
    have hsecond : 18 * (k - 1) < 2 * k * d := by
      have hkpred : k - 1 + 1 = k := Nat.sub_add_cancel (by omega)
      have hsq : 18 * (k - 1) < 2 * k * k := by nlinarith
      exact hsq.trans_le (Nat.mul_le_mul_left (2 * k) hd)
    calc
      (13 * k - 6) * d + 18 * (k - 1) ≤
          13 * k * d + 18 * (k - 1) := Nat.add_le_add_right hfirst _
      _ < 13 * k * d + 2 * k * d := Nat.add_lt_add_left hsecond _
      _ = 15 * k * d := by ring
  have hcomp := componentSquare_le_k_mul_highPower (by omega) hcomponent
  have hkpos : 0 < k := by omega
  have hscaled : 5 * k ^ 2 * d ≤
      8 * k * 2 ^ (2 * e - highComponentLambda 2 k) := by
    calc
      5 * k ^ 2 * d ≤ 8 * 2 ^ (2 * e) := hsquare
      _ ≤ 8 * (k * 2 ^ (2 * e - highComponentLambda 2 k)) :=
        Nat.mul_le_mul_left 8 hcomp
      _ = 8 * k * 2 ^ (2 * e - highComponentLambda 2 k) := by ring
  have hmain : 15 * k * d ≤
      24 * 2 ^ (2 * e - highComponentLambda 2 k) := by
    nlinarith
  exact (Nat.le_of_lt hRlt).trans hmain

/-- Cleaner sufficient condition for a component with prime base at least
five. -/
theorem no_four_solution_of_highPrimePower_ge_five_component_of_square
    {p e k n d : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hk : 16 ≤ k) (hd : k ≤ d)
    (hexact : d.factorization p = e)
    (hcomponent : k ≤ p ^ e)
    (hsquare : 2 * p ^ (2 * e) ≥ 5 * k ^ 2 * d) :
    blockProduct k (n + d) ≠ 4 * blockProduct k n := by
  exact no_four_solution_of_highPrimePower_ge_five_component
    hp hp5 hk hd hexact hcomponent
      (highComponent_dominance_of_square_ge_five hk hd hcomponent hsquare)

/-- Cleaner sufficient condition for a two-power component. -/
theorem no_four_solution_of_highTwoPower_component_of_square
    {e k n d : ℕ} (hk : 16 ≤ k) (hd : k ≤ d)
    (hexact : d.factorization 2 = e)
    (hcomponent : k ≤ 2 ^ e)
    (hsquare : 8 * 2 ^ (2 * e) ≥ 5 * k ^ 2 * d) :
    blockProduct k (n + d) ≠ 4 * blockProduct k n := by
  exact no_four_solution_of_highTwoPower_component hk hd hexact hcomponent
    (highComponent_dominance_two_of_square hk hd hcomponent hsquare)

lemma sq_le_two_pow {k : ℕ} (hk : 4 ≤ k) : k ^ 2 ≤ 2 ^ k := by
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
      calc
        (k + 1) ^ 2 ≤ 2 * k ^ 2 := by nlinarith [sq_nonneg (k - 1)]
        _ ≤ 2 * 2 ^ k := Nat.mul_le_mul_left 2 ih
        _ = 2 ^ (k + 1) := by rw [pow_succ]; ring

lemma eight_mul_sq_le_three_pow {k : ℕ} (hk : 5 ≤ k) :
    8 * k ^ 2 ≤ 3 ^ k := by
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
      calc
        8 * (k + 1) ^ 2 ≤ 3 * (8 * k ^ 2) := by
          nlinarith [sq_nonneg (k - 1)]
        _ ≤ 3 * 3 ^ k := Nat.mul_le_mul_left 3 ih
        _ = 3 ^ (k + 1) := by rw [pow_succ]; ring

lemma three_mul_sq_le_five_pow {k : ℕ} (hk : 2 ≤ k) :
    3 * k ^ 2 ≤ 5 ^ k := by
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
      calc
        3 * (k + 1) ^ 2 ≤ 5 * (3 * k ^ 2) := by
          nlinarith [sq_nonneg (k - 1)]
        _ ≤ 5 * 5 ^ k := Nat.mul_le_mul_left 5 ih
        _ = 5 ^ (k + 1) := by rw [pow_succ]; ring

lemma base_pow_le_prime_pow_add
    {b p k t : ℕ} (hb : 0 < b) (hbp : b ≤ p) :
    b ^ k ≤ p ^ (k + t) := by
  exact (Nat.pow_le_pow_left hbp k).trans
    (Nat.pow_le_pow_right (by omega) (by omega))

theorem no_four_solution_primePowerGap_ge_five
    {p k t n : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hk : 16 ≤ k) :
    blockProduct k (n + p ^ (k + t)) ≠ 4 * blockProduct k n := by
  let e := k + t
  let d := p ^ e
  have hd : k ≤ d := by
    have hpow : 5 ^ k ≤ p ^ e := by
      exact base_pow_le_prime_pow_add (by norm_num) hp5
    have hkSq : k ^ 2 ≤ 5 ^ k := by
      have := three_mul_sq_le_five_pow (by omega : 2 ≤ k)
      omega
    have hkLeSq : k ≤ k ^ 2 := by nlinarith
    exact hkLeSq.trans (hkSq.trans hpow)
  have hexact : d.factorization p = e := by
    exact Nat.factorization_pow_self hp
  have hsquare : 2 * p ^ (2 * e) ≥ 5 * k ^ 2 * d := by
    have hpow : 3 * k ^ 2 ≤ d := by
      have hfive := three_mul_sq_le_five_pow (by omega : 2 ≤ k)
      exact hfive.trans (base_pow_le_prime_pow_add (by norm_num) hp5)
    have hdpos : 0 < d := pow_pos hp.pos e
    have hpowsq : p ^ (2 * e) = d ^ 2 := by
      dsimp [d]
      rw [show 2 * e = e * 2 by omega, pow_mul]
    rw [hpowsq]
    nlinarith
  have hcomponent : k ≤ p ^ e := by simpa [d] using hd
  exact no_four_solution_of_highPrimePower_ge_five_component_of_square
    hp hp5 hk hd hexact hcomponent hsquare

theorem no_four_solution_primePowerGap_two
    {k t n : ℕ} (hk : 16 ≤ k) :
    blockProduct k (n + 2 ^ (k + t)) ≠ 4 * blockProduct k n := by
  let e := k + t
  let d := 2 ^ e
  have hkSq : k ^ 2 ≤ d := by
    have htwo : k ^ 2 ≤ 2 ^ k := sq_le_two_pow (by omega)
    exact htwo.trans
      (Nat.pow_le_pow_right (by norm_num : 0 < 2) (by omega))
  have hd : k ≤ d := by
    have hkLeSq : k ≤ k ^ 2 := by nlinarith
    exact hkLeSq.trans hkSq
  have hexact : d.factorization 2 = e := by
    exact Nat.factorization_pow_self (by norm_num)
  have hsquare : 8 * 2 ^ (2 * e) ≥ 5 * k ^ 2 * d := by
    have hdpos : 0 < d := pow_pos (by norm_num) e
    have hpowsq : 2 ^ (2 * e) = d ^ 2 := by
      dsimp [d]
      rw [show 2 * e = e * 2 by omega, pow_mul]
    rw [hpowsq]
    nlinarith
  have hcomponent : k ≤ 2 ^ e := by simpa [d] using hd
  exact no_four_solution_of_highTwoPower_component_of_square
    hk hd hexact hcomponent hsquare

lemma threeComponentSquare_lt_three_k_mul_highPower
    {e k : ℕ} (he2 : 2 ≤ e) (hk : 2 ≤ k) :
    3 ^ (2 * e) <
      3 * k * 3 ^ (2 * e - highComponentMuThree k e - 1) := by
  let mu := highComponentMuThree k e
  have hmuLeE : mu ≤ e - 2 := by
    exact min_le_right _ _
  have hmuLeLambda : mu ≤ highComponentLambda 3 k := by
    exact min_le_left _ _
  have hk1ne : k - 1 ≠ 0 := by omega
  have hlambdaPow : 3 ^ highComponentLambda 3 k ≤ k - 1 :=
    Nat.pow_log_le_self 3 hk1ne
  have hmuPow : 3 ^ mu < k := by
    have hbase : 3 ^ mu ≤ 3 ^ highComponentLambda 3 k :=
      Nat.pow_le_pow_right (by norm_num) hmuLeLambda
    exact (hbase.trans hlambdaPow).trans_lt (by omega)
  have hsmall : 3 ^ (mu + 1) < 3 * k := by
    rw [pow_succ]
    nlinarith
  have hpow :
      3 ^ (2 * e) =
        3 ^ (2 * e - mu - 1) * 3 ^ (mu + 1) := by
    rw [← pow_add]
    congr 1
    have hmu1 : mu + 1 ≤ 2 * e := by omega
    omega
  rw [hpow]
  simpa [mul_assoc, mul_left_comm, mul_comm] using
    Nat.mul_lt_mul_left
      (show 0 < 3 ^ (2 * e - mu - 1) by positivity) |>.mpr hsmall

lemma highComponent_dominance_three_of_square
    {e k d : ℕ} (he2 : 2 ≤ e) (hk : 16 ≤ k) (hd : k ≤ d)
    (hsquare : 2 * 3 ^ (2 * e) ≥ 15 * k ^ 2 * d) :
    (13 * k - 6) * d + 18 * (k - 1) ≤
      6 * 3 ^ (2 * e - highComponentMuThree k e - 1) := by
  have hRlt : (13 * k - 6) * d + 18 * (k - 1) < 15 * k * d := by
    have hfirst : (13 * k - 6) * d ≤ 13 * k * d := by
      exact Nat.mul_le_mul_right d (Nat.sub_le (13 * k) 6)
    have hsecond : 18 * (k - 1) < 2 * k * d := by
      have hkpred : k - 1 + 1 = k := Nat.sub_add_cancel (by omega)
      have hsq : 18 * (k - 1) < 2 * k * k := by nlinarith
      exact hsq.trans_le (Nat.mul_le_mul_left (2 * k) hd)
    calc
      (13 * k - 6) * d + 18 * (k - 1) ≤
          13 * k * d + 18 * (k - 1) := Nat.add_le_add_right hfirst _
      _ < 13 * k * d + 2 * k * d := Nat.add_lt_add_left hsecond _
      _ = 15 * k * d := by ring
  let M := 3 ^ (2 * e - highComponentMuThree k e - 1)
  have hcomp : 3 ^ (2 * e) < 3 * k * M := by
    exact threeComponentSquare_lt_three_k_mul_highPower he2 (by omega)
  have hscaled : 15 * k ^ 2 * d < 6 * k * M := by
    calc
      15 * k ^ 2 * d ≤ 2 * 3 ^ (2 * e) := hsquare
      _ < 2 * (3 * k * M) :=
        (Nat.mul_lt_mul_left (by norm_num : 0 < 2)).mpr hcomp
      _ = 6 * k * M := by ring
  have hmain : 15 * k * d < 6 * M := by
    apply Nat.lt_of_mul_lt_mul_left (a := k)
    simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using hscaled
  exact Nat.le_of_lt (hRlt.trans hmain)

/-- Cleaner sufficient condition for a three-power component. -/
theorem no_four_solution_of_highThreePower_component_of_square
    {e k n d : ℕ} (hk : 16 ≤ k) (hd : k ≤ d)
    (hexact : d.factorization 3 = e)
    (hcomponent : k ≤ 3 ^ e)
    (hsquare : 2 * 3 ^ (2 * e) ≥ 15 * k ^ 2 * d) :
    blockProduct k (n + d) ≠ 4 * blockProduct k n := by
  have he2 : 2 ≤ e := by
    by_contra hnot
    have he1 : e ≤ 1 := by omega
    interval_cases e <;> norm_num at hcomponent <;> omega
  exact no_four_solution_of_highThreePower_component
    hk hd hexact hcomponent
      (highComponent_dominance_three_of_square he2 hk hd hsquare)

theorem no_four_solution_primePowerGap_three
    {k t n : ℕ} (hk : 16 ≤ k) :
    blockProduct k (n + 3 ^ (k + t)) ≠ 4 * blockProduct k n := by
  let e := k + t
  let d := 3 ^ e
  have hkSq : 8 * k ^ 2 ≤ d := by
    have hthree : 8 * k ^ 2 ≤ 3 ^ k :=
      eight_mul_sq_le_three_pow (by omega)
    exact hthree.trans
      (Nat.pow_le_pow_right (by norm_num : 0 < 3) (by omega))
  have hd : k ≤ d := by nlinarith
  have hexact : d.factorization 3 = e := by
    exact Nat.factorization_pow_self (by norm_num)
  have hsquare : 2 * 3 ^ (2 * e) ≥ 15 * k ^ 2 * d := by
    have hdpos : 0 < d := pow_pos (by norm_num) e
    have hpowsq : 3 ^ (2 * e) = d ^ 2 := by
      dsimp [d]
      rw [show 2 * e = e * 2 by omega, pow_mul]
    rw [hpowsq]
    nlinarith
  have hcomponent : k ≤ 3 ^ e := by simpa [d] using hd
  exact no_four_solution_of_highThreePower_component_of_square
    hk hd hexact hcomponent hsquare

/-- Uniform explicit family from the high prime-power component theorem:
every gap `p^(k+t)` is excluded once `k ≥ 16`, for every prime base. -/
theorem no_four_solution_primePowerGap
    {p k t n : ℕ} (hp : p.Prime) (hk : 16 ≤ k) :
    blockProduct k (n + p ^ (k + t)) ≠ 4 * blockProduct k n := by
  by_cases hp2 : p = 2
  · subst p
    exact no_four_solution_primePowerGap_two hk
  by_cases hp3 : p = 3
  · subst p
    exact no_four_solution_primePowerGap_three hk
  have hp5 : 5 ≤ p := by
    have hpOdd : p % 2 = 1 := (hp.eq_two_or_odd).resolve_left hp2
    have hpTwoLe : 2 ≤ p := hp.two_le
    omega
  exact no_four_solution_primePowerGap_ge_five hp hp5 hk

#print axioms factorization_add_eq_left_of_lt
#print axioms factorization_add_eq_right_of_gt
#print axioms ordCompl_add_eq_of_factorization_lt
#print axioms nonowner_factorization_le_highComponentLambda
#print axioms max_factorization_not_gt_component
#print axioms max_factorization_not_lt_component_of_five_le
#print axioms highPrimePower_ge_five_exists_residual_lift
#print axioms no_four_solution_of_highPrimePower_ge_five_component
#print axioms highTwoPower_exists_residual_lift
#print axioms no_four_solution_of_highTwoPower_component
#print axioms p3HalfOwners_card_le_two
#print axioms p3HalfOwner_product_modEq_nine
#print axioms p3HalfOwners_existsUnique
#print axioms max_factorization_eq_component_sub_one_three
#print axioms highThreePower_exists_residual_lift
#print axioms no_four_solution_of_highThreePower_component
#print axioms no_four_solution_of_highPrimePower_component
#print axioms no_four_solution_of_highPrimePower_ge_five_component_of_square
#print axioms no_four_solution_of_highTwoPower_component_of_square
#print axioms no_four_solution_of_highThreePower_component_of_square
#print axioms no_four_solution_primePowerGap

end Erdos686Variant
end Erdos686
