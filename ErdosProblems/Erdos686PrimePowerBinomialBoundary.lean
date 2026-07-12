/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import ErdosProblems.Erdos686
import Mathlib.Data.Nat.Choose.Lucas

/-!
# A Lucas restriction for prime-power block lengths

Put `q = p^a` and `k=q-1`.  Lucas's theorem makes the boundary
binomial

`C(x+q-1,q-1)`

equal to `1` modulo `p` whenever `q | x`, and divisible by `p` whenever
`q ∤ x`.  For `p ≥ 5`, the quotient-four equation therefore cannot have
either endpoint parameter divisible by `q`.

This is a proper infinite-family restriction, not a solution of the large-row
target: the case in which both endpoint residues are nonzero remains open.
-/

namespace Erdos686

namespace Erdos686Variant

private lemma blockProduct_eq_ascFactorial_pp (k x : ℕ) :
    blockProduct k x = (x + 1).ascFactorial k := by
  have hs : Finset.Icc 1 k = Finset.Ico 1 (k + 1) := by
    ext i
    simp
  rw [Nat.ascFactorial_eq_prod_range]
  unfold blockProduct
  rw [hs, Finset.prod_Ico_eq_prod_range]
  simp only [Nat.add_sub_cancel]
  apply Finset.prod_congr rfl
  intro i hi
  omega

/-- The exact binomial translation of the block product. -/
theorem blockProduct_eq_factorial_mul_choose (k x : ℕ) :
    blockProduct k x = k.factorial * (x + k).choose k := by
  rw [blockProduct_eq_ascFactorial_pp, Nat.ascFactorial_eq_factorial_mul_choose]

/-- One half of the prime-power Lucas delta: a boundary multiple gives
residue one. -/
lemma choose_prime_pow_pred_modEq_one_of_dvd
    (p a x : ℕ) (hp : p.Prime) (hqx : p ^ a ∣ x) :
    (x + p ^ a - 1).choose (p ^ a - 1) ≡ 1 [MOD p] := by
  letI : Fact p.Prime := ⟨hp⟩
  induction a generalizing x with
  | zero =>
      simpa using (Nat.ModEq.refl 1 : 1 ≡ 1 [MOD p])
  | succ a ih =>
      obtain ⟨t, rfl⟩ := hqx
      let y : ℕ := p ^ a * t
      have hy : p ^ a ∣ y := ⟨t, rfl⟩
      have hp0 : 0 < p := hp.pos
      have hpa0 : 0 < p ^ a := pow_pos hp0 _
      have decompose (A : ℕ) (hA : 0 < A) :
          p * A - 1 = (p - 1) + p * (A - 1) := by
        rw [Nat.mul_sub_left_distrib]
        simp only [Nat.mul_one]
        have hpA : p ≤ p * A := by
          simpa using Nat.mul_le_mul_left p hA
        omega
      have htop :
          p ^ (a + 1) * t + p ^ (a + 1) - 1 =
            (p - 1) + p * (y + p ^ a - 1) := by
        calc
          p ^ (a + 1) * t + p ^ (a + 1) - 1 =
              p * (y + p ^ a) - 1 := by
                dsimp [y]
                rw [pow_succ]
                ring
          _ = (p - 1) + p * (y + p ^ a - 1) :=
            decompose (y + p ^ a) (by positivity)
      have hbot :
          p ^ (a + 1) - 1 = (p - 1) + p * (p ^ a - 1) := by
        calc
          p ^ (a + 1) - 1 = p * p ^ a - 1 := by
            rw [pow_succ]
            ring
          _ = (p - 1) + p * (p ^ a - 1) := decompose (p ^ a) hpa0
      have hLucas :=
        (Choose.choose_modEq_choose_mod_mul_choose_div_nat
          (n := p ^ (a + 1) * t + p ^ (a + 1) - 1)
          (k := p ^ (a + 1) - 1) (p := p))
      rw [htop, hbot] at hLucas
      have hpPred : p - 1 < p := Nat.sub_lt hp0 (by omega)
      have hmod (z : ℕ) : ((p - 1) + p * z) % p = p - 1 := by
        rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hpPred]
      have hdiv (z : ℕ) : ((p - 1) + p * z) / p = z := by
        rw [Nat.add_mul_div_left _ _ hp0, Nat.div_eq_of_lt hpPred]
        simp
      simp only [hmod, hdiv, Nat.choose_self, one_mul] at hLucas
      rw [htop, hbot]
      exact hLucas.trans (ih y hy)

/-- The other half of the Lucas delta: away from a boundary multiple, the
binomial is zero modulo the prime base. -/
lemma choose_prime_pow_pred_modEq_zero_of_not_dvd
    (p a x : ℕ) (hp : p.Prime) (hqx : ¬ p ^ a ∣ x) :
    (x + p ^ a - 1).choose (p ^ a - 1) ≡ 0 [MOD p] := by
  letI : Fact p.Prime := ⟨hp⟩
  induction a generalizing x with
  | zero =>
      exact False.elim (hqx (by simp))
  | succ a ih =>
      have hp0 : 0 < p := hp.pos
      have hpa0 : 0 < p ^ a := pow_pos hp0 _
      have decompose (A : ℕ) (hA : 0 < A) :
          p * A - 1 = (p - 1) + p * (A - 1) := by
        rw [Nat.mul_sub_left_distrib]
        simp only [Nat.mul_one]
        have hpA : p ≤ p * A := by
          simpa using Nat.mul_le_mul_left p hA
        omega
      have hbot :
          p ^ (a + 1) - 1 = (p - 1) + p * (p ^ a - 1) := by
        calc
          p ^ (a + 1) - 1 = p * p ^ a - 1 := by
            rw [pow_succ]
            ring
          _ = (p - 1) + p * (p ^ a - 1) := decompose (p ^ a) hpa0
      have hpPred : p - 1 < p := Nat.sub_lt hp0 (by omega)
      have hmodPred (z : ℕ) : ((p - 1) + p * z) % p = p - 1 := by
        rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hpPred]
      have hdivPred (z : ℕ) : ((p - 1) + p * z) / p = z := by
        rw [Nat.add_mul_div_left _ _ hp0, Nat.div_eq_of_lt hpPred]
        simp
      by_cases hpx : p ∣ x
      · obtain ⟨y, rfl⟩ := hpx
        have hyNot : ¬ p ^ a ∣ y := by
          intro hy
          apply hqx
          obtain ⟨t, rfl⟩ := hy
          refine ⟨t, ?_⟩
          rw [pow_succ]
          ring
        have htop :
            p * y + p ^ (a + 1) - 1 =
              (p - 1) + p * (y + p ^ a - 1) := by
          calc
            p * y + p ^ (a + 1) - 1 = p * (y + p ^ a) - 1 := by
              rw [pow_succ]
              ring
            _ = (p - 1) + p * (y + p ^ a - 1) :=
              decompose (y + p ^ a) (by positivity)
        have hLucas :=
          (Choose.choose_modEq_choose_mod_mul_choose_div_nat
            (n := p * y + p ^ (a + 1) - 1)
            (k := p ^ (a + 1) - 1) (p := p))
        rw [htop, hbot] at hLucas
        simp only [hmodPred, hdivPred, Nat.choose_self, one_mul] at hLucas
        rw [htop, hbot]
        exact hLucas.trans (ih y hyNot)
      · let y : ℕ := x / p
        let r : ℕ := x % p
        have hr0 : 0 < r := by
          have hrNe : r ≠ 0 := by
            intro hr
            apply hpx
            rw [Nat.dvd_iff_mod_eq_zero]
            exact hr
          exact Nat.pos_of_ne_zero hrNe
        have hrp : r < p := Nat.mod_lt _ hp0
        have hx : x = r + p * y := by
          dsimp [r, y]
          exact (Nat.mod_add_div x p).symm
        have htop :
            x + p ^ (a + 1) - 1 =
              (r - 1) + p * (y + p ^ a) := by
          calc
            x + p ^ (a + 1) - 1 =
                r + p * (y + p ^ a) - 1 := by
                  rw [hx, pow_succ]
                  ring
            _ = (r - 1) + p * (y + p ^ a) := by omega
        have hrPred : r - 1 < p := by omega
        have hdigit : r - 1 < p - 1 := by omega
        have hmodR (z : ℕ) : ((r - 1) + p * z) % p = r - 1 := by
          rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hrPred]
        have hdivR (z : ℕ) : ((r - 1) + p * z) / p = z := by
          rw [Nat.add_mul_div_left _ _ hp0, Nat.div_eq_of_lt hrPred]
          simp
        have hchoose : (r - 1).choose (p - 1) = 0 :=
          Nat.choose_eq_zero_of_lt hdigit
        have hLucas :=
          (Choose.choose_modEq_choose_mod_mul_choose_div_nat
            (n := x + p ^ (a + 1) - 1)
            (k := p ^ (a + 1) - 1) (p := p))
        rw [htop, hbot] at hLucas
        simp only [hmodR, hdivR, hmodPred, hdivPred, hchoose, zero_mul] at hLucas
        rw [htop, hbot]
        exact hLucas

private lemma prime_not_dvd_of_modEq_one
    {p z : ℕ} (hp : p.Prime) (hz : z ≡ 1 [MOD p]) : ¬ p ∣ z := by
  intro hpz
  have hz0 : z ≡ 0 [MOD p] := Nat.modEq_zero_iff_dvd.mpr hpz
  exact hp.not_dvd_one (Nat.modEq_zero_iff_dvd.mp (hz.symm.trans hz0))

/-- Choose-form endpoint exclusion for `k+1=p^a`: when `p≥5`, neither
endpoint parameter can be a multiple of `p^a`. -/
theorem prime_power_pred_choose_ratio_four_endpoints_not_dvd
    {p a n d : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p)
    (heq :
      (n + d + p ^ a - 1).choose (p ^ a - 1) =
        4 * (n + p ^ a - 1).choose (p ^ a - 1)) :
    ¬ p ^ a ∣ n ∧ ¬ p ^ a ∣ n + d := by
  let lower := (n + p ^ a - 1).choose (p ^ a - 1)
  let upper := (n + d + p ^ a - 1).choose (p ^ a - 1)
  have heq' : upper = 4 * lower := by simpa [upper, lower] using heq
  have hleft : ¬ p ^ a ∣ n := by
    intro hqn
    have hLowerOne : lower ≡ 1 [MOD p] := by
      dsimp [lower]
      exact choose_prime_pow_pred_modEq_one_of_dvd p a n hp hqn
    have hpLower : ¬ p ∣ lower := prime_not_dvd_of_modEq_one hp hLowerOne
    have hpUpper : ¬ p ∣ upper := by
      intro hpU
      have hpRhs : p ∣ 4 * lower := by rwa [← heq']
      rcases hp.dvd_mul.mp hpRhs with hp4 | hpL
      · have hple4 := Nat.le_of_dvd (by norm_num : 0 < 4) hp4
        omega
      · exact hpLower hpL
    have hqUpper : p ^ a ∣ n + d := by
      by_contra hnot
      have hUpperZero : upper ≡ 0 [MOD p] := by
        dsimp [upper]
        simpa [Nat.add_assoc] using
          choose_prime_pow_pred_modEq_zero_of_not_dvd p a (n + d) hp hnot
      exact hpUpper (Nat.modEq_zero_iff_dvd.mp hUpperZero)
    have hUpperOne : upper ≡ 1 [MOD p] := by
      dsimp [upper]
      simpa [Nat.add_assoc] using
        choose_prime_pow_pred_modEq_one_of_dvd p a (n + d) hp hqUpper
    have hEqMod : upper ≡ 4 * lower [MOD p] := by rw [heq']
    have hFourLower : 4 * lower ≡ 4 [MOD p] := by
      simpa using (Nat.ModEq.refl 4).mul hLowerOne
    have hOneFour : 1 ≡ 4 [MOD p] :=
      hUpperOne.symm.trans (hEqMod.trans hFourLower)
    have hp3 : p ∣ 3 :=
      (Nat.modEq_iff_dvd' (by norm_num : 1 ≤ 4)).mp hOneFour
    have hple3 := Nat.le_of_dvd (by norm_num : 0 < 3) hp3
    omega
  refine ⟨hleft, ?_⟩
  intro hqUpper
  have hUpperOne : upper ≡ 1 [MOD p] := by
    dsimp [upper]
    simpa [Nat.add_assoc] using
      choose_prime_pow_pred_modEq_one_of_dvd p a (n + d) hp hqUpper
  have hpUpper : ¬ p ∣ upper := prime_not_dvd_of_modEq_one hp hUpperOne
  have hLowerZero : lower ≡ 0 [MOD p] := by
    dsimp [lower]
    exact choose_prime_pow_pred_modEq_zero_of_not_dvd p a n hp hleft
  have hpLower : p ∣ lower := Nat.modEq_zero_iff_dvd.mp hLowerZero
  have hpRhs : p ∣ 4 * lower := dvd_mul_of_dvd_right hpLower 4
  exact hpUpper (by rwa [← heq'] at hpRhs)

/-- Original block-product form of the prime-power endpoint restriction. -/
theorem prime_power_pred_four_solution_endpoints_not_dvd
    {p a n d : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p)
    (heq :
      blockProduct (p ^ a - 1) (n + d) =
        4 * blockProduct (p ^ a - 1) n) :
    ¬ p ^ a ∣ n ∧ ¬ p ^ a ∣ n + d := by
  have hfac := Nat.factorial_pos (p ^ a - 1)
  have heqChoose :
      (n + d + p ^ a - 1).choose (p ^ a - 1) =
        4 * (n + p ^ a - 1).choose (p ^ a - 1) := by
    rw [blockProduct_eq_factorial_mul_choose,
      blockProduct_eq_factorial_mul_choose] at heq
    have hq0 : 0 < p ^ a := pow_pos hp.pos _
    have hupperIndex : n + d + (p ^ a - 1) = n + d + p ^ a - 1 := by omega
    have hlowerIndex : n + (p ^ a - 1) = n + p ^ a - 1 := by omega
    rw [hupperIndex, hlowerIndex] at heq
    apply Nat.eq_of_mul_eq_mul_left hfac
    calc
      (p ^ a - 1).factorial *
          (n + d + p ^ a - 1).choose (p ^ a - 1) =
          4 * ((p ^ a - 1).factorial *
            (n + p ^ a - 1).choose (p ^ a - 1)) := heq
      _ = (p ^ a - 1).factorial *
          (4 * (n + p ^ a - 1).choose (p ^ a - 1)) := by ring
  exact prime_power_pred_choose_ratio_four_endpoints_not_dvd hp hp5 heqChoose

#print axioms blockProduct_eq_factorial_mul_choose
#print axioms choose_prime_pow_pred_modEq_one_of_dvd
#print axioms choose_prime_pow_pred_modEq_zero_of_not_dvd
#print axioms prime_power_pred_choose_ratio_four_endpoints_not_dvd
#print axioms prime_power_pred_four_solution_endpoints_not_dvd

end Erdos686Variant

end Erdos686
