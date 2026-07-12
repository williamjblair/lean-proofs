import ErdosProblems.Erdos686SylvesterSchur
import Mathlib.NumberTheory.Padics.PadicVal.Basic

/-!
# Nonintegrality of the reflected harmonic obstruction

This module converts the kernel-checked Sylvester--Schur theorem into the
exact nonintegrality statement required by the simultaneous-zero branch of
the large odd two-prime Pell reduction.  The boundary `k=3, i=1`, where the
value is the integer `12`, is excluded sharply by `k ≥ 5`.
-/

open scoped BigOperators

namespace Erdos686
namespace Erdos686Variant

open Erdos699Formalization

noncomputable def reciprocalSum (S : Finset ℕ) : ℚ :=
  ∑ s ∈ S, (s : ℚ)⁻¹

lemma unique_prime_harmonic_not_integer
    {S : Finset ℕ} {p M u : ℕ}
    (hp : p.Prime)
    (hMpos : 0 < M)
    (hu : u ∈ S)
    (hSpos : ∀ s ∈ S, 0 < s)
    (hpu : p ∣ u)
    (hpM : ¬ p ∣ M)
    (hunique : ∀ s ∈ S, s ≠ u → ¬ p ∣ s) :
    ¬ ∃ z : ℤ, (M : ℚ) * reciprocalSum S = z := by
  letI : Fact p.Prime := ⟨hp⟩
  let F : ℕ → ℚ := fun s ↦ (s : ℚ)⁻¹
  have hu0 : u ≠ 0 := Nat.ne_of_gt (hSpos u hu)
  have hvalUneg : padicValRat p (F u) < 0 := by
    rw [show F u = (u : ℚ)⁻¹ by rfl, padicValRat.inv, padicValRat.of_nat]
    have hvalU : 1 ≤ padicValNat p u := one_le_padicValNat_of_dvd hu0 hpu
    omega
  have hsumPos : 0 < reciprocalSum S := by
    unfold reciprocalSum
    exact Finset.sum_pos (fun s hs ↦ inv_pos.mpr (by exact_mod_cast hSpos s hs)) ⟨u, hu⟩
  have hsumNe : reciprocalSum S ≠ 0 := ne_of_gt hsumPos
  have hvalSum : padicValRat p (reciprocalSum S) = padicValRat p (F u) := by
    by_cases hrest : (S.erase u).Nonempty
    · have hvalOther :
          ∀ s, s ∈ S.erase u → padicValRat p (F u) < padicValRat p (F s) := by
        intro s hs
        have hsS : s ∈ S := Finset.mem_of_mem_erase hs
        have hsu : s ≠ u := (Finset.mem_erase.mp hs).1
        have hps : ¬ p ∣ s := hunique s hsS hsu
        have hs0 : s ≠ 0 := Nat.ne_of_gt (hSpos s hsS)
        have hvalS : padicValRat p (F s) = 0 := by
          rw [show F s = (s : ℚ)⁻¹ by rfl, padicValRat.inv,
            padicValRat.of_nat, padicValNat.eq_zero_of_not_dvd hps]
          norm_num
        rw [hvalS]
        exact hvalUneg
      have hrestPos : 0 < ∑ s ∈ S.erase u, F s := by
        exact Finset.sum_pos
          (fun s hs ↦ inv_pos.mpr (by
            exact_mod_cast hSpos s (Finset.mem_of_mem_erase hs))) hrest
      let G : ℕ → ℚ := fun s ↦ if s ∈ S then F s else 1
      have hGu : G u = F u := by simp [G, hu]
      have hGs : ∀ s ∈ S.erase u, G s = F s := by
        intro s hs
        simp [G, Finset.mem_of_mem_erase hs]
      have hvalRest :
          padicValRat p (F u) < padicValRat p (∑ s ∈ S.erase u, F s) :=
        by
          have hG := padicValRat.lt_sum_of_lt (p := p) (j := u) (F := G) hrest
            (fun s hs ↦ by rw [hGu, hGs s hs]; exact hvalOther s hs)
            (fun s ↦ by
              dsimp [G]
              split_ifs with hs
              · exact inv_pos.mpr (by exact_mod_cast hSpos s hs)
              · norm_num)
          have hsumG : ∑ s ∈ S.erase u, G s = ∑ s ∈ S.erase u, F s :=
            Finset.sum_congr rfl hGs
          rw [hGu, hsumG] at hG
          exact hG
      have hadd : F u + ∑ s ∈ S.erase u, F s ≠ 0 := by positivity
      have hFu : F u ≠ 0 := inv_ne_zero (by exact_mod_cast hu0)
      have hrestNe : ∑ s ∈ S.erase u, F s ≠ 0 := ne_of_gt hrestPos
      have hv := padicValRat.add_eq_of_lt hadd hFu hrestNe hvalRest
      rw [reciprocalSum, ← Finset.add_sum_erase _ _ hu]
      exact hv
    · have hrestEmpty : S.erase u = ∅ := Finset.not_nonempty_iff_eq_empty.mp hrest
      rw [reciprocalSum, ← Finset.add_sum_erase _ _ hu, hrestEmpty]
      simp [F]
  rintro ⟨z, hz⟩
  have hMne : (M : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hMpos)
  have hzpos : (0 : ℚ) < z := by rw [← hz]; positivity
  have hz0 : z ≠ 0 := by exact_mod_cast (ne_of_gt hzpos)
  have hvalM : padicValRat p (M : ℚ) = 0 := by
    have hv : padicValNat p M = 0 := padicValNat.eq_zero_of_not_dvd hpM
    simp [hv]
  have hvalProd :
      padicValRat p ((M : ℚ) * reciprocalSum S) < 0 := by
    rw [padicValRat.mul hMne hsumNe, hvalM, zero_add, hvalSum]
    exact hvalUneg
  have hvalZ : 0 ≤ padicValRat p (z : ℚ) := by
    rw [padicValRat.of_int]
    exact Int.natCast_nonneg (padicValInt p z)
  rw [hz] at hvalProd
  exact (not_lt_of_ge hvalZ) hvalProd

lemma prime_not_dvd_four_mul_of_half_lt_of_even
    {p N : ℕ} (hp : p.Prime) (hN4 : 4 ≤ N) (hEven : Even N)
    (hhalf : N / 2 < p) : ¬ p ∣ 4 * N := by
  intro hdiv
  rcases hp.dvd_mul.mp hdiv with hp4 | hpN
  · have hpPow : p ∣ 2 ^ 2 := by norm_num; exact hp4
    have hp2 : p ∣ 2 := hp.dvd_of_dvd_pow hpPow
    have hpEq : p = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hp2
    subst p
    omega
  · have hNpos : 0 < N := by omega
    have hNp : N < p * 2 := (Nat.div_lt_iff_lt_mul (by norm_num : 0 < 2)).mp hhalf
    obtain ⟨c, hc⟩ := hpN
    have hcpos : 0 < c := by
      apply Nat.pos_of_ne_zero
      intro hc0
      subst c
      simp at hc
      exact hNpos.ne' hc
    have hcLt : c < 2 := by
      rw [hc] at hNp
      nlinarith [hp.pos]
    have hc1 : c = 1 := by omega
    subst c
    simp at hc
    subst N
    have h2p : 2 ∣ p := (even_iff_two_dvd.mp hEven)
    have hpEq : 2 = p := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp h2p
    omega

lemma prime_unique_in_short_interval
    {x N p u : ℕ} (hpN : N < p)
    (hu : u ∈ Finset.Icc x (x + N - 1)) (hpu : p ∣ u) :
    ∀ s ∈ Finset.Icc x (x + N - 1), s ≠ u → ¬ p ∣ s := by
  intro s hs hsu hps
  rcases lt_or_gt_of_ne hsu with hsuLt | husLt
  · have hpDiff : p ∣ u - s := Nat.dvd_sub hpu hps
    have hdiffPos : 0 < u - s := Nat.sub_pos_of_lt hsuLt
    have hpLe : p ≤ u - s := Nat.le_of_dvd hdiffPos hpDiff
    have huhi := (Finset.mem_Icc.mp hu).2
    have hslo := (Finset.mem_Icc.mp hs).1
    omega
  · have hpDiff : p ∣ s - u := Nat.dvd_sub hps hpu
    have hdiffPos : 0 < s - u := Nat.sub_pos_of_lt husLt
    have hpLe : p ≤ s - u := Nat.le_of_dvd hdiffPos hpDiff
    have hshi := (Finset.mem_Icc.mp hs).2
    have hulo := (Finset.mem_Icc.mp hu).1
    omega

lemma prime_unique_below_twice
    {x U p : ℕ} (hxpos : 0 < x)
    (hU2p : U < 2 * p) :
    ∀ s ∈ Finset.Icc x U, s ≠ p → ¬ p ∣ s := by
  intro s hs hsp hps
  obtain ⟨c, hc⟩ := hps
  have hspos : 0 < s := lt_of_lt_of_le hxpos (Finset.mem_Icc.mp hs).1
  have hcpos : 0 < c := by
    apply Nat.pos_of_ne_zero
    intro hc0
    subst c
    simp at hc
    exact hspos.ne' hc
  have hcLt : c < 2 := by
    have hsU := (Finset.mem_Icc.mp hs).2
    have hpPos : 0 < p := by omega
    rw [hc] at hsU
    nlinarith
  have hc1 : c = 1 := by omega
  subst c
  simp at hc
  exact hsp hc

lemma even_interval_prime_witness
    {x N : ℕ} (hx : 1 ≤ x) (hN4 : 4 ≤ N) (hEven : Even N) :
    ∃ p u : ℕ,
      p.Prime ∧
      u ∈ Finset.Icc x (x + N - 1) ∧
      p ∣ u ∧
      ¬ p ∣ 4 * N ∧
      ∀ s ∈ Finset.Icc x (x + N - 1), s ≠ u → ¬ p ∣ s := by
  by_cases hxN : x ≤ N
  · let U := x + N - 1
    let m := U / 2
    have hU4 : 4 ≤ U := by dsimp [U]; omega
    have hm0 : m ≠ 0 := by
      dsimp [m]
      have : 2 ≤ U / 2 := (Nat.le_div_iff_mul_le (by norm_num : 0 < 2)).mpr (by omega)
      omega
    obtain ⟨p, hp, hmp, hp2m⟩ := Nat.exists_prime_lt_and_le_two_mul m hm0
    have hdecomp := Nat.div_add_mod U 2
    have hrem := Nat.mod_lt U (by norm_num : 0 < 2)
    have hpU : p ≤ U := by dsimp [m] at hp2m hmp; omega
    have hU2p : U < 2 * p := by dsimp [m] at hp2m hmp; omega
    have hxp : x ≤ p := by
      have hxm : x - 1 ≤ m := by
        dsimp [m, U]
        apply (Nat.le_div_iff_mul_le (by norm_num : 0 < 2)).mpr
        omega
      omega
    have hhalf : N / 2 < p := by
      have hNU : N ≤ U := by dsimp [U]; omega
      have hdiv : N / 2 ≤ U / 2 := Nat.div_le_div_right hNU
      dsimp [m] at hmp
      omega
    refine ⟨p, p, hp, Finset.mem_Icc.mpr ⟨hxp, hpU⟩, dvd_rfl,
      prime_not_dvd_four_mul_of_half_lt_of_even hp hN4 hEven hhalf, ?_⟩
    simpa [U] using prime_unique_below_twice (by omega) hU2p
  · have hNx : N < x := Nat.lt_of_not_ge hxN
    have hhalf : N ≤ (x + N - 1) / 2 := by
      apply (Nat.le_div_iff_mul_le (by norm_num : 0 < 2)).mpr
      omega
    obtain ⟨p, hp, hNp, hpChoose⟩ :=
      sylvester_schur (x + N - 1) N (by omega) hhalf
    have hAsc : x.ascFactorial N = N.factorial * Nat.choose (x + N - 1) N := by
      have hxsub : x - 1 + 1 = x := Nat.sub_add_cancel hx
      have hsum : x - 1 + N = x + N - 1 := by omega
      simpa [hxsub, hsum] using Nat.ascFactorial_eq_factorial_mul_choose (x - 1) N
    have hpAsc : p ∣ x.ascFactorial N := by
      rw [hAsc]
      exact dvd_mul_of_dvd_right hpChoose N.factorial
    obtain ⟨u, huIco, hpu⟩ :=
      exists_mem_Ico_dvd_of_prime_dvd_ascFactorial hp hpAsc
    have hu : u ∈ Finset.Icc x (x + N - 1) := by
      rw [Finset.mem_Icc]
      exact ⟨huIco.1,
        (Nat.le_sub_one_iff_lt (by omega : 0 < x + N)).mpr huIco.2⟩
    have hpM : ¬ p ∣ 4 * N := by
      intro hpM
      rcases hp.dvd_mul.mp hpM with hp4 | hpNdvd
      · have hpPow : p ∣ 2 ^ 2 := by norm_num; exact hp4
        have hp2 : p ∣ 2 := hp.dvd_of_dvd_pow hpPow
        have hpEq : p = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hp2
        omega
      · have hpLeN : p ≤ N := Nat.le_of_dvd (by omega) hpNdvd
        omega
    exact ⟨p, u, hp, hu, hpu, hpM,
      prime_unique_in_short_interval hNp hu hpu⟩

lemma two_interval_harmonic_not_integer {x : ℕ} (hx2 : 2 ≤ x) :
    ¬ ∃ z : ℤ,
      (8 : ℚ) * reciprocalSum (Finset.Icc x (x + 1)) = z := by
  have hset : Finset.Icc x (x + 1) = {x, x + 1} := by
    ext s
    simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]
    omega
  rw [hset]
  by_cases hx15 : x ≤ 15
  · rintro ⟨z, hz⟩
    interval_cases x <;>
      norm_num [reciprocalSum, div_eq_iff] at hz <;>
      norm_cast at hz <;> omega
  · have hx16 : 16 ≤ x := by omega
    rintro ⟨z, hz⟩
    have hxQ : (16 : ℚ) ≤ x := by exact_mod_cast hx16
    have hxQpos : (0 : ℚ) < x := by exact_mod_cast (by omega : 0 < x)
    have hx1Qpos : (0 : ℚ) < x + 1 := by positivity
    have hInv1 : (x : ℚ)⁻¹ ≤ 1 / 16 := by
      simpa only [one_div] using
        one_div_le_one_div_of_le (by norm_num : (0 : ℚ) < 16) hxQ
    have hInv2 : ((x + 1 : ℕ) : ℚ)⁻¹ < 1 / 16 := by
      have hxLt : (16 : ℚ) < x + 1 := by exact_mod_cast (by omega : 16 < x + 1)
      rw [show (((x + 1 : ℕ) : ℚ)) = (x : ℚ) + 1 by norm_num]
      simpa only [one_div] using one_div_lt_one_div_of_lt
        (by norm_num : (0 : ℚ) < 16) hxLt
    have hpos : (0 : ℚ) <
        8 * reciprocalSum ({x, x + 1} : Finset ℕ) := by
      simp [reciprocalSum]
      positivity
    have hlt : (8 : ℚ) * reciprocalSum ({x, x + 1} : Finset ℕ) < 1 := by
      have hsum : reciprocalSum ({x, x + 1} : Finset ℕ) =
          (x : ℚ)⁻¹ + (((x + 1 : ℕ) : ℚ))⁻¹ := by
        simp [reciprocalSum]
      rw [hsum]
      nlinarith
    have hzposQ : (0 : ℚ) < z := by rw [← hz]; exact hpos
    have hzltQ : (z : ℚ) < 1 := by rw [← hz]; exact hlt
    have hzpos : (0 : ℤ) < z := by exact_mod_cast hzposQ
    have hzlt : z < (1 : ℤ) := by exact_mod_cast hzltQ
    omega

/-- The reflected simultaneous-zero slope is never integral in any live odd
row.  The excluded boundary `k=3, i=1` has value `12`. -/
theorem reflected_harmonic_not_integer
    {k i : ℕ} (hkOdd : Odd k) (hk5 : 5 ≤ k)
    (hi1 : 1 ≤ i) (hiMid : i < (k + 1) / 2) :
    ¬ ∃ z : ℤ,
      (((4 * (k + 1 - 2 * i) : ℕ) : ℚ) *
        reciprocalSum (Finset.Icc i (k - i))) = z := by
  let N : ℕ := k + 1 - 2 * i
  have hkEven : Even (k + 1) := hkOdd.add_one
  have h2dvd : 2 ∣ k + 1 := even_iff_two_dvd.mp hkEven
  have h2i : 2 * i < k + 1 :=
    (Nat.lt_div_iff_mul_lt' h2dvd i).mp hiMid
  have hNpos : 0 < N := by dsimp [N]; omega
  have hNEven : Even N := by
    dsimp [N]
    rw [Nat.even_sub (le_of_lt h2i)]
    exact ⟨fun _ ↦ even_two_mul i, fun _ ↦ hkEven⟩
  have hend : i + N - 1 = k - i := by dsimp [N]; omega
  change ¬ ∃ z : ℤ,
    (((4 * N : ℕ) : ℚ) * reciprocalSum (Finset.Icc i (k - i))) = z
  by_cases hN2 : N = 2
  · have hi2 : 2 ≤ i := by
      dsimp [N] at hN2
      omega
    have hend2 : k - i = i + 1 := by omega
    simpa [hN2, hend2] using two_interval_harmonic_not_integer hi2
  · obtain ⟨c, hc⟩ := hNEven
    have hN4 : 4 ≤ N := by
      have hcpos : 0 < c := by nlinarith
      have hc2 : 2 ≤ c := by
        by_contra hcnot
        have hc1 : c = 1 := by omega
        subst c
        simp at hc
        exact hN2 hc
      omega
    obtain ⟨p, u, hp, hu, hpu, hpM, hunique⟩ :=
      even_interval_prime_witness hi1 hN4 (show Even N from ⟨c, hc⟩)
    have hnot := unique_prime_harmonic_not_integer
      (S := Finset.Icc i (i + N - 1)) (p := p) (M := 4 * N) (u := u)
      hp (by positivity) hu
      (fun s hs ↦ lt_of_lt_of_le (by omega : 0 < i) (Finset.mem_Icc.mp hs).1)
      hpu hpM hunique
    simpa only [hend] using hnot

#print axioms unique_prime_harmonic_not_integer
#print axioms even_interval_prime_witness
#print axioms reflected_harmonic_not_integer

end Erdos686Variant
end Erdos686
