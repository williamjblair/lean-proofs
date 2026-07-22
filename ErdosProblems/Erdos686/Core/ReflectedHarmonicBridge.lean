import ErdosProblems.Erdos686.Core.ReflectedHarmonic
import ErdosProblems.Erdos686.Core.TwoPrimeSecondLift

/-!
# The second-obstruction to reflected-harmonic bridge

This file proves the generic coefficient identities omitted from the initial
Pell package.  In every odd row `k ≥ 5`, two distinct owners cannot have both
fixed second obstructions equal to zero: the two equations force reflection
and then force an integer to equal the nonintegral harmonic value excluded by
`reflected_harmonic_not_integer`.
-/

open scoped BigOperators

namespace Erdos686
namespace Erdos686Variant

lemma affineLinear_cast_eq_constant_mul_reciprocalSum
    {α : Type*} [DecidableEq α] (s : Finset α) (f : α → ℤ)
    (hf : ∀ x ∈ s, f x ≠ 0) :
    ((finsetAffineLinear s f : ℤ) : ℚ) =
      (finsetAffineConstant s f : ℚ) *
        ∑ x ∈ s, (((f x : ℤ) : ℚ))⁻¹ := by
  unfold finsetAffineLinear finsetAffineConstant
  push_cast
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  rw [← Finset.mul_prod_erase s (fun y ↦ ((f y : ℤ) : ℚ)) hx]
  field_simp [hf x hx]

noncomputable def ownerSlope (k i : ℕ) : ℚ :=
  ∑ j ∈ (Finset.Icc 1 k).erase i,
    (((j : ℤ) - (i : ℤ) : ℤ) : ℚ)⁻¹

noncomputable def harmonicPrefix (n : ℕ) : ℚ :=
  reciprocalSum (Finset.Icc 1 n)

lemma upper_offset_sum_eq_harmonicPrefix {k i : ℕ} (hik : i ≤ k) :
    (∑ j ∈ Finset.Icc (i + 1) k,
        (((j : ℤ) - (i : ℤ) : ℤ) : ℚ)⁻¹) =
      harmonicPrefix (k - i) := by
  unfold harmonicPrefix reciprocalSum
  apply Finset.sum_bij (fun j _ ↦ j - i)
  · intro j hj
    simp only [Finset.mem_Icc] at hj ⊢
    omega
  · intro a ha b hb hab
    simp only [Finset.mem_Icc] at ha hb
    omega
  · intro s hs
    refine ⟨i + s, ?_, ?_⟩
    · simp only [Finset.mem_Icc] at hs ⊢
      omega
    · omega
  · intro j hj
    simp only [Finset.mem_Icc] at hj
    congr 1
    have hz : (j : ℤ) - (i : ℤ) = ((j - i : ℕ) : ℤ) := by
      omega
    rw [hz]
    norm_num

lemma lower_offset_sum_eq_neg_harmonicPrefix {i : ℕ} (hi1 : 1 ≤ i) :
    (∑ j ∈ Finset.Icc 1 (i - 1),
        (((j : ℤ) - (i : ℤ) : ℤ) : ℚ)⁻¹) =
      -harmonicPrefix (i - 1) := by
  unfold harmonicPrefix reciprocalSum
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_bij (fun j _ ↦ i - j)
  · intro j hj
    simp only [Finset.mem_Icc] at hj ⊢
    omega
  · intro a ha b hb hab
    simp only [Finset.mem_Icc] at ha hb
    omega
  · intro s hs
    have hs' := Finset.mem_Icc.mp hs
    refine ⟨i - s, ?_, ?_⟩
    · simp only [Finset.mem_Icc] at hs ⊢
      omega
    · exact Nat.sub_sub_self (by omega : s ≤ i)
  · intro j hj
    simp only [Finset.mem_Icc] at hj
    have hji : (j : ℤ) - (i : ℤ) = -((i - j : ℕ) : ℤ) := by
      rw [Int.ofNat_sub (by omega : j ≤ i)]
      ring
    rw [hji]
    simp

lemma ownerSlope_eq_harmonicPrefix_sub
    {k i : ℕ} (hi1 : 1 ≤ i) (hik : i ≤ k) :
    ownerSlope k i = harmonicPrefix (k - i) - harmonicPrefix (i - 1) := by
  unfold ownerSlope
  have hset : (Finset.Icc 1 k).erase i =
      Finset.Icc 1 (i - 1) ∪ Finset.Icc (i + 1) k := by
    ext j
    simp only [Finset.mem_erase, Finset.mem_Icc, Finset.mem_union]
    omega
  rw [hset, Finset.sum_union]
  · rw [upper_offset_sum_eq_harmonicPrefix hik,
      lower_offset_sum_eq_neg_harmonicPrefix hi1]
    ring
  · rw [Finset.disjoint_left]
    intro j hjlow hjhigh
    simp only [Finset.mem_Icc] at hjlow hjhigh
    omega

lemma localSecondLinear_cast_eq_constant_mul_ownerSlope
    (k i : ℕ) :
    (localSecondLinear k i : ℚ) =
      (localSecondConstant k i : ℚ) * ownerSlope k i := by
  have hraw := affineLinear_cast_eq_constant_mul_reciprocalSum
    ((Finset.Icc 1 k).erase i) (fun j ↦ (j : ℤ) - (i : ℤ))
    (by
      intro j hj
      have hji := (Finset.mem_erase.mp hj).1
      exact sub_ne_zero.mpr (by exact_mod_cast hji))
  simpa [localSecondLinear, localSecondConstant, ownerSlope] using hraw

lemma localSecondConstant_ne_zero_of_mem_Icc
    {k i : ℕ} (hi : i ∈ Finset.Icc 1 k) :
    localSecondConstant k i ≠ 0 := by
  rw [localSecondConstant_eq_localBlockCoefficient,
    localBlockCoefficient_eq_sign_mul_nat hi]
  apply mul_ne_zero
  · exact pow_ne_zero _ (by norm_num)
  · exact_mod_cast (by
      unfold localBlockCoefficientNat
      exact mul_ne_zero (Nat.factorial_ne_zero _) (Nat.factorial_ne_zero _))

lemma harmonicPrefix_succ (n : ℕ) :
    harmonicPrefix (n + 1) = harmonicPrefix n + ((n + 1 : ℕ) : ℚ)⁻¹ := by
  have hset : Finset.Icc 1 (n + 1) =
      insert (n + 1) (Finset.Icc 1 n) := by
    ext s
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  have hnot : n + 1 ∉ Finset.Icc 1 n := by
    simp only [Finset.mem_Icc, not_and_or]
    omega
  unfold harmonicPrefix reciprocalSum
  rw [hset]
  simp [hnot, add_comm]

lemma ownerSlope_strictAnti_step
    {k i : ℕ} (hi1 : 1 ≤ i) (hik : i < k) :
    ownerSlope k (i + 1) < ownerSlope k i := by
  rw [ownerSlope_eq_harmonicPrefix_sub (by omega) (by omega),
    ownerSlope_eq_harmonicPrefix_sub hi1 (by omega)]
  have hkidecomp : k - i = (k - (i + 1)) + 1 := by omega
  have hipred : i = (i - 1) + 1 := by omega
  have hkH := harmonicPrefix_succ (k - (i + 1))
  rw [← hkidecomp] at hkH
  have hiH := harmonicPrefix_succ (i - 1)
  rw [← hipred] at hiH
  simp only [Nat.add_sub_cancel] at *
  rw [hkH, hiH]
  have hpos1 : (0 : ℚ) < ((k - i : ℕ) : ℚ)⁻¹ := by
    apply inv_pos.mpr
    exact_mod_cast (by omega : 0 < k - i)
  have hpos2 : (0 : ℚ) < (i : ℚ)⁻¹ := by
    exact inv_pos.mpr (by exact_mod_cast hi1)
  linarith

lemma ownerSlope_strictAnti
    {k i j : ℕ} (hi1 : 1 ≤ i) (hjk : j ≤ k) (hij : i < j) :
    ownerSlope k j < ownerSlope k i := by
  induction j with
  | zero => omega
  | succ j ih =>
      by_cases hijEq : i = j
      · subst j
        exact ownerSlope_strictAnti_step hi1 (by omega)
      · have hiJ : i < j := by omega
        have hj1 : 1 ≤ j := by omega
        have hjk' : j ≤ k := by omega
        exact lt_trans (ownerSlope_strictAnti_step hj1 (by omega))
          (ih hjk' hiJ)

lemma ownerSlope_reflect
    {k i : ℕ} (hi1 : 1 ≤ i) (hik : i ≤ k) :
    ownerSlope k (k + 1 - i) = -ownerSlope k i := by
  have hr1 : 1 ≤ k + 1 - i := by omega
  have hrk : k + 1 - i ≤ k := by omega
  rw [ownerSlope_eq_harmonicPrefix_sub hr1 hrk,
    ownerSlope_eq_harmonicPrefix_sub hi1 hik]
  have hleft : k - (k + 1 - i) = i - 1 := by omega
  have hright : k + 1 - i - 1 = k - i := by omega
  rw [hleft, hright]
  ring

lemma ownerSlope_neg_eq_forces_reflection
    {k i j : ℕ}
    (hi1 : 1 ≤ i) (hik : i ≤ k)
    (hj1 : 1 ≤ j) (hjk : j ≤ k)
    (hslope : ownerSlope k i = -ownerSlope k j) :
    i + j = k + 1 := by
  have href := ownerSlope_reflect hj1 hjk
  have heq : ownerSlope k i = ownerSlope k (k + 1 - j) := by
    rw [href]
    exact hslope
  have hr1 : 1 ≤ k + 1 - j := by omega
  have hrk : k + 1 - j ≤ k := by omega
  have hindex : i = k + 1 - j := by
    rcases lt_trichotomy i (k + 1 - j) with hlt | heqIdx | hgt
    · have hsl := ownerSlope_strictAnti hi1 hrk hlt
      rw [heq] at hsl
      exact (lt_irrefl _ hsl).elim
    · exact heqIdx
    · have hsl := ownerSlope_strictAnti hr1 hik hgt
      rw [heq] at hsl
      exact (lt_irrefl _ hsl).elim
  omega

lemma harmonicPrefix_sub_eq_reciprocalSum_Icc
    {a b : ℕ} (ha1 : 1 ≤ a) (hab : a ≤ b) :
    harmonicPrefix b - harmonicPrefix (a - 1) =
      reciprocalSum (Finset.Icc a b) := by
  have hset : Finset.Icc 1 b =
      Finset.Icc 1 (a - 1) ∪ Finset.Icc a b := by
    ext s
    simp only [Finset.mem_Icc, Finset.mem_union]
    omega
  have hdisj : Disjoint (Finset.Icc 1 (a - 1)) (Finset.Icc a b) := by
    rw [Finset.disjoint_left]
    intro s hs1 hs2
    simp only [Finset.mem_Icc] at hs1 hs2
    omega
  unfold harmonicPrefix reciprocalSum
  rw [hset, Finset.sum_union hdisj]
  ring

theorem no_simultaneous_second_obstruction_zero_ordered
    {k i j t : ℕ}
    (hkOdd : Odd k) (hk5 : 5 ≤ k)
    (hi : i ∈ Finset.Icc 1 k) (hj : j ∈ Finset.Icc 1 k)
    (hij : i < j)
    (hL : secondObstructionLeft k i j t = 0)
    (hR : secondObstructionRight k i j t = 0) : False := by
  have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
  have hik : i ≤ k := (Finset.mem_Icc.mp hi).2
  have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
  have hjk : j ≤ k := (Finset.mem_Icc.mp hj).2
  have hCi : localSecondConstant k i ≠ 0 :=
    localSecondConstant_ne_zero_of_mem_Icc hi
  have hCj : localSecondConstant k j ≠ 0 :=
    localSecondConstant_ne_zero_of_mem_Icc hj
  have hCiQ : (localSecondConstant k i : ℚ) ≠ 0 := by
    exact_mod_cast hCi
  have hCjQ : (localSecondConstant k j : ℚ) ≠ 0 := by
    exact_mod_cast hCj
  have hL0 :
      localSecondConstant k i * (t : ℤ) +
        4 * localSecondLinear k i * ((i : ℤ) - (j : ℤ)) = 0 := by
    unfold secondObstructionLeft at hL
    nlinarith
  have hR0 :
      localSecondConstant k j * (t : ℤ) -
        4 * localSecondLinear k j * ((i : ℤ) - (j : ℤ)) = 0 := by
    unfold secondObstructionRight at hR
    nlinarith
  have hLQ :
      (localSecondConstant k i : ℚ) * (t : ℚ) +
        4 * (localSecondLinear k i : ℚ) *
          (((i : ℤ) - (j : ℤ) : ℤ) : ℚ) = 0 := by
    exact_mod_cast hL0
  have hRQ :
      (localSecondConstant k j : ℚ) * (t : ℚ) -
        4 * (localSecondLinear k j : ℚ) *
          (((i : ℤ) - (j : ℤ) : ℤ) : ℚ) = 0 := by
    exact_mod_cast hR0
  rw [localSecondLinear_cast_eq_constant_mul_ownerSlope k i] at hLQ
  rw [localSecondLinear_cast_eq_constant_mul_ownerSlope k j] at hRQ
  have hLfactor :
      (localSecondConstant k i : ℚ) *
        ((t : ℚ) + 4 * ownerSlope k i *
          (((i : ℤ) - (j : ℤ) : ℤ) : ℚ)) = 0 := by
    nlinarith [hLQ]
  have hRfactor :
      (localSecondConstant k j : ℚ) *
        ((t : ℚ) - 4 * ownerSlope k j *
          (((i : ℤ) - (j : ℤ) : ℤ) : ℚ)) = 0 := by
    nlinarith [hRQ]
  have hLslope :
      (t : ℚ) + 4 * ownerSlope k i *
        (((i : ℤ) - (j : ℤ) : ℤ) : ℚ) = 0 :=
    (mul_eq_zero.mp hLfactor).resolve_left hCiQ
  have hRslope :
      (t : ℚ) - 4 * ownerSlope k j *
        (((i : ℤ) - (j : ℤ) : ℤ) : ℚ) = 0 :=
    (mul_eq_zero.mp hRfactor).resolve_left hCjQ
  have hdiff : (((i : ℤ) - (j : ℤ) : ℤ) : ℚ) ≠ 0 := by
    exact_mod_cast (show (i : ℤ) - (j : ℤ) ≠ 0 by
      apply sub_ne_zero.mpr
      exact_mod_cast (ne_of_lt hij))
  have hslope : ownerSlope k i = -ownerSlope k j := by
    apply (mul_left_cancel₀ hdiff)
    nlinarith [hLslope, hRslope]
  have hreflect : i + j = k + 1 :=
    ownerSlope_neg_eq_forces_reflection hi1 hik hj1 hjk hslope
  have hkEven : Even (k + 1) := hkOdd.add_one
  have h2dvd : 2 ∣ k + 1 := even_iff_two_dvd.mp hkEven
  have hiMid : i < (k + 1) / 2 := by
    apply (Nat.lt_div_iff_mul_lt' h2dvd i).mpr
    omega
  have hiHalf : i ≤ k - i := by omega
  have hSlopeRec : ownerSlope k i =
      reciprocalSum (Finset.Icc i (k - i)) := by
    rw [ownerSlope_eq_harmonicPrefix_sub hi1 hik,
      harmonicPrefix_sub_eq_reciprocalSum_Icc hi1 hiHalf]
  have hdiffReflect :
      (((i : ℤ) - (j : ℤ) : ℤ) : ℚ) =
        -((k + 1 - 2 * i : ℕ) : ℚ) := by
    have hjEq : j = k + 1 - i := by omega
    have hz : (i : ℤ) - (j : ℤ) =
        -((k + 1 - 2 * i : ℕ) : ℤ) := by
      omega
    exact_mod_cast hz
  have hvalue :
      (((4 * (k + 1 - 2 * i) : ℕ) : ℚ) *
        reciprocalSum (Finset.Icc i (k - i))) = ((t : ℤ) : ℚ) := by
    rw [hSlopeRec, hdiffReflect] at hLslope
    push_cast
    nlinarith
  exact reflected_harmonic_not_integer hkOdd hk5 hi1 hiMid
    ⟨(t : ℤ), hvalue⟩

/-- The two exact second obstructions cannot vanish simultaneously at two
distinct owners in any odd row `k ≥ 5`. -/
theorem no_simultaneous_second_obstruction_zero
    {k i j t : ℕ}
    (hkOdd : Odd k) (hk5 : 5 ≤ k)
    (hi : i ∈ Finset.Icc 1 k) (hj : j ∈ Finset.Icc 1 k)
    (hij : i ≠ j)
    (hL : secondObstructionLeft k i j t = 0)
    (hR : secondObstructionRight k i j t = 0) : False := by
  rcases lt_or_gt_of_ne hij with hijLt | hjiLt
  · exact no_simultaneous_second_obstruction_zero_ordered
      hkOdd hk5 hi hj hijLt hL hR
  · have hLswap : secondObstructionLeft k j i t = 0 := by
      calc
        secondObstructionLeft k j i t =
            secondObstructionRight k i j t := by
              unfold secondObstructionLeft secondObstructionRight
              ring
        _ = 0 := hR
    have hRswap : secondObstructionRight k j i t = 0 := by
      calc
        secondObstructionRight k j i t =
            secondObstructionLeft k i j t := by
              unfold secondObstructionLeft secondObstructionRight
              ring
        _ = 0 := hL
    exact no_simultaneous_second_obstruction_zero_ordered
      hkOdd hk5 hj hi hjiLt hLswap hRswap

/-- Equivalently, at least one of the two exact second obstructions is
nonzero at distinct owners in every odd row `k ≥ 5`. -/
theorem second_obstruction_pair_not_both_zero
    {k i j t : ℕ}
    (hkOdd : Odd k) (hk5 : 5 ≤ k)
    (hi : i ∈ Finset.Icc 1 k) (hj : j ∈ Finset.Icc 1 k)
    (hij : i ≠ j) :
    secondObstructionLeft k i j t ≠ 0 ∨
      secondObstructionRight k i j t ≠ 0 := by
  by_contra h
  simp only [not_or, not_not] at h
  exact no_simultaneous_second_obstruction_zero
    hkOdd hk5 hi hj hij h.1 h.2

#print axioms no_simultaneous_second_obstruction_zero
#print axioms second_obstruction_pair_not_both_zero

end Erdos686Variant
end Erdos686
