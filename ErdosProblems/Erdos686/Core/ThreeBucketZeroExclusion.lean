/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import ErdosProblems.Erdos686.Core.ThreeBucketShortCrtLcm
import ErdosProblems.Erdos686.Core.GlobalResidualTwoPrime

/-!
# Erdős 686: target-row exclusion of a zero three-bucket obstruction

This module closes the formal interface left open by the generic
three-bucket LCM packing theorem.  It derives coarse, kernel-checked bounds
for the two cross determinants and the third-order repair coefficient in all
six target rows.  The deliberately rounded ceilings `10^30` and `10^18`
still leave the resulting gap bound strictly below `10^120`.

The final theorem is only a zero-obstruction exclusion.  It does not close
the nonzero short-CRT branch or the odd Thue tail.
-/

namespace Erdos686
namespace Erdos686Variant

/-- Signed product of the two offsets from an owner to the other buckets. -/
def threeBucketOwnerDelta (owner left right : ℕ) : ℤ :=
  ((owner : ℤ) - (left : ℤ)) * ((owner : ℤ) - (right : ℤ))

/-- Integer cross determinant obtained by eliminating a vanishing second
obstruction at `zeroOwner` from the obstruction at `owner`. -/
def threeBucketZeroCrossNumerator
    (k owner zeroOwner other : ℕ) : ℤ :=
  36 *
    (localSecondConstant k owner * localSecondLinear k zeroOwner *
        threeBucketOwnerDelta zeroOwner owner other -
      localSecondLinear k owner *
        threeBucketOwnerDelta owner zeroOwner other *
        localSecondConstant k zeroOwner)

/-- Third-order coefficient at the owner whose second obstruction vanishes. -/
noncomputable def threeBucketZeroThirdCoefficient
    (k zeroOwner left right : ℕ) : ℤ :=
  180 * localThirdQuadratic k zeroOwner *
    threeBucketOwnerDelta zeroOwner left right

/-- Computable table form of the cross determinant. -/
def threeBucketZeroCrossNumeratorTable
    (k owner zeroOwner other : ℕ) : ℤ :=
  36 *
    ((secondCoefficientTable k owner).1 *
        (secondCoefficientTable k zeroOwner).2 *
        threeBucketOwnerDelta zeroOwner owner other -
      (secondCoefficientTable k owner).2 *
        threeBucketOwnerDelta owner zeroOwner other *
        (secondCoefficientTable k zeroOwner).1)

/-- Computable table form of the zero owner's third coefficient. -/
def threeBucketZeroThirdCoefficientTable
    (k zeroOwner left right : ℕ) : ℤ :=
  180 * thirdCoefficientTable k zeroOwner *
    threeBucketOwnerDelta zeroOwner left right

/-- Finite Boolean certificate over the explicit list `0,...,k`. -/
def threeBucketZeroRowCertificateBool (k : ℕ) : Bool :=
  (List.range (k + 1)).all fun owner =>
    (List.range (k + 1)).all fun zeroOwner =>
      (List.range (k + 1)).all fun other =>
        decide (
          1 ≤ owner → 1 ≤ zeroOwner → 1 ≤ other →
          owner ≠ zeroOwner → owner ≠ other → zeroOwner ≠ other →
          0 < Int.natAbs (threeBucketZeroCrossNumeratorTable k
              owner zeroOwner other) ∧
            Int.natAbs (threeBucketZeroCrossNumeratorTable k
                owner zeroOwner other) < 10 ^ 30 ∧
            0 < Int.natAbs (threeBucketZeroThirdCoefficientTable k
                zeroOwner owner other) ∧
            Int.natAbs (threeBucketZeroThirdCoefficientTable k
                zeroOwner owner other) < 10 ^ 18)

/-- One compact ordinary-kernel certificate covers all 6,210 ordered target
triples.  This uses `decide`, not native evaluation. -/
theorem target_three_bucket_zero_table_certificate :
    threeBucketZeroRowCertificateBool 5 = true ∧
      threeBucketZeroRowCertificateBool 7 = true ∧
      threeBucketZeroRowCertificateBool 9 = true ∧
      threeBucketZeroRowCertificateBool 11 = true ∧
      threeBucketZeroRowCertificateBool 13 = true ∧
      threeBucketZeroRowCertificateBool 15 = true := by
  decide

private theorem target_three_bucket_zero_coefficient_certificate_of_row
    {k owner zeroOwner other : ℕ}
    (hk : k = 5 ∨ k = 7 ∨ k = 9 ∨ k = 11 ∨ k = 13 ∨ k = 15)
    (hcert : threeBucketZeroRowCertificateBool k = true)
    (howner : owner ∈ Finset.Icc 1 k)
    (hzeroOwner : zeroOwner ∈ Finset.Icc 1 k)
    (hother : other ∈ Finset.Icc 1 k)
    (hoz : owner ≠ zeroOwner)
    (hoo : owner ≠ other)
    (hzo : zeroOwner ≠ other) :
    0 < Int.natAbs
        (threeBucketZeroCrossNumerator k owner zeroOwner other) ∧
      Int.natAbs
          (threeBucketZeroCrossNumerator k owner zeroOwner other) < 10 ^ 30 ∧
      0 < Int.natAbs
          (threeBucketZeroThirdCoefficient k zeroOwner owner other) ∧
      Int.natAbs
          (threeBucketZeroThirdCoefficient k zeroOwner owner other) < 10 ^ 18 := by
  have hownerBounds := Finset.mem_Icc.mp howner
  have hzeroBounds := Finset.mem_Icc.mp hzeroOwner
  have hotherBounds := Finset.mem_Icc.mp hother
  simp only [threeBucketZeroRowCertificateBool, List.all_eq_true,
    List.mem_range, decide_eq_true_eq] at hcert
  have hfin := hcert owner (by omega) zeroOwner (by omega) other (by omega)
    hownerBounds.1 hzeroBounds.1 hotherBounds.1 hoz hoo hzo
  simpa [threeBucketZeroCrossNumerator,
    threeBucketZeroThirdCoefficient, threeBucketZeroCrossNumeratorTable,
    threeBucketZeroThirdCoefficientTable,
    localSecondConstant_eq_table hk howner,
    localSecondLinear_eq_table hk howner,
    localSecondConstant_eq_table hk hzeroOwner,
    localSecondLinear_eq_table hk hzeroOwner,
    localThirdQuadratic_eq_table hk hzeroOwner] using hfin

/-- Finite target-row certificate.  Distinct slopes make the cross
determinant nonzero, and the quadratic Taylor coefficient is nonzero in all
six rows.  The magnitude ceilings are intentionally coarse. -/
theorem target_three_bucket_zero_coefficient_certificate
    {k owner zeroOwner other : ℕ}
    (hk : k = 5 ∨ k = 7 ∨ k = 9 ∨ k = 11 ∨ k = 13 ∨ k = 15)
    (howner : owner ∈ Finset.Icc 1 k)
    (hzeroOwner : zeroOwner ∈ Finset.Icc 1 k)
    (hother : other ∈ Finset.Icc 1 k)
    (hoz : owner ≠ zeroOwner)
    (hoo : owner ≠ other)
    (hzo : zeroOwner ≠ other) :
    0 < Int.natAbs
        (threeBucketZeroCrossNumerator k owner zeroOwner other) ∧
      Int.natAbs
          (threeBucketZeroCrossNumerator k owner zeroOwner other) < 10 ^ 30 ∧
      0 < Int.natAbs
          (threeBucketZeroThirdCoefficient k zeroOwner owner other) ∧
      Int.natAbs
          (threeBucketZeroThirdCoefficient k zeroOwner owner other) < 10 ^ 18 := by
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl
  · exact target_three_bucket_zero_coefficient_certificate_of_row
      (by omega) target_three_bucket_zero_table_certificate.1
      howner hzeroOwner hother hoz hoo hzo
  · exact target_three_bucket_zero_coefficient_certificate_of_row
      (by omega) target_three_bucket_zero_table_certificate.2.1
      howner hzeroOwner hother hoz hoo hzo
  · exact target_three_bucket_zero_coefficient_certificate_of_row
      (by omega) target_three_bucket_zero_table_certificate.2.2.1
      howner hzeroOwner hother hoz hoo hzo
  · exact target_three_bucket_zero_coefficient_certificate_of_row
      (by omega) target_three_bucket_zero_table_certificate.2.2.2.1
      howner hzeroOwner hother hoz hoo hzo
  · exact target_three_bucket_zero_coefficient_certificate_of_row
      (by omega) target_three_bucket_zero_table_certificate.2.2.2.2.1
      howner hzeroOwner hother hoz hoo hzo
  · exact target_three_bucket_zero_coefficient_certificate_of_row
      (by omega) target_three_bucket_zero_table_certificate.2.2.2.2.2
      howner hzeroOwner hother hoz hoo hzo

/-- The rounded coefficient ceilings, even with the largest target-row loss,
remain strictly below the odd-tail cutoff. -/
theorem three_bucket_zero_target_numeric_cutoff :
    (10 ^ 30) ^ 2 * 10 ^ 18 * 18914575680 ^ 4 < 10 ^ 120 := by
  norm_num

/-- Generic cutoff specialized to the rounded target-row coefficient
ceilings. -/
theorem three_bucket_zero_gap_lt_cutoff_of_target_coefficients
    {P Q R g d A B K : ℕ}
    (hRpos : 0 < R)
    (hPQ : P.Coprime Q)
    (hPR : P.Coprime R)
    (hQR : Q.Coprime R)
    (hd : d = g * P * Q * R)
    (hP : P ∣ A * g ^ 2)
    (hQ : Q ∣ B * g ^ 2)
    (hthird : R ^ 2 ∣ K * g ^ 2 * d)
    (hApos : 0 < A) (hBpos : 0 < B) (hKpos : 0 < K)
    (hAmax : A < 10 ^ 30)
    (hBmax : B < 10 ^ 30)
    (hKmax : K < 10 ^ 18)
    (hgpos : 0 < g) (hgmax : g ≤ 18914575680) :
    d < 10 ^ 120 := by
  let L : ℕ := A * B * K
  have hAdiv : A ∣ L := by
    exact ⟨B * K, by simp [L, mul_assoc]⟩
  have hBdiv : B ∣ L := by
    refine ⟨A * K, ?_⟩
    dsimp [L]
    ring
  have hKdiv : K ∣ L := by
    refine ⟨A * B, ?_⟩
    dsimp [L]
    ring
  have hLpos : 0 < L := by
    dsimp [L]
    positivity
  have hdiv : d ∣ L * g ^ 4 :=
    three_bucket_zero_owner_gap_dvd_lcm_power
      hRpos hPQ hPR hQR hd hP hQ hthird hAdiv hBdiv hKdiv
  have hABmax : A * B ≤ (10 ^ 30) ^ 2 := by
    have hAle : A ≤ 10 ^ 30 := Nat.le_of_lt hAmax
    have hBle : B ≤ 10 ^ 30 := Nat.le_of_lt hBmax
    simpa [pow_two] using Nat.mul_le_mul hAle hBle
  have hLmax : L ≤ (10 ^ 30) ^ 2 * 10 ^ 18 := by
    dsimp [L]
    exact Nat.mul_le_mul hABmax (Nat.le_of_lt hKmax)
  exact three_bucket_zero_owner_gap_lt_of_lcm_bounds
    hLpos hgpos hdiv hLmax hgmax three_bucket_zero_target_numeric_cutoff

/-- Row-specialized composed second obstruction at one cleaned owner. -/
def targetThreeBucketSecondObstruction
    (k owner left right a b c g : ℕ) : ℤ :=
  3 * (localSecondConstant k owner * (a : ℤ) * (b : ℤ) * (c : ℤ) -
    12 * localSecondLinear k owner * (g : ℤ) ^ 2 *
      threeBucketOwnerDelta owner left right)

/-- Row-specialized composed third obstruction at one cleaned owner. -/
noncomputable def targetThreeBucketThirdObstruction
    (k owner left right a b c g d : ℕ) : ℤ :=
  -3 * targetThreeBucketSecondObstruction k owner left right a b c g +
    180 * localThirdQuadratic k owner * (g : ℤ) ^ 2 *
      threeBucketOwnerDelta owner left right * (d : ℤ)

lemma targetThreeBucketSecondObstruction_swap
    (k owner left right a b c g : ℕ) :
    targetThreeBucketSecondObstruction k owner left right a b c g =
      targetThreeBucketSecondObstruction k owner right left a b c g := by
  unfold targetThreeBucketSecondObstruction threeBucketOwnerDelta
  ring

lemma targetThreeBucketThirdObstruction_swap
    (k owner left right a b c g d : ℕ) :
    targetThreeBucketThirdObstruction k owner left right a b c g d =
      targetThreeBucketThirdObstruction k owner right left a b c g d := by
  unfold targetThreeBucketThirdObstruction targetThreeBucketSecondObstruction
    threeBucketOwnerDelta
  ring

/-- In a target row, a designated zero second obstruction forces the gap
below `10^120`.  The two other components are `P,Q`; the component at the
zero owner is `R`. -/
theorem target_three_bucket_designated_zero_gap_lt
    {k i j l P Q R g d a b c : ℕ}
    (hk : k = 5 ∨ k = 7 ∨ k = 9 ∨ k = 11 ∨ k = 13 ∨ k = 15)
    (hi : i ∈ Finset.Icc 1 k)
    (hj : j ∈ Finset.Icc 1 k)
    (hl : l ∈ Finset.Icc 1 k)
    (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l)
    (hRpos : 0 < R)
    (hPQ : P.Coprime Q)
    (hPR : P.Coprime R)
    (hQR : Q.Coprime R)
    (hd : d = g * P * Q * R)
    (hgpos : 0 < g) (hgmax : g ≤ 18914575680)
    (hP : (P : ℤ) ∣
      targetThreeBucketSecondObstruction k i l j a b c g)
    (hQ : (Q : ℤ) ∣
      targetThreeBucketSecondObstruction k j l i a b c g)
    (hRthird : (R : ℤ) ^ 2 ∣
      targetThreeBucketThirdObstruction k l i j a b c g d)
    (hzero : targetThreeBucketSecondObstruction k l i j a b c g = 0) :
    d < 10 ^ 120 := by
  let AI : ℤ := threeBucketZeroCrossNumerator k i l j
  let BI : ℤ := threeBucketZeroCrossNumerator k j l i
  let KI : ℤ := threeBucketZeroThirdCoefficient k l i j
  let A : ℕ := Int.natAbs AI
  let B : ℕ := Int.natAbs BI
  let K : ℕ := Int.natAbs KI
  have hAcert := target_three_bucket_zero_coefficient_certificate
    hk hi hl hj hil hij hjl.symm
  have hBcert := target_three_bucket_zero_coefficient_certificate
    hk hj hl hi hjl hij.symm hil.symm
  have hPbase : (P : ℤ) ∣
      3 * (localSecondConstant k i *
          ((a : ℤ) * (b : ℤ) * (c : ℤ)) -
        12 * localSecondLinear k i * (g : ℤ) ^ 2 *
          threeBucketOwnerDelta i l j) := by
    convert hP using 1 <;>
      simp [targetThreeBucketSecondObstruction] <;> ring
  have hzeroBase :
      3 * (localSecondConstant k l *
          ((a : ℤ) * (b : ℤ) * (c : ℤ)) -
        12 * localSecondLinear k l * (g : ℤ) ^ 2 *
          threeBucketOwnerDelta l i j) = 0 := by
    convert hzero using 1 <;>
      simp [targetThreeBucketSecondObstruction] <;> ring
  have hQbase : (Q : ℤ) ∣
      3 * (localSecondConstant k j *
          ((a : ℤ) * (b : ℤ) * (c : ℤ)) -
        12 * localSecondLinear k j * (g : ℤ) ^ 2 *
          threeBucketOwnerDelta j l i) := by
    convert hQ using 1 <;>
      simp [targetThreeBucketSecondObstruction] <;> ring
  have hzeroBase' :
      3 * (localSecondConstant k l *
          ((a : ℤ) * (b : ℤ) * (c : ℤ)) -
        12 * localSecondLinear k l * (g : ℤ) ^ 2 *
          threeBucketOwnerDelta l j i) = 0 := by
    have hdelta : threeBucketOwnerDelta l j i =
        threeBucketOwnerDelta l i j := by
      unfold threeBucketOwnerDelta
      ring
    rw [hdelta]
    exact hzeroBase
  have hPcross : (P : ℤ) ∣ AI * (g : ℤ) ^ 2 := by
    have h := second_obstruction_cross_dvd_of_other_zero
      (P := (P : ℤ))
      (C := localSecondConstant k i)
      (D := localSecondLinear k i)
      (Czero := localSecondConstant k l)
      (Dzero := localSecondLinear k l)
      (t := (a : ℤ) * (b : ℤ) * (c : ℤ))
      (g := (g : ℤ))
      (delta := threeBucketOwnerDelta i l j)
      (deltaZero := threeBucketOwnerDelta l i j)
      hPbase hzeroBase
    simpa [AI, threeBucketZeroCrossNumerator] using h
  have hQcross : (Q : ℤ) ∣ BI * (g : ℤ) ^ 2 := by
    have h := second_obstruction_cross_dvd_of_other_zero
      (P := (Q : ℤ))
      (C := localSecondConstant k j)
      (D := localSecondLinear k j)
      (Czero := localSecondConstant k l)
      (Dzero := localSecondLinear k l)
      (t := (a : ℤ) * (b : ℤ) * (c : ℤ))
      (g := (g : ℤ))
      (delta := threeBucketOwnerDelta j l i)
      (deltaZero := threeBucketOwnerDelta l j i)
      hQbase hzeroBase'
    simpa [BI, threeBucketZeroCrossNumerator] using h
  have hPnat : P ∣ A * g ^ 2 := by
    have h := Int.natAbs_dvd_natAbs.mpr hPcross
    simpa [A, AI, Int.natAbs_mul, Int.natAbs_pow] using h
  have hQnat : Q ∣ B * g ^ 2 := by
    have h := Int.natAbs_dvd_natAbs.mpr hQcross
    simpa [B, BI, Int.natAbs_mul, Int.natAbs_pow] using h
  have hRthird' : (R : ℤ) ^ 2 ∣ KI * (g : ℤ) ^ 2 * (d : ℤ) := by
    have heqThird :
        targetThreeBucketThirdObstruction k l i j a b c g d =
          KI * (g : ℤ) ^ 2 * (d : ℤ) := by
      unfold targetThreeBucketThirdObstruction
      rw [hzero]
      dsimp [KI, threeBucketZeroThirdCoefficient]
      ring
    rwa [heqThird] at hRthird
  have hRnat : R ^ 2 ∣ K * g ^ 2 * d := by
    have h := Int.natAbs_dvd_natAbs.mpr hRthird'
    simpa [K, KI, Int.natAbs_mul, Int.natAbs_pow] using h
  exact three_bucket_zero_gap_lt_cutoff_of_target_coefficients
    hRpos hPQ hPR hQR hd hPnat hQnat hRnat
    hAcert.1 hBcert.1 hAcert.2.2.1
    hAcert.2.1 hBcert.2.1 hAcert.2.2.2 hgpos hgmax

/-- Above the certified cutoff, none of the three composed second
obstructions can vanish.  This is the row-quantified kernel wrapper missing
from the generic LCM checkpoint. -/
theorem target_three_bucket_all_second_obstructions_nonzero
    {k i j l P Q R g d a b c : ℕ}
    (hk : k = 5 ∨ k = 7 ∨ k = 9 ∨ k = 11 ∨ k = 13 ∨ k = 15)
    (hi : i ∈ Finset.Icc 1 k)
    (hj : j ∈ Finset.Icc 1 k)
    (hl : l ∈ Finset.Icc 1 k)
    (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l)
    (hPpos : 0 < P) (hQpos : 0 < Q) (hRpos : 0 < R)
    (hPQ : P.Coprime Q)
    (hPR : P.Coprime R)
    (hQR : Q.Coprime R)
    (hd : d = g * P * Q * R)
    (hdlarge : 10 ^ 120 ≤ d)
    (hgpos : 0 < g) (hgmax : g ≤ 18914575680)
    (hPi : (P : ℤ) ∣
      targetThreeBucketSecondObstruction k i j l a b c g)
    (hQj : (Q : ℤ) ∣
      targetThreeBucketSecondObstruction k j i l a b c g)
    (hRl : (R : ℤ) ∣
      targetThreeBucketSecondObstruction k l i j a b c g)
    (hPiThird : (P : ℤ) ^ 2 ∣
      targetThreeBucketThirdObstruction k i j l a b c g d)
    (hQjThird : (Q : ℤ) ^ 2 ∣
      targetThreeBucketThirdObstruction k j i l a b c g d)
    (hRlThird : (R : ℤ) ^ 2 ∣
      targetThreeBucketThirdObstruction k l i j a b c g d) :
    targetThreeBucketSecondObstruction k i j l a b c g ≠ 0 ∧
      targetThreeBucketSecondObstruction k j i l a b c g ≠ 0 ∧
      targetThreeBucketSecondObstruction k l i j a b c g ≠ 0 := by
  have hPiSwap : (P : ℤ) ∣
      targetThreeBucketSecondObstruction k i l j a b c g := by
    rw [targetThreeBucketSecondObstruction_swap]
    exact hPi
  have hQjSwap : (Q : ℤ) ∣
      targetThreeBucketSecondObstruction k j l i a b c g := by
    rw [targetThreeBucketSecondObstruction_swap]
    exact hQj
  have hRlSwap : (R : ℤ) ∣
      targetThreeBucketSecondObstruction k l j i a b c g := by
    rw [targetThreeBucketSecondObstruction_swap]
    exact hRl
  have hdQRP : d = g * Q * R * P := by rw [hd]; ring
  have hdPRQ : d = g * P * R * Q := by rw [hd]; ring
  constructor
  · intro hzeroI
    have hlt := target_three_bucket_designated_zero_gap_lt
      (k := k) (i := j) (j := l) (l := i)
      (P := Q) (Q := R) (R := P)
      (g := g) (d := d) (a := a) (b := b) (c := c)
      hk hj hl hi hjl hij.symm hil.symm hPpos
      hQR hPQ.symm hPR.symm hdQRP hgpos hgmax
      hQj hRl hPiThird hzeroI
    omega
  constructor
  · intro hzeroJ
    have hlt := target_three_bucket_designated_zero_gap_lt
      (k := k) (i := i) (j := l) (l := j)
      (P := P) (Q := R) (R := Q)
      (g := g) (d := d) (a := a) (b := b) (c := c)
      hk hi hl hj hil hij hjl.symm hQpos
      hPR hPQ hQR.symm hdPRQ hgpos hgmax
      hPi hRlSwap hQjThird hzeroJ
    omega
  · intro hzeroL
    have hlt := target_three_bucket_designated_zero_gap_lt
      (k := k) (i := i) (j := j) (l := l)
      (P := P) (Q := Q) (R := R)
      (g := g) (d := d) (a := a) (b := b) (c := c)
      hk hi hj hl hij hil hjl hRpos hPQ hPR hQR hd hgpos hgmax
      hPiSwap hQjSwap hRlThird hzeroL
    omega

#print axioms target_three_bucket_zero_coefficient_certificate
#print axioms three_bucket_zero_target_numeric_cutoff
#print axioms three_bucket_zero_gap_lt_cutoff_of_target_coefficients
#print axioms target_three_bucket_designated_zero_gap_lt
#print axioms target_three_bucket_all_second_obstructions_nonzero

end Erdos686Variant
end Erdos686
