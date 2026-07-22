/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import ErdosProblems.Erdos686.Core.ThreeBucketRestriction

/-!
# Erdős 686: the three-bucket zero-obstruction LCM filter

Suppose three pairwise-coprime cleaned components are `P,Q,R` and
`d=g*P*Q*R`.  If the second obstruction at the `R` owner vanishes, the
other two second obstructions put `P` and `Q` into fixed coefficient
multiples of `g^2`.  The composed third lift at `R` has the form

`R^2 | K*g^2*d`.

After substituting the gap factorization, one copy of `R` cancels and
coprimality removes `P*Q`, giving `R | K*g^3`.  Pairwise coprimality then
packs all three cleaned components into one common multiple, rather than
paying the product of three unrelated upper bounds.  This module proves
that generic arithmetic node.  The finite six-row coefficient certificate
is reproduced independently in
`compute/campaign686/three_bucket_short_crt_lcm_verify.py`.
-/

namespace Erdos686
namespace Erdos686Variant

/-- Eliminate the shared positive scale from one nonzero-owner second
obstruction using a vanishing second obstruction at another owner.  The
result is the integral cross determinant used by the finite LCM certificate;
no rational slope is divided modulo `P`. -/
theorem second_obstruction_cross_dvd_of_other_zero
    {P C D Czero Dzero t g delta deltaZero : ℤ}
    (hP : P ∣ 3 * (C * t - 12 * D * g ^ 2 * delta))
    (hzero : 3 * (Czero * t - 12 * Dzero * g ^ 2 * deltaZero) = 0) :
    P ∣ 36 *
      (C * Dzero * deltaZero - D * delta * Czero) * g ^ 2 := by
  have hleft : P ∣
      Czero * (3 * (C * t - 12 * D * g ^ 2 * delta)) :=
    dvd_mul_of_dvd_right hP Czero
  have hright : P ∣
      C * (3 * (Czero * t - 12 * Dzero * g ^ 2 * deltaZero)) := by
    rw [hzero]
    simp
  have hdiff := dvd_sub hleft hright
  convert hdiff using 1 <;> ring

/-- Cancel one positive natural factor from a square divisibility. -/
theorem sq_dvd_self_mul_cancel
    {r x : ℕ} (hr : 0 < r) (hdiv : r ^ 2 ∣ r * x) : r ∣ x := by
  rw [pow_two] at hdiv
  exact (Nat.mul_dvd_mul_iff_left hr).mp hdiv

/-- Three pairwise-coprime natural divisors of the same integer have their
product dividing that integer. -/
theorem pairwise_coprime_three_mul_dvd
    {P Q R M : ℕ}
    (hPQ : P.Coprime Q)
    (hPR : P.Coprime R)
    (hQR : Q.Coprime R)
    (hP : P ∣ M) (hQ : Q ∣ M) (hR : R ∣ M) :
    P * Q * R ∣ M := by
  have hPQdiv : P * Q ∣ M :=
    hPQ.mul_dvd_of_dvd_of_dvd hP hQ
  have hPQRcop : (P * Q).Coprime R :=
    hPR.mul_left hQR
  exact hPQRcop.mul_dvd_of_dvd_of_dvd hPQdiv hR

/-- In a three-bucket factorization, the square third-order divisibility at
one owner removes the two opposite pairwise-coprime components after one
copy of the owner has been cancelled. -/
theorem zero_owner_third_component_dvd
    {P Q R g d K : ℕ}
    (hRpos : 0 < R)
    (hPR : P.Coprime R)
    (hQR : Q.Coprime R)
    (hd : d = g * P * Q * R)
    (hthird : R ^ 2 ∣ K * g ^ 2 * d) :
    R ∣ K * g ^ 3 := by
  have hcancelForm : R ^ 2 ∣ R * (K * g ^ 3 * P * Q) := by
    rw [hd] at hthird
    convert hthird using 1 <;> ring
  have hRrest : R ∣ K * g ^ 3 * P * Q :=
    sq_dvd_self_mul_cancel hRpos hcancelForm
  have hRcop : R.Coprime (P * Q) :=
    hPR.symm.mul_right hQR.symm
  apply hRcop.dvd_of_dvd_mul_right
  simpa [mul_assoc] using hRrest

/-- LCM packing consequence for a vanishing second obstruction.

`A` and `B` are the numerator coefficients obtained from the other two
second obstructions after substituting the zero slope.  `K` is the nonzero
third-order coefficient at the zero owner.  Any common multiple `L` of
`A,B,K` absorbs all three pairwise-coprime components, and hence the whole
gap divides `L*g^4`. -/
theorem three_bucket_zero_owner_gap_dvd_lcm_power
    {P Q R g d A B K L : ℕ}
    (hRpos : 0 < R)
    (hPQ : P.Coprime Q)
    (hPR : P.Coprime R)
    (hQR : Q.Coprime R)
    (hd : d = g * P * Q * R)
    (hP : P ∣ A * g ^ 2)
    (hQ : Q ∣ B * g ^ 2)
    (hthird : R ^ 2 ∣ K * g ^ 2 * d)
    (hA : A ∣ L) (hB : B ∣ L) (hK : K ∣ L) :
    d ∣ L * g ^ 4 := by
  have hpow : g ^ 2 ∣ g ^ 3 := pow_dvd_pow g (by omega)
  have hPcommon : P ∣ L * g ^ 3 :=
    dvd_trans hP (Nat.mul_dvd_mul hA hpow)
  have hQcommon : Q ∣ L * g ^ 3 :=
    dvd_trans hQ (Nat.mul_dvd_mul hB hpow)
  have hRbase : R ∣ K * g ^ 3 :=
    zero_owner_third_component_dvd hRpos hPR hQR hd hthird
  have hRcommon : R ∣ L * g ^ 3 :=
    dvd_trans hRbase (Nat.mul_dvd_mul hK dvd_rfl)
  have hcomponents : P * Q * R ∣ L * g ^ 3 :=
    pairwise_coprime_three_mul_dvd hPQ hPR hQR
      hPcommon hQcommon hRcommon
  have hgap : g * (P * Q * R) ∣ g * (L * g ^ 3) :=
    Nat.mul_dvd_mul_left g hcomponents
  rw [hd]
  convert hgap using 1 <;> ring

/-- Turn the LCM divisibility into a strict cutoff once uniform bounds for
the coefficient LCM and loss factor are supplied. -/
theorem three_bucket_zero_owner_gap_lt_of_lcm_bounds
    {d L g Lmax G cutoff : ℕ}
    (hLpos : 0 < L) (hgpos : 0 < g)
    (hdiv : d ∣ L * g ^ 4)
    (hL : L ≤ Lmax) (hg : g ≤ G)
    (hcut : Lmax * G ^ 4 < cutoff) :
    d < cutoff := by
  have hdle : d ≤ L * g ^ 4 :=
    Nat.le_of_dvd (Nat.mul_pos hLpos (pow_pos hgpos 4)) hdiv
  have hgpow : g ^ 4 ≤ G ^ 4 := Nat.pow_le_pow_left hg 4
  have hmajor : L * g ^ 4 ≤ Lmax * G ^ 4 :=
    Nat.mul_le_mul hL hgpow
  omega

/-- The largest finite LCM and loss budget in the six target rows still
miss the target cutoff by more than forty-six decimal digits. -/
theorem three_bucket_zero_owner_global_numeric_cutoff :
    138245988147349868236401258147840 * 18914575680 ^ 4 <
      10 ^ 120 := by
  norm_num

/-- A table-independent coarse numerator bound obtained from
`|C_s|<=87178291200`, `|D_s|<=283465647360`, and
`|delta_s|<=14^2`. -/
def threeBucketZeroSecondNumeratorBound : ℕ :=
  348736460194535895465984000

/-- A table-independent coarse third coefficient bound obtained from
`|E_s|<=392156797824` and `|delta_s|<=14^2`. -/
def threeBucketZeroThirdCoefficientBound : ℕ :=
  13835291827230720

/-- Even the product majorant for the two nonzero second numerators and the
zero owner's third coefficient remains below the target after paying the
largest loss factor to the fourth power. -/
theorem three_bucket_zero_owner_coarse_numeric_cutoff :
    threeBucketZeroSecondNumeratorBound ^ 2 *
        threeBucketZeroThirdCoefficientBound * 18914575680 ^ 4 <
      10 ^ 120 := by
  norm_num [threeBucketZeroSecondNumeratorBound,
    threeBucketZeroThirdCoefficientBound]

/-- Fully generic cutoff consequence using only the coarse coefficient
majorants.  A row-specific application supplies `A,B` from the two
nonvanishing second determinants and `K` from the zero owner's third term. -/
theorem three_bucket_zero_owner_gap_lt_cutoff_of_coarse_coefficients
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
    (hAmax : A ≤ threeBucketZeroSecondNumeratorBound)
    (hBmax : B ≤ threeBucketZeroSecondNumeratorBound)
    (hKmax : K ≤ threeBucketZeroThirdCoefficientBound)
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
  have hABmax : A * B ≤
      threeBucketZeroSecondNumeratorBound ^ 2 := by
    simpa [pow_two] using Nat.mul_le_mul hAmax hBmax
  have hLmax : L ≤
      threeBucketZeroSecondNumeratorBound ^ 2 *
        threeBucketZeroThirdCoefficientBound := by
    dsimp [L]
    exact Nat.mul_le_mul hABmax hKmax
  exact three_bucket_zero_owner_gap_lt_of_lcm_bounds
    hLpos hgpos hdiv hLmax hgmax
      three_bucket_zero_owner_coarse_numeric_cutoff

#print axioms sq_dvd_self_mul_cancel
#print axioms second_obstruction_cross_dvd_of_other_zero
#print axioms pairwise_coprime_three_mul_dvd
#print axioms zero_owner_third_component_dvd
#print axioms three_bucket_zero_owner_gap_dvd_lcm_power
#print axioms three_bucket_zero_owner_gap_lt_of_lcm_bounds
#print axioms three_bucket_zero_owner_global_numeric_cutoff
#print axioms three_bucket_zero_owner_coarse_numeric_cutoff
#print axioms three_bucket_zero_owner_gap_lt_cutoff_of_coarse_coefficients

end Erdos686Variant
end Erdos686
