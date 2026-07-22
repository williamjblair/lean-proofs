/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import ErdosProblems.Erdos686.Core.ShortWindowQuotient

/-!
# Erdős 686: one-sided consequences of the third-quotient lattice

This module contains only generic arithmetic bridges.  The finite exact scan
of the target rows determines when the signed lattice terms are one-sided.
When two nonzero weighted terms have magnitude at most `H * g^2`, their two
component squares have the same bound.  The short upper window then bounds
the third component and gives

`d < A * H^2 * g^6`.

In the reflected one-sided cells the two nonzero primitive weights have
absolute value one and the correction identity itself supplies `H = Gamma`.
The row-by-row coefficient scan is external exact arithmetic; it is not
asserted as a kernel theorem here.
-/

namespace Erdos686
namespace Erdos686Variant

/-- Removing a positive integer weight and a positive integer quotient can
only decrease a nonnegative weighted square term. -/
theorem square_le_of_nonzero_weighted_term
    {P W z H g : ℕ}
    (hW : 0 < W) (hz : 0 < z)
    (hterm : P ^ 2 * W * z ≤ H * g ^ 2) :
    P ^ 2 ≤ H * g ^ 2 := by
  have hWz : 1 ≤ W * z := Nat.one_le_iff_ne_zero.mpr (mul_ne_zero hW.ne' hz.ne')
  calc
    P ^ 2 = P ^ 2 * 1 := by ring
    _ ≤ P ^ 2 * (W * z) := Nat.mul_le_mul_left (P ^ 2) hWz
    _ = P ^ 2 * W * z := by ring
    _ ≤ H * g ^ 2 := hterm

/-- Two component-square bounds plus one short upper-window inequality bound
the entire gap.  This is the quantitative bridge used after a one-sided or
cancellation-budget estimate for two lattice terms. -/
theorem two_component_short_window_gap_bound
    {P Q R g d A H : ℕ}
    (hPpos : 0 < P) (hQpos : 0 < Q) (hRpos : 0 < R)
    (hg : 0 < g)
    (hd : d = g * P * Q * R)
    (hupper : Q ^ 2 < A * d)
    (hP : P ^ 2 ≤ H * g ^ 2)
    (hR : R ^ 2 ≤ H * g ^ 2) :
    d < A * H ^ 2 * g ^ 6 := by
  have hQmul : Q * Q < Q * (A * g * P * R) := by
    rw [hd] at hupper
    convert hupper using 1 <;> ring
  have hQ : Q < A * g * P * R :=
    (Nat.mul_lt_mul_left hQpos).mp hQmul
  have hfactor : 0 < g * P * R := by positivity
  have hPR : P ^ 2 * R ^ 2 ≤ (H * g ^ 2) * (H * g ^ 2) :=
    Nat.mul_le_mul hP hR
  calc
    d = g * P * Q * R := hd
    _ = (g * P * R) * Q := by ring
    _ < (g * P * R) * (A * g * P * R) :=
      Nat.mul_lt_mul_of_pos_left hQ hfactor
    _ = A * g ^ 2 * (P ^ 2 * R ^ 2) := by ring
    _ ≤ A * g ^ 2 * ((H * g ^ 2) * (H * g ^ 2)) :=
      Nat.mul_le_mul_left (A * g ^ 2) hPR
    _ = A * H ^ 2 * g ^ 6 := by ring

/-- Numeric cutoff interface for `two_component_short_window_gap_bound`. -/
theorem two_component_short_window_gap_lt_cutoff
    {P Q R g d A H G cutoff : ℕ}
    (hPpos : 0 < P) (hQpos : 0 < Q) (hRpos : 0 < R)
    (hg : 0 < g)
    (hd : d = g * P * Q * R)
    (hupper : Q ^ 2 < A * d)
    (hP : P ^ 2 ≤ H * g ^ 2)
    (hR : R ^ 2 ≤ H * g ^ 2)
    (hgmax : g ≤ G)
    (hcut : A * H ^ 2 * G ^ 6 < cutoff) :
    d < cutoff := by
  have hbound := two_component_short_window_gap_bound
    hPpos hQpos hRpos hg hd hupper hP hR
  have hgpow : g ^ 6 ≤ G ^ 6 := Nat.pow_le_pow_left hgmax 6
  have hmajor : A * H ^ 2 * g ^ 6 ≤ A * H ^ 2 * G ^ 6 :=
    Nat.mul_le_mul_left (A * H ^ 2) hgpow
  exact lt_trans (lt_of_lt_of_le hbound hmajor) hcut

/-- If two actual weighted quotient terms are bounded by the cancellation
budget, the short-window cutoff follows.  This is the kernel-checked
consequence needed from the remaining quantified cancellation lemma. -/
theorem two_weighted_terms_short_window_gap_lt_cutoff
    {P Q R WP WR zP zR g d A H G cutoff : ℕ}
    (hPpos : 0 < P) (hQpos : 0 < Q) (hRpos : 0 < R)
    (hWP : 0 < WP) (hWR : 0 < WR)
    (hzP : 0 < zP) (hzR : 0 < zR)
    (hg : 0 < g)
    (hd : d = g * P * Q * R)
    (hupper : Q ^ 2 < A * d)
    (htermP : P ^ 2 * WP * zP ≤ H * g ^ 2)
    (htermR : R ^ 2 * WR * zR ≤ H * g ^ 2)
    (hgmax : g ≤ G)
    (hcut : A * H ^ 2 * G ^ 6 < cutoff) :
    d < cutoff := by
  apply two_component_short_window_gap_lt_cutoff
      hPpos hQpos hRpos hg hd hupper
  · exact square_le_of_nonzero_weighted_term hWP hzP htermP
  · exact square_le_of_nonzero_weighted_term hWR hzR htermR
  · exact hgmax
  · exact hcut

/-- In a reflected one-sided cell the center weight is zero and the two
remaining primitive weights have absolute value one.  If both signed
quotients are nonzero, their positive terms sum to the correction, so both
component squares are bounded by `Gamma * g^2`. -/
theorem reflected_one_sided_short_window_gap_lt_cutoff
    {P Q R zP zR g d A Gamma G cutoff : ℕ}
    (hPpos : 0 < P) (hQpos : 0 < Q) (hRpos : 0 < R)
    (hzP : 0 < zP) (hzR : 0 < zR)
    (hg : 0 < g)
    (hd : d = g * P * Q * R)
    (hupper : Q ^ 2 < A * d)
    (hlattice : P ^ 2 * zP + R ^ 2 * zR = Gamma * g ^ 2)
    (hgmax : g ≤ G)
    (hcut : A * Gamma ^ 2 * G ^ 6 < cutoff) :
    d < cutoff := by
  have htermP : P ^ 2 * 1 * zP ≤ Gamma * g ^ 2 := by
    calc
      P ^ 2 * 1 * zP = P ^ 2 * zP := by ring
      _ ≤ P ^ 2 * zP + R ^ 2 * zR := Nat.le_add_right _ _
      _ = Gamma * g ^ 2 := hlattice
  have htermR : R ^ 2 * 1 * zR ≤ Gamma * g ^ 2 := by
    calc
      R ^ 2 * 1 * zR = R ^ 2 * zR := by ring
      _ ≤ P ^ 2 * zP + R ^ 2 * zR := Nat.le_add_left _ _
      _ = Gamma * g ^ 2 := hlattice
  exact two_weighted_terms_short_window_gap_lt_cutoff
    hPpos hQpos hRpos (by norm_num) (by norm_num) hzP hzR hg hd hupper
    htermP htermR hgmax hcut

/-- Two coprime square divisors of two possibly different integers pack into
their least common multiple. -/
theorem coprime_square_product_dvd_lcm
    {P R M N : ℕ}
    (hPR : P.Coprime R)
    (hP : P ^ 2 ∣ M) (hR : R ^ 2 ∣ N) :
    P ^ 2 * R ^ 2 ∣ Nat.lcm M N := by
  have hPto : P ^ 2 ∣ Nat.lcm M N :=
    dvd_trans hP (Nat.dvd_lcm_left M N)
  have hRto : R ^ 2 ∣ Nat.lcm M N :=
    dvd_trans hR (Nat.dvd_lcm_right M N)
  exact ((hPR.pow_left 2).pow_right 2).mul_dvd_of_dvd_of_dvd hPto hRto

/-- If two lcm inputs share the displayed factor `S*g^2`, factoring it
before applying `lcm | product` saves exactly two powers of `g` and one copy
of `S`. -/
theorem reflected_boundary_lcm_bound
    {S K₀ Gamma₀ g : ℕ}
    (hS : 0 < S) (hK₀ : 0 < K₀) (hGamma₀ : 0 < Gamma₀) (hg : 0 < g) :
    Nat.lcm ((S * K₀) * g ^ 8) ((S * Gamma₀) * g ^ 2) ≤
      S * K₀ * Gamma₀ * g ^ 8 := by
  have hproduct : 0 < (K₀ * g ^ 6) * Gamma₀ := by positivity
  have hlcmSmall : Nat.lcm (K₀ * g ^ 6) Gamma₀ ≤
      (K₀ * g ^ 6) * Gamma₀ :=
    Nat.le_of_dvd hproduct (Nat.lcm_dvd_mul _ _)
  calc
    Nat.lcm ((S * K₀) * g ^ 8) ((S * Gamma₀) * g ^ 2) =
        Nat.lcm ((S * g ^ 2) * (K₀ * g ^ 6))
          ((S * g ^ 2) * Gamma₀) := by congr 1 <;> ring
    _ = (S * g ^ 2) * Nat.lcm (K₀ * g ^ 6) Gamma₀ := by
      simpa only [normalize_eq] using
        (lcm_mul_left (S * g ^ 2) (K₀ * g ^ 6) Gamma₀)
    _ ≤ (S * g ^ 2) * ((K₀ * g ^ 6) * Gamma₀) :=
      Nat.mul_le_mul_left (S * g ^ 2) hlcmSmall
    _ = S * K₀ * Gamma₀ * g ^ 8 := by ring

/-- Exact generic boundary estimate.  One endpoint quotient is zero, so its
component divides `K*g^4`; the other endpoint square divides `Gamma*g^2`.
After coprime lcm packing and the short upper window this gives a tenth-power
loss bound. -/
theorem reflected_one_zero_short_window_gap_bound
    {P Q R K Gamma S K₀ Gamma₀ g d A : ℕ}
    (hPpos : 0 < P) (hQpos : 0 < Q) (hRpos : 0 < R)
    (hK : 0 < K) (hGamma : 0 < Gamma)
    (hS : 0 < S) (hK₀ : 0 < K₀) (hGamma₀ : 0 < Gamma₀)
    (hg : 0 < g)
    (hPR : P.Coprime R)
    (hd : d = g * P * Q * R)
    (hupper : Q ^ 2 < A * d)
    (hP : P ∣ K * g ^ 4)
    (hR : R ^ 2 ∣ Gamma * g ^ 2)
    (hKfactor : K ^ 2 = S * K₀)
    (hGammaFactor : Gamma = S * Gamma₀) :
    d < A * S * K₀ * Gamma₀ * g ^ 10 := by
  have hPtwo : P ^ 2 ∣ K ^ 2 * g ^ 8 := by
    rcases hP with ⟨m, hm⟩
    refine ⟨m ^ 2, ?_⟩
    calc
      K ^ 2 * g ^ 8 = (K * g ^ 4) ^ 2 := by ring
      _ = (P * m) ^ 2 := by rw [hm]
      _ = P ^ 2 * m ^ 2 := by ring
  have hpackDvd : P ^ 2 * R ^ 2 ∣
      Nat.lcm (K ^ 2 * g ^ 8) (Gamma * g ^ 2) :=
    coprime_square_product_dvd_lcm hPR hPtwo hR
  have hlcmPos : 0 < Nat.lcm (K ^ 2 * g ^ 8) (Gamma * g ^ 2) := by
    positivity
  have hpack : P ^ 2 * R ^ 2 ≤
      Nat.lcm (K ^ 2 * g ^ 8) (Gamma * g ^ 2) :=
    Nat.le_of_dvd hlcmPos hpackDvd
  have hlcm : Nat.lcm (K ^ 2 * g ^ 8) (Gamma * g ^ 2) ≤
      S * K₀ * Gamma₀ * g ^ 8 := by
    rw [hKfactor, hGammaFactor]
    exact reflected_boundary_lcm_bound hS hK₀ hGamma₀ hg
  have hPRsq : P ^ 2 * R ^ 2 ≤ S * K₀ * Gamma₀ * g ^ 8 :=
    le_trans hpack hlcm
  have hQmul : Q * Q < Q * (A * g * P * R) := by
    rw [hd] at hupper
    convert hupper using 1 <;> ring
  have hQ : Q < A * g * P * R :=
    (Nat.mul_lt_mul_left hQpos).mp hQmul
  have hfactor : 0 < g * P * R := by positivity
  calc
    d = g * P * Q * R := hd
    _ = (g * P * R) * Q := by ring
    _ < (g * P * R) * (A * g * P * R) :=
      Nat.mul_lt_mul_of_pos_left hQ hfactor
    _ = A * g ^ 2 * (P ^ 2 * R ^ 2) := by ring
    _ ≤ A * g ^ 2 * (S * K₀ * Gamma₀ * g ^ 8) :=
      Nat.mul_le_mul_left (A * g ^ 2) hPRsq
    _ = A * S * K₀ * Gamma₀ * g ^ 10 := by ring

/-- Numeric cutoff interface for the reflected one-zero boundary estimate. -/
theorem reflected_one_zero_short_window_gap_lt_cutoff
    {P Q R K Gamma S K₀ Gamma₀ g d A G cutoff : ℕ}
    (hPpos : 0 < P) (hQpos : 0 < Q) (hRpos : 0 < R)
    (hK : 0 < K) (hGamma : 0 < Gamma)
    (hS : 0 < S) (hK₀ : 0 < K₀) (hGamma₀ : 0 < Gamma₀)
    (hg : 0 < g)
    (hPR : P.Coprime R)
    (hd : d = g * P * Q * R)
    (hupper : Q ^ 2 < A * d)
    (hP : P ∣ K * g ^ 4)
    (hR : R ^ 2 ∣ Gamma * g ^ 2)
    (hKfactor : K ^ 2 = S * K₀)
    (hGammaFactor : Gamma = S * Gamma₀)
    (hgmax : g ≤ G)
    (hcut : A * S * K₀ * Gamma₀ * G ^ 10 < cutoff) :
    d < cutoff := by
  have hbound := reflected_one_zero_short_window_gap_bound
    hPpos hQpos hRpos hK hGamma hS hK₀ hGamma₀ hg hPR hd hupper
    hP hR hKfactor hGammaFactor
  have hgpow : g ^ 10 ≤ G ^ 10 := Nat.pow_le_pow_left hgmax 10
  have hmajor : A * S * K₀ * Gamma₀ * g ^ 10 ≤
      A * S * K₀ * Gamma₀ * G ^ 10 :=
    Nat.mul_le_mul_left (A * S * K₀ * Gamma₀) hgpow
  exact lt_trans (lt_of_lt_of_le hbound hmajor) hcut

#print axioms square_le_of_nonzero_weighted_term
#print axioms two_component_short_window_gap_bound
#print axioms two_component_short_window_gap_lt_cutoff
#print axioms two_weighted_terms_short_window_gap_lt_cutoff
#print axioms reflected_one_sided_short_window_gap_lt_cutoff
#print axioms coprime_square_product_dvd_lcm
#print axioms reflected_boundary_lcm_bound
#print axioms reflected_one_zero_short_window_gap_bound
#print axioms reflected_one_zero_short_window_gap_lt_cutoff

end Erdos686Variant
end Erdos686
