/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import ErdosProblems.Erdos686ShortWindowLatticeSign

/-!
# Hostile kernel audit of the Erdős 686 short-window lattice-sign package

Every public generic theorem in the producer module is reproved below under a
fresh name.  No proof invokes the corresponding producer theorem.  The finite
row scan remains external exact arithmetic and is therefore not promoted to a
kernel theorem here.
-/

namespace Erdos686
namespace Erdos686Variant

theorem hostile_square_le_of_nonzero_weighted_term
    {P W z H g : ℕ}
    (hW : 0 < W) (hz : 0 < z)
    (hterm : P ^ 2 * W * z ≤ H * g ^ 2) :
    P ^ 2 ≤ H * g ^ 2 := by
  have hWz : 1 ≤ W * z :=
    Nat.one_le_iff_ne_zero.mpr (mul_ne_zero hW.ne' hz.ne')
  calc
    P ^ 2 = P ^ 2 * 1 := by ring
    _ ≤ P ^ 2 * (W * z) := Nat.mul_le_mul_left (P ^ 2) hWz
    _ = P ^ 2 * W * z := by ring
    _ ≤ H * g ^ 2 := hterm

theorem hostile_two_component_short_window_gap_bound
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

theorem hostile_two_component_short_window_gap_lt_cutoff
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
  have hbound := hostile_two_component_short_window_gap_bound
    hPpos hQpos hRpos hg hd hupper hP hR
  have hgpow : g ^ 6 ≤ G ^ 6 := Nat.pow_le_pow_left hgmax 6
  have hmajor : A * H ^ 2 * g ^ 6 ≤ A * H ^ 2 * G ^ 6 :=
    Nat.mul_le_mul_left (A * H ^ 2) hgpow
  exact lt_trans (lt_of_lt_of_le hbound hmajor) hcut

theorem hostile_two_weighted_terms_short_window_gap_lt_cutoff
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
  apply hostile_two_component_short_window_gap_lt_cutoff
      hPpos hQpos hRpos hg hd hupper
  · exact hostile_square_le_of_nonzero_weighted_term hWP hzP htermP
  · exact hostile_square_le_of_nonzero_weighted_term hWR hzR htermR
  · exact hgmax
  · exact hcut

theorem hostile_reflected_one_sided_short_window_gap_lt_cutoff
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
  exact hostile_two_weighted_terms_short_window_gap_lt_cutoff
    hPpos hQpos hRpos (by norm_num) (by norm_num) hzP hzR hg hd hupper
    htermP htermR hgmax hcut

theorem hostile_coprime_square_product_dvd_lcm
    {P R M N : ℕ}
    (hPR : P.Coprime R)
    (hP : P ^ 2 ∣ M) (hR : R ^ 2 ∣ N) :
    P ^ 2 * R ^ 2 ∣ Nat.lcm M N := by
  have hPto : P ^ 2 ∣ Nat.lcm M N :=
    dvd_trans hP (Nat.dvd_lcm_left M N)
  have hRto : R ^ 2 ∣ Nat.lcm M N :=
    dvd_trans hR (Nat.dvd_lcm_right M N)
  exact ((hPR.pow_left 2).pow_right 2).mul_dvd_of_dvd_of_dvd hPto hRto

theorem hostile_reflected_boundary_lcm_bound
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

theorem hostile_reflected_one_zero_short_window_gap_bound
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
    hostile_coprime_square_product_dvd_lcm hPR hPtwo hR
  have hlcmPos : 0 < Nat.lcm (K ^ 2 * g ^ 8) (Gamma * g ^ 2) := by
    positivity
  have hpack : P ^ 2 * R ^ 2 ≤
      Nat.lcm (K ^ 2 * g ^ 8) (Gamma * g ^ 2) :=
    Nat.le_of_dvd hlcmPos hpackDvd
  have hlcm : Nat.lcm (K ^ 2 * g ^ 8) (Gamma * g ^ 2) ≤
      S * K₀ * Gamma₀ * g ^ 8 := by
    rw [hKfactor, hGammaFactor]
    exact hostile_reflected_boundary_lcm_bound hS hK₀ hGamma₀ hg
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

theorem hostile_reflected_one_zero_short_window_gap_lt_cutoff
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
  have hbound := hostile_reflected_one_zero_short_window_gap_bound
    hPpos hQpos hRpos hK hGamma hS hK₀ hGamma₀ hg hPR hd hupper
    hP hR hKfactor hGammaFactor
  have hgpow : g ^ 10 ≤ G ^ 10 := Nat.pow_le_pow_left hgmax 10
  have hmajor : A * S * K₀ * Gamma₀ * g ^ 10 ≤
      A * S * K₀ * Gamma₀ * G ^ 10 :=
    Nat.mul_le_mul_left (A * S * K₀ * Gamma₀) hgpow
  exact lt_trans (lt_of_lt_of_le hbound hmajor) hcut

/- Exact aggregate checks for the externally enumerated finite scan.  These
checks certify the arithmetic partitions, not the row enumeration itself. -/
theorem hostile_weight_component_total : 1539 + 1539 + 27 = 3 * 1035 := by
  norm_num

theorem hostile_open_cell_total : 2381 + 9 = 2390 := by
  norm_num

theorem hostile_boundary_cell_total : 1337 + 18 = 1355 := by
  norm_num

theorem hostile_boundary_partition : 18 = 8 + 10 := by
  norm_num

-- Exact cutoff checks for all nine one-sided open slivers.
example : 14 * 86400 ^ 2 * 108 ^ 6 < 10 ^ 120 := by norm_num
example : 17 * 6858432 ^ 2 * 1620 ^ 6 < 10 ^ 120 := by norm_num
example : 23 * 757444608 ^ 2 * 136080 ^ 6 < 10 ^ 120 := by norm_num
example : 26 * 114789312000 ^ 2 * 1224720 ^ 6 < 10 ^ 120 := by norm_num
example : 26 * 4587466752 ^ 2 * 1224720 ^ 6 < 10 ^ 120 := by norm_num
example : 29 * 23117159669760 ^ 2 * 242494560 ^ 6 < 10 ^ 120 := by norm_num
example : 29 * 870772032000 ^ 2 * 242494560 ^ 6 < 10 ^ 120 := by norm_num
example : 35 * 6000400823316480 ^ 2 * 18914575680 ^ 6 < 10 ^ 120 := by norm_num
example : 35 * 211129881108480 ^ 2 * 18914575680 ^ 6 < 10 ^ 120 := by norm_num

-- Exact cutoff checks for the eight closed one-zero boundaries.
example : 14 * 86400 * 37489271629676544 * 1 * 108 ^ 10 < 10 ^ 120 := by norm_num
example : 17 * 6858432 * 30377147165271015636860928 * 1 * 1620 ^ 10 < 10 ^ 120 := by norm_num
example : 23 * 995328 * 144950283561643585705211385172388216832 * 761 *
    136080 ^ 10 < 10 ^ 120 := by norm_num
example : 26 * 10948608 * 2491164671075202474309932966010553569902592 *
    419 * 1224720 ^ 10 < 10 ^ 120 := by norm_num

#print axioms hostile_square_le_of_nonzero_weighted_term
#print axioms hostile_two_component_short_window_gap_bound
#print axioms hostile_two_component_short_window_gap_lt_cutoff
#print axioms hostile_two_weighted_terms_short_window_gap_lt_cutoff
#print axioms hostile_reflected_one_sided_short_window_gap_lt_cutoff
#print axioms hostile_coprime_square_product_dvd_lcm
#print axioms hostile_reflected_boundary_lcm_bound
#print axioms hostile_reflected_one_zero_short_window_gap_bound
#print axioms hostile_reflected_one_zero_short_window_gap_lt_cutoff

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
