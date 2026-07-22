/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import ErdosProblems.Erdos686.Core.ReflectionCompression
import ErdosProblems.Erdos686.Core.MatchingCompression

/-!
# Erdős 686: hostile-audit composition for reflection-owner correlation

This module composes the already banked reflection congruence, consecutive
block valuation concentration, and two-block matching.  It is intentionally
not imported by the shared integration surface.
-/

namespace Erdos686
namespace Erdos686Variant

/-- The prime-power exponent left in the reflection center after the parity
coefficient and one universal consecutive-block factorial loss. -/
def reflectionResidualExponent (p k n d : ℕ) : ℕ :=
  (2 * n + d + k + 1).factorization p -
    (reflectionCoeff k).factorization p -
      (k - 1).factorial.factorization p

/-- LCM of the possible nonzero owner offsets. -/
def ownerOffsetLcm (k : ℕ) : ℕ :=
  (Finset.Icc 1 (k - 1)).lcm id

/-- LCM of the positive reflected differences. -/
def reflectionDiffLcm (k d : ℕ) : ℕ :=
  (Finset.Icc 1 k).lcm (fun i => d + k + 1 - 2 * i)

lemma reflectionDiffLcm_ne_zero
    {k d : ℕ} (hd : k ≤ d) :
    reflectionDiffLcm k d ≠ 0 := by
  intro hzero
  unfold reflectionDiffLcm at hzero
  rw [Finset.lcm_eq_zero_iff] at hzero
  rcases hzero with ⟨i, hi, hterm⟩
  have hik : i ≤ k := (Finset.mem_Icc.mp hi).2
  have hpos : 0 < d + k + 1 - 2 * i := by omega
  omega

/-- For every prime, an exact equation supplies lower and upper
concentration owners on which the same residual reflection-center power
lands. -/
theorem exists_reflection_owner_correlation_four
    {p k n d : ℕ} (hp : p.Prime) (hk : 1 ≤ k) (hd : k ≤ d)
    (heq : blockProduct k (n + d) = 4 * blockProduct k n) :
    ∃ i, i ∈ Finset.Icc 1 k ∧
      ∃ j, j ∈ Finset.Icc 1 k ∧
        p ^ reflectionResidualExponent p k n d ∣ n + i ∧
        p ^ reflectionResidualExponent p k n d ∣ n + d + j ∧
        p ^ reflectionResidualExponent p k n d ∣
            d + k + 1 - 2 * i ∧
        p ^ reflectionResidualExponent p k n d ∣ d + j - i := by
  let S := 2 * n + d + k + 1
  let c := reflectionCoeff k
  let e := reflectionResidualExponent p k n d
  have hS0 : S ≠ 0 := by
    dsimp [S]
    omega
  have hc0 : c ≠ 0 := by
    dsimp [c]
    unfold reflectionCoeff
    split <;> norm_num
  have hlower0 : blockProduct k n ≠ 0 :=
    ne_of_gt (blockProduct_pos k n)
  have hupper0 : blockProduct k (n + d) ≠ 0 :=
    ne_of_gt (blockProduct_pos k (n + d))
  have hcLower0 : c * blockProduct k n ≠ 0 := mul_ne_zero hc0 hlower0
  have hSdvd : S ∣ c * blockProduct k n := by
    simpa [S, c] using reflection_congruence heq
  have hSval : S.factorization p ≤
      c.factorization p + (blockProduct k n).factorization p := by
    have h := ((Nat.factorization_le_iff_dvd hS0 hcLower0).mpr hSdvd) p
    rw [Nat.factorization_mul hc0 hlower0, Finsupp.add_apply] at h
    exact h
  obtain ⟨i, hi, hlowerConcentration⟩ :=
    exists_blockProduct_factorization_concentration hp hk (n := n)
  obtain ⟨j, hj, hupperConcentration⟩ :=
    exists_blockProduct_factorization_concentration hp hk (n := n + d)
  have hlowerDvdUpper : blockProduct k n ∣ blockProduct k (n + d) := by
    rw [heq]
    exact dvd_mul_of_dvd_right (dvd_refl (blockProduct k n)) 4
  have hlowerLeUpper :
      (blockProduct k n).factorization p ≤
        (blockProduct k (n + d)).factorization p :=
    ((Nat.factorization_le_iff_dvd hlower0 hupper0).mpr hlowerDvdUpper) p
  have heDef : e =
      S.factorization p - c.factorization p -
        (k - 1).factorial.factorization p := by
    simp [e, reflectionResidualExponent, S, c]
  have heS : e ≤ S.factorization p := by
    rw [heDef]
    omega
  have heLower : e ≤ (n + i).factorization p := by
    rw [heDef]
    omega
  have heUpper : e ≤ (n + d + j).factorization p := by
    rw [heDef]
    omega
  have hpowS : p ^ e ∣ S :=
    (hp.pow_dvd_iff_le_factorization hS0).mpr heS
  have hni0 : n + i ≠ 0 := by
    have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
    omega
  have hnuj0 : n + d + j ≠ 0 := by
    have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
    omega
  have hpowLower : p ^ e ∣ n + i :=
    (hp.pow_dvd_iff_le_factorization hni0).mpr heLower
  have hpowUpper : p ^ e ∣ n + d + j :=
    (hp.pow_dvd_iff_le_factorization hnuj0).mpr heUpper
  have hpowGcd : p ^ e ∣ Nat.gcd S (n + i) :=
    Nat.dvd_gcd hpowS hpowLower
  have hreflection : p ^ e ∣ d + k + 1 - 2 * i := by
    exact dvd_trans hpowGcd (by simpa [S] using reflection_gcd_bound k n d i)
  have hcentered : p ^ e ∣ d + j - i := by
    have hsub := Nat.dvd_sub hpowUpper hpowLower
    have hdiff : (n + d + j) - (n + i) = d + j - i := by
      have hik : i ≤ k := (Finset.mem_Icc.mp hi).2
      omega
    rwa [hdiff] at hsub
  refine ⟨i, hi, j, hj, ?_, ?_, ?_, ?_⟩
  · simpa [e] using hpowLower
  · simpa [e] using hpowUpper
  · simpa [e] using hreflection
  · simpa [e] using hcentered

/-- The two landings force the residual power into the absolute owner
offset.  A non-reflected pair therefore lands in `lcm(1,...,k-1)`. -/
theorem reflection_owner_correlation_offset_and_lcm
    {p k n d i j : ℕ} (hk : 1 ≤ k) (hd : k ≤ d)
    (hi : i ∈ Finset.Icc 1 k) (hj : j ∈ Finset.Icc 1 k)
    (hreflection : p ^ reflectionResidualExponent p k n d ∣
      d + k + 1 - 2 * i)
    (hcentered : p ^ reflectionResidualExponent p k n d ∣ d + j - i) :
    p ^ reflectionResidualExponent p k n d ∣ Nat.dist (i + j) (k + 1) ∧
      (i + j ≠ k + 1 →
        p ^ reflectionResidualExponent p k n d ∣ ownerOffsetLcm k) := by
  let q := p ^ reflectionResidualExponent p k n d
  have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
  have hik : i ≤ k := (Finset.mem_Icc.mp hi).2
  have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
  have hjk : j ≤ k := (Finset.mem_Icc.mp hj).2
  have hRpos : 0 < d + k + 1 - 2 * i := by omega
  have hCpos : 0 < d + j - i := by omega
  have hoffset : q ∣ Nat.dist (i + j) (k + 1) := by
    by_cases hsum : i + j ≤ k + 1
    · rw [Nat.dist_eq_sub_of_le hsum]
      have hsub := Nat.dvd_sub hreflection hcentered
      have heq :
          (d + k + 1 - 2 * i) - (d + j - i) =
            k + 1 - (i + j) := by omega
      rwa [heq] at hsub
    · have hrev : k + 1 ≤ i + j := by omega
      rw [Nat.dist_eq_sub_of_le_right hrev]
      have hsub := Nat.dvd_sub hcentered hreflection
      have heq :
          (d + j - i) - (d + k + 1 - 2 * i) =
            i + j - (k + 1) := by omega
      rwa [heq] at hsub
  refine ⟨by simpa [q] using hoffset, ?_⟩
  intro hnonreflected
  have hdistPos : 1 ≤ Nat.dist (i + j) (k + 1) := by
    by_cases hsum : i + j ≤ k + 1
    · rw [Nat.dist_eq_sub_of_le hsum]
      omega
    · have hrev : k + 1 ≤ i + j := by omega
      rw [Nat.dist_eq_sub_of_le_right hrev]
      omega
  have hdistLe : Nat.dist (i + j) (k + 1) ≤ k - 1 := by
    by_cases hsum : i + j ≤ k + 1
    · rw [Nat.dist_eq_sub_of_le hsum]
      omega
    · have hrev : k + 1 ≤ i + j := by omega
      rw [Nat.dist_eq_sub_of_le_right hrev]
      omega
  have hmem : Nat.dist (i + j) (k + 1) ∈ Finset.Icc 1 (k - 1) :=
    Finset.mem_Icc.mpr ⟨hdistPos, hdistLe⟩
  have hdistDvd : Nat.dist (i + j) (k + 1) ∣ ownerOffsetLcm k := by
    unfold ownerOffsetLcm
    exact Finset.dvd_lcm hmem
  exact dvd_trans hoffset hdistDvd

/-- Fully composed proper restriction.  It does not assert that the owner
pair is non-reflected. -/
theorem exists_reflection_owner_offset_restriction_four
    {p k n d : ℕ} (hp : p.Prime) (hk : 1 ≤ k) (hd : k ≤ d)
    (heq : blockProduct k (n + d) = 4 * blockProduct k n) :
    ∃ i, i ∈ Finset.Icc 1 k ∧
      ∃ j, j ∈ Finset.Icc 1 k ∧
        p ^ reflectionResidualExponent p k n d ∣
          Nat.dist (i + j) (k + 1) ∧
        (i + j ≠ k + 1 →
          p ^ reflectionResidualExponent p k n d ∣ ownerOffsetLcm k) := by
  obtain ⟨i, hi, j, hj, _hpowLower, _hpowUpper, hreflection, hcentered⟩ :=
    exists_reflection_owner_correlation_four hp hk hd heq
  have hcorr := reflection_owner_correlation_offset_and_lcm hk hd hi hj
    hreflection hcentered
  exact ⟨i, hi, j, hj, hcorr.1, hcorr.2⟩

/-- Aggregate one-factorial reflection-lcm compression.  The factorial-lcm
and full-product right sides are not uniformly ordered as raw integers; this
is a distinct necessary consequence of the equation. -/
theorem reflection_lcm_compression_four
    {k n d : ℕ} (hk : 1 ≤ k) (hd : k ≤ d)
    (heq : blockProduct k (n + d) = 4 * blockProduct k n) :
    2 * n + d + k + 1 ∣
      reflectionCoeff k * (k - 1).factorial * reflectionDiffLcm k d := by
  let S := 2 * n + d + k + 1
  let c := reflectionCoeff k
  let F := (k - 1).factorial
  let L := reflectionDiffLcm k d
  have hS0 : S ≠ 0 := by
    dsimp [S]
    omega
  have hc0 : c ≠ 0 := by
    dsimp [c]
    unfold reflectionCoeff
    split <;> norm_num
  have hF0 : F ≠ 0 := Nat.factorial_ne_zero _
  have hL0 : L ≠ 0 := by
    simpa [L] using reflectionDiffLcm_ne_zero hd
  have hrhs0 : c * F * L ≠ 0 :=
    mul_ne_zero (mul_ne_zero hc0 hF0) hL0
  apply (Nat.factorization_le_iff_dvd hS0 hrhs0).mp
  intro p
  by_cases hp : p.Prime
  · obtain ⟨i, hi, j, hj, _hpowLower, _hpowUpper, hreflection,
        _hcentered⟩ :=
      exists_reflection_owner_correlation_four hp hk hd heq
    have htermDvd : d + k + 1 - 2 * i ∣ L := by
      dsimp [L, reflectionDiffLcm]
      exact Finset.dvd_lcm hi
    have hpowL : p ^ reflectionResidualExponent p k n d ∣ L :=
      dvd_trans hreflection htermDvd
    have heL : reflectionResidualExponent p k n d ≤ L.factorization p :=
      (hp.pow_dvd_iff_le_factorization hL0).mp hpowL
    have hvaluation :
        S.factorization p ≤
          c.factorization p + F.factorization p + L.factorization p := by
      dsimp [reflectionResidualExponent, S, c, F, L] at heL ⊢
      omega
    calc
      S.factorization p ≤
          c.factorization p + F.factorization p + L.factorization p :=
        hvaluation
      _ = (c * F * L).factorization p := by
        rw [Nat.factorization_mul (mul_ne_zero hc0 hF0) hL0,
          Nat.factorization_mul hc0 hF0]
        simp [add_assoc]
  · simp [Nat.factorization_eq_zero_of_not_prime _ hp]

#print axioms exists_reflection_owner_correlation_four
#print axioms reflection_owner_correlation_offset_and_lcm
#print axioms exists_reflection_owner_offset_restriction_four
#print axioms reflection_lcm_compression_four
#print axioms reflection_congruence
#print axioms reflection_gcd_bound
#print axioms exists_blockProduct_factorization_concentration
#print axioms reflection_compression
#print axioms blockProduct_dvd_factorial_mul_centeredDiffLcm_four

end Erdos686Variant
end Erdos686
