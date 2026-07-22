/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import ErdosProblems.Erdos686.Core.CenterComponentLogStrip
import ErdosProblems.Erdos686.Core.CenteredRatioWindowSharp

/-!
# Erdős 686: an even reflected-center component with gap-supported cofactor

For an even target row, write the reflection center as `H = a*q`, where `q`
is one complete prime-power component with prime base at least the row length.
If the complementary cofactor `a` also divides the gap, the centered-gcd
restriction puts `a` inside `(k-1)!!`.  Combining this with the reflected
square lift gives the equation-facing bound

`2*q < 5*(k-1)!!`.

This is stronger than the standalone dominant-component bound when the
cofactor is only known indirectly through its gap support.

The conditional premise `a ∣ d` is deliberately explicit: no banked owner or
factorization theorem supplies it for an arbitrary reflection center.  The
module therefore also proves an unconditional version with the exact penalty
`b = a / gcd(a,d)`.  This removes the premise but does not by itself bound `b`,
so neither form is a global large-row closure.
-/

namespace Erdos686
namespace Erdos686Variant

private lemma prime_ge_even_row_is_gt
    {p k : ℕ} (hp : p.Prime) (hk : 16 ≤ k)
    (hkeven : Even k) (hkp : k ≤ p) :
    k < p := by
  apply lt_of_le_of_ne hkp
  intro hEq
  subst p
  have hk2 : k = 2 := hp.even_iff.mp hkeven
  omega

/-- If `H = a*q` and the complementary cofactor `a` divides the gap, then
`a` divides the fixed odd double factorial.  The equation is essential: it
supplies the centered-gcd restriction. -/
theorem even_reflectionCenter_gapCofactor_dvd_oddDoubleFactorial
    {p k n d a : ℕ}
    (hk : 16 ≤ k) (hkeven : Even k)
    (hfactor : 2 * n + d + k + 1 =
      a * p ^ (2 * n + d + k + 1).factorization p)
    (haGap : a ∣ d)
    (heq : blockProduct k (n + d) = 4 * blockProduct k n) :
    a ∣ (k - 1).doubleFactorial := by
  obtain ⟨r, hr⟩ := hkeven
  have hkEq : k = 2 * r := by omega
  have hrPos : 1 ≤ r := by omega
  let q := p ^ (2 * n + d + k + 1).factorization p
  have haCenter : a ∣ 2 * n + d + k + 1 := by
    refine ⟨q, ?_⟩
    simpa [q] using hfactor
  have haGcd : a ∣ Nat.gcd d (2 * n + d + k + 1) :=
    Nat.dvd_gcd haGap haCenter
  have hgFixed : Nat.gcd d (2 * n + d + k + 1) ∣
      (k - 1).doubleFactorial := by
    have hraw := gcd_gap_reflectionCenter_dvd_oddDoubleFactorial
      (r := r) (n := n) (d := d) hrPos (by simpa [hkEq] using heq)
    simpa [hkEq] using hraw
  exact dvd_trans haGcd hgFixed

/-- Unconditional cofactor form of the centered-gcd restriction.  For any
factorization `H = a*q`, only the part `gcd(a,d)` is forced into the fixed
odd double factorial; the quotient `a / gcd(a,d)` measures the exact
cofactor support not shared with the gap. -/
theorem even_reflectionCenter_cofactorGcd_dvd_oddDoubleFactorial
    {p k n d a : ℕ}
    (hk : 16 ≤ k) (hkeven : Even k)
    (hfactor : 2 * n + d + k + 1 =
      a * p ^ (2 * n + d + k + 1).factorization p)
    (heq : blockProduct k (n + d) = 4 * blockProduct k n) :
    Nat.gcd a d ∣ (k - 1).doubleFactorial := by
  obtain ⟨r, hr⟩ := hkeven
  have hkEq : k = 2 * r := by omega
  have hrPos : 1 ≤ r := by omega
  let q := p ^ (2 * n + d + k + 1).factorization p
  have haCenter : a ∣ 2 * n + d + k + 1 := by
    refine ⟨q, ?_⟩
    simpa [q] using hfactor
  have hgCenter : Nat.gcd a d ∣ 2 * n + d + k + 1 :=
    dvd_trans (Nat.gcd_dvd_left a d) haCenter
  have hgMain : Nat.gcd a d ∣ Nat.gcd d (2 * n + d + k + 1) :=
    Nat.dvd_gcd (Nat.gcd_dvd_right a d) hgCenter
  have hmainFixed : Nat.gcd d (2 * n + d + k + 1) ∣
      (k - 1).doubleFactorial := by
    have hraw := gcd_gap_reflectionCenter_dvd_oddDoubleFactorial
      (r := r) (n := n) (d := d) hrPos (by simpa [hkEq] using heq)
    simpa [hkEq] using hraw
  exact dvd_trans hgMain hmainFixed

private lemma even_reflectionCenter_component_two_lt_five_cofactor
    {p k n d a : ℕ}
    (hp : p.Prime) (hk : 16 ≤ k) (hd : k ≤ d)
    (hkp : k ≤ p) (hpCenter : p ∣ 2 * n + d + k + 1)
    (hkeven : Even k)
    (hfactor : 2 * n + d + k + 1 =
      a * p ^ (2 * n + d + k + 1).factorization p)
    (heq : blockProduct k (n + d) = 4 * blockProduct k n) :
    2 * p ^ (2 * n + d + k + 1).factorization p < 5 * a := by
  let q := p ^ (2 * n + d + k + 1).factorization p
  have hkpStrict : k < p :=
    prime_ge_even_row_is_gt hp hk hkeven hkp
  have hsq :=
    even_large_prime_reflection_center_power_two_sq_lt_five_center
      hp hk hd hkpStrict hpCenter hkeven heq
  have hqPos : 0 < q := by
    dsimp [q]
    exact pow_pos hp.pos _
  apply (Nat.mul_lt_mul_right hqPos).mp
  rw [show (2 * q) * q = 2 * q ^ 2 by ring,
    show (5 * a) * q = 5 * (a * q) by ring]
  have hcenterEq : 2 * n + d + k + 1 = a * q := by
    simpa only [q] using hfactor
  rw [← hcenterEq]
  simpa only [q] using hsq

/-- Necessary size bound for a complete large-base center component whose
complementary center cofactor divides the gap.  The weak hypothesis `k ≤ p`
includes the apparent boundary `p = k`; for an even row `k ≥ 16`, primality
forces that boundary to be impossible, so the banked strict-base square lift
applies. -/
theorem even_reflectionCenter_gapCofactor_component_two_lt_five_doubleFactorial
    {p k n d a : ℕ}
    (hp : p.Prime) (hk : 16 ≤ k) (hd : k ≤ d)
    (hkp : k ≤ p) (hpCenter : p ∣ 2 * n + d + k + 1)
    (hkeven : Even k)
    (hfactor : 2 * n + d + k + 1 =
      a * p ^ (2 * n + d + k + 1).factorization p)
    (haGap : a ∣ d)
    (heq : blockProduct k (n + d) = 4 * blockProduct k n) :
    2 * p ^ (2 * n + d + k + 1).factorization p <
      5 * (k - 1).doubleFactorial := by
  let q := p ^ (2 * n + d + k + 1).factorization p
  have hkpStrict : k < p :=
    prime_ge_even_row_is_gt hp hk hkeven hkp
  have hsq :=
    even_large_prime_reflection_center_power_two_sq_lt_five_center
      hp hk hd hkpStrict hpCenter hkeven heq
  have hqPos : 0 < q := by
    dsimp [q]
    exact pow_pos hp.pos _
  have hcomponent : 2 * q < 5 * a := by
    apply (Nat.mul_lt_mul_right hqPos).mp
    rw [show (2 * q) * q = 2 * q ^ 2 by ring,
      show (5 * a) * q = 5 * (a * q) by ring]
    have hcenterEq : 2 * n + d + k + 1 = a * q := by
      simpa only [q] using hfactor
    rw [← hcenterEq]
    simpa only [q] using hsq
  have haFixed := even_reflectionCenter_gapCofactor_dvd_oddDoubleFactorial
    hk hkeven hfactor haGap heq
  have haLe : a ≤ (k - 1).doubleFactorial :=
    Nat.le_of_dvd (Nat.doubleFactorial_pos _) haFixed
  exact lt_of_lt_of_le hcomponent (Nat.mul_le_mul_left 5 haLe)

/-- A gap bound with no dominance premise.  If the complementary center
cofactor divides the gap, write `d = a*c`.  The target equation gives
`19*d < H = a*q`, while the reflected square lift gives `2*q < 5*a`.
Consequently `38*d < 5*a^2`, and the centered-gcd theorem replaces `a` by
the fixed row constant `(k-1)!!`. -/
theorem even_reflectionCenter_gapCofactor_thirtyEight_gap_lt_five_doubleFactorial_sq
    {p k n d a : ℕ}
    (hp : p.Prime) (hk : 16 ≤ k) (hd : k ≤ d)
    (hkp : k ≤ p) (hpCenter : p ∣ 2 * n + d + k + 1)
    (hkeven : Even k)
    (hfactor : 2 * n + d + k + 1 =
      a * p ^ (2 * n + d + k + 1).factorization p)
    (haGap : a ∣ d)
    (heq : blockProduct k (n + d) = 4 * blockProduct k n) :
    38 * d < 5 * (k - 1).doubleFactorial ^ 2 := by
  let q := p ^ (2 * n + d + k + 1).factorization p
  let O := (k - 1).doubleFactorial
  have hcenterEq : 2 * n + d + k + 1 = a * q := by
    simpa only [q] using hfactor
  have hcenterPos : 0 < 2 * n + d + k + 1 := by omega
  have haPos : 0 < a := by
    by_contra hnot
    have haZero : a = 0 := by omega
    rw [haZero, zero_mul] at hcenterEq
    omega
  have haFixed := even_reflectionCenter_gapCofactor_dvd_oddDoubleFactorial
    hk hkeven hfactor haGap heq
  obtain ⟨c, hc⟩ := haGap
  have hn9 : 9 * d < n :=
    nine_mul_gap_lt_n_of_four_solution hk hd heq
  have hcenterGt : 19 * d < 2 * n + d + k + 1 := by omega
  have hcq : 19 * c < q := by
    apply (Nat.mul_lt_mul_left haPos).mp
    calc
      a * (19 * c) = 19 * d := by rw [hc]; ring
      _ < 2 * n + d + k + 1 := hcenterGt
      _ = a * q := hcenterEq
  have hkpStrict : k < p :=
    prime_ge_even_row_is_gt hp hk hkeven hkp
  have hsq :=
    even_large_prime_reflection_center_power_two_sq_lt_five_center
      hp hk hd hkpStrict hpCenter hkeven heq
  have hqPos : 0 < q := by
    dsimp [q]
    exact pow_pos hp.pos _
  have hcomponent : 2 * q < 5 * a := by
    apply (Nat.mul_lt_mul_right hqPos).mp
    rw [show (2 * q) * q = 2 * q ^ 2 by ring,
      show (5 * a) * q = 5 * (a * q) by ring]
    rw [← hcenterEq]
    simpa only [q] using hsq
  have hcBound : 38 * c < 5 * a := by omega
  have hdBound : 38 * d < 5 * a ^ 2 := by
    have hscaled := (Nat.mul_lt_mul_left haPos).mpr hcBound
    rw [hc]
    convert hscaled using 1 <;> ring
  have haLe : a ≤ O := by
    exact Nat.le_of_dvd (by dsimp [O]; exact Nat.doubleFactorial_pos _) haFixed
  have haSqLe : a ^ 2 ≤ O ^ 2 := Nat.pow_le_pow_left haLe 2
  exact lt_of_lt_of_le hdBound (by
    simpa [O] using Nat.mul_le_mul_left 5 haSqLe)

/-- The centered-ratio checkpoint sharpens the preceding fixed-row gap
bound by a factor linear in `k`.  All constants are exact: combining
`1218443*k*d < 1853952*n`, `2*n < H = a*q`, and `2*q < 5*a` gives

`1218443*k*d < 2317440*a^2`.

The centered-gcd restriction again replaces `a` by `(k-1)!!`. -/
theorem even_reflectionCenter_gapCofactor_sharp_gap_bound
    {p k n d a : ℕ}
    (hp : p.Prime) (hk : 16 ≤ k) (hd : k ≤ d)
    (hkp : k ≤ p) (hpCenter : p ∣ 2 * n + d + k + 1)
    (hkeven : Even k)
    (hfactor : 2 * n + d + k + 1 =
      a * p ^ (2 * n + d + k + 1).factorization p)
    (haGap : a ∣ d)
    (heq : blockProduct k (n + d) = 4 * blockProduct k n) :
    1218443 * k * d <
      2317440 * (k - 1).doubleFactorial ^ 2 := by
  let q := p ^ (2 * n + d + k + 1).factorization p
  let O := (k - 1).doubleFactorial
  have hcenterEq : 2 * n + d + k + 1 = a * q := by
    simpa only [q] using hfactor
  have hcenterPos : 0 < 2 * n + d + k + 1 := by omega
  have haPos : 0 < a := by
    by_contra hnot
    have haZero : a = 0 := by omega
    rw [haZero, zero_mul] at hcenterEq
    omega
  have haFixed := even_reflectionCenter_gapCofactor_dvd_oddDoubleFactorial
    hk hkeven hfactor haGap heq
  obtain ⟨c, hc⟩ := haGap
  have hratio : 1218443 * k * d < 1853952 * n :=
    maximal_sharp_bracket_ratio_of_four_solution hk hd heq
  have hcenterBand :
      2 * 1218443 * k * d <
        1853952 * (2 * n + d + k + 1) := by
    calc
      2 * 1218443 * k * d = 2 * (1218443 * k * d) := by ring
      _ < 2 * (1853952 * n) :=
        (Nat.mul_lt_mul_left (by norm_num : 0 < 2)).mpr hratio
      _ = 1853952 * (2 * n) := by ring
      _ < 1853952 * (2 * n + d + k + 1) := by omega
  have hcCenter : 2 * 1218443 * k * c < 1853952 * q := by
    apply (Nat.mul_lt_mul_left haPos).mp
    calc
      a * (2 * 1218443 * k * c) = 2 * 1218443 * k * d := by
        rw [hc]
        ring
      _ < 1853952 * (2 * n + d + k + 1) := hcenterBand
      _ = a * (1853952 * q) := by rw [hcenterEq]; ring
  have hkpStrict : k < p :=
    prime_ge_even_row_is_gt hp hk hkeven hkp
  have hsq :=
    even_large_prime_reflection_center_power_two_sq_lt_five_center
      hp hk hd hkpStrict hpCenter hkeven heq
  have hqPos : 0 < q := by
    dsimp [q]
    exact pow_pos hp.pos _
  have hcomponent : 2 * q < 5 * a := by
    apply (Nat.mul_lt_mul_right hqPos).mp
    rw [show (2 * q) * q = 2 * q ^ 2 by ring,
      show (5 * a) * q = 5 * (a * q) by ring]
    rw [← hcenterEq]
    simpa only [q] using hsq
  have hcSharp : 4 * 1218443 * k * c < 5 * 1853952 * a := by
    calc
      4 * 1218443 * k * c = 2 * (2 * 1218443 * k * c) := by ring
      _ < 2 * (1853952 * q) :=
        (Nat.mul_lt_mul_left (by norm_num : 0 < 2)).mpr hcCenter
      _ = 1853952 * (2 * q) := by ring
      _ < 1853952 * (5 * a) :=
        (Nat.mul_lt_mul_left (by norm_num : 0 < 1853952)).mpr hcomponent
      _ = 5 * 1853952 * a := by ring
  have hdSharp : 4 * 1218443 * k * d < 5 * 1853952 * a ^ 2 := by
    have hscaled := (Nat.mul_lt_mul_left haPos).mpr hcSharp
    rw [hc]
    convert hscaled using 1 <;> ring
  have haLe : a ≤ O := by
    exact Nat.le_of_dvd (by dsimp [O]; exact Nat.doubleFactorial_pos _) haFixed
  have haSqLe : a ^ 2 ≤ O ^ 2 := Nat.pow_le_pow_left haLe 2
  have hOSharp : 4 * 1218443 * k * d < 5 * 1853952 * O ^ 2 :=
    lt_of_lt_of_le hdSharp (Nat.mul_le_mul_left (5 * 1853952) haSqLe)
  have hfour :
      4 * (1218443 * k * d) < 4 * (2317440 * O ^ 2) := by
    convert hOSharp using 1 <;> ring
  exact (Nat.mul_lt_mul_left (by norm_num : 0 < 4)).mp (by
    simpa [O] using hfour)

/-- Unconditional component balance.  If `q` is one complete large-base
center component and `a` its complementary cofactor, the part of `a` shared
with the gap is at most `(k-1)!!`.  Therefore `q` can be large only when the
gap-coprime quotient `a / gcd(a,d)` is correspondingly large. -/
theorem even_reflectionCenter_gapCoprimeQuotient_component_bound
    {p k n d a : ℕ}
    (hp : p.Prime) (hk : 16 ≤ k) (hd : k ≤ d)
    (hkp : k ≤ p) (hpCenter : p ∣ 2 * n + d + k + 1)
    (hkeven : Even k)
    (hfactor : 2 * n + d + k + 1 =
      a * p ^ (2 * n + d + k + 1).factorization p)
    (heq : blockProduct k (n + d) = 4 * blockProduct k n) :
    2 * p ^ (2 * n + d + k + 1).factorization p <
      5 * (k - 1).doubleFactorial * (a / Nat.gcd a d) := by
  let g := Nat.gcd a d
  let b := a / g
  let O := (k - 1).doubleFactorial
  have hcomponent :
      2 * p ^ (2 * n + d + k + 1).factorization p < 5 * a :=
    even_reflectionCenter_component_two_lt_five_cofactor
      hp hk hd hkp hpCenter hkeven hfactor heq
  have hgFixed : g ∣ O := by
    simpa only [g, O] using
      even_reflectionCenter_cofactorGcd_dvd_oddDoubleFactorial
        hk hkeven hfactor heq
  have hgLe : g ≤ O :=
    Nat.le_of_dvd (by dsimp [O]; exact Nat.doubleFactorial_pos _) hgFixed
  have hgb : g * b = a := by
    dsimp [g, b]
    exact Nat.mul_div_cancel' (Nat.gcd_dvd_left a d)
  have haLe : a ≤ O * b := by
    rw [← hgb]
    exact Nat.mul_le_mul_right b hgLe
  calc
    2 * p ^ (2 * n + d + k + 1).factorization p < 5 * a := hcomponent
    _ ≤ 5 * (O * b) := Nat.mul_le_mul_left 5 haLe
    _ = 5 * (k - 1).doubleFactorial * (a / Nat.gcd a d) := by
      simp only [O, b, g]
      ring

/-- Exclusion form of the unconditional component balance. -/
theorem no_four_solution_of_even_reflectionCenter_gapCoprimeQuotient_dominant_component
    {p k n d a : ℕ}
    (hp : p.Prime) (hk : 16 ≤ k) (hd : k ≤ d)
    (hkp : k ≤ p) (hpCenter : p ∣ 2 * n + d + k + 1)
    (hkeven : Even k)
    (hfactor : 2 * n + d + k + 1 =
      a * p ^ (2 * n + d + k + 1).factorization p)
    (hdominant : 5 * (k - 1).doubleFactorial * (a / Nat.gcd a d) ≤
      2 * p ^ (2 * n + d + k + 1).factorization p) :
    blockProduct k (n + d) ≠ 4 * blockProduct k n := by
  intro heq
  exact (Nat.not_lt_of_ge hdominant)
    (even_reflectionCenter_gapCoprimeQuotient_component_bound
      hp hk hd hkp hpCenter hkeven hfactor heq)

/-- Unconditional coprime-cofactor bound.  For `H = a*q`, set
`b = a / gcd(a,d)`.  The reflected square lift gives
`38*d < 5*a^2`, while the centered-gcd theorem gives
`a ≤ (k-1)!! * b`.  Thus every equation with a large center component obeys
the displayed bound; no premise says that the full cofactor divides `d`. -/
theorem even_reflectionCenter_gapCoprimeQuotient_thirtyEight_gap_bound
    {p k n d a : ℕ}
    (hp : p.Prime) (hk : 16 ≤ k) (hd : k ≤ d)
    (hkp : k ≤ p) (hpCenter : p ∣ 2 * n + d + k + 1)
    (hkeven : Even k)
    (hfactor : 2 * n + d + k + 1 =
      a * p ^ (2 * n + d + k + 1).factorization p)
    (heq : blockProduct k (n + d) = 4 * blockProduct k n) :
    38 * d < 5 * (k - 1).doubleFactorial ^ 2 *
      (a / Nat.gcd a d) ^ 2 := by
  let q := p ^ (2 * n + d + k + 1).factorization p
  let g := Nat.gcd a d
  let b := a / g
  let O := (k - 1).doubleFactorial
  have hcenterEq : 2 * n + d + k + 1 = a * q := by
    simpa only [q] using hfactor
  have hcenterPos : 0 < 2 * n + d + k + 1 := by omega
  have haPos : 0 < a := by
    by_contra hnot
    have haZero : a = 0 := by omega
    rw [haZero, zero_mul] at hcenterEq
    omega
  have hn9 : 9 * d < n :=
    nine_mul_gap_lt_n_of_four_solution hk hd heq
  have hcomponent : 2 * q < 5 * a := by
    simpa only [q] using
      even_reflectionCenter_component_two_lt_five_cofactor
        hp hk hd hkp hpCenter hkeven hfactor heq
  have hraw : 38 * d < 5 * a ^ 2 := by
    calc
      38 * d < 2 * (2 * n + d + k + 1) := by omega
      _ = a * (2 * q) := by rw [hcenterEq]; ring
      _ < a * (5 * a) := (Nat.mul_lt_mul_left haPos).mpr hcomponent
      _ = 5 * a ^ 2 := by ring
  have hgFixed : g ∣ O := by
    simpa only [g, O] using
      even_reflectionCenter_cofactorGcd_dvd_oddDoubleFactorial
        hk hkeven hfactor heq
  have hgLe : g ≤ O :=
    Nat.le_of_dvd (by dsimp [O]; exact Nat.doubleFactorial_pos _) hgFixed
  have hgb : g * b = a := by
    dsimp [g, b]
    exact Nat.mul_div_cancel' (Nat.gcd_dvd_left a d)
  have haLe : a ≤ O * b := by
    rw [← hgb]
    exact Nat.mul_le_mul_right b hgLe
  have haSqLe : a ^ 2 ≤ (O * b) ^ 2 := Nat.pow_le_pow_left haLe 2
  exact lt_of_lt_of_le hraw (by
    have := Nat.mul_le_mul_left 5 haSqLe
    simpa [O, b, g, mul_pow, mul_assoc] using this)

/-- Sharp unconditional coprime-cofactor bound.  This is the strengthened
large-row form requested by the aggregation audit:

`1218443*k*d < 2317440*((k-1)!!)^2*(a/gcd(a,d))^2`.

In particular, a residual center component can evade the `a ∣ d` exclusion
only by carrying a quantitatively large gap-coprime cofactor quotient. -/
theorem even_reflectionCenter_gapCoprimeQuotient_sharp_gap_bound
    {p k n d a : ℕ}
    (hp : p.Prime) (hk : 16 ≤ k) (hd : k ≤ d)
    (hkp : k ≤ p) (hpCenter : p ∣ 2 * n + d + k + 1)
    (hkeven : Even k)
    (hfactor : 2 * n + d + k + 1 =
      a * p ^ (2 * n + d + k + 1).factorization p)
    (heq : blockProduct k (n + d) = 4 * blockProduct k n) :
    1218443 * k * d < 2317440 * (k - 1).doubleFactorial ^ 2 *
      (a / Nat.gcd a d) ^ 2 := by
  let q := p ^ (2 * n + d + k + 1).factorization p
  let g := Nat.gcd a d
  let b := a / g
  let O := (k - 1).doubleFactorial
  have hcenterEq : 2 * n + d + k + 1 = a * q := by
    simpa only [q] using hfactor
  have hcenterPos : 0 < 2 * n + d + k + 1 := by omega
  have haPos : 0 < a := by
    by_contra hnot
    have haZero : a = 0 := by omega
    rw [haZero, zero_mul] at hcenterEq
    omega
  have hratio : 1218443 * k * d < 1853952 * n :=
    maximal_sharp_bracket_ratio_of_four_solution hk hd heq
  have hcenterBand :
      2 * 1218443 * k * d <
        1853952 * (2 * n + d + k + 1) := by
    calc
      2 * 1218443 * k * d = 2 * (1218443 * k * d) := by ring
      _ < 2 * (1853952 * n) :=
        (Nat.mul_lt_mul_left (by norm_num : 0 < 2)).mpr hratio
      _ = 1853952 * (2 * n) := by ring
      _ < 1853952 * (2 * n + d + k + 1) := by omega
  have hcomponent : 2 * q < 5 * a := by
    simpa only [q] using
      even_reflectionCenter_component_two_lt_five_cofactor
        hp hk hd hkp hpCenter hkeven hfactor heq
  have hrawFour :
      4 * 1218443 * k * d < 5 * 1853952 * a ^ 2 := by
    calc
      4 * 1218443 * k * d = 2 * (2 * 1218443 * k * d) := by ring
      _ < 2 * (1853952 * (2 * n + d + k + 1)) :=
        (Nat.mul_lt_mul_left (by norm_num : 0 < 2)).mpr hcenterBand
      _ = 1853952 * a * (2 * q) := by rw [hcenterEq]; ring
      _ < 1853952 * a * (5 * a) :=
        (Nat.mul_lt_mul_left (by positivity : 0 < 1853952 * a)).mpr hcomponent
      _ = 5 * 1853952 * a ^ 2 := by ring
  have hraw : 1218443 * k * d < 2317440 * a ^ 2 := by
    have hfour :
        4 * (1218443 * k * d) < 4 * (2317440 * a ^ 2) := by
      convert hrawFour using 1 <;> ring
    exact (Nat.mul_lt_mul_left (by norm_num : 0 < 4)).mp hfour
  have hgFixed : g ∣ O := by
    simpa only [g, O] using
      even_reflectionCenter_cofactorGcd_dvd_oddDoubleFactorial
        hk hkeven hfactor heq
  have hgLe : g ≤ O :=
    Nat.le_of_dvd (by dsimp [O]; exact Nat.doubleFactorial_pos _) hgFixed
  have hgb : g * b = a := by
    dsimp [g, b]
    exact Nat.mul_div_cancel' (Nat.gcd_dvd_left a d)
  have haLe : a ≤ O * b := by
    rw [← hgb]
    exact Nat.mul_le_mul_right b hgLe
  have haSqLe : a ^ 2 ≤ (O * b) ^ 2 := Nat.pow_le_pow_left haLe 2
  exact lt_of_lt_of_le hraw (by
    have := Nat.mul_le_mul_left 2317440 haSqLe
    simpa [O, b, g, mul_pow, mul_assoc] using this)

/-- Exclusion form of the unconditional coprime-cofactor bound. -/
theorem no_four_solution_of_even_reflectionCenter_gapCoprimeQuotient_sharp_large_gap
    {p k n d a : ℕ}
    (hp : p.Prime) (hk : 16 ≤ k) (hd : k ≤ d)
    (hkp : k ≤ p) (hpCenter : p ∣ 2 * n + d + k + 1)
    (hkeven : Even k)
    (hfactor : 2 * n + d + k + 1 =
      a * p ^ (2 * n + d + k + 1).factorization p)
    (hlarge : 2317440 * (k - 1).doubleFactorial ^ 2 *
        (a / Nat.gcd a d) ^ 2 ≤ 1218443 * k * d) :
    blockProduct k (n + d) ≠ 4 * blockProduct k n := by
  intro heq
  exact (Nat.not_lt_of_ge hlarge)
    (even_reflectionCenter_gapCoprimeQuotient_sharp_gap_bound
      hp hk hd hkp hpCenter hkeven hfactor heq)

/-- Exclusion form of the sharp fixed-row gap bound. -/
theorem no_four_solution_of_even_reflectionCenter_gapCofactor_sharp_large_gap
    {p k n d a : ℕ}
    (hp : p.Prime) (hk : 16 ≤ k) (hd : k ≤ d)
    (hkp : k ≤ p) (hpCenter : p ∣ 2 * n + d + k + 1)
    (hkeven : Even k)
    (hfactor : 2 * n + d + k + 1 =
      a * p ^ (2 * n + d + k + 1).factorization p)
    (haGap : a ∣ d)
    (hlarge : 2317440 * (k - 1).doubleFactorial ^ 2 ≤
      1218443 * k * d) :
    blockProduct k (n + d) ≠ 4 * blockProduct k n := by
  intro heq
  exact (Nat.not_lt_of_ge hlarge)
    (even_reflectionCenter_gapCofactor_sharp_gap_bound
      hp hk hd hkp hpCenter hkeven hfactor haGap heq)

/-- Exclusion form of the fixed-row gap bound. -/
theorem no_four_solution_of_even_reflectionCenter_gapCofactor_large_gap
    {p k n d a : ℕ}
    (hp : p.Prime) (hk : 16 ≤ k) (hd : k ≤ d)
    (hkp : k ≤ p) (hpCenter : p ∣ 2 * n + d + k + 1)
    (hkeven : Even k)
    (hfactor : 2 * n + d + k + 1 =
      a * p ^ (2 * n + d + k + 1).factorization p)
    (haGap : a ∣ d)
    (hlarge : 5 * (k - 1).doubleFactorial ^ 2 ≤ 38 * d) :
    blockProduct k (n + d) ≠ 4 * blockProduct k n := by
  intro heq
  exact (Nat.not_lt_of_ge hlarge)
    (even_reflectionCenter_gapCofactor_thirtyEight_gap_lt_five_doubleFactorial_sq
      hp hk hd hkp hpCenter hkeven hfactor haGap heq)

/-- Exclusion form of the preceding necessary bound. -/
theorem no_four_solution_of_even_reflectionCenter_gapCofactor_dominant_component
    {p k n d a : ℕ}
    (hp : p.Prime) (hk : 16 ≤ k) (hd : k ≤ d)
    (hkp : k ≤ p) (hpCenter : p ∣ 2 * n + d + k + 1)
    (hkeven : Even k)
    (hfactor : 2 * n + d + k + 1 =
      a * p ^ (2 * n + d + k + 1).factorization p)
    (haGap : a ∣ d)
    (hdominant : 5 * (k - 1).doubleFactorial ≤
      2 * p ^ (2 * n + d + k + 1).factorization p) :
    blockProduct k (n + d) ≠ 4 * blockProduct k n := by
  intro heq
  exact (Nat.not_lt_of_ge hdominant)
    (even_reflectionCenter_gapCofactor_component_two_lt_five_doubleFactorial
      hp hk hd hkp hpCenter hkeven hfactor haGap heq)

#print axioms even_reflectionCenter_gapCofactor_dvd_oddDoubleFactorial
#print axioms even_reflectionCenter_cofactorGcd_dvd_oddDoubleFactorial
#print axioms even_reflectionCenter_gapCofactor_component_two_lt_five_doubleFactorial
#print axioms even_reflectionCenter_gapCofactor_thirtyEight_gap_lt_five_doubleFactorial_sq
#print axioms no_four_solution_of_even_reflectionCenter_gapCofactor_large_gap
#print axioms even_reflectionCenter_gapCofactor_sharp_gap_bound
#print axioms no_four_solution_of_even_reflectionCenter_gapCofactor_sharp_large_gap
#print axioms even_reflectionCenter_gapCoprimeQuotient_component_bound
#print axioms no_four_solution_of_even_reflectionCenter_gapCoprimeQuotient_dominant_component
#print axioms even_reflectionCenter_gapCoprimeQuotient_thirtyEight_gap_bound
#print axioms even_reflectionCenter_gapCoprimeQuotient_sharp_gap_bound
#print axioms no_four_solution_of_even_reflectionCenter_gapCoprimeQuotient_sharp_large_gap
#print axioms no_four_solution_of_even_reflectionCenter_gapCofactor_dominant_component

end Erdos686Variant
end Erdos686
