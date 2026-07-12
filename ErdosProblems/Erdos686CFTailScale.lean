/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import ErdosProblems.Erdos686ConvergentMachinery

/-!
# Erdős 686: signed CF remainder and primitive-scale bounds

Kernel-only arithmetic used by the continued-fraction/primitive-scale attack
on the six open odd tails.  These lemmas do not assert the open tail theorem.

For centered coordinates `X = g*u`, `Y = g*v`, put `z = g^2` and
`A_j = 4*v^j-u^j`.  The reduced centered equation is an alternating
polynomial in `z`.  Its constant coefficient gives

`z ∣ (r!)^2 * A_1`.

The first two lemmas isolate that divisibility and the exact signed-remainder
floor pin.  The next lemmas turn the constant divisibility into the uniform
proper restriction `v ≥ 10^77` at the target cutoff `d ≥ 10^120`.

The exact finite CF reproduction and the resulting bounded tail extension are
in `compute/campaign686/agent_cf_tail/cf_primitive_tail_verify.py`.
-/

namespace Erdos686

namespace Erdos686Variant

/-- If all nonconstant scale-polynomial terms have a factor `z`, equality
forces `z` to divide the constant term. -/
lemma scale_constant_dvd {z L R c : ℕ} (h : z * L = z * R + c) : z ∣ c := by
  have hzsum : z ∣ z * R + c := by
    rw [← h]
    exact dvd_mul_right z L
  exact (Nat.dvd_add_iff_right (dvd_mul_right z R)).2 hzsum

/-- Exact signed-remainder pin.  If the first two scale terms differ by a
strictly positive remainder smaller than one denominator block, their ratio
has quotient exactly `z`.  This is the division-free kernel form of
`z = floor (B/A)`. -/
lemma floor_pin_of_signed_remainder {z A B M R : ℕ}
    (hM : 0 < M) (hR : 0 < R) (hRlt : R < M * A)
    (heq : M * B = M * (z * A) + R) :
    B / A = z := by
  have hloM : M * (z * A) < M * B := by omega
  have hlo : z * A < B := (Nat.mul_lt_mul_left hM).mp hloM
  have hhiM : M * B < M * ((z + 1) * A) := by
    calc
      M * B = M * (z * A) + R := heq
      _ < M * (z * A) + M * A := Nat.add_lt_add_left hRlt _
      _ = M * ((z + 1) * A) := by ring
  have hhi : B < (z + 1) * A := (Nat.mul_lt_mul_left hM).mp hhiM
  exact Nat.div_eq_of_lt_le hlo.le hhi

/-- Primitive-scale denominator inequality.  The hypotheses are exactly the
positive-coordinate consequences used in the CF decomposition:

* `d = g*(u-v)`;
* `1 < u/v < 2` in division-free form;
* the constant scale coefficient gives `g^2 ∣ E*(4v-u)`.

They imply `d^2 < 3*E*v^3`. -/
lemma gap_sq_lt_of_scale_constant {g u v d E : ℕ}
    (hg : 0 < g) (hE : 0 < E) (hvu : v < u) (hu2 : u < 2 * v)
    (hd : d = g * (u - v)) (hdiv : g ^ 2 ∣ E * (4 * v - u)) :
    d ^ 2 < 3 * E * v ^ 3 := by
  have hv : 0 < v := by omega
  have huv : u - v < v := by omega
  have hdlt : d < g * v := by
    rw [hd]
    exact Nat.mul_lt_mul_of_pos_left huv hg
  have hd2lt : d ^ 2 < (g * v) ^ 2 := Nat.pow_lt_pow_left hdlt (by omega)
  have ha1pos : 0 < 4 * v - u := by omega
  have hprodpos : 0 < E * (4 * v - u) := Nat.mul_pos hE ha1pos
  have hg2le : g ^ 2 ≤ E * (4 * v - u) := Nat.le_of_dvd hprodpos hdiv
  have ha1lt : 4 * v - u < 3 * v := by omega
  have hg2lt : g ^ 2 < 3 * E * v := by
    calc
      g ^ 2 ≤ E * (4 * v - u) := hg2le
      _ < E * (3 * v) := Nat.mul_lt_mul_of_pos_left ha1lt hE
      _ = 3 * E * v := by ring
  calc
    d ^ 2 < (g * v) ^ 2 := hd2lt
    _ = g ^ 2 * v ^ 2 := by ring
    _ < (3 * E * v) * v ^ 2 :=
      Nat.mul_lt_mul_of_pos_right hg2lt (pow_pos hv 2)
    _ = 3 * E * v ^ 3 := by ring

/-- The exact numerical cutoff behind the primitive-denominator trap. -/
lemma primitive_denominator_ge_ten_pow_77 {d v : ℕ}
    (hd : 10 ^ 120 ≤ d) (hbound : d ^ 2 < 76204800 * v ^ 3) :
    10 ^ 77 ≤ v := by
  by_contra hnot
  have hv : v < 10 ^ 77 := Nat.lt_of_not_ge hnot
  have hv3 : v ^ 3 < (10 ^ 77) ^ 3 := Nat.pow_lt_pow_left hv (by omega)
  have hd2 : (10 ^ 120) ^ 2 ≤ d ^ 2 := Nat.pow_le_pow_left hd 2
  have hmul : 76204800 * v ^ 3 < 76204800 * (10 ^ 77) ^ 3 :=
    Nat.mul_lt_mul_of_pos_left hv3 (by norm_num)
  have hconst : 76204800 * (10 ^ 77) ^ 3 < (10 ^ 120) ^ 2 := by
    norm_num
  omega

/-- Uniform target-row consequence.  For the six rows,
`E = (r!)^2 ≤ (7!)^2 = 25401600`; hence target-size gaps force the reduced
denominator `v` to have at least 78 decimal digits. -/
theorem primitive_denominator_ge_ten_pow_77_of_scale_constant
    {g u v d E : ℕ}
    (hg : 0 < g) (hE : 0 < E) (hEle : E ≤ 25401600)
    (hvu : v < u) (hu2 : u < 2 * v)
    (hd : d = g * (u - v)) (hdiv : g ^ 2 ∣ E * (4 * v - u))
    (hdlarge : 10 ^ 120 ≤ d) :
    10 ^ 77 ≤ v := by
  have hraw := gap_sq_lt_of_scale_constant hg hE hvu hu2 hd hdiv
  have hbound : d ^ 2 < 76204800 * v ^ 3 := by
    calc
      d ^ 2 < 3 * E * v ^ 3 := hraw
      _ ≤ 76204800 * v ^ 3 := by
        gcongr
        omega
  exact primitive_denominator_ge_ten_pow_77 hdlarge hbound

/-- The weakest of the six banked ratio lower bounds is the `k=15` bound
`109651/100000`.  It gives the uniform conversion `v < 11d`. -/
lemma primitive_denominator_lt_eleven_gap {g u v d : ℕ}
    (hg : 0 < g) (hvu : v < u) (hd : d = g * (u - v))
    (hratio : 109651 * v < 100000 * u) :
    v < 11 * d := by
  have hu : u = v + (u - v) := (Nat.add_sub_of_le hvu.le).symm
  have hbase : v < 11 * (u - v) := by omega
  have hgap : u - v ≤ d := by
    rw [hd]
    nth_rewrite 1 [← one_mul (u - v)]
    exact Nat.mul_le_mul_right (u - v) hg
  exact lt_of_lt_of_le hbase (Nat.mul_le_mul_left 11 hgap)

/-! ## Reverse divisibility at the first p-adic Newton step -/

/-- For a primitive pair, the linear and cubic approximation remainders can
share only a divisor of `60`.  Indeed `u = 4v` modulo the linear remainder,
so the cubic remainder is congruent to `-60v^3`; primitivity cancels `v^3`.
-/
lemma gcd_linear_cubic_dvd_sixty {u v : ℕ}
    (hcop : Nat.Coprime u v) (hu4 : u ≤ 4 * v) (hu3 : u ^ 3 ≤ 4 * v ^ 3) :
    Nat.gcd (4 * v - u) (4 * v ^ 3 - u ^ 3) ∣ 60 := by
  let h := Nat.gcd (4 * v - u) (4 * v ^ 3 - u ^ 3)
  have hlin : h ∣ 4 * v - u := Nat.gcd_dvd_left _ _
  have hcub : h ∣ 4 * v ^ 3 - u ^ 3 := Nat.gcd_dvd_right _ _
  have hmod1 : u ≡ 4 * v [MOD h] := (Nat.modEq_iff_dvd' hu4).2 hlin
  have hmod3a : u ^ 3 ≡ (4 * v) ^ 3 [MOD h] := hmod1.pow 3
  have hmod3b : u ^ 3 ≡ 4 * v ^ 3 [MOD h] :=
    (Nat.modEq_iff_dvd' hu3).2 hcub
  have hmod64 : 4 * v ^ 3 ≡ 64 * v ^ 3 [MOD h] := by
    have hcombined := hmod3b.symm.trans hmod3a
    simpa [mul_pow] using hcombined
  have h60 : h ∣ 60 * v ^ 3 := by
    have hle : 4 * v ^ 3 ≤ 64 * v ^ 3 := by omega
    have hd := (Nat.modEq_iff_dvd' hle).1 hmod64
    simpa [← Nat.mul_sub_right_distrib] using hd
  have hcopv : Nat.Coprime h v := by
    let q := Nat.gcd h v
    have hqh : q ∣ h := Nat.gcd_dvd_left _ _
    have hqv : q ∣ v := Nat.gcd_dvd_right _ _
    have hqa : q ∣ 4 * v - u := dvd_trans hqh hlin
    have hq4v : q ∣ 4 * v := dvd_mul_of_dvd_right hqv 4
    have hqu : q ∣ u := by
      have hdiff : 4 * v - (4 * v - u) = u := by omega
      rw [← hdiff]
      exact (Nat.dvd_sub_iff_left (Nat.sub_le _ _) hqa).2 hq4v
    have hq1 : q ∣ 1 := by
      have hqgcd : q ∣ Nat.gcd u v := Nat.dvd_gcd hqu hqv
      simpa [hcop.gcd_eq_one] using hqgcd
    exact Nat.dvd_one.mp hq1
  exact (hcopv.pow_right 3).dvd_of_dvd_mul_right h60

/-- General resultant bound for the linear remainder and every higher power
remainder.  The cubic constant `60` is the case `t=2`.
-/
lemma gcd_linear_power_remainder_dvd {u v t : ℕ}
    (hcop : Nat.Coprime u v) (hu4 : u ≤ 4 * v)
    (hupow : u ^ (t + 1) ≤ 4 * v ^ (t + 1)) :
    Nat.gcd (4 * v - u) (4 * v ^ (t + 1) - u ^ (t + 1)) ∣
      4 * (4 ^ t - 1) := by
  let h := Nat.gcd (4 * v - u) (4 * v ^ (t + 1) - u ^ (t + 1))
  have hlin : h ∣ 4 * v - u := Nat.gcd_dvd_left _ _
  have hpow : h ∣ 4 * v ^ (t + 1) - u ^ (t + 1) := Nat.gcd_dvd_right _ _
  have hmod1 : u ≡ 4 * v [MOD h] := (Nat.modEq_iff_dvd' hu4).2 hlin
  have hmodpa : u ^ (t + 1) ≡ (4 * v) ^ (t + 1) [MOD h] :=
    hmod1.pow (t + 1)
  have hmodpb : u ^ (t + 1) ≡ 4 * v ^ (t + 1) [MOD h] :=
    (Nat.modEq_iff_dvd' hupow).2 hpow
  have hmodbig :
      4 * v ^ (t + 1) ≡ 4 ^ (t + 1) * v ^ (t + 1) [MOD h] := by
    have hcombined := hmodpb.symm.trans hmodpa
    simpa [mul_pow] using hcombined
  have hcoef : 4 * (4 ^ t - 1) = 4 ^ (t + 1) - 4 := by
    rw [pow_succ]
    omega
  have hsmall : 4 ≤ 4 ^ (t + 1) := by
    rw [pow_succ]
    exact Nat.le_mul_of_pos_left 4 (pow_pos (by norm_num) t)
  have hdivprod : h ∣ (4 * (4 ^ t - 1)) * v ^ (t + 1) := by
    have hd :=
      (Nat.modEq_iff_dvd' (Nat.mul_le_mul_right _ hsmall)).1 hmodbig
    rw [hcoef]
    simpa [← Nat.mul_sub_right_distrib] using hd
  have hcopv : Nat.Coprime h v := by
    let q := Nat.gcd h v
    have hqh : q ∣ h := Nat.gcd_dvd_left _ _
    have hqv : q ∣ v := Nat.gcd_dvd_right _ _
    have hqa : q ∣ 4 * v - u := dvd_trans hqh hlin
    have hq4v : q ∣ 4 * v := dvd_mul_of_dvd_right hqv 4
    have hqu : q ∣ u := by
      have hdiff : 4 * v - (4 * v - u) = u := by omega
      rw [← hdiff]
      exact (Nat.dvd_sub_iff_left (Nat.sub_le _ _) hqa).2 hq4v
    have hq1 : q ∣ 1 := by
      have hqgcd : q ∣ Nat.gcd u v := Nat.dvd_gcd hqu hqv
      simpa [hcop.gcd_eq_one] using hqgcd
    exact Nat.dvd_one.mp hq1
  exact (hcopv.pow_right (t + 1)).dvd_of_dvd_mul_right hdivprod

/-- General coefficient-overlap bound used at any low-end Horner stage. -/
lemma gcd_scale_coefficient_dvd_of_gcd_bound
    {z E F G A1 As : ℕ}
    (hconst : z ∣ E * A1) (hgcd : Nat.gcd A1 As ∣ G) :
    Nat.gcd z (F * As) ∣ G * E * F := by
  let h := Nat.gcd z (F * As)
  have hz : h ∣ z := Nat.gcd_dvd_left _ _
  have hfas : h ∣ F * As := Nat.gcd_dvd_right _ _
  have hea1 : h ∣ E * A1 := dvd_trans hz hconst
  have hca1 : h ∣ (E * F) * A1 := by
    simpa [mul_assoc, mul_comm, mul_left_comm] using
      dvd_mul_of_dvd_right hea1 F
  have hcas : h ∣ (E * F) * As := by
    simpa [mul_assoc, mul_comm, mul_left_comm] using
      dvd_mul_of_dvd_right hfas E
  have hcommon : h ∣ (E * F) * Nat.gcd A1 As := by
    have hboth := Nat.dvd_gcd hca1 hcas
    simpa [Nat.gcd_mul_left] using hboth
  have hsmall : (E * F) * Nat.gcd A1 As ∣ G * E * F := by
    simpa [mul_assoc, mul_comm, mul_left_comm] using
      Nat.mul_dvd_mul_left (E * F) hgcd
  exact dvd_trans hcommon hsmall

/-- If `z` divides the constant coefficient `E*A1`, then its overlap with
the first Newton coefficient `F*A3` is bounded by the fixed resultant loss
`60*E*F`. -/
lemma gcd_scale_first_coefficient_dvd {z E F A1 A3 : ℕ}
    (hconst : z ∣ E * A1) (hgcd : Nat.gcd A1 A3 ∣ 60) :
    Nat.gcd z (F * A3) ∣ 60 * E * F := by
  let h := Nat.gcd z (F * A3)
  have hz : h ∣ z := Nat.gcd_dvd_left _ _
  have hfa : h ∣ F * A3 := Nat.gcd_dvd_right _ _
  have hea1 : h ∣ E * A1 := dvd_trans hz hconst
  have hca1 : h ∣ (E * F) * A1 := by
    simpa [mul_assoc, mul_comm, mul_left_comm] using
      dvd_mul_of_dvd_right hea1 F
  have hca3 : h ∣ (E * F) * A3 := by
    simpa [mul_assoc, mul_comm, mul_left_comm] using
      dvd_mul_of_dvd_right hfa E
  have hcommon : h ∣ (E * F) * Nat.gcd A1 A3 := by
    have hboth := Nat.dvd_gcd hca1 hca3
    simpa [Nat.gcd_mul_left] using hboth
  have hsmall : (E * F) * Nat.gcd A1 A3 ∣ 60 * E * F := by
    simpa [mul_assoc, mul_comm, mul_left_comm] using
      Nat.mul_dvd_mul_left (E * F) hgcd
  exact dvd_trans hcommon hsmall

/-- Bounded valuation discrepancy for the constant scale quotient.  The
low-end Horner recurrence says `q = F*A3 (mod z)`, so its overlap with `z`
is bounded by `60*E*F`.  In a target row, `E=e_r` and `F=e_(r-1)`.
-/
theorem scale_quotient_gcd_bound {z q E F A1 A3 L R : ℕ}
    (hconst : E * A1 = z * q)
    (hgcd : Nat.gcd A1 A3 ∣ 60)
    (hrel : q + z * L = F * A3 + z * R) :
    Nat.gcd z q ∣ 60 * E * F := by
  have hmod : q ≡ F * A3 [MOD z] := by
    unfold Nat.ModEq
    have hm := congrArg (fun x : ℕ => x % z) hrel
    simpa [Nat.add_mod] using hm
  have heqgcd : Nat.gcd z q = Nat.gcd z (F * A3) := by
    simpa [Nat.gcd_comm] using hmod.gcd_eq
  rw [heqgcd]
  exact gcd_scale_first_coefficient_dvd ⟨q, hconst⟩ hgcd

/-- Every Horner remainder has bounded overlap with the square scale once
its coefficient remainder has a fixed resultant bound with `A1`. -/
theorem scale_horner_remainder_gcd_bound
    {z H E F G A1 As L R : ℕ}
    (hconst : z ∣ E * A1)
    (hgcd : Nat.gcd A1 As ∣ G)
    (hrel : H + z * L = F * As + z * R) :
    Nat.gcd z H ∣ G * E * F := by
  have hmod : H ≡ F * As [MOD z] := by
    unfold Nat.ModEq
    have hm := congrArg (fun x : ℕ => x % z) hrel
    simpa [Nat.add_mod] using hm
  have heqgcd : Nat.gcd z H = Nat.gcd z (F * As) := by
    simpa [Nat.gcd_comm] using hmod.gcd_eq
  rw [heqgcd]
  exact gcd_scale_coefficient_dvd_of_gcd_bound hconst hgcd

/-- Outside the fixed discrepancy divisor, a divisor of the square scale
cannot also divide the complementary constant-term quotient. -/
lemma not_dvd_scale_quotient_of_not_dvd_discrepancy
    {p z q D : ℕ} (hpz : p ∣ z) (hpD : ¬p ∣ D)
    (hoverlap : Nat.gcd z q ∣ D) :
    ¬p ∣ q := by
  intro hpq
  exact hpD (dvd_trans (Nat.dvd_gcd hpz hpq) hoverlap)

/-- A good prime in the square scale cannot divide the primitive denominator.
This is the first half of the exact-center calculation: after reduction to
`X=g*u`, `Y=g*v`, the full good-prime component of `Y` is already in `g`. -/
lemma good_scale_prime_not_dvd_primitive_denominator
    {p z E u v : ℕ}
    (hp : p.Prime) (hpz : p ∣ z) (hz : z ∣ E * (4 * v - u))
    (hpE : ¬p ∣ E) (hcop : Nat.Coprime u v) (hu4 : u ≤ 4 * v) :
    ¬p ∣ v := by
  have hpProd : p ∣ E * (4 * v - u) := dvd_trans hpz hz
  have hpA1 : p ∣ 4 * v - u := (hp.dvd_mul.mp hpProd).resolve_left hpE
  intro hpv
  have hp4v : p ∣ 4 * v := dvd_mul_of_dvd_right hpv 4
  have hpu : p ∣ u := by
    have hdiff : 4 * v - (4 * v - u) = u := by omega
    rw [← hdiff]
    exact (Nat.dvd_sub_iff_left (Nat.sub_le _ _) hpA1).2 hp4v
  exact hp.not_dvd_one (by
    have hpgcd : p ∣ Nat.gcd u v := Nat.dvd_gcd hpu hpv
    simpa [hcop.gcd_eq_one] using hpgcd)

/-- A good prime in the square scale cannot divide the primitive gap
`u-v`.  Hence its full gap exponent belongs to the centered common scale.
-/
lemma good_scale_prime_not_dvd_primitive_gap
    {p z E u v : ℕ}
    (hp : p.Prime) (hpz : p ∣ z) (hz : z ∣ E * (4 * v - u))
    (hpE : ¬p ∣ E) (hp3 : ¬p ∣ 3)
    (hcop : Nat.Coprime u v) (hvu : v ≤ u) (hu4 : u ≤ 4 * v) :
    ¬p ∣ u - v := by
  have hpProd : p ∣ E * (4 * v - u) := dvd_trans hpz hz
  have hpA1 : p ∣ 4 * v - u := (hp.dvd_mul.mp hpProd).resolve_left hpE
  have hpnv : ¬p ∣ v :=
    good_scale_prime_not_dvd_primitive_denominator hp hpz hz hpE hcop hu4
  intro hpGap
  have hp3v : p ∣ 3 * v := by
    have hpsum : p ∣ (4 * v - u) + (u - v) := Nat.dvd_add hpA1 hpGap
    have heq : (4 * v - u) + (u - v) = 3 * v := by omega
    rwa [heq] at hpsum
  rcases hp.dvd_mul.mp hp3v with hp3' | hpv
  · exact hp3 hp3'
  · exact hpnv hpv

/-- A displayed prime power `H=p^a` is the exact `p`-component of `x=H*c`
as soon as the complementary factor is not divisible by `p`.  The coprimality
conclusion is the valuation-free, kernel-friendly form of
`v_p(x)=a`. -/
lemma primePower_exact_factor_of_not_dvd
    {p a H c x : ℕ}
    (hp : p.Prime) (ha : 0 < a) (hH : H = p ^ a)
    (hx : x = H * c) (hpc : ¬p ∣ c) :
    x = H * c ∧ Nat.Coprime H c := by
  refine ⟨hx, ?_⟩
  rw [hH]
  exact (Nat.coprime_pow_left_iff ha p c).2
    (hp.coprime_iff_not_dvd.mpr hpc)

/-- Exact good-prime factorization of both the target gap and the centered
primitive denominator.  If `H=p^a` is the full `p`-part of `g`, then the
same `H` is the full `p`-part of `d=g(u-v)` and of `Y=g*v`.

Thus no good-prime exponent is hidden in either primitive cofactor. -/
theorem good_primePower_exact_gap_and_center
    {p a H g0 g z E u v d Y : ℕ}
    (hp : p.Prime) (ha : 0 < a) (hH : H = p ^ a)
    (hg : g = H * g0) (hpng0 : ¬p ∣ g0)
    (hd : d = g * (u - v)) (hY : Y = g * v)
    (hpz : p ∣ z) (hz : z ∣ E * (4 * v - u))
    (hpE : ¬p ∣ E) (hp3 : ¬p ∣ 3)
    (hcop : Nat.Coprime u v) (hvu : v ≤ u) (hu4 : u ≤ 4 * v) :
    (d = H * (g0 * (u - v)) ∧ Nat.Coprime H (g0 * (u - v))) ∧
      (Y = H * (g0 * v) ∧ Nat.Coprime H (g0 * v)) := by
  have hpnGap : ¬p ∣ u - v :=
    good_scale_prime_not_dvd_primitive_gap
      hp hpz hz hpE hp3 hcop hvu hu4
  have hpnv : ¬p ∣ v :=
    good_scale_prime_not_dvd_primitive_denominator hp hpz hz hpE hcop hu4
  have hpnGapCofactor : ¬p ∣ g0 * (u - v) := by
    intro hpdvd
    rcases hp.dvd_mul.mp hpdvd with hpg0 | hpGap
    · exact hpng0 hpg0
    · exact hpnGap hpGap
  have hpnCenterCofactor : ¬p ∣ g0 * v := by
    intro hpdvd
    rcases hp.dvd_mul.mp hpdvd with hpg0 | hpv
    · exact hpng0 hpg0
    · exact hpnv hpv
  constructor
  · apply primePower_exact_factor_of_not_dvd hp ha hH
      (c := g0 * (u - v))
    · rw [hd, hg]
      ring
    · exact hpnGapCofactor
  · apply primePower_exact_factor_of_not_dvd hp ha hH
      (c := g0 * v)
    · rw [hY, hg]
      ring
    · exact hpnCenterCofactor

/-- Exact factorization of a good center component.  If `g=H*g0` and `H`
is coprime to the fixed coefficient, the complementary scale factor, and
the remaining common scale, then `A1` contains exactly `H^2`; its cofactor
is coprime to `H`.
-/
theorem good_center_component_exact_square_cofactor
    {H g0 g E A1 q : ℕ}
    (hH : 0 < H) (hg : g = H * g0)
    (hconst : E * A1 = g ^ 2 * q)
    (hcop : Nat.Coprime H (E * g0 * q)) :
    ∃ a1 : ℕ, A1 = H ^ 2 * a1 ∧ E * a1 = g0 ^ 2 * q ∧
      Nat.Coprime H a1 := by
  have hHE : Nat.Coprime H E := by
    apply Nat.Coprime.of_dvd_right (b₂ := E * g0 * q) _ hcop
    use g0 * q
    ring
  have hH2E : Nat.Coprime (H ^ 2) E := hHE.pow_left 2
  have hH2dvdprod : H ^ 2 ∣ E * A1 := by
    use g0 ^ 2 * q
    rw [hconst, hg]
    ring
  have hH2dvd : H ^ 2 ∣ A1 := hH2E.dvd_of_dvd_mul_left hH2dvdprod
  obtain ⟨a1, hA1⟩ := hH2dvd
  have hscaled : H ^ 2 * (E * a1) = H ^ 2 * (g0 ^ 2 * q) := by
    calc
      H ^ 2 * (E * a1) = E * A1 := by rw [hA1]; ring
      _ = g ^ 2 * q := hconst
      _ = H ^ 2 * (g0 ^ 2 * q) := by rw [hg]; ring
  have hEa1 : E * a1 = g0 ^ 2 * q :=
    Nat.mul_left_cancel (pow_pos hH 2) hscaled
  have hHg0 : Nat.Coprime H g0 := by
    apply Nat.Coprime.of_dvd_right (b₂ := E * g0 * q) _ hcop
    use E * q
    ring
  have hHq : Nat.Coprime H q := by
    apply Nat.Coprime.of_dvd_right (b₂ := E * g0 * q) _ hcop
    use E * g0
    ring
  have hHrhs : Nat.Coprime H (g0 ^ 2 * q) :=
    (hHg0.pow_right 2).mul_right hHq
  have hHlhs : Nat.Coprime H (E * a1) := by
    rw [hEa1]
    exact hHrhs
  exact ⟨a1, hA1, hEa1, (Nat.coprime_mul_iff_right.mp hHlhs).2⟩

/-- Multiplying the exact square cofactor by the centered common scale makes
the center residual contain exactly `H^3`, with coprime residual cofactor.
-/
lemma center_residual_exact_component {H g0 g A1 a1 : ℕ}
    (hg : g = H * g0) (hA1 : A1 = H ^ 2 * a1)
    (hcop : Nat.Coprime H (g0 * a1)) :
    g * A1 = H ^ 3 * (g0 * a1) ∧ Nat.Coprime H (g0 * a1) := by
  constructor
  · rw [hg, hA1]
    ring
  · exact hcop

/-- Full exact-component package for a good prime.  Under the constant scale
identity, the exact `p^a` component `H` of `g` occurs:

* exactly once in the gap `d`;
* exactly once in the centered denominator `Y`;
* exactly twice in the primitive linear residual `A1=4v-u`; and
* exactly three times in the centered residual `g*A1`.

Every displayed complementary cofactor is coprime to `H`, so these are exact
component statements rather than mere divisibilities. -/
theorem good_primePower_exact_gap_center_residual
    {p a H g0 g z E u v d Y A1 q : ℕ}
    (hp : p.Prime) (ha : 0 < a) (hH : H = p ^ a)
    (hg : g = H * g0) (hpng0 : ¬p ∣ g0)
    (hd : d = g * (u - v)) (hY : Y = g * v)
    (hpz : p ∣ z) (hz : z ∣ E * (4 * v - u))
    (hpE : ¬p ∣ E) (hp3 : ¬p ∣ 3)
    (hcopUV : Nat.Coprime u v) (hvu : v ≤ u) (hu4 : u ≤ 4 * v)
    (hA1def : A1 = 4 * v - u)
    (hconst : E * A1 = g ^ 2 * q)
    (hcopScale : Nat.Coprime H (E * g0 * q)) :
    ∃ a1 : ℕ,
      (d = H * (g0 * (u - v)) ∧ Nat.Coprime H (g0 * (u - v))) ∧
      (Y = H * (g0 * v) ∧ Nat.Coprime H (g0 * v)) ∧
      A1 = 4 * v - u ∧ A1 = H ^ 2 * a1 ∧ E * a1 = g0 ^ 2 * q ∧
      (g * A1 = H ^ 3 * (g0 * a1) ∧ Nat.Coprime H (g0 * a1)) := by
  have hgapCenter := good_primePower_exact_gap_and_center
    hp ha hH hg hpng0 hd hY hpz hz hpE hp3 hcopUV hvu hu4
  have hHpos : 0 < H := by
    rw [hH]
    exact pow_pos hp.pos a
  obtain ⟨a1, hA1, hEa1, hHa1⟩ :=
    good_center_component_exact_square_cofactor
      hHpos hg hconst hcopScale
  have hHg0 : Nat.Coprime H g0 := by
    apply Nat.Coprime.of_dvd_right (b₂ := E * g0 * q) _ hcopScale
    use E * q
    ring
  have hHres : Nat.Coprime H (g0 * a1) := hHg0.mul_right hHa1
  have hres := center_residual_exact_component hg hA1 hHres
  exact ⟨a1, hgapCenter.1, hgapCenter.2, hA1def, hA1, hEa1, hres⟩

/-! The mandatory overlapping-block fixtures.  Ordinary kernel `decide`
evaluates the two finite products; no `native_decide` is used. -/

theorem k9_d1_telescope :
    blockProduct 9 (2 + 1) = 4 * blockProduct 9 2 := by
  decide

theorem k15_d1_telescope :
    blockProduct 15 (4 + 1) = 4 * blockProduct 15 4 := by
  decide

theorem k9_d1_telescope_outside_disjoint_domain : ¬9 ≤ 1 := by
  norm_num

theorem k15_d1_telescope_outside_disjoint_domain : ¬15 ≤ 1 := by
  norm_num

#print axioms scale_constant_dvd
#print axioms floor_pin_of_signed_remainder
#print axioms gap_sq_lt_of_scale_constant
#print axioms primitive_denominator_ge_ten_pow_77
#print axioms primitive_denominator_ge_ten_pow_77_of_scale_constant
#print axioms primitive_denominator_lt_eleven_gap
#print axioms gcd_linear_cubic_dvd_sixty
#print axioms gcd_linear_power_remainder_dvd
#print axioms gcd_scale_coefficient_dvd_of_gcd_bound
#print axioms gcd_scale_first_coefficient_dvd
#print axioms scale_quotient_gcd_bound
#print axioms scale_horner_remainder_gcd_bound
#print axioms not_dvd_scale_quotient_of_not_dvd_discrepancy
#print axioms good_scale_prime_not_dvd_primitive_denominator
#print axioms good_scale_prime_not_dvd_primitive_gap
#print axioms primePower_exact_factor_of_not_dvd
#print axioms good_primePower_exact_gap_and_center
#print axioms good_center_component_exact_square_cofactor
#print axioms center_residual_exact_component
#print axioms good_primePower_exact_gap_center_residual
#print axioms k9_d1_telescope
#print axioms k15_d1_telescope

end Erdos686Variant

end Erdos686
