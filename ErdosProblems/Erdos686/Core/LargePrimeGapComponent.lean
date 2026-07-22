/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import ErdosProblems.Erdos686.Core.PadicLift
import ErdosProblems.Erdos686.Core.LargeKWedge
import Mathlib.Analysis.Complex.Exponential

/-!
# A large-prime component exclusion for Erdős 686

Let `p ≥ k` be prime and let a positive power `p^e` divide the gap.  The
local quadratic lift puts `p^(2e)` into one positive residual
`3(n+i)-d`.  An exact upper ratio bracket then makes that residual too short
whenever

`(13*k-6)*d + 18*(k-1) ≤ 6*p^(2*e)`.

In particular this closes every whole prime-power gap `d=p^e` with `e≥2`
in the large-row range.  No computation and no external theorem enters the
proof.
-/

namespace Erdos686
namespace Erdos686Variant

private lemma exp_nine_thirteenths_lt_two :
    Real.exp (9 / 13 : ℝ) < 2 := by
  have h := Real.exp_bound'
    (x := (9 / 13 : ℝ)) (by norm_num) (by norm_num) (n := 4) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢
  linarith

/-- An exact rational upper bracket for `4^(1/k)`.  The proof uses the
four-term certified Taylor upper bound for `exp(9/13)`, twice. -/
lemma thirteen_k_add_eighteen_pow_lt_four_mul_thirteen_k_pow
    {k : ℕ} (hk : 1 ≤ k) :
    (13 * k + 18) ^ k < 4 * (13 * k) ^ k := by
  have hk0 : k ≠ 0 := by omega
  have hkR : (0 : ℝ) < k := by exact_mod_cast (Nat.pos_of_ne_zero hk0)
  let x : ℝ := 18 / (13 * k)
  have hx : 0 < x := by dsimp [x]; positivity
  have hone : 1 + x < Real.exp x := by
    simpa [add_comm] using Real.add_one_lt_exp hx.ne'
  have hpow : (1 + x) ^ k < Real.exp x ^ k :=
    pow_lt_pow_left₀ hone (by positivity) hk0
  have hexpPow : Real.exp x ^ k = Real.exp (18 / 13 : ℝ) := by
    rw [← Real.exp_nat_mul]
    congr 1
    dsimp [x]
    field_simp
  have hexp18 : Real.exp (18 / 13 : ℝ) < 4 := by
    rw [show (18 / 13 : ℝ) = 9 / 13 + 9 / 13 by norm_num,
      Real.exp_add]
    have hpos := Real.exp_pos (9 / 13 : ℝ)
    nlinarith [exp_nine_thirteenths_lt_two]
  have hxpow : (1 + x) ^ k < 4 := by
    rw [hexpPow] at hpow
    exact hpow.trans hexp18
  have hscale : (0 : ℝ) < (13 * (k : ℝ)) ^ k := by positivity
  have hscaled := mul_lt_mul_of_pos_left hxpow hscale
  have hid :
      (13 * (k : ℝ) + 18) ^ k =
        (13 * (k : ℝ)) ^ k * (1 + x) ^ k := by
    rw [← mul_pow]
    congr 1
    dsimp [x]
    field_simp
  have hreal :
      (13 * (k : ℝ) + 18) ^ k < 4 * (13 * (k : ℝ)) ^ k := by
    rw [hid]
    nlinarith
  exact_mod_cast hreal

/-- The upper endpoint ratio window in the convenient `18/13` form. -/
theorem eighteen_mul_n_add_one_lt_thirteen_mul_k_mul_gap_of_four_solution
    {k n d : ℕ} (hk : 16 ≤ k)
    (heq : blockProduct k (n + d) = 4 * blockProduct k n) :
    18 * (n + 1) < 13 * k * d := by
  have hbracket : (13 * k + 18) ^ k < 4 * (13 * k) ^ k :=
    thirteen_k_add_eighteen_pow_lt_four_mul_thirteen_k_pow (by omega)
  have hlin := ratio_window_upper_gap_bound_of_pow_bracket
    (N := 4) (A := 13 * k + 18) (B := 13 * k)
    (k := k) (n := n) (d := d) (by omega) (by omega)
    hbracket (ratio_window_four_nat heq).2
  simpa using hlin

/-- A large prime-power component whose square already exceeds the explicit
residual ceiling rules out the quotient-four equation.  The exponent need
not be the full `p`-adic valuation: any positive `e` satisfying the displayed
divisibility and dominance hypotheses suffices. -/
theorem no_four_solution_of_large_prime_gap_component_dominance
    {p e k n d : ℕ}
    (hp : p.Prime) (he : 0 < e)
    (hk : 16 ≤ k) (hd : k ≤ d) (hkp : k ≤ p)
    (hpowDvd : p ^ e ∣ d)
    (hdominant :
      (13 * k - 6) * d + 18 * (k - 1) ≤ 6 * p ^ (2 * e)) :
    blockProduct k (n + d) ≠ 4 * blockProduct k n := by
  intro heq
  obtain ⟨i, hi, _huniq⟩ := gap_primePower_existsUnique_local_sq_lift
    hp he (by omega) hkp hpowDvd heq
  have h9d : 9 * d < n := nine_mul_gap_lt_n_of_four_solution hk hd heq
  have hresPosZ : (0 : ℤ) < 3 * ((n + i : ℕ) : ℤ) - (d : ℤ) := by
    have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi.1).1
    apply sub_pos.mpr
    exact_mod_cast (show d < 3 * (n + i) by omega)
  have hresNat :
      3 * ((n + i : ℕ) : ℤ) - (d : ℤ) =
        ((3 * (n + i) - d : ℕ) : ℤ) := by
    rw [Nat.cast_sub (by omega : d ≤ 3 * (n + i))]
    norm_num
  have hpowDvdNat : p ^ (2 * e) ∣ 3 * (n + i) - d := by
    have hz := hi.2.2
    rw [hresNat] at hz
    have hz' : ((p ^ (2 * e) : ℕ) : ℤ) ∣
        ((3 * (n + i) - d : ℕ) : ℤ) := by
      simpa [Nat.cast_pow, ← pow_mul, mul_comm] using hz
    exact Int.natCast_dvd_natCast.mp hz'
  have hresPos : 0 < 3 * (n + i) - d := by omega
  have hp2le : p ^ (2 * e) ≤ 3 * (n + i) - d :=
    Nat.le_of_dvd hresPos hpowDvdNat
  have hresAdd : (3 * (n + i) - d) + d = 3 * (n + i) :=
    Nat.sub_add_cancel (by omega)
  have hliftCeil : 6 * p ^ (2 * e) + 6 * d ≤ 18 * (n + i) := by
    nlinarith
  have hik : i ≤ k := (Finset.mem_Icc.mp hi.1).2
  have hindexCeil : 18 * (n + i) ≤ 18 * (n + 1) + 18 * (k - 1) := by
    omega
  have hratio : 18 * (n + 1) < 13 * k * d :=
    eighteen_mul_n_add_one_lt_thirteen_mul_k_mul_gap_of_four_solution hk heq
  have hstrict :
      6 * p ^ (2 * e) + 6 * d < 13 * k * d + 18 * (k - 1) :=
    lt_of_le_of_lt (hliftCeil.trans hindexCeil) (Nat.add_lt_add_right hratio _)
  have h6 : 6 ≤ 13 * k := by omega
  have hdominant' :
      13 * k * d + 18 * (k - 1) ≤ 6 * p ^ (2 * e) + 6 * d := by
    have hadd := Nat.add_le_add_right hdominant (6 * d)
    let A := 13 * k - 6
    have hA : A + 6 = 13 * k := by dsimp [A]; omega
    calc
      13 * k * d + 18 * (k - 1) =
          (A * d + 18 * (k - 1)) + 6 * d := by
            rw [← hA]
            ring
      _ = ((13 * k - 6) * d + 18 * (k - 1)) + 6 * d := by rfl
      _ ≤ 6 * p ^ (2 * e) + 6 * d := hadd
  exact (Nat.not_lt_of_ge hdominant') hstrict

/-- Positive necessary-condition form of the component exclusion. -/
theorem large_prime_gap_component_square_strict_upper_of_four_solution
    {p e k n d : ℕ}
    (hp : p.Prime) (he : 0 < e)
    (hk : 16 ≤ k) (hd : k ≤ d) (hkp : k ≤ p)
    (hpowDvd : p ^ e ∣ d)
    (heq : blockProduct k (n + d) = 4 * blockProduct k n) :
    6 * p ^ (2 * e) < (13 * k - 6) * d + 18 * (k - 1) := by
  exact Nat.lt_of_not_ge fun hdominant ↦
    no_four_solution_of_large_prime_gap_component_dominance
      hp he hk hd hkp hpowDvd hdominant heq

/-- A whole prime-power gap is excluded as soon as it is at least three
times the row length.  This includes exponent-one prime gaps with a
sufficiently large prime. -/
theorem no_four_solution_gap_eq_large_prime_power_of_three_k_le
    {p e k n d : ℕ}
    (hp : p.Prime) (he : 0 < e)
    (hk : 16 ≤ k) (hkp : k ≤ p)
    (hthree : 3 * k ≤ d)
    (hgap : d = p ^ e) :
    blockProduct k (n + d) ≠ 4 * blockProduct k n := by
  have h3pred : 3 * (k - 1) ≤ d := by omega
  have htail : 18 * (k - 1) ≤ 6 * d := by
    calc
      18 * (k - 1) = 6 * (3 * (k - 1)) := by ring
      _ ≤ 6 * d := Nat.mul_le_mul_left 6 h3pred
  have h6 : 6 ≤ 13 * k := by omega
  let A := 13 * k - 6
  have hA : A + 6 = 13 * k := by dsimp [A]; omega
  have hcombine : (13 * k - 6) * d + 6 * d = 13 * k * d := by
    change A * d + 6 * d = 13 * k * d
    rw [← hA]
    ring
  have h13 : 13 * k ≤ 6 * d := by nlinarith
  have hdominant :
      (13 * k - 6) * d + 18 * (k - 1) ≤ 6 * p ^ (2 * e) := by
    calc
      _ ≤ (13 * k - 6) * d + 6 * d :=
        Nat.add_le_add_left htail _
      _ = 13 * k * d := hcombine
      _ ≤ (6 * d) * d := Nat.mul_le_mul_right d h13
      _ = 6 * p ^ (2 * e) := by
        rw [hgap]
        calc
          (6 * p ^ e) * p ^ e = 6 * (p ^ e * p ^ e) := by ring
          _ = 6 * p ^ (e + e) := by rw [pow_add]
          _ = 6 * p ^ (2 * e) := by congr 2; omega
  exact no_four_solution_of_large_prime_gap_component_dominance
    hp he hk (by omega) hkp (by rw [hgap]) hdominant

/-- Every whole prime-power gap with exponent at least two satisfies the
dominance inequality automatically once its prime base exceeds the row
length. -/
theorem no_four_solution_gap_eq_large_prime_power_exponent_ge_two
    {p e k n d : ℕ}
    (hp : p.Prime) (he : 2 ≤ e)
    (hk : 16 ≤ k) (hkp : k ≤ p)
    (hgap : d = p ^ e) :
    blockProduct k (n + d) ≠ 4 * blockProduct k n := by
  have hp1 : 1 ≤ p := hp.one_le
  have hpSq : p ^ 2 ≤ p ^ e := Nat.pow_le_pow_right hp1 he
  have hkThree : 3 * k ≤ k ^ 2 := by nlinarith
  have hkSq : k ^ 2 ≤ p ^ 2 := Nat.pow_le_pow_left hkp 2
  have hthree : 3 * k ≤ p ^ 2 := hkThree.trans hkSq
  have hthreeD : 3 * k ≤ d := by omega
  exact no_four_solution_gap_eq_large_prime_power_of_three_k_le
    hp (by omega) hk hkp hthreeD hgap

#print axioms thirteen_k_add_eighteen_pow_lt_four_mul_thirteen_k_pow
#print axioms eighteen_mul_n_add_one_lt_thirteen_mul_k_mul_gap_of_four_solution
#print axioms no_four_solution_of_large_prime_gap_component_dominance
#print axioms large_prime_gap_component_square_strict_upper_of_four_solution
#print axioms no_four_solution_gap_eq_large_prime_power_of_three_k_le
#print axioms no_four_solution_gap_eq_large_prime_power_exponent_ge_two

end Erdos686Variant
end Erdos686
