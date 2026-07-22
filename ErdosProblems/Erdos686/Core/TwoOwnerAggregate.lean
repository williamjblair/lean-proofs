/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import ErdosProblems.Erdos686.Core.GlobalResidualTwoPrime

/-!
# Erdős 686: aggregate closure for at most two cleaned residual owners

This module does not alter either audited dependency.  It replaces the
two-prime-support loss `59049^2` by the exact all-prime row budget `G_k`,
sharpens the second obstruction from `10^30` to `10^16`, and cancels the
owner coefficient in the cubic branch through

`gcd(P,b) | 3|i-j|` and `gcd(Q,a) | 3|i-j|`.

Frozen dependency SHAs:

* `Erdos686GlobalResidualConcentration.lean =
  495981605282c4a1963f95bdce0788b4baba6cfa05c8be00b8c57154f49f9e24`;
* `Erdos686GlobalResidualTwoPrime.lean =
  ca1a59a8e3cef454d9255a8fd70dff3d7c516492bd4c379b097e711ef24c060d`.
-/

namespace Erdos686
namespace Erdos686Variant

/-- Product of every possible prime-power loss in a target row. -/
def targetAggregateLoss : ℕ → ℕ
  | 5 => 108
  | 7 => 1620
  | 9 => 136080
  | 11 => 1224720
  | 13 => 242494560
  | 15 => 18914575680
  | _ => 1

/-- Exact aggregate loss table for the six target rows. -/
theorem targetAggregateLoss_table :
    targetAggregateLoss 5 = 108 ∧
    targetAggregateLoss 7 = 1620 ∧
    targetAggregateLoss 9 = 136080 ∧
    targetAggregateLoss 11 = 1224720 ∧
    targetAggregateLoss 13 = 242494560 ∧
    targetAggregateLoss 15 = 18914575680 := by
  norm_num [targetAggregateLoss]

/-- Exact uniform ceiling for either cleaned second obstruction. -/
def aggregateSecondObstructionBound : ℕ := 10 ^ 16

/-- The coefficient arithmetic behind the `10^16` obstruction ceiling. -/
theorem aggregate_second_obstruction_abs_lt
    {C D delta : ℤ} {t g A : ℕ}
    (hgpos : 0 < g)
    (hA : A ≤ 35)
    (ht : t < A ^ 2 * g ^ 2)
    (hC : Int.natAbs C < 10 ^ 12)
    (hD : Int.natAbs D < 10 ^ 12)
    (hdelta : Int.natAbs delta < 15) :
    Int.natAbs (3 * (C * (t : ℤ) + 4 * D * (g : ℤ) ^ 2 * delta)) <
      aggregateSecondObstructionBound * g ^ 2 := by
  have hA2 : A ^ 2 ≤ 35 ^ 2 := Nat.pow_le_pow_left hA 2
  have ht' : t < 35 ^ 2 * g ^ 2 :=
    lt_of_lt_of_le ht (Nat.mul_le_mul_right (g ^ 2) hA2)
  have htri := Int.natAbs_add_le (C * (t : ℤ))
    (4 * D * (g : ℤ) ^ 2 * delta)
  have htri' :
      Int.natAbs (C * (t : ℤ) + 4 * D * (g : ℤ) ^ 2 * delta) ≤
        Int.natAbs C * t + 4 * Int.natAbs D * g ^ 2 * Int.natAbs delta := by
    simpa [Int.natAbs_mul, Int.natAbs_pow] using htri
  have hct : Int.natAbs C * t < 10 ^ 12 * (35 ^ 2 * g ^ 2) :=
    Nat.mul_lt_mul_of_le_of_lt (Nat.le_of_lt hC) ht' (by norm_num)
  have hdg : 4 * Int.natAbs D * g ^ 2 * Int.natAbs delta ≤
      4 * 10 ^ 12 * g ^ 2 * 15 := by
    exact Nat.mul_le_mul
      (Nat.mul_le_mul
        (Nat.mul_le_mul (by omega : 4 ≤ 4) (Nat.le_of_lt hD))
        (le_rfl : g ^ 2 ≤ g ^ 2))
      (Nat.le_of_lt hdelta)
  have hinside :
      Int.natAbs (C * (t : ℤ) + 4 * D * (g : ℤ) ^ 2 * delta) <
        (10 ^ 12 * 35 ^ 2 + 4 * 10 ^ 12 * 15) * g ^ 2 := by
    calc
      Int.natAbs (C * (t : ℤ) + 4 * D * (g : ℤ) ^ 2 * delta) ≤
          Int.natAbs C * t + 4 * Int.natAbs D * g ^ 2 * Int.natAbs delta := htri'
      _ < 10 ^ 12 * (35 ^ 2 * g ^ 2) +
          4 * 10 ^ 12 * g ^ 2 * 15 := Nat.add_lt_add_of_lt_of_le hct hdg
      _ = (10 ^ 12 * 35 ^ 2 + 4 * 10 ^ 12 * 15) * g ^ 2 := by ring
  have hthree :
      Int.natAbs (3 * (C * (t : ℤ) + 4 * D * (g : ℤ) ^ 2 * delta)) =
        3 * Int.natAbs (C * (t : ℤ) + 4 * D * (g : ℤ) ^ 2 * delta) := by
    simp [Int.natAbs_mul]
  rw [hthree]
  have hmul := Nat.mul_lt_mul_of_pos_left hinside (by norm_num : 0 < 3)
  dsimp [aggregateSecondObstructionBound]
  have hg2pos : 0 < g ^ 2 := pow_pos hgpos _
  nlinarith

/-- A divisor of `K*b` can be moved from `b` to any multiple of `gcd(m,b)`. -/
theorem dvd_scaled_of_dvd_mul_of_gcd_dvd
    {m b K D : ℕ}
    (hmul : m ∣ K * b)
    (hgcd : Nat.gcd m b ∣ D) :
    m ∣ K * D := by
  have hmul' : m ∣ b * K := by simpa [Nat.mul_comm] using hmul
  have hcore : m ∣ Nat.gcd m b * K := dvd_gcd_mul_of_dvd_mul hmul'
  have hscale : Nat.gcd m b * K ∣ D * K :=
    mul_dvd_mul hgcd (dvd_refl K)
  have htrans := dvd_trans hcore hscale
  simpa [Nat.mul_comm] using htrans

/-- The Pell identity controls the common factor of the left owner and the
opposite local coefficient. -/
theorem pell_left_gcd_dvd_three_natAbs
    {P Q a b : ℕ} {delta : ℤ}
    (hPell : (a : ℤ) * (P : ℤ) ^ 2 - (b : ℤ) * (Q : ℤ) ^ 2 =
      3 * delta) :
    Nat.gcd P b ∣ 3 * Int.natAbs delta := by
  have hgP : ((Nat.gcd P b : ℕ) : ℤ) ∣ (P : ℤ) := by
    exact_mod_cast Nat.gcd_dvd_left P b
  have hgb : ((Nat.gcd P b : ℕ) : ℤ) ∣ (b : ℤ) := by
    exact_mod_cast Nat.gcd_dvd_right P b
  have hleft : ((Nat.gcd P b : ℕ) : ℤ) ∣
      (a : ℤ) * (P : ℤ) ^ 2 := by
    simpa [pow_two] using
      dvd_mul_of_dvd_right (dvd_mul_of_dvd_right hgP (P : ℤ)) (a : ℤ)
  have hright : ((Nat.gcd P b : ℕ) : ℤ) ∣
      (b : ℤ) * (Q : ℤ) ^ 2 :=
    dvd_mul_of_dvd_left hgb ((Q : ℤ) ^ 2)
  have hdiff := dvd_sub hleft hright
  rw [hPell] at hdiff
  have habs := Int.natAbs_dvd_natAbs.mpr hdiff
  simpa [Int.natAbs_mul] using habs

/-- Symmetric Pell-gcd control for the right owner. -/
theorem pell_right_gcd_dvd_three_natAbs
    {P Q a b : ℕ} {delta : ℤ}
    (hPell : (a : ℤ) * (P : ℤ) ^ 2 - (b : ℤ) * (Q : ℤ) ^ 2 =
      3 * delta) :
    Nat.gcd Q a ∣ 3 * Int.natAbs delta := by
  have hga : ((Nat.gcd Q a : ℕ) : ℤ) ∣ (a : ℤ) := by
    exact_mod_cast Nat.gcd_dvd_right Q a
  have hgQ : ((Nat.gcd Q a : ℕ) : ℤ) ∣ (Q : ℤ) := by
    exact_mod_cast Nat.gcd_dvd_left Q a
  have hleft : ((Nat.gcd Q a : ℕ) : ℤ) ∣
      (a : ℤ) * (P : ℤ) ^ 2 :=
    dvd_mul_of_dvd_left hga ((P : ℤ) ^ 2)
  have hright : ((Nat.gcd Q a : ℕ) : ℤ) ∣
      (b : ℤ) * (Q : ℤ) ^ 2 := by
    simpa [pow_two] using
      dvd_mul_of_dvd_right (dvd_mul_of_dvd_right hgQ (Q : ℤ)) (b : ℤ)
  have hdiff := dvd_sub hleft hright
  rw [hPell] at hdiff
  have habs := Int.natAbs_dvd_natAbs.mpr hdiff
  simpa [Int.natAbs_mul] using habs

/-- Gcd-refined cubic consequence when one cleaned second obstruction is zero. -/
theorem clean_third_zero_component_dvd_refined
    {P Q a b g : ℕ} {C D E delta : ℤ}
    (hPpos : 0 < P)
    (hgpos : 0 < g)
    (hbpos : 0 < b)
    (hcop : P.Coprime Q)
    (hPell : (a : ℤ) * (P : ℤ) ^ 2 - (b : ℤ) * (Q : ℤ) ^ 2 =
      3 * delta)
    (hSecond : (P : ℤ) ∣
      3 * C * (a : ℤ) - 4 * D * ((g * Q : ℕ) : ℤ) ^ 2)
    (hThird : (P : ℤ) ^ 2 ∣
      -3 * (3 * C * (a : ℤ) - 4 * D * ((g * Q : ℕ) : ℤ) ^ 2) +
        20 * E * (P : ℤ) * ((g * Q : ℕ) : ℤ) ^ 3)
    (hzero : C * (a * b : ℕ) + 4 * D * (g : ℤ) ^ 2 * delta = 0) :
    P ∣ 60 * Int.natAbs delta * Int.natAbs E * g ^ 3 := by
  have hraw : P ∣ 20 * Int.natAbs E * b * g ^ 3 :=
    clean_third_zero_component_dvd hPpos hgpos hbpos hcop hPell
      hSecond hThird hzero
  have hraw' : P ∣ (20 * Int.natAbs E * g ^ 3) * b := by
    simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hraw
  have hgcd : Nat.gcd P b ∣ 3 * Int.natAbs delta :=
    pell_left_gcd_dvd_three_natAbs hPell
  have hcancel := dvd_scaled_of_dvd_mul_of_gcd_dvd hraw' hgcd
  convert hcancel using 1 <;> ring

private theorem aggregate_gap_lt_of_nonzero_second_obstruction
    {P Q g A b : ℕ} {L : ℤ}
    (hQpos : 0 < Q)
    (hgpos : 0 < g)
    (hbpos : 0 < b)
    (hbRatio : b * Q < A * (g * P))
    (hdiv : (P : ℤ) ∣ L)
    (hLne : L ≠ 0)
    (hLbound : Int.natAbs L < aggregateSecondObstructionBound * g ^ 2) :
    g * P * Q < A * aggregateSecondObstructionBound ^ 2 * g ^ 6 := by
  have hPle : P ≤ Int.natAbs L := by
    simpa using Int.natAbs_le_of_dvd_ne_zero hdiv hLne
  have hPB : P < aggregateSecondObstructionBound * g ^ 2 :=
    lt_of_le_of_lt hPle hLbound
  have hQbQ : Q ≤ b * Q := by nlinarith
  have hQAP : Q < A * (g * P) := lt_of_le_of_lt hQbQ hbRatio
  have hApos : 0 < A := by
    have htarget : 0 < A * (g * P) :=
      lt_trans (Nat.mul_pos hbpos hQpos) hbRatio
    apply Nat.pos_of_ne_zero
    intro hA
    rw [hA, zero_mul] at htarget
    exact (Nat.lt_irrefl 0) htarget
  have hQBound : Q < A * (g * (aggregateSecondObstructionBound * g ^ 2)) := by
    exact lt_trans hQAP (Nat.mul_lt_mul_of_pos_left
      (Nat.mul_lt_mul_of_pos_left hPB hgpos) hApos)
  calc
    g * P * Q < g * (aggregateSecondObstructionBound * g ^ 2) * Q := by
      exact Nat.mul_lt_mul_of_pos_right
        (Nat.mul_lt_mul_of_pos_left hPB hgpos) hQpos
    _ < g * (aggregateSecondObstructionBound * g ^ 2) *
        (A * (g * (aggregateSecondObstructionBound * g ^ 2))) :=
      Nat.mul_lt_mul_of_pos_left hQBound
        (Nat.mul_pos hgpos (Nat.mul_pos (by norm_num [aggregateSecondObstructionBound])
          (pow_pos hgpos _)))
    _ = A * aggregateSecondObstructionBound ^ 2 * g ^ 6 := by ring

private lemma aggregate_one_owner_numeric_cutoff
    {k A g : ℕ}
    (hk : k = 5 ∨ k = 7 ∨ k = 9 ∨ k = 11 ∨ k = 13 ∨ k = 15)
    (hA : A ≤ 35)
    (hg : g ≤ targetAggregateLoss k) :
    A * g ^ 2 < 10 ^ 120 := by
  calc
    A * g ^ 2 ≤ 35 * targetAggregateLoss k ^ 2 :=
      Nat.mul_le_mul hA (Nat.pow_le_pow_left hg 2)
    _ < 10 ^ 120 := by
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
        norm_num [targetAggregateLoss]

private lemma aggregate_generic_numeric_cutoff
    {k A g : ℕ}
    (hk : k = 5 ∨ k = 7 ∨ k = 9 ∨ k = 11 ∨ k = 13 ∨ k = 15)
    (hA : A ≤ 35)
    (hg : g ≤ targetAggregateLoss k) :
    A * aggregateSecondObstructionBound ^ 2 * g ^ 6 < 10 ^ 120 := by
  calc
    A * aggregateSecondObstructionBound ^ 2 * g ^ 6 ≤
        35 * aggregateSecondObstructionBound ^ 2 * targetAggregateLoss k ^ 6 :=
      Nat.mul_le_mul
        (Nat.mul_le_mul hA
          (le_rfl : aggregateSecondObstructionBound ^ 2 ≤
            aggregateSecondObstructionBound ^ 2))
        (Nat.pow_le_pow_left hg 6)
    _ < 10 ^ 120 := by
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
        norm_num [aggregateSecondObstructionBound, targetAggregateLoss]

private lemma aggregate_third_numeric_cutoff
    {k g : ℕ}
    (hk : k = 5 ∨ k = 7 ∨ k = 9 ∨ k = 11 ∨ k = 13 ∨ k = 15)
    (hg : g ≤ targetAggregateLoss k) :
    3600 * 15 ^ 2 * (10 ^ 12) ^ 2 * g ^ 7 < 10 ^ 120 := by
  calc
    3600 * 15 ^ 2 * (10 ^ 12) ^ 2 * g ^ 7 ≤
        3600 * 15 ^ 2 * (10 ^ 12) ^ 2 * targetAggregateLoss k ^ 7 :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hg 7)
    _ < 10 ^ 120 := by
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
        norm_num [targetAggregateLoss]

/-- Abstract closure for two distinct cleaned owner buckets under the exact
all-prime row loss budget.  The hypotheses before the four local divisibility
statements are the grouped global data; the divisibility statements are the
audited second and third local lifts. -/
theorem two_owner_abstract_buckets_below_cutoff
    {k A P Q g i j a b : ℕ}
    (hk : k = 5 ∨ k = 7 ∨ k = 9 ∨ k = 11 ∨ k = 13 ∨ k = 15)
    (hi : i ∈ Finset.Icc 1 k)
    (hj : j ∈ Finset.Icc 1 k)
    (hij : i ≠ j)
    (hA : A ≤ 35)
    (hPpos : 0 < P)
    (hQpos : 0 < Q)
    (hgpos : 0 < g)
    (hapos : 0 < a)
    (hbpos : 0 < b)
    (hcop : P.Coprime Q)
    (hg : g ≤ targetAggregateLoss k)
    (haRatio : a * P < A * (g * Q))
    (hbRatio : b * Q < A * (g * P))
    (hab : a * b < A ^ 2 * g ^ 2)
    (hPell : (a : ℤ) * (P : ℤ) ^ 2 - (b : ℤ) * (Q : ℤ) ^ 2 =
      3 * ((i : ℤ) - (j : ℤ)))
    (hPSecond : (P : ℤ) ∣
      3 * localSecondConstant k i * (a : ℤ) -
        4 * localSecondLinear k i * ((g * Q : ℕ) : ℤ) ^ 2)
    (hQSecond : (Q : ℤ) ∣
      3 * localSecondConstant k j * (b : ℤ) -
        4 * localSecondLinear k j * ((g * P : ℕ) : ℤ) ^ 2)
    (hPThird : (P : ℤ) ^ 2 ∣
      -3 * (3 * localSecondConstant k i * (a : ℤ) -
        4 * localSecondLinear k i * ((g * Q : ℕ) : ℤ) ^ 2) +
      20 * localThirdQuadratic k i * (P : ℤ) * ((g * Q : ℕ) : ℤ) ^ 3)
    (hQThird : (Q : ℤ) ^ 2 ∣
      -3 * (3 * localSecondConstant k j * (b : ℤ) -
        4 * localSecondLinear k j * ((g * P : ℕ) : ℤ) ^ 2) +
      20 * localThirdQuadratic k j * (Q : ℤ) * ((g * P : ℕ) : ℤ) ^ 3) :
    g * P * Q < 10 ^ 120 := by
  let delta : ℤ := (i : ℤ) - (j : ℤ)
  let L : ℤ := 3 *
    (localSecondConstant k i * (a * b : ℕ) +
      4 * localSecondLinear k i * (g : ℤ) ^ 2 * delta)
  let R : ℤ := 3 *
    (localSecondConstant k j * (a * b : ℕ) -
      4 * localSecondLinear k j * (g : ℤ) ^ 2 * delta)
  have hobs := clean_second_obstruction_divisibilities
    hPSecond hQSecond (by simpa [delta] using hPell)
  have hPObs : (P : ℤ) ∣ L := by simpa [L, delta] using hobs.1
  have hQObs : (Q : ℤ) ∣ R := by simpa [R, delta] using hobs.2
  obtain ⟨hCi, hDi, hEi, hEine⟩ := target_local_taylor_bounds hk hi
  obtain ⟨hCj, hDj, hEj, hEjne⟩ := target_local_taylor_bounds hk hj
  have hdeltaEq : Int.natAbs delta = Nat.dist i j := by
    rcases le_total i j with hij' | hji'
    · have heq : delta = -((j - i : ℕ) : ℤ) := by
        dsimp [delta]
        push_cast
        omega
      rw [heq, Int.natAbs_neg, Int.natAbs_natCast,
        Nat.dist_eq_sub_of_le hij']
    · have heq : delta = ((i - j : ℕ) : ℤ) := by
        dsimp [delta]
        push_cast
        omega
      rw [heq, Int.natAbs_natCast,
        Nat.dist_eq_sub_of_le_right hji']
  have hdelta : Int.natAbs delta < 15 := by
    rw [hdeltaEq]
    have hi1 := (Finset.mem_Icc.mp hi).1
    have hj1 := (Finset.mem_Icc.mp hj).1
    have hi' := (Finset.mem_Icc.mp hi).2
    have hj' := (Finset.mem_Icc.mp hj).2
    rcases le_total i j with hij' | hji'
    · rw [Nat.dist_eq_sub_of_le hij']
      omega
    · rw [Nat.dist_eq_sub_of_le_right hji']
      omega
  have hdeltaNe : delta ≠ 0 := by
    dsimp [delta]
    intro hzero
    apply hij
    exact_mod_cast (sub_eq_zero.mp hzero)
  have hdeltaPos : 0 < Int.natAbs delta := Int.natAbs_pos.mpr hdeltaNe
  have hLbound : Int.natAbs L < aggregateSecondObstructionBound * g ^ 2 := by
    dsimp [L]
    exact aggregate_second_obstruction_abs_lt hgpos hA hab hCi hDi hdelta
  have hRbound : Int.natAbs R < aggregateSecondObstructionBound * g ^ 2 := by
    dsimp [R]
    have hnegD : Int.natAbs (-localSecondLinear k j) =
        Int.natAbs (localSecondLinear k j) := Int.natAbs_neg _
    have h := aggregate_second_obstruction_abs_lt
      (C := localSecondConstant k j) (D := -localSecondLinear k j)
      (delta := delta) hgpos hA hab hCj (by simpa [hnegD] using hDj) hdelta
    convert h using 1 <;> push_cast <;> ring
  by_cases hLne : L ≠ 0
  · exact lt_trans
      (aggregate_gap_lt_of_nonzero_second_obstruction hQpos hgpos hbpos
        hbRatio hPObs hLne hLbound)
      (aggregate_generic_numeric_cutoff hk hA hg)
  by_cases hRne : R ≠ 0
  · have hsmall := aggregate_gap_lt_of_nonzero_second_obstruction
      hPpos hgpos hapos haRatio hQObs hRne hRbound
    have hreorder : g * P * Q = g * Q * P := by ring
    rw [hreorder]
    exact lt_trans hsmall (aggregate_generic_numeric_cutoff hk hA hg)
  have hLzero :
      localSecondConstant k i * (a * b : ℕ) +
        4 * localSecondLinear k i * (g : ℤ) ^ 2 * delta = 0 := by
    dsimp [L] at hLne
    by_contra hne
    exact hLne (mul_ne_zero (by norm_num) hne)
  have hRzero :
      localSecondConstant k j * (a * b : ℕ) -
        4 * localSecondLinear k j * (g : ℤ) ^ 2 * delta = 0 := by
    dsimp [R] at hRne
    by_contra hne
    exact hRne (mul_ne_zero (by norm_num) hne)
  have hPsmallDvd : P ∣
      60 * Int.natAbs delta * Int.natAbs (localThirdQuadratic k i) * g ^ 3 :=
    clean_third_zero_component_dvd_refined hPpos hgpos hbpos hcop
      (by simpa [delta] using hPell) hPSecond hPThird hLzero
  have hQsmallDvd : Q ∣
      60 * Int.natAbs delta * Int.natAbs (localThirdQuadratic k j) * g ^ 3 := by
    have hswapPell :
        (b : ℤ) * (Q : ℤ) ^ 2 - (a : ℤ) * (P : ℤ) ^ 2 =
          3 * (-delta) := by
      calc
        (b : ℤ) * (Q : ℤ) ^ 2 - (a : ℤ) * (P : ℤ) ^ 2 =
            -((a : ℤ) * (P : ℤ) ^ 2 - (b : ℤ) * (Q : ℤ) ^ 2) := by ring
        _ = -(3 * delta) := by simpa [delta] using congrArg Neg.neg hPell
        _ = 3 * (-delta) := by ring
    have h := clean_third_zero_component_dvd_refined
      (P := Q) (Q := P) (a := b) (b := a) (g := g)
      (C := localSecondConstant k j) (D := localSecondLinear k j)
      (E := localThirdQuadratic k j) (delta := -delta)
      hQpos hgpos hapos hcop.symm hswapPell hQSecond hQThird (by
        convert hRzero using 1 <;> push_cast <;> ring)
    simpa [Int.natAbs_neg] using h
  have hEiPos : 0 < Int.natAbs (localThirdQuadratic k i) :=
    Int.natAbs_pos.mpr hEine
  have hEjPos : 0 < Int.natAbs (localThirdQuadratic k j) :=
    Int.natAbs_pos.mpr hEjne
  have hPsmall : P ≤
      60 * Int.natAbs delta * Int.natAbs (localThirdQuadratic k i) * g ^ 3 :=
    Nat.le_of_dvd (by positivity) hPsmallDvd
  have hQsmall : Q ≤
      60 * Int.natAbs delta * Int.natAbs (localThirdQuadratic k j) * g ^ 3 :=
    Nat.le_of_dvd (by positivity) hQsmallDvd
  have hprodBound : g * P * Q ≤
      3600 * Int.natAbs delta ^ 2 *
        (Int.natAbs (localThirdQuadratic k i) *
          Int.natAbs (localThirdQuadratic k j)) * g ^ 7 := by
    calc
      g * P * Q ≤ g *
          (60 * Int.natAbs delta * Int.natAbs (localThirdQuadratic k i) * g ^ 3) *
          (60 * Int.natAbs delta * Int.natAbs (localThirdQuadratic k j) * g ^ 3) :=
        Nat.mul_le_mul (Nat.mul_le_mul (le_rfl : g ≤ g) hPsmall) hQsmall
      _ = 3600 * Int.natAbs delta ^ 2 *
          (Int.natAbs (localThirdQuadratic k i) *
            Int.natAbs (localThirdQuadratic k j)) * g ^ 7 := by ring
  have hdelta2 : Int.natAbs delta ^ 2 ≤ 15 ^ 2 :=
    Nat.pow_le_pow_left (Nat.le_of_lt hdelta) 2
  have hEprod : Int.natAbs (localThirdQuadratic k i) *
      Int.natAbs (localThirdQuadratic k j) ≤ (10 ^ 12) ^ 2 := by
    exact Nat.mul_le_mul (Nat.le_of_lt hEi) (Nat.le_of_lt hEj)
  have hcoeff :
      3600 * Int.natAbs delta ^ 2 *
          (Int.natAbs (localThirdQuadratic k i) *
            Int.natAbs (localThirdQuadratic k j)) ≤
        3600 * 15 ^ 2 * (10 ^ 12) ^ 2 :=
    Nat.mul_le_mul (Nat.mul_le_mul (le_rfl : 3600 ≤ 3600) hdelta2) hEprod
  have hthirdBound : g * P * Q ≤
      3600 * 15 ^ 2 * (10 ^ 12) ^ 2 * g ^ 7 := by
    exact le_trans hprodBound (Nat.mul_le_mul_right (g ^ 7) hcoeff)
  exact lt_of_le_of_lt hthirdBound (aggregate_third_numeric_cutoff hk hg)

/-- Equation-level grouped decomposition.  This is the exact interface a
finite prime-owner grouping argument must produce: all cleaned mass is in the
coprime buckets `P,Q`, the remaining loss is `g ≤ G_k`, and each bucket has
its factor and square at its owner residual.  `P=1` or `Q=1` covers zero or
one nontrivial owner bucket. -/
def HasAtMostTwoGlobalResidualOwners (k n d : ℕ) : Prop :=
  ∃ g P Q i j : ℕ,
    d = g * P * Q ∧
    0 < g ∧ 0 < P ∧ 0 < Q ∧
    P.Coprime Q ∧
    g ≤ targetAggregateLoss k ∧
    i ∈ Finset.Icc 1 k ∧ j ∈ Finset.Icc 1 k ∧
    P ∣ n + i ∧ Q ∣ n + j ∧
    P ^ 2 ∣ localResidual n d i ∧
    Q ^ 2 ∣ localResidual n d j

/-- Complete equation-level closure once the finite global prime components
have been grouped into at most two owner buckets.  Unlike the abstract theorem
above, this wrapper derives positivity, coefficient bounds, the Pell identity,
and both local lifts directly from the exact block equation. -/
theorem grouped_two_owner_equation_below_cutoff
    {k n d C A g P Q i j : ℕ}
    (hk : k = 5 ∨ k = 7 ∨ k = 9 ∨ k = 11 ∨ k = 13 ∨ k = 15)
    (heq : blockProduct k (n + d) = 4 * blockProduct k n)
    (hbase : n + 1 < C * d)
    (hA : A = 3 * C + 2)
    (hA35 : A ≤ 35)
    (hgap : d = g * P * Q)
    (hgpos : 0 < g)
    (hPpos : 0 < P)
    (hQpos : 0 < Q)
    (hcop : P.Coprime Q)
    (hg : g ≤ targetAggregateLoss k)
    (hi : i ∈ Finset.Icc 1 k)
    (hj : j ∈ Finset.Icc 1 k)
    (hPFactor : P ∣ n + i)
    (hQFactor : Q ∣ n + j)
    (hPSquare : P ^ 2 ∣ localResidual n d i)
    (hQSquare : Q ^ 2 ∣ localResidual n d j) :
    d < 10 ^ 120 := by
  have hk5 : 5 ≤ k := by
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> omega
  have hk15 : k ≤ 15 := by
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> omega
  by_contra hnot
  have hlarge : 10 ^ 120 ≤ d := Nat.le_of_not_gt hnot
  have hkd : k ≤ d := by omega
  obtain ⟨hXiPos, hXiUpper⟩ :=
    localResidual_pos_lt_of_base_bound hk5 hkd hi heq hbase hA
  obtain ⟨hXjPos, hXjUpper⟩ :=
    localResidual_pos_lt_of_base_bound hk5 hkd hj heq hbase hA
  by_cases hij : i = j
  · subst j
    have hcopSq : (P ^ 2).Coprime (Q ^ 2) := Nat.Coprime.pow 2 2 hcop
    have hboth : P ^ 2 * Q ^ 2 ∣ localResidual n d i :=
      hcopSq.mul_dvd_of_dvd_of_dvd hPSquare hQSquare
    have hPQSq : (P * Q) ^ 2 ∣ localResidual n d i := by
      convert hboth using 1 <;> ring
    have hPQpos : 0 < P * Q := Nat.mul_pos hPpos hQpos
    have hsqLe : (P * Q) ^ 2 ≤ localResidual n d i :=
      Nat.le_of_dvd hXiPos hPQSq
    have hHlt : P * Q < A * g := by
      apply (Nat.mul_lt_mul_right hPQpos).mp
      calc
        (P * Q) * (P * Q) = (P * Q) ^ 2 := by ring
        _ ≤ localResidual n d i := hsqLe
        _ < A * d := hXiUpper
        _ = (A * g) * (P * Q) := by rw [hgap]; ring
    have hdSmall : d < A * g ^ 2 := by
      rw [hgap]
      calc
        g * P * Q = g * (P * Q) := by ring
        _ < g * (A * g) := Nat.mul_lt_mul_of_pos_left hHlt hgpos
        _ = A * g ^ 2 := by ring
    exact hnot (lt_trans hdSmall (aggregate_one_owner_numeric_cutoff hk hA35 hg))
  · have hgapP : d = P * (g * Q) := by rw [hgap]; ring
    have hgapQ : d = Q * (g * P) := by rw [hgap]; ring
    obtain ⟨a, hapos, haeq, haRatio⟩ :=
      exists_positive_local_coefficient hPpos hgapP hXiPos hXiUpper hPSquare
    obtain ⟨b, hbpos, hbeq, hbRatio⟩ :=
      exists_positive_local_coefficient hQpos hgapQ hXjPos hXjUpper hQSquare
    have hAgPos : 0 < A * g := by
      have htarget : 0 < A * (g * Q) :=
        lt_trans (Nat.mul_pos hapos hPpos) haRatio
      have hApos : 0 < A := by
        apply Nat.pos_of_ne_zero
        intro hAzero
        rw [hAzero, zero_mul] at htarget
        exact (Nat.lt_irrefl 0) htarget
      exact Nat.mul_pos hApos hgpos
    have haRatio' : a * P < (A * g) * Q := by
      simpa [mul_assoc] using haRatio
    have hbRatio' : b * Q < (A * g) * P := by
      simpa [mul_assoc] using hbRatio
    have hab' := coefficient_product_lt hbpos hPpos hQpos hAgPos
      haRatio' hbRatio'
    have hab : a * b < A ^ 2 * g ^ 2 := by
      simpa [Nat.mul_pow] using hab'
    have hXiCast : ((localResidual n d i : ℕ) : ℤ) =
        3 * ((n + i : ℕ) : ℤ) - (d : ℤ) := by
      unfold localResidual
      rw [Int.ofNat_sub (by
        unfold localResidual at hXiPos
        omega)]
      push_cast
      ring
    have hXjCast : ((localResidual n d j : ℕ) : ℤ) =
        3 * ((n + j : ℕ) : ℤ) - (d : ℤ) := by
      unfold localResidual
      rw [Int.ofNat_sub (by
        unfold localResidual at hXjPos
        omega)]
      push_cast
      ring
    have hresP : 3 * ((n + i : ℕ) : ℤ) - (d : ℤ) =
        (a : ℤ) * (P : ℤ) ^ 2 := by
      rw [← hXiCast, haeq]
      push_cast
      ring
    have hresQ : 3 * ((n + j : ℕ) : ℤ) - (d : ℤ) =
        (b : ℤ) * (Q : ℤ) ^ 2 := by
      rw [← hXjCast, hbeq]
      push_cast
      ring
    have hPell : (a : ℤ) * (P : ℤ) ^ 2 - (b : ℤ) * (Q : ℤ) ^ 2 =
        3 * ((i : ℤ) - (j : ℤ)) := by
      calc
        (a : ℤ) * (P : ℤ) ^ 2 - (b : ℤ) * (Q : ℤ) ^ 2 =
            (localResidual n d i : ℤ) - (localResidual n d j : ℤ) := by
              rw [haeq, hbeq]
              push_cast
              ring
        _ = 3 * ((i : ℤ) - (j : ℤ)) := by
          rw [hXiCast, hXjCast]
          push_cast
          ring
    have hPSecond := second_order_local_lift hi hPpos hgapP hPFactor hresP heq
    have hQSecond := second_order_local_lift hj hQpos hgapQ hQFactor hresQ heq
    have hPThird := third_order_local_lift hi hPpos hgapP hPFactor hresP heq
    have hQThird := third_order_local_lift hj hQpos hgapQ hQFactor hresQ heq
    have hsmall := two_owner_abstract_buckets_below_cutoff hk hi hj hij hA35
      hPpos hQpos hgpos hapos hbpos hcop hg haRatio hbRatio hab hPell
      hPSecond hQSecond hPThird hQThird
    apply hnot
    simpa [hgap] using hsmall

/-- Direct consequence for a solution equipped with an at-most-two-owner
grouped decomposition. -/
theorem atMostTwoGlobalResidualOwners_below_cutoff
    {k n d C A : ℕ}
    (hk : k = 5 ∨ k = 7 ∨ k = 9 ∨ k = 11 ∨ k = 13 ∨ k = 15)
    (heq : blockProduct k (n + d) = 4 * blockProduct k n)
    (hbase : n + 1 < C * d)
    (hA : A = 3 * C + 2)
    (hA35 : A ≤ 35)
    (howners : HasAtMostTwoGlobalResidualOwners k n d) :
    d < 10 ^ 120 := by
  rcases howners with
    ⟨g, P, Q, i, j, hgap, hgpos, hPpos, hQpos, hcop, hg, hi, hj,
      hPFactor, hQFactor, hPSquare, hQSquare⟩
  exact grouped_two_owner_equation_below_cutoff hk heq hbase hA hA35 hgap
    hgpos hPpos hQpos hcop hg hi hj hPFactor hQFactor hPSquare hQSquare

end Erdos686Variant
end Erdos686
