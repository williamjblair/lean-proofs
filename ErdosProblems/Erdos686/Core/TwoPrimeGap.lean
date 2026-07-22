/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import ErdosProblems.Erdos686.Core.PadicLift

/-!
# Two-prime-support consequences for Erdős 686

This module combines valuation concentration with the exact quadratic and
cubic local lifts.  It does not solve the remaining Pell-type equations.  Its
main unconditional consequence is that a target-size odd-tail solution whose
gap has exactly two prime divisors must concentrate the two primary components
at two distinct noncentral lower factors.
-/

namespace Erdos686
namespace Erdos686Variant

/-- The positive local residual appearing in the exact Taylor lift. -/
def localResidual (n d i : ℕ) : ℕ := 3 * (n + i) - d

/-- Uniform archimedean control of the exact local residual. -/
lemma localResidual_pos_lt_of_base_bound
    {k n d i C A : ℕ}
    (hk5 : 5 ≤ k)
    (hkd : k ≤ d)
    (hi : i ∈ Finset.Icc 1 k)
    (heq : blockProduct k (n + d) = 4 * blockProduct k n)
    (hbase : n + 1 < C * d)
    (hA : A = 3 * C + 2) :
    0 < localResidual n d i ∧ localResidual n d i < A * d := by
  have hgap := twice_gap_lt_n_of_four_solution hk5 hkd heq
  have hdlt : d < 3 * (n + i) := by omega
  have hi_d : i ≤ d := le_trans (Finset.mem_Icc.mp hi).2 hkd
  have hnCd : n < C * d := by omega
  have h3n : 3 * n < 3 * (C * d) :=
    (Nat.mul_lt_mul_left (by norm_num : 0 < 3)).mpr hnCd
  have h3i : 3 * i ≤ 3 * d := Nat.mul_le_mul_left 3 hi_d
  have hsum : 3 * (n + i) < (3 * C + 3) * d := by
    calc
      3 * (n + i) = 3 * n + 3 * i := by ring
      _ ≤ 3 * n + 3 * d := Nat.add_le_add_left h3i (3 * n)
      _ < 3 * (C * d) + 3 * d := Nat.add_lt_add_right h3n (3 * d)
      _ = (3 * C + 3) * d := by ring
  have hsumA : 3 * (n + i) < (A + 1) * d := by
    simpa [hA] using hsum
  constructor
  · unfold localResidual
    omega
  · unfold localResidual
    have hAd : A * d + d = (A + 1) * d := by ring
    omega

/-- The uncancelled quadratic lift gives a square bound for any divisor
concentrated in one lower factor. -/
theorem local_raw_square_lt_factorial_mul
    {h k n d i C A : ℕ}
    (hk5 : 5 ≤ k)
    (hkd : k ≤ d)
    (hi : i ∈ Finset.Icc 1 k)
    (heq : blockProduct k (n + d) = 4 * blockProduct k n)
    (hbase : n + 1 < C * d)
    (hA : A = 3 * C + 2)
    (hd : h ∣ d)
    (hfactor : h ∣ n + i) :
    h ^ 2 < (k - 1).factorial * A * d := by
  obtain ⟨hXpos, hXupper⟩ :=
    localResidual_pos_lt_of_base_bound hk5 hkd hi heq hbase hA
  have hdlt : d < 3 * (n + i) := by
    unfold localResidual at hXpos
    omega
  have hcast : ((localResidual n d i : ℕ) : ℤ) =
      3 * ((n + i : ℕ) : ℤ) - (d : ℤ) := by
    unfold localResidual
    rw [Int.ofNat_sub (by omega : d ≤ 3 * (n + i))]
    push_cast
    ring
  have hraw := localBlockCoefficientNat_mul_three_factor_sub_gap_dvd_sq
    hi hd hfactor heq
  rw [← hcast] at hraw
  have hrawNat : h ^ 2 ∣
      localBlockCoefficientNat k i * localResidual n d i := by
    exact Int.natCast_dvd_natCast.mp (by
      simpa [Nat.cast_pow, Nat.cast_mul] using hraw)
  have hcoeffPos : 0 < localBlockCoefficientNat k i := by
    unfold localBlockCoefficientNat
    exact Nat.mul_pos (Nat.factorial_pos _) (Nat.factorial_pos _)
  have hcoeffDvd : localBlockCoefficientNat k i ∣ (k - 1).factorial :=
    localBlockCoefficientNat_dvd_factorial_pred hi
  have hcoeffLe : localBlockCoefficientNat k i ≤ (k - 1).factorial :=
    Nat.le_of_dvd (Nat.factorial_pos _) hcoeffDvd
  have hsqLe : h ^ 2 ≤
      localBlockCoefficientNat k i * localResidual n d i :=
    Nat.le_of_dvd (Nat.mul_pos hcoeffPos hXpos) hrawNat
  calc
    h ^ 2 ≤ localBlockCoefficientNat k i * localResidual n d i := hsqLe
    _ ≤ (k - 1).factorial * localResidual n d i :=
      Nat.mul_le_mul_right (localResidual n d i) hcoeffLe
    _ < (k - 1).factorial * (A * d) :=
      (Nat.mul_lt_mul_left (Nat.factorial_pos _)).mpr hXupper
    _ = (k - 1).factorial * A * d := by ring

/-- At the middle factor, the uncancelled cubic lift gives a cubic bound. -/
theorem center_raw_cube_lt_factorial_sq_mul
    {h r n d C A : ℕ}
    (hr2 : 2 ≤ r)
    (hkd : 2 * r + 1 ≤ d)
    (heq : blockProduct (2 * r + 1) (n + d) =
      4 * blockProduct (2 * r + 1) n)
    (hbase : n + 1 < C * d)
    (hA : A = 3 * C + 2)
    (hd : h ∣ d)
    (hcenter : h ∣ n + r + 1) :
    h ^ 3 < r.factorial ^ 2 * A * d := by
  have hi : r + 1 ∈ Finset.Icc 1 (2 * r + 1) := by
    simp only [Finset.mem_Icc]
    omega
  obtain ⟨hXpos, hXupper⟩ :=
    localResidual_pos_lt_of_base_bound (by omega : 5 ≤ 2 * r + 1)
      hkd hi heq hbase hA
  have hdlt : d < 3 * (n + (r + 1)) := by
    unfold localResidual at hXpos
    omega
  have hcast : ((localResidual n d (r + 1) : ℕ) : ℤ) =
      3 * ((n + r + 1 : ℕ) : ℤ) - (d : ℤ) := by
    unfold localResidual
    rw [Int.ofNat_sub (by omega : d ≤ 3 * (n + (r + 1)))]
    push_cast
    ring
  have hraw := center_factorial_sq_mul_three_factor_sub_gap_dvd_cube
    hd hcenter heq
  rw [← hcast] at hraw
  have hrawNat : h ^ 3 ∣
      r.factorial ^ 2 * localResidual n d (r + 1) := by
    exact Int.natCast_dvd_natCast.mp (by
      simpa [Nat.cast_pow, Nat.cast_mul] using hraw)
  have hcoeffPos : 0 < r.factorial ^ 2 := pow_pos (Nat.factorial_pos _) _
  have hcubeLe : h ^ 3 ≤
      r.factorial ^ 2 * localResidual n d (r + 1) :=
    Nat.le_of_dvd (Nat.mul_pos hcoeffPos hXpos) hrawNat
  calc
    h ^ 3 ≤ r.factorial ^ 2 * localResidual n d (r + 1) := hcubeLe
    _ < r.factorial ^ 2 * (A * d) :=
      (Nat.mul_lt_mul_left hcoeffPos).mpr hXupper
    _ = r.factorial ^ 2 * A * d := by ring

/-- Mixed-gap version of valuation concentration: a primary component of the
gap loses at most one exponent (for the multiplier `3`) and the valuation of
`(k-1)!` before landing in one lower factor. -/
theorem primePower_component_exists_concentrated_factor
    {p e k n d : ℕ}
    (hp : p.Prime)
    (hk : 1 ≤ k)
    (hd : p ^ e ∣ d)
    (heq : blockProduct k (n + d) = 4 * blockProduct k n) :
    ∃ i, i ∈ Finset.Icc 1 k ∧
      p ^ (e - 1 - (k - 1).factorial.factorization p) ∣ n + i := by
  have hblock0 : blockProduct k n ≠ 0 := by
    unfold blockProduct
    apply Finset.prod_ne_zero_iff.mpr
    intro i hi
    have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
    omega
  have hthreeBlock0 : 3 * blockProduct k n ≠ 0 :=
    mul_ne_zero (by norm_num) hblock0
  have hpow : p ^ e ∣ 3 * blockProduct k n :=
    dvd_trans hd (gap_dvd_three_blockProduct heq)
  have heVal : e ≤ (3 * blockProduct k n).factorization p :=
    (hp.pow_dvd_iff_le_factorization hthreeBlock0).mp hpow
  have hthreeVal : (3 : ℕ).factorization p ≤ 1 := by
    by_cases hp3 : p = 3
    · subst p
      norm_num
    · have hpNotDvdThree : ¬ p ∣ 3 := by
        intro hdiv
        rcases (Nat.dvd_prime (by norm_num : Nat.Prime 3)).mp hdiv with hp1 | hp3'
        · exact hp.ne_one hp1
        · exact hp3 hp3'
      rw [Nat.factorization_eq_zero_of_not_dvd hpNotDvdThree]
      omega
  obtain ⟨i, hi, hconcentrated⟩ :=
    exists_blockProduct_factorization_concentration hp hk (n := n)
  have hfactorVal :
      e - 1 - (k - 1).factorial.factorization p ≤
        (n + i).factorization p := by
    rw [Nat.factorization_mul (by norm_num : 3 ≠ 0) hblock0,
      Finsupp.add_apply] at heVal
    omega
  have hfactor0 : n + i ≠ 0 := by
    have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
    omega
  refine ⟨i, hi, ?_⟩
  exact (hp.pow_dvd_iff_le_factorization hfactor0).mpr hfactorVal

/-- For a prime below a block of length at most fifteen, the exact
concentration loss is at most `4096 = 2^(1+v₂(14!))`. -/
lemma small_prime_factorial_loss_le_4096
    {p k : ℕ}
    (hp : p.Prime)
    (hk5 : 5 ≤ k)
    (hk15 : k ≤ 15)
    (hpk : p < k) :
    p ^ (1 + (k - 1).factorial.factorization p) ≤ 4096 := by
  have hkPred14 : k - 1 ≤ 14 := by omega
  have hfacDvd : (k - 1).factorial ∣ (14 : ℕ).factorial :=
    Nat.factorial_dvd_factorial hkPred14
  have hfacLe : (k - 1).factorial.factorization p ≤
      (14 : ℕ).factorial.factorization p :=
    ((Nat.factorization_le_iff_dvd
      (Nat.factorial_ne_zero _) (Nat.factorial_ne_zero _)).mpr hfacDvd) p
  have hp13 : p ≤ 13 := by
    have hp14 : p ≤ 14 := by omega
    by_contra hnot
    have hpEq : p = 14 := by omega
    subst p
    norm_num at hp
  have hpCases : p = 2 ∨ p = 3 ∨ p = 5 ∨ p = 7 ∨ p = 11 ∨ p = 13 := by
    interval_cases p <;> norm_num at hp
    all_goals simp
  rcases hpCases with rfl | rfl | rfl | rfl | rfl | rfl
  · have hval : ((14 : ℕ).factorial).factorization 2 = 11 := by
      rw [Nat.factorization_factorial (by norm_num : Nat.Prime 2)
        (show Nat.log 2 14 < 4 by norm_num)]
      norm_num [Finset.sum_Ico_succ_top]
    rw [hval] at hfacLe
    calc
      2 ^ (1 + (k - 1).factorial.factorization 2) ≤ 2 ^ 12 :=
        Nat.pow_le_pow_right (by norm_num) (by omega)
      _ = 4096 := by norm_num
  · have hval : ((14 : ℕ).factorial).factorization 3 = 5 := by
      rw [Nat.factorization_factorial (by norm_num : Nat.Prime 3)
        (show Nat.log 3 14 < 3 by norm_num)]
      norm_num [Finset.sum_Ico_succ_top]
    rw [hval] at hfacLe
    calc
      3 ^ (1 + (k - 1).factorial.factorization 3) ≤ 3 ^ 6 :=
        Nat.pow_le_pow_right (by norm_num) (by omega)
      _ ≤ 4096 := by norm_num
  · have hcoarse := Nat.factorization_factorial_le_div_pred
      (by norm_num : Nat.Prime 5) (k - 1)
    calc
      5 ^ (1 + (k - 1).factorial.factorization 5) ≤ 5 ^ 4 :=
        Nat.pow_le_pow_right (by norm_num) (by omega)
      _ ≤ 4096 := by norm_num
  · have hcoarse := Nat.factorization_factorial_le_div_pred
      (by norm_num : Nat.Prime 7) (k - 1)
    calc
      7 ^ (1 + (k - 1).factorial.factorization 7) ≤ 7 ^ 3 :=
        Nat.pow_le_pow_right (by norm_num) (by omega)
      _ ≤ 4096 := by norm_num
  · have hcoarse := Nat.factorization_factorial_le_div_pred
      (by norm_num : Nat.Prime 11) (k - 1)
    calc
      11 ^ (1 + (k - 1).factorial.factorization 11) ≤ 11 ^ 2 :=
        Nat.pow_le_pow_right (by norm_num) (by omega)
      _ ≤ 4096 := by norm_num
  · have hcoarse := Nat.factorization_factorial_le_div_pred
      (by norm_num : Nat.Prime 13) (k - 1)
    calc
      13 ^ (1 + (k - 1).factorial.factorization 13) ≤ 13 ^ 2 :=
        Nat.pow_le_pow_right (by norm_num) (by omega)
      _ ≤ 4096 := by norm_num

/-- Every primary component of a target odd-tail gap has a divisor, losing by
at most a factor `4096`, concentrated in one lower factor.  For `p ≥ k` the
chosen exponent is the full exponent; for `p < k` it is the valuation-
concentration exponent. -/
theorem primePower_component_exists_large_local_divisor
    {p e k n d : ℕ}
    (hp : p.Prime)
    (he : 0 < e)
    (hk5 : 5 ≤ k)
    (hk15 : k ≤ 15)
    (hd : p ^ e ∣ d)
    (heq : blockProduct k (n + d) = 4 * blockProduct k n) :
    ∃ i t, i ∈ Finset.Icc 1 k ∧
      p ^ t ∣ p ^ e ∧ p ^ t ∣ d ∧ p ^ t ∣ n + i ∧
      p ^ e ≤ 4096 * p ^ t := by
  by_cases hkp : k ≤ p
  · obtain ⟨i, hi, _huniq⟩ := gap_primePower_existsUnique_local_sq_lift
      hp he (by omega : 4 ≤ k) hkp hd heq
    refine ⟨i, e, hi.1, dvd_rfl, hd, hi.2.1, ?_⟩
    exact Nat.le_mul_of_pos_left (p ^ e) (by norm_num)
  · have hpk : p < k := by omega
    let V : ℕ := (k - 1).factorial.factorization p
    let t : ℕ := e - 1 - V
    obtain ⟨i, hi, hfactor⟩ :=
      primePower_component_exists_concentrated_factor
        hp (by omega : 1 ≤ k) hd heq
    have hte : t ≤ e := by
      dsimp [t]
      omega
    have htDvd : p ^ t ∣ p ^ e := pow_dvd_pow p hte
    have htFactor : p ^ t ∣ n + i := by
      simpa [t, V] using hfactor
    have hLoss4096 : p ^ (1 + V) ≤ 4096 := by
      simpa [V] using small_prime_factorial_loss_le_4096 hp hk5 hk15 hpk
    have hExpLoss : e - t ≤ 1 + V := by
      dsimp [t]
      omega
    have hPowLoss : p ^ (e - t) ≤ p ^ (1 + V) :=
      Nat.pow_le_pow_right hp.pos hExpLoss
    have hdecomp : p ^ e = p ^ t * p ^ (e - t) := by
      rw [← pow_add]
      congr 1
      omega
    refine ⟨i, t, hi, htDvd, dvd_trans htDvd hd, htFactor, ?_⟩
    rw [hdecomp]
    calc
      p ^ t * p ^ (e - t) ≤ p ^ t * p ^ (1 + V) :=
        Nat.mul_le_mul_left (p ^ t) hPowLoss
      _ ≤ p ^ t * 4096 := Nat.mul_le_mul_left (p ^ t) hLoss4096
      _ = 4096 * p ^ t := by ring

/-- If both concentrated components occupy one factor, the raw square lift
gives an absolute gap bound. -/
lemma gap_lt_of_same_concentration_bucket
    {d L h F A : ℕ}
    (hdpos : 0 < d)
    (hLpos : 0 < L)
    (hdle : d ≤ L * h)
    (hsquare : h ^ 2 < F * A * d) :
    d < L ^ 2 * F * A := by
  have hdd : d * d ≤ (L * h) * (L * h) := Nat.mul_le_mul hdle hdle
  have hLsqPos : 0 < L ^ 2 := pow_pos hLpos _
  have hscaled : L ^ 2 * h ^ 2 < L ^ 2 * (F * A * d) :=
    Nat.mul_lt_mul_of_pos_left hsquare hLsqPos
  have hmain : d * d < (L ^ 2 * F * A) * d := by
    calc
      d * d ≤ (L * h) * (L * h) := hdd
      _ = L ^ 2 * h ^ 2 := by ring
      _ < L ^ 2 * (F * A * d) := hscaled
      _ = (L ^ 2 * F * A) * d := by ring
  exact (Nat.mul_lt_mul_right hdpos).mp hmain

/-- If one concentrated component occupies the middle factor and the other
occupies a different factor, combining the cubic and square lifts gives an
absolute gap bound. -/
lemma gap_lt_of_center_and_other_concentration
    {d L hc ho R F A : ℕ}
    (hdpos : 0 < d)
    (hLpos : 0 < L)
    (hhcpos : 0 < hc)
    (hhopos : 0 < ho)
    (hdle : d ≤ L * hc * ho)
    (hcube : hc ^ 3 < R * A * d)
    (hsquare : ho ^ 2 < F * A * d) :
    d < L ^ 6 * R ^ 2 * F ^ 3 * A ^ 5 := by
  have hc6 : hc ^ 6 < (R * A * d) ^ 2 := by
    have hpow := Nat.pow_lt_pow_left hcube (by norm_num : 2 ≠ 0)
    simpa [← pow_mul] using hpow
  have ho6 : ho ^ 6 < (F * A * d) ^ 3 := by
    have hpow := Nat.pow_lt_pow_left hsquare (by norm_num : 3 ≠ 0)
    simpa [← pow_mul] using hpow
  have hUpos : 0 < (R * A * d) ^ 2 := lt_trans (pow_pos hhcpos 6) hc6
  have hho6pos : 0 < ho ^ 6 := pow_pos hhopos _
  have hprod : hc ^ 6 * ho ^ 6 <
      (R * A * d) ^ 2 * (F * A * d) ^ 3 := by
    calc
      hc ^ 6 * ho ^ 6 < (R * A * d) ^ 2 * ho ^ 6 :=
        Nat.mul_lt_mul_of_pos_right hc6 hho6pos
      _ < (R * A * d) ^ 2 * (F * A * d) ^ 3 :=
        Nat.mul_lt_mul_of_pos_left ho6 hUpos
  have hd6 : d ^ 6 ≤ (L * hc * ho) ^ 6 := Nat.pow_le_pow_left hdle 6
  have hL6pos : 0 < L ^ 6 := pow_pos hLpos _
  have hmain : d ^ 6 <
      (L ^ 6 * R ^ 2 * F ^ 3 * A ^ 5) * d ^ 5 := by
    calc
      d ^ 6 ≤ (L * hc * ho) ^ 6 := hd6
      _ = L ^ 6 * (hc ^ 6 * ho ^ 6) := by ring
      _ < L ^ 6 *
          ((R * A * d) ^ 2 * (F * A * d) ^ 3) :=
        Nat.mul_lt_mul_of_pos_left hprod hL6pos
      _ = (L ^ 6 * R ^ 2 * F ^ 3 * A ^ 5) * d ^ 5 := by ring
  have hd5pos : 0 < d ^ 5 := pow_pos hdpos _
  apply (Nat.mul_lt_mul_right hd5pos).mp
  convert hmain using 1 <;> ring

/-- The product of the two per-prime concentration losses. -/
def twoPrimeConcentrationLoss : ℕ := 4096 ^ 2

/-- Convert an integral local lift to divisibility of the positive natural
residual. -/
lemma nat_pow_dvd_localResidual_of_int_lift
    {u t n d i : ℕ}
    (hpos : 0 < localResidual n d i)
    (hlift : ((u : ℤ) ^ t) ∣
      3 * ((n + i : ℕ) : ℤ) - (d : ℤ)) :
    u ^ t ∣ localResidual n d i := by
  have hdlt : d < 3 * (n + i) := by
    unfold localResidual at hpos
    omega
  have hcast : ((localResidual n d i : ℕ) : ℤ) =
      3 * ((n + i : ℕ) : ℤ) - (d : ℤ) := by
    unfold localResidual
    rw [Int.ofNat_sub (by omega : d ≤ 3 * (n + i))]
    push_cast
    ring
  exact Int.natCast_dvd_natCast.mp (by
    rw [hcast]
    simpa [Nat.cast_pow] using hlift)

/-- A square divisor of the bounded positive residual produces a positive
integer coefficient and the sharp ratio bound used in the Pell reduction. -/
lemma exists_positive_local_coefficient
    {u v n d i A : ℕ}
    (hupos : 0 < u)
    (hgap : d = u * v)
    (hXpos : 0 < localResidual n d i)
    (hXupper : localResidual n d i < A * d)
    (hsquare : u ^ 2 ∣ localResidual n d i) :
    ∃ a, 0 < a ∧ localResidual n d i = a * u ^ 2 ∧
      a * u < A * v := by
  rcases hsquare with ⟨a, ha⟩
  have hapos : 0 < a := by
    by_contra hnot
    have ha0 : a = 0 := by omega
    subst a
    simp at ha
    omega
  have haeq : localResidual n d i = a * u ^ 2 := by
    rw [ha]
    ring
  have haratio : a * u < A * v := by
    apply (Nat.mul_lt_mul_left hupos).mp
    calc
      u * (a * u) = a * u ^ 2 := by ring
      _ = localResidual n d i := haeq.symm
      _ < A * d := hXupper
      _ = u * (A * v) := by rw [hgap]; ring
  exact ⟨a, hapos, haeq, haratio⟩

/-- Multiplying the two sharp ratio bounds leaves only finitely many
coefficient pairs, independently of the sizes of the two prime powers. -/
lemma coefficient_product_lt
    {a b u v A : ℕ}
    (hbpos : 0 < b)
    (hupos : 0 < u)
    (hvpos : 0 < v)
    (hApos : 0 < A)
    (hau : a * u < A * v)
    (hbv : b * v < A * u) :
    a * b < A ^ 2 := by
  have hbvp : 0 < b * v := Nat.mul_pos hbpos hvpos
  have hAvpos : 0 < A * v := Nat.mul_pos hApos hvpos
  have hprod : (a * u) * (b * v) < (A * v) * (A * u) := by
    calc
      (a * u) * (b * v) < (A * v) * (b * v) :=
        Nat.mul_lt_mul_of_pos_right hau hbvp
      _ < (A * v) * (A * u) :=
        Nat.mul_lt_mul_of_pos_left hbv hAvpos
  have huvpos : 0 < u * v := Nat.mul_pos hupos hvpos
  apply (Nat.mul_lt_mul_right huvpos).mp
  convert hprod using 1 <;> ring

/-- Clean two-large-prime Pell reduction.  If `d = p^e q^f` with both
primes at least the block length, the two full primary components produce
positive coefficients with product `< A²` and an exact bounded-right-hand-
side Pell equation.  Equal localization indices and center localization at a
target-size gap are eliminated elementarily; no Pell or prime-power theorem
is assumed. -/
theorem two_large_prime_support_bounded_pell
    {p q e f r n d C A : ℕ}
    (hp : p.Prime)
    (hq : q.Prime)
    (hpq : p ≠ q)
    (he : 0 < e)
    (hf : 0 < f)
    (hr2 : 2 ≤ r)
    (hpk : 2 * r + 1 ≤ p)
    (hqk : 2 * r + 1 ≤ q)
    (hkd : 2 * r + 1 ≤ d)
    (hgap : d = p ^ e * q ^ f)
    (heq : blockProduct (2 * r + 1) (n + d) =
      4 * blockProduct (2 * r + 1) n)
    (hbase : n + 1 < C * d)
    (hA : A = 3 * C + 2)
    (hAk : A < (2 * r + 1) ^ 2) :
    ∃ i j a b,
      i ∈ Finset.Icc 1 (2 * r + 1) ∧
      j ∈ Finset.Icc 1 (2 * r + 1) ∧
      i ≠ j ∧
      0 < a ∧ 0 < b ∧
      localResidual n d i = a * (p ^ e) ^ 2 ∧
      localResidual n d j = b * (q ^ f) ^ 2 ∧
      a * p ^ e < A * q ^ f ∧
      b * q ^ f < A * p ^ e ∧
      a * b < A ^ 2 ∧
      ((a * (p ^ e) ^ 2 : ℕ) : ℤ) -
          ((b * (q ^ f) ^ 2 : ℕ) : ℤ) =
        3 * ((i : ℤ) - (j : ℤ)) ∧
      (i = r + 1 →
        (p ^ e) ^ 3 ∣ localResidual n d i ∧ d < A ^ 5) ∧
      (j = r + 1 →
        (q ^ f) ^ 3 ∣ localResidual n d j ∧ d < A ^ 5) := by
  have hk5 : 5 ≤ 2 * r + 1 := by omega
  have hpDvd : p ^ e ∣ d := by
    rw [hgap]
    exact dvd_mul_right _ _
  have hqDvd : q ^ f ∣ d := by
    rw [hgap]
    exact dvd_mul_left _ _
  obtain ⟨i, hip, _huniqP⟩ := gap_primePower_existsUnique_local_sq_lift
    hp he (by omega : 4 ≤ 2 * r + 1) hpk hpDvd heq
  obtain ⟨j, hiq, _huniqQ⟩ := gap_primePower_existsUnique_local_sq_lift
    hq hf (by omega : 4 ≤ 2 * r + 1) hqk hqDvd heq
  obtain ⟨hXiPos, hXiUpper⟩ := localResidual_pos_lt_of_base_bound
    hk5 hkd hip.1 heq hbase hA
  obtain ⟨hXjPos, hXjUpper⟩ := localResidual_pos_lt_of_base_bound
    hk5 hkd hiq.1 heq hbase hA
  have hpSqDvd : (p ^ e) ^ 2 ∣ localResidual n d i :=
    nat_pow_dvd_localResidual_of_int_lift hXiPos hip.2.2
  have hqSqDvd : (q ^ f) ^ 2 ∣ localResidual n d j :=
    nat_pow_dvd_localResidual_of_int_lift hXjPos hiq.2.2
  have hpPowPos : 0 < p ^ e := pow_pos hp.pos _
  have hqPowPos : 0 < q ^ f := pow_pos hq.pos _
  have hApos : 0 < A := by omega
  have hdpos : 0 < d := by rw [hgap]; exact Nat.mul_pos hpPowPos hqPowPos
  obtain ⟨a, hapos, haeq, haratio⟩ := exists_positive_local_coefficient
    hpPowPos hgap hXiPos hXiUpper hpSqDvd
  obtain ⟨b, hbpos, hbeq, hbratio⟩ := exists_positive_local_coefficient
    hqPowPos (by simpa [mul_comm] using hgap) hXjPos hXjUpper hqSqDvd
  have hab : a * b < A ^ 2 :=
    coefficient_product_lt hbpos hpPowPos hqPowPos hApos haratio hbratio
  have hpSize : (p ^ e) ^ 2 < A * d :=
    lt_of_le_of_lt (Nat.le_of_dvd hXiPos hpSqDvd) hXiUpper
  have hqSize : (q ^ f) ^ 2 < A * d :=
    lt_of_le_of_lt (Nat.le_of_dvd hXjPos hqSqDvd) hXjUpper
  have hneq : i ≠ j := by
    intro hij
    have hqSqAtI : (q ^ f) ^ 2 ∣ localResidual n d i := by
      simpa [hij] using hqSqDvd
    have hcop : Nat.Coprime (p ^ e) (q ^ f) :=
      Nat.coprime_pow_primes e f hp hq hpq
    have hcopSq : Nat.Coprime ((p ^ e) ^ 2) ((q ^ f) ^ 2) :=
      hcop.pow 2 2
    have hprodDvd : (p ^ e) ^ 2 * (q ^ f) ^ 2 ∣
        localResidual n d i :=
      hcopSq.mul_dvd_of_dvd_of_dvd hpSqDvd hqSqAtI
    have hdSqDvd : d ^ 2 ∣ localResidual n d i := by
      have hdSqEq : d ^ 2 = (p ^ e) ^ 2 * (q ^ f) ^ 2 := by
        rw [hgap]
        ring
      rw [hdSqEq]
      exact hprodDvd
    have hdSqLe : d ^ 2 ≤ localResidual n d i :=
      Nat.le_of_dvd hXiPos hdSqDvd
    have hdd : d * d < A * d := by
      calc
        d * d = d ^ 2 := by ring
        _ ≤ localResidual n d i := hdSqLe
        _ < A * d := hXiUpper
    have hdA : d < A := (Nat.mul_lt_mul_right hdpos).mp hdd
    have hpBaseLe : p ≤ p ^ e := by
      simpa using Nat.pow_le_pow_right hp.pos (by omega : 1 ≤ e)
    have hqBaseLe : q ≤ q ^ f := by
      simpa using Nat.pow_le_pow_right hq.pos (by omega : 1 ≤ f)
    have hkSqD : (2 * r + 1) ^ 2 ≤ d := by
      calc
        (2 * r + 1) ^ 2 = (2 * r + 1) * (2 * r + 1) := by ring
        _ ≤ p * q := Nat.mul_le_mul hpk hqk
        _ ≤ p ^ e * q ^ f := Nat.mul_le_mul hpBaseLe hqBaseLe
        _ = d := hgap.symm
    omega
  have hpCenter : i = r + 1 →
      (p ^ e) ^ 3 ∣ localResidual n d i ∧ d < A ^ 5 := by
    intro hic
    have hpCenterFactor : p ^ e ∣ n + r + 1 := by
      simpa [hic, Nat.add_assoc] using hip.2.1
    have hpCubeInt := primePower_cube_dvd_three_center_sub_gap
      hp hpk hpDvd hpCenterFactor heq
    have hpCubeDvd : (p ^ e) ^ 3 ∣ localResidual n d i := by
      subst i
      exact nat_pow_dvd_localResidual_of_int_lift hXiPos hpCubeInt
    have hpCubeSize : (p ^ e) ^ 3 < A * d :=
      lt_of_le_of_lt (Nat.le_of_dvd hXiPos hpCubeDvd) hXiUpper
    have hdle : d ≤ 1 * (p ^ e) * (q ^ f) := by simp [hgap]
    have hsmall := gap_lt_of_center_and_other_concentration
      (L := 1) (R := 1) (F := 1)
      hdpos (by norm_num) hpPowPos hqPowPos hdle
      (by simpa using hpCubeSize) (by simpa using hqSize)
    exact ⟨hpCubeDvd, by simpa using hsmall⟩
  have hqCenter : j = r + 1 →
      (q ^ f) ^ 3 ∣ localResidual n d j ∧ d < A ^ 5 := by
    intro hjc
    have hqCenterFactor : q ^ f ∣ n + r + 1 := by
      simpa [hjc, Nat.add_assoc] using hiq.2.1
    have hqCubeInt := primePower_cube_dvd_three_center_sub_gap
      hq hqk hqDvd hqCenterFactor heq
    have hqCubeDvd : (q ^ f) ^ 3 ∣ localResidual n d j := by
      subst j
      exact nat_pow_dvd_localResidual_of_int_lift hXjPos hqCubeInt
    have hqCubeSize : (q ^ f) ^ 3 < A * d :=
      lt_of_le_of_lt (Nat.le_of_dvd hXjPos hqCubeDvd) hXjUpper
    have hdle : d ≤ 1 * (q ^ f) * (p ^ e) := by simp [hgap, mul_comm]
    have hsmall := gap_lt_of_center_and_other_concentration
      (L := 1) (R := 1) (F := 1)
      hdpos (by norm_num) hqPowPos hpPowPos hdle
      (by simpa using hqCubeSize) (by simpa using hpSize)
    exact ⟨hqCubeDvd, by simpa using hsmall⟩
  have hXiCast : ((localResidual n d i : ℕ) : ℤ) =
      3 * ((n + i : ℕ) : ℤ) - (d : ℤ) := by
    unfold localResidual
    rw [Int.ofNat_sub (by
      unfold localResidual at hXiPos
      omega : d ≤ 3 * (n + i))]
    push_cast
    ring
  have hXjCast : ((localResidual n d j : ℕ) : ℤ) =
      3 * ((n + j : ℕ) : ℤ) - (d : ℤ) := by
    unfold localResidual
    rw [Int.ofNat_sub (by
      unfold localResidual at hXjPos
      omega : d ≤ 3 * (n + j))]
    push_cast
    ring
  have hPell : ((a * (p ^ e) ^ 2 : ℕ) : ℤ) -
        ((b * (q ^ f) ^ 2 : ℕ) : ℤ) =
      3 * ((i : ℤ) - (j : ℤ)) := by
    calc
      ((a * (p ^ e) ^ 2 : ℕ) : ℤ) -
          ((b * (q ^ f) ^ 2 : ℕ) : ℤ) =
          (localResidual n d i : ℤ) - (localResidual n d j : ℤ) := by
            rw [haeq, hbeq]
      _ = (3 * ((n + i : ℕ) : ℤ) - (d : ℤ)) -
          (3 * ((n + j : ℕ) : ℤ) - (d : ℤ)) := by
            rw [hXiCast, hXjCast]
      _ = 3 * ((i : ℤ) - (j : ℤ)) := by
        push_cast
        ring
  exact ⟨i, j, a, b, hip.1, hiq.1, hneq, hapos, hbpos,
    haeq, hbeq, haratio, hbratio, hab, hPell, hpCenter, hqCenter⟩

/-- A target-size odd-tail solution with exactly two prime divisors must put
large concentrated divisors of its two primary components at distinct,
noncentral lower factors.  The returned square bounds are the exact local
input to the residual finite-coefficient Pell equations.

This theorem allows either prime to be below the block length, including
`p = 2` or `p = 3`; the explicit `4096` loss handles those cases. -/
theorem two_prime_support_has_distinct_noncenter_concentrations
    {p q e f r n d C A : ℕ}
    (hp : p.Prime)
    (hq : q.Prime)
    (hpq : p ≠ q)
    (he : 0 < e)
    (hf : 0 < f)
    (hr2 : 2 ≤ r)
    (hk15 : 2 * r + 1 ≤ 15)
    (hgap : d = p ^ e * q ^ f)
    (hlarge : 10 ^ 120 ≤ d)
    (heq : blockProduct (2 * r + 1) (n + d) =
      4 * blockProduct (2 * r + 1) n)
    (hbase : n + 1 < C * d)
    (hA : A = 3 * C + 2)
    (hA35 : A ≤ 35) :
    ∃ i j ep eq,
      i ∈ Finset.Icc 1 (2 * r + 1) ∧
      j ∈ Finset.Icc 1 (2 * r + 1) ∧
      i ≠ j ∧ i ≠ r + 1 ∧ j ≠ r + 1 ∧
      p ^ ep ∣ p ^ e ∧ q ^ eq ∣ q ^ f ∧
      p ^ ep ∣ d ∧ q ^ eq ∣ d ∧
      p ^ ep ∣ n + i ∧ q ^ eq ∣ n + j ∧
      p ^ e ≤ 4096 * p ^ ep ∧ q ^ f ≤ 4096 * q ^ eq ∧
      (p ^ ep) ^ 2 < (2 * r).factorial * A * d ∧
      (q ^ eq) ^ 2 < (2 * r).factorial * A * d := by
  have hk5 : 5 ≤ 2 * r + 1 := by omega
  have hkd : 2 * r + 1 ≤ d := by
    have hnumeric : 15 < 10 ^ 120 := by norm_num
    omega
  have hpDvd : p ^ e ∣ d := by
    rw [hgap]
    exact dvd_mul_right _ _
  have hqDvd : q ^ f ∣ d := by
    rw [hgap]
    exact dvd_mul_left _ _
  obtain ⟨i, ep, hi, hepPow, hepDvd, hepFactor, hepLoss⟩ :=
    primePower_component_exists_large_local_divisor
      hp he hk5 hk15 hpDvd heq
  obtain ⟨j, eq, hj, heqPow, heqDvd, heqFactor, heqLoss⟩ :=
    primePower_component_exists_large_local_divisor
      hq hf hk5 hk15 hqDvd heq
  have hpPartPos : 0 < p ^ ep := pow_pos hp.pos _
  have hqPartPos : 0 < q ^ eq := pow_pos hq.pos _
  have hdpos : 0 < d := lt_of_lt_of_le (by norm_num : 0 < 10 ^ 120) hlarge
  have hFpos : 0 < (2 * r).factorial := Nat.factorial_pos _
  have hApos : 0 < A := by omega
  have hpSquare : (p ^ ep) ^ 2 < (2 * r).factorial * A * d := by
    simpa using local_raw_square_lt_factorial_mul
      hk5 hkd hi heq hbase hA hepDvd hepFactor
  have hqSquare : (q ^ eq) ^ 2 < (2 * r).factorial * A * d := by
    simpa using local_raw_square_lt_factorial_mul
      hk5 hkd hj heq hbase hA heqDvd heqFactor
  have hdConcentrated :
      d ≤ twoPrimeConcentrationLoss * (p ^ ep * q ^ eq) := by
    calc
      d = p ^ e * q ^ f := hgap
      _ ≤ (4096 * p ^ ep) * (4096 * q ^ eq) :=
        Nat.mul_le_mul hepLoss heqLoss
      _ = twoPrimeConcentrationLoss * (p ^ ep * q ^ eq) := by
        unfold twoPrimeConcentrationLoss
        ring
  have hLossPos : 0 < twoPrimeConcentrationLoss := by
    unfold twoPrimeConcentrationLoss
    norm_num
  have hF14 : (2 * r).factorial ≤ (14 : ℕ).factorial :=
    Nat.factorial_le (by omega)
  have hr7 : r ≤ 7 := by omega
  have hrFact7 : r.factorial ≤ (7 : ℕ).factorial := Nat.factorial_le hr7
  have hneq : i ≠ j := by
    intro hij
    have hcop : Nat.Coprime (p ^ ep) (q ^ eq) :=
      Nat.coprime_pow_primes ep eq hp hq hpq
    have hqFactorAtI : q ^ eq ∣ n + i := by simpa [hij] using heqFactor
    have hbucketFactor : p ^ ep * q ^ eq ∣ n + i :=
      hcop.mul_dvd_of_dvd_of_dvd hepFactor hqFactorAtI
    have hbucketDvd : p ^ ep * q ^ eq ∣ d := by
      rw [hgap]
      exact mul_dvd_mul hepPow heqPow
    have hbucketSquare : (p ^ ep * q ^ eq) ^ 2 <
        (2 * r).factorial * A * d :=
      local_raw_square_lt_factorial_mul
        hk5 hkd hi heq hbase hA hbucketDvd hbucketFactor
    have hsmall := gap_lt_of_same_concentration_bucket
      hdpos hLossPos hdConcentrated hbucketSquare
    have hmax : twoPrimeConcentrationLoss ^ 2 * (2 * r).factorial * A ≤
        twoPrimeConcentrationLoss ^ 2 * (14 : ℕ).factorial * 35 := by
      gcongr
    have hnumeric :
        twoPrimeConcentrationLoss ^ 2 * (14 : ℕ).factorial * 35 <
          10 ^ 120 := by
      unfold twoPrimeConcentrationLoss
      norm_num
    omega
  have hiCenter : i ≠ r + 1 := by
    intro hic
    have hpCenterFactor : p ^ ep ∣ n + r + 1 := by
      simpa [hic, Nat.add_assoc] using hepFactor
    have hpCube : (p ^ ep) ^ 3 < r.factorial ^ 2 * A * d :=
      center_raw_cube_lt_factorial_sq_mul
        hr2 hkd heq hbase hA hepDvd hpCenterFactor
    have hdConcentrated' :
        d ≤ twoPrimeConcentrationLoss * (p ^ ep) * (q ^ eq) := by
      simpa [mul_assoc] using hdConcentrated
    have hcenterSmall := gap_lt_of_center_and_other_concentration
      hdpos hLossPos hpPartPos hqPartPos hdConcentrated' hpCube hqSquare
    have hmax :
        twoPrimeConcentrationLoss ^ 6 * (r.factorial ^ 2) ^ 2 *
            (2 * r).factorial ^ 3 * A ^ 5 ≤
          twoPrimeConcentrationLoss ^ 6 * ((7 : ℕ).factorial ^ 2) ^ 2 *
            (14 : ℕ).factorial ^ 3 * 35 ^ 5 := by
      gcongr
    have hnumeric :
        twoPrimeConcentrationLoss ^ 6 * ((7 : ℕ).factorial ^ 2) ^ 2 *
            (14 : ℕ).factorial ^ 3 * 35 ^ 5 < 10 ^ 120 := by
      unfold twoPrimeConcentrationLoss
      norm_num
    omega
  have hjCenter : j ≠ r + 1 := by
    intro hjc
    have hqCenterFactor : q ^ eq ∣ n + r + 1 := by
      simpa [hjc, Nat.add_assoc] using heqFactor
    have hqCube : (q ^ eq) ^ 3 < r.factorial ^ 2 * A * d :=
      center_raw_cube_lt_factorial_sq_mul
        hr2 hkd heq hbase hA heqDvd hqCenterFactor
    have hdConcentrated' :
        d ≤ twoPrimeConcentrationLoss * (q ^ eq) * (p ^ ep) := by
      simpa [mul_assoc, mul_comm, mul_left_comm] using hdConcentrated
    have hcenterSmall := gap_lt_of_center_and_other_concentration
      hdpos hLossPos hqPartPos hpPartPos hdConcentrated' hqCube hpSquare
    have hmax :
        twoPrimeConcentrationLoss ^ 6 * (r.factorial ^ 2) ^ 2 *
            (2 * r).factorial ^ 3 * A ^ 5 ≤
          twoPrimeConcentrationLoss ^ 6 * ((7 : ℕ).factorial ^ 2) ^ 2 *
            (14 : ℕ).factorial ^ 3 * 35 ^ 5 := by
      gcongr
    have hnumeric :
        twoPrimeConcentrationLoss ^ 6 * ((7 : ℕ).factorial ^ 2) ^ 2 *
            (14 : ℕ).factorial ^ 3 * 35 ^ 5 < 10 ^ 120 := by
      unfold twoPrimeConcentrationLoss
      norm_num
    omega
  exact ⟨i, j, ep, eq, hi, hj, hneq, hiCenter, hjCenter,
    hepPow, heqPow, hepDvd, heqDvd, hepFactor, heqFactor,
    hepLoss, heqLoss, hpSquare, hqSquare⟩

end Erdos686Variant
end Erdos686
