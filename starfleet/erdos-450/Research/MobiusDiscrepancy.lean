import Research.PeriodicBounds
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Algebra.BigOperators.Field

namespace Erdos450

/-- LCM of the actual medium divisors; this is a far smaller common period than
`(2n)!` (though not asserted to be the least possible period). -/
def divisorPeriod (n : ℕ) : ℕ :=
  (Finset.Ioo n (2 * n)).lcm id

/-- The divisor-LCM period is positive, including when the indexing interval is
empty (whose LCM is one). -/
theorem divisorPeriod_pos (n : ℕ) : 0 < divisorPeriod n := by
  apply Nat.pos_of_ne_zero
  intro hzero
  rw [divisorPeriod, Finset.lcm_eq_zero_iff] at hzero
  obtain ⟨d, hdmem, hd0⟩ := hzero
  simp only [Finset.mem_Ioo] at hdmem
  dsimp at hd0
  omega

/-- Every medium divisor divides the divisor-LCM period. -/
theorem dvd_divisorPeriod {n d : ℕ} (hnd : n < d) (hd2 : d < 2 * n) :
    d ∣ divisorPeriod n := by
  apply Finset.dvd_lcm
  simpa only [Finset.mem_Ioo] using And.intro hnd hd2

/-- Exact 0/1 indicator, valued in the integers for Möbius inversion. -/
noncomputable def badIndicator (n m : ℕ) : ℤ := by
  classical
  exact if HasMediumDivisor n m then 1 else 0

/-- Möbius coefficient of the medium-divisor indicator on the divisor lattice. -/
noncomputable def mobiusCoeff (n q : ℕ) : ℤ :=
  ∑ x ∈ q.divisorsAntidiagonal,
    ArithmeticFunction.moebius x.1 * badIndicator n x.2

/-- Möbius inversion recovers the indicator from its coefficients. -/
theorem sum_mobiusCoeff_divisors (n g : ℕ) (hg : 0 < g) :
    (∑ q ∈ g.divisors, mobiusCoeff n q) = badIndicator n g := by
  apply (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq
      (f := mobiusCoeff n) (g := badIndicator n)).2
  · intro q hq
    rfl
  · exact hg

/-- Taking gcd with the common period preserves the bad-divisor predicate. -/
theorem hasMediumDivisor_gcd_divisorPeriod (n m : ℕ) :
    HasMediumDivisor n (Nat.gcd m (divisorPeriod n)) ↔
      HasMediumDivisor n m := by
  constructor
  · rintro ⟨d, hnd, hd2, hdg⟩
    exact ⟨d, hnd, hd2, dvd_trans hdg (Nat.gcd_dvd_left _ _)⟩
  · rintro ⟨d, hnd, hd2, hdm⟩
    exact ⟨d, hnd, hd2,
      (Nat.dvd_gcd_iff).2 ⟨hdm, dvd_divisorPeriod hnd hd2⟩⟩

/-- Expansion of the badness indicator as a signed sum of divisibility
indicators whose moduli divide the common period. -/
theorem badIndicator_eq_mobius_sum (n m : ℕ) :
    badIndicator n m =
      ∑ q ∈ (divisorPeriod n).divisors,
        if q ∣ m then mobiusCoeff n q else 0 := by
  classical
  let P := divisorPeriod n
  let g := Nat.gcd m P
  have hP : 0 < P := by simpa [P] using divisorPeriod_pos n
  have hg : 0 < g := Nat.gcd_pos_of_pos_right m hP
  have hsets : g.divisors = P.divisors.filter (fun q => q ∣ m) := by
    ext q
    constructor
    · intro hq
      have hqg : q ∣ Nat.gcd m P := by
        simpa only [g] using (Nat.mem_divisors.mp hq).1
      obtain ⟨hqm, hqP⟩ := (Nat.dvd_gcd_iff.mp hqg)
      exact Finset.mem_filter.mpr
        ⟨Nat.mem_divisors.mpr ⟨hqP, hP.ne'⟩, hqm⟩
    · intro hq
      obtain ⟨hqPmem, hqm⟩ := Finset.mem_filter.mp hq
      have hqP := (Nat.mem_divisors.mp hqPmem).1
      apply Nat.mem_divisors.mpr
      exact ⟨by simpa only [g] using Nat.dvd_gcd hqm hqP, hg.ne'⟩
  calc
    badIndicator n m = badIndicator n g := by
      simp only [badIndicator]
      rw [if_congr (hasMediumDivisor_gcd_divisorPeriod n m).symm rfl rfl]
    _ = ∑ q ∈ g.divisors, mobiusCoeff n q :=
      (sum_mobiusCoeff_divisors n g hg).symm
    _ = ∑ q ∈ P.divisors with q ∣ m, mobiusCoeff n q := by rw [← hsets]
    _ = ∑ q ∈ P.divisors, if q ∣ m then mobiusCoeff n q else 0 :=
      Finset.sum_filter _ _
    _ = ∑ q ∈ (divisorPeriod n).divisors,
          if q ∣ m then mobiusCoeff n q else 0 := by rfl

/-- Number of multiples of `q` in a half-open natural interval of length `l`. -/
def multipleCount (q x l : ℕ) : ℕ :=
  ((Finset.Ico x (x + l)).filter fun m => q ∣ m).card

/-- Divisibility by a positive modulus is periodic with that modulus. -/
theorem dvd_predicate_periodic (q : ℕ) :
    Function.Periodic (fun m : ℕ => q ∣ m) q := by
  intro m
  exact propext (Nat.dvd_add_iff_left (dvd_refl q)).symm

/-- In the canonical residue interval `[0,q)` there is exactly one multiple of
positive `q`, namely zero. -/
theorem count_dvd_one_period (q : ℕ) (hq : 0 < q) :
    Nat.count (fun m : ℕ => q ∣ m) q = 1 := by
  rw [Nat.count_eq_card_filter_range]
  have heq : (Finset.range q).filter (fun m => q ∣ m) = {0} := by
    ext m
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
    constructor
    · rintro ⟨hmq, hdiv⟩
      exact Nat.eq_zero_of_dvd_of_lt hdiv hmq
    · rintro rfl
      exact ⟨hq, Nat.dvd_zero q⟩
  rw [heq, Finset.card_singleton]

/-- Every interval of length `l` contains either `⌊l/q⌋` or one more multiple
of a positive modulus `q`. -/
theorem multipleCount_floor_bounds (q x l : ℕ) (hq : 0 < q) :
    l / q ≤ multipleCount q x l ∧ multipleCount q x l ≤ l / q + 1 := by
  constructor
  · have hlen : (l / q) * q ≤ l := Nat.div_mul_le_self l q
    have hsub : Finset.Ico x (x + (l / q) * q) ⊆
        Finset.Ico x (x + l) := by
      intro m hm
      simp only [Finset.mem_Ico] at hm ⊢
      omega
    have hfsub :
        (Finset.Ico x (x + (l / q) * q)).filter (fun m => q ∣ m) ⊆
          (Finset.Ico x (x + l)).filter (fun m => q ∣ m) := by
      intro m hm
      exact Finset.mem_filter.mpr
        ⟨hsub (Finset.mem_filter.mp hm).1, (Finset.mem_filter.mp hm).2⟩
    have hcard := Finset.card_le_card hfsub
    rw [periodic_filter_Ico_mul (fun m : ℕ => q ∣ m)
      (dvd_predicate_periodic q) (l / q) x,
      count_dvd_one_period q hq, Nat.mul_one] at hcard
    exact hcard
  · simpa only [multipleCount, count_dvd_one_period q hq, Nat.mul_one] using
      periodic_filter_Ico_le (fun m : ℕ => q ∣ m) hq
        (dvd_predicate_periodic q) x l

/-- After scaling by any common multiple `P` of `q`, the multiple count differs
from its exact density term by at most one scaled unit `P`. -/
theorem multipleCount_scaled_discrepancy
    (P q x l : ℕ) (hP : 0 < P) (hqP : q ∣ P) :
    |(P : ℤ) * (multipleCount q x l : ℤ) -
        (P / q : ℕ) * (l : ℤ)| ≤ (P : ℤ) := by
  have hq : 0 < q := Nat.pos_of_dvd_of_pos hqP hP
  obtain ⟨hfloor, hceil⟩ := multipleCount_floor_bounds q x l hq
  have hqfloor : q * (l / q) ≤ l := by
    simpa [Nat.mul_comm] using Nat.div_mul_le_self l q
  have hlt : l < q * (l / q) + q := by
    have hmod := Nat.mod_lt l hq
    have hdecomp := Nat.div_add_mod l q
    omega
  have hupp : q * multipleCount q x l ≤ l + q := by
    calc
      q * multipleCount q x l ≤ q * (l / q + 1) :=
        Nat.mul_le_mul_left q hceil
      _ = q * (l / q) + q := by ring
      _ ≤ l + q := Nat.add_le_add_right hqfloor q
  have hlow : l ≤ q * multipleCount q x l + q := by
    calc
      l ≤ q * (l / q) + q := le_of_lt hlt
      _ ≤ q * multipleCount q x l + q :=
        Nat.add_le_add_right (Nat.mul_le_mul_left q hfloor) q
  have hbase :
      |(q : ℤ) * (multipleCount q x l : ℤ) - (l : ℤ)| ≤ (q : ℤ) := by
    have hlowZ : (l : ℤ) ≤
        (q : ℤ) * (multipleCount q x l : ℤ) + (q : ℤ) := by
      exact_mod_cast hlow
    have huppZ : (q : ℤ) * (multipleCount q x l : ℤ) ≤
        (l : ℤ) + (q : ℤ) := by
      exact_mod_cast hupp
    rw [abs_le]
    constructor <;> omega
  have hfactor :
      (P : ℤ) * (multipleCount q x l : ℤ) -
          ((P / q : ℕ) : ℤ) * (l : ℤ) =
        ((P / q : ℕ) : ℤ) *
          ((q : ℤ) * (multipleCount q x l : ℤ) - (l : ℤ)) := by
    have hcancel : q * (P / q) = P := Nat.mul_div_cancel' hqP
    have hcancelZ : (P : ℤ) = (q : ℤ) * ((P / q : ℕ) : ℤ) := by
      exact_mod_cast hcancel.symm
    rw [hcancelZ]
    ring
  rw [hfactor, abs_mul, abs_of_nonneg (by positivity : (0 : ℤ) ≤ (P / q : ℕ))]
  calc
    (P / q : ℤ) *
        |(q : ℤ) * (multipleCount q x l : ℤ) - (l : ℤ)|
        ≤ (P / q : ℤ) * (q : ℤ) :=
      mul_le_mul_of_nonneg_left hbase (by positivity)
    _ = (P : ℤ) := by
      norm_cast
      simpa [Nat.mul_comm] using Nat.mul_div_cancel' hqP

/-- Summing the pointwise Möbius expansion and exchanging the two finite sums. -/
theorem sum_badIndicator_Ico (n x l : ℕ) :
    (∑ m ∈ Finset.Ico x (x + l), badIndicator n m) =
      ∑ q ∈ (divisorPeriod n).divisors,
        mobiusCoeff n q * (multipleCount q x l : ℤ) := by
  classical
  simp_rw [badIndicator_eq_mobius_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q hq
  calc
    (∑ m ∈ Finset.Ico x (x + l),
        if q ∣ m then mobiusCoeff n q else 0) =
        ∑ m ∈ Finset.Ico x (x + l),
          mobiusCoeff n q * (if q ∣ m then (1 : ℤ) else 0) := by
      apply Finset.sum_congr rfl
      intro m hm
      by_cases hqm : q ∣ m <;> simp [hqm]
    _ = mobiusCoeff n q *
        (∑ m ∈ Finset.Ico x (x + l), if q ∣ m then (1 : ℤ) else 0) := by
      rw [Finset.mul_sum]
    _ = mobiusCoeff n q * (multipleCount q x l : ℤ) := by
      rw [Finset.sum_boole]
      rfl

/-- Exact number of bad residue classes in the smaller divisor-LCM period. -/
noncomputable def divisorPeriodCount (n : ℕ) : ℕ := by
  classical
  exact Nat.count (HasMediumDivisor n) (divisorPeriod n)

/-- The ℓ¹ norm of the signed Möbius coefficients.  This, rather than the
period itself, controls interval discrepancy. -/
noncomputable def mobiusCoeffNorm (n : ℕ) : ℕ := by
  classical
  exact ∑ q ∈ (divisorPeriod n).divisors, (mobiusCoeff n q).natAbs

/-- Bad elements of a finite set, with classical decidability encapsulated in
a definition so statements do not depend on a choice of `DecidablePred`. -/
noncomputable def badFilter (n : ℕ) (s : Finset ℕ) : Finset ℕ := by
  classical
  exact s.filter (HasMediumDivisor n)

/-- A sum of the integer-valued badness indicator is exactly the cardinality
of the corresponding filtered set. -/
theorem sum_badIndicator_eq_filter_card (n : ℕ) (s : Finset ℕ) :
    (∑ m ∈ s, badIndicator n m) = ((badFilter n s).card : ℤ) := by
  classical
  simp only [badIndicator, badFilter]
  rw [Finset.sum_boole]

/-- A modulus dividing `P` occurs exactly `P/q` times in `[0,P)`. -/
theorem multipleCount_full_divisorPeriod (n q : ℕ)
    (hqmem : q ∈ (divisorPeriod n).divisors) :
    multipleCount q 0 (divisorPeriod n) = divisorPeriod n / q := by
  have hP : 0 < divisorPeriod n := divisorPeriod_pos n
  have hqP : q ∣ divisorPeriod n := (Nat.mem_divisors.mp hqmem).1
  have hq : 0 < q := Nat.pos_of_dvd_of_pos hqP hP
  have hmul := periodic_filter_Ico_mul (fun m : ℕ => q ∣ m)
    (dvd_predicate_periodic q) (divisorPeriod n / q) 0
  rw [count_dvd_one_period q hq, Nat.mul_one] at hmul
  have hcancel : divisorPeriod n / q * q = divisorPeriod n :=
    Nat.div_mul_cancel hqP
  simpa only [multipleCount, zero_add, hcancel] using hmul

/-- The complete-period count is the signed density numerator obtained from
Möbius inversion. -/
theorem divisorPeriodCount_eq_mobius_sum (n : ℕ) :
    (divisorPeriodCount n : ℤ) =
      ∑ q ∈ (divisorPeriod n).divisors,
        mobiusCoeff n q * ((divisorPeriod n / q : ℕ) : ℤ) := by
  classical
  calc
    (divisorPeriodCount n : ℤ) =
        ∑ m ∈ Finset.Ico 0 (divisorPeriod n), badIndicator n m := by
      rw [sum_badIndicator_eq_filter_card]
      simp only [divisorPeriodCount, Nat.count_eq_card_filter_range,
        Finset.range_eq_Ico, badFilter]
    _ = ∑ q ∈ (divisorPeriod n).divisors,
          mobiusCoeff n q * (multipleCount q 0 (divisorPeriod n) : ℤ) := by
      simpa only [zero_add] using sum_badIndicator_Ico n 0 (divisorPeriod n)
    _ = ∑ q ∈ (divisorPeriod n).divisors,
          mobiusCoeff n q * ((divisorPeriod n / q : ℕ) : ℤ) := by
      apply Finset.sum_congr rfl
      intro q hq
      rw [multipleCount_full_divisorPeriod n q hq]

/-- Algebraic identity expressing local discrepancy as the signed sum of the
individual divisibility discrepancies. -/
theorem mobius_discrepancy_identity (n x l : ℕ) :
    (divisorPeriod n : ℤ) *
          (∑ m ∈ Finset.Ico x (x + l), badIndicator n m) -
        (divisorPeriodCount n : ℤ) * (l : ℤ) =
      ∑ q ∈ (divisorPeriod n).divisors,
        mobiusCoeff n q *
          ((divisorPeriod n : ℤ) * (multipleCount q x l : ℤ) -
            ((divisorPeriod n / q : ℕ) : ℤ) * (l : ℤ)) := by
  rw [sum_badIndicator_Ico, divisorPeriodCount_eq_mobius_sum]
  rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro q hq
  ring

/-- Uniform interval-discrepancy theorem.  The error is the period times the
ℓ¹ norm of the Möbius coefficients; after division by the period, the count is
within `mobiusCoeffNorm n` of exact global-density prediction. -/
theorem mobius_discrepancy_Ico (n x l : ℕ) :
    |(divisorPeriod n : ℤ) * ((badFilter n (Finset.Ico x (x + l))).card : ℤ) -
        (divisorPeriodCount n : ℤ) * (l : ℤ)| ≤
      ((divisorPeriod n * mobiusCoeffNorm n : ℕ) : ℤ) := by
  rw [← sum_badIndicator_eq_filter_card,
    mobius_discrepancy_identity]
  calc
    |∑ q ∈ (divisorPeriod n).divisors,
        mobiusCoeff n q *
          ((divisorPeriod n : ℤ) * (multipleCount q x l : ℤ) -
            ((divisorPeriod n / q : ℕ) : ℤ) * (l : ℤ))| ≤
        ∑ q ∈ (divisorPeriod n).divisors,
          |mobiusCoeff n q *
            ((divisorPeriod n : ℤ) * (multipleCount q x l : ℤ) -
              ((divisorPeriod n / q : ℕ) : ℤ) * (l : ℤ))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ q ∈ (divisorPeriod n).divisors,
          (divisorPeriod n : ℤ) * ((mobiusCoeff n q).natAbs : ℤ) := by
      apply Finset.sum_le_sum
      intro q hq
      rw [abs_mul, ← Int.natCast_natAbs]
      have herr := multipleCount_scaled_discrepancy
        (divisorPeriod n) q x l (divisorPeriod_pos n)
        (Nat.mem_divisors.mp hq).1
      calc
        ((mobiusCoeff n q).natAbs : ℤ) *
            |(divisorPeriod n : ℤ) * (multipleCount q x l : ℤ) -
              ((divisorPeriod n / q : ℕ) : ℤ) * (l : ℤ)|
            ≤ ((mobiusCoeff n q).natAbs : ℤ) * (divisorPeriod n : ℤ) :=
          mul_le_mul_of_nonneg_left herr (by positivity)
        _ = (divisorPeriod n : ℤ) * ((mobiusCoeff n q).natAbs : ℤ) := by
          ring
    _ = ((divisorPeriod n * mobiusCoeffNorm n : ℕ) : ℤ) := by
      rw [← Finset.mul_sum]
      simp only [mobiusCoeffNorm]
      push_cast
      rfl

/-- One-sided natural-number form of the discrepancy estimate. -/
theorem badFilter_Ico_scaled_upper (n x l : ℕ) :
    divisorPeriod n * (badFilter n (Finset.Ico x (x + l))).card ≤
      divisorPeriodCount n * l + divisorPeriod n * mobiusCoeffNorm n := by
  have habs := mobius_discrepancy_Ico n x l
  have hone :
      (divisorPeriod n : ℤ) * ((badFilter n (Finset.Ico x (x + l))).card : ℤ) -
          (divisorPeriodCount n : ℤ) * (l : ℤ) ≤
        ((divisorPeriod n * mobiusCoeffNorm n : ℕ) : ℤ) :=
    le_trans (le_abs_self _) habs
  have hcast :
      ((divisorPeriod n * (badFilter n (Finset.Ico x (x + l))).card : ℕ) : ℤ) ≤
        ((divisorPeriodCount n * l +
          divisorPeriod n * mobiusCoeffNorm n : ℕ) : ℤ) := by
    push_cast
    omega
  exact_mod_cast hcast

/-- The original open interval is the half-open interval beginning at `x+1`
of length `y-1`. -/
theorem localCount_eq_badFilter_Ico (n x y : ℕ) :
    localCount n x y =
      (badFilter n (Finset.Ico (x + 1) (x + 1 + (y - 1)))).card := by
  classical
  have hinter : Finset.Ioo x (x + y) =
      Finset.Ico (x + 1) (x + 1 + (y - 1)) := by
    ext m
    simp only [Finset.mem_Ioo, Finset.mem_Ico]
    omega
  unfold localCount badIntegers badFilter
  rw [hinter]

/-- Main local transference inequality: uniformly in the translate, the local
count is at most its exact global-density term plus `mobiusCoeffNorm n`, after
scaling by the divisor-LCM period. -/
theorem localCount_mobius_scaled_upper (n x y : ℕ) :
    divisorPeriod n * localCount n x y ≤
      divisorPeriodCount n * (y - 1) +
        divisorPeriod n * mobiusCoeffNorm n := by
  rw [localCount_eq_badFilter_Ico]
  exact badFilter_Ico_scaled_upper n (x + 1) (y - 1)

/-- Pointwise form of the doubled-density transference estimate. -/
theorem localCount_fraction_of_twice_periodDensity
    (n a b y x : ℕ) (ha : 0 < a)
    (hdensity : 2 * b * divisorPeriodCount n ≤ a * divisorPeriod n)
    (hy : 2 * b * mobiusCoeffNorm n ≤ y) :
    b * localCount n x y ≤ a * y := by
  let P := divisorPeriod n
  let A := divisorPeriodCount n
  let B := mobiusCoeffNorm n
  have hlocal : P * localCount n x y ≤ A * (y - 1) + P * B := by
    simpa only [P, A, B] using localCount_mobius_scaled_upper n x y
  have hbudget : 2 * b * B ≤ a * y := by
    calc
      2 * b * B ≤ y := by simpa only [B] using hy
      _ ≤ a * y := by
        exact le_mul_of_one_le_left' (by omega : 1 ≤ a)
  have hscaled :
      2 * P * (b * localCount n x y) ≤ 2 * P * (a * y) := by
    calc
      2 * P * (b * localCount n x y) =
          2 * b * (P * localCount n x y) := by ring
      _ ≤ 2 * b * (A * (y - 1) + P * B) :=
        Nat.mul_le_mul_left (2 * b) hlocal
      _ = (2 * b * A) * (y - 1) + P * (2 * b * B) := by ring
      _ ≤ (a * P) * (y - 1) + P * (a * y) :=
        Nat.add_le_add
          (Nat.mul_le_mul_right (y - 1) (by simpa [P, A] using hdensity))
          (Nat.mul_le_mul_left P hbudget)
      _ ≤ (a * P) * y + P * (a * y) :=
        Nat.add_le_add_right
          (Nat.mul_le_mul_left (a * P) (Nat.sub_le y 1)) _
      _ = 2 * P * (a * y) := by ring
  exact Nat.le_of_mul_le_mul_left hscaled (by
    dsimp only [P]
    have := divisorPeriod_pos n
    positivity)

/-- If the target rational density `a/b` is at least twice the exact period
density, then the explicit threshold `2*b*mobiusCoeffNorm n` suffices.  Unlike
the factorial-period threshold, this threshold contains no factor equal to the
period. -/
theorem eventually_localCount_fraction_of_twice_periodDensity
    (n a b : ℕ) (ha : 0 < a)
    (hdensity : 2 * b * divisorPeriodCount n ≤ a * divisorPeriod n) :
    ∃ Y : ℕ, ∀ y : ℕ, Y ≤ y → ∀ x : ℕ,
      b * localCount n x y ≤ a * y := by
  refine ⟨2 * b * mobiusCoeffNorm n, ?_⟩
  intro y hy x
  exact localCount_fraction_of_twice_periodDensity n a b y x ha hdensity hy

/-- Real-valued `UniformlySparse` consequence of the Möbius threshold. -/
theorem eventually_uniformlySparse_rational_of_twice_periodDensity
    (n a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    (hdensity : 2 * b * divisorPeriodCount n ≤ a * divisorPeriod n) :
    ∃ Y : ℕ, ∀ y : ℕ, Y ≤ y →
      UniformlySparse ((a : ℝ) / (b : ℝ)) n y := by
  obtain ⟨Y, hY⟩ :=
    eventually_localCount_fraction_of_twice_periodDensity n a b ha hdensity
  refine ⟨Y, ?_⟩
  intro y hy x
  exact (natCast_le_rational_mul_iff a b (localCount n x y) y hb).2
    (hY y hy x)

/-- The 0/1 indicator has integer absolute value at most one. -/
theorem badIndicator_natAbs_le_one (n m : ℕ) :
    (badIndicator n m).natAbs ≤ 1 := by
  classical
  by_cases h : HasMediumDivisor n m <;> simp [badIndicator, h]

/-- Natural absolute value of the Möbius function is at most one. -/
theorem moebius_natAbs_le_one (q : ℕ) :
    (ArithmeticFunction.moebius q).natAbs ≤ 1 := by
  have h := ArithmeticFunction.abs_moebius_le_one (n := q)
  rw [← Int.natCast_natAbs] at h
  exact_mod_cast h

/-- Each Möbius coefficient is bounded by the number of divisors of its
index. -/
theorem mobiusCoeff_natAbs_le_card_divisors (n q : ℕ) :
    (mobiusCoeff n q).natAbs ≤ q.divisors.card := by
  classical
  unfold mobiusCoeff
  calc
    (∑ x ∈ q.divisorsAntidiagonal,
        ArithmeticFunction.moebius x.1 * badIndicator n x.2).natAbs ≤
      ∑ x ∈ q.divisorsAntidiagonal,
        (ArithmeticFunction.moebius x.1 * badIndicator n x.2).natAbs :=
      Int.natAbs_sum_le _ _
    _ ≤ ∑ _x ∈ q.divisorsAntidiagonal, 1 := by
      apply Finset.sum_le_sum
      intro x hx
      rw [Int.natAbs_mul]
      calc
        (ArithmeticFunction.moebius x.1).natAbs *
            (badIndicator n x.2).natAbs ≤ 1 * 1 :=
          Nat.mul_le_mul (moebius_natAbs_le_one x.1)
            (badIndicator_natAbs_le_one n x.2)
        _ = 1 := by rfl
    _ = q.divisorsAntidiagonal.card := by simp
    _ = q.divisors.card := by
      have hcard := congrArg Finset.card (Nat.map_div_right_divisors (n := q))
      simpa using hcard.symm

/-- The coefficient norm is at most the square of the divisor count of the
common period.  This converts the abstract exact norm into a standard
arithmetic function. -/
theorem mobiusCoeffNorm_le_card_divisors_sq (n : ℕ) :
    mobiusCoeffNorm n ≤ ((divisorPeriod n).divisors.card) ^ 2 := by
  classical
  have hP : divisorPeriod n ≠ 0 := (divisorPeriod_pos n).ne'
  unfold mobiusCoeffNorm
  calc
    ∑ q ∈ (divisorPeriod n).divisors, (mobiusCoeff n q).natAbs ≤
        ∑ q ∈ (divisorPeriod n).divisors, q.divisors.card := by
      apply Finset.sum_le_sum
      intro q hq
      exact mobiusCoeff_natAbs_le_card_divisors n q
    _ ≤ ∑ _q ∈ (divisorPeriod n).divisors,
          (divisorPeriod n).divisors.card := by
      apply Finset.sum_le_sum
      intro q hq
      exact Finset.card_le_card
        (Nat.divisors_subset_of_dvd hP (Nat.mem_divisors.mp hq).1)
    _ = ((divisorPeriod n).divisors.card) ^ 2 := by
      simp [pow_two]

/-- Fully standard explicit version: under the same doubled-density hypothesis,
`2*b*τ(P)^2` is a sufficient threshold, where `τ(P)` is the number of divisors
of the divisor-LCM period. -/
theorem eventually_localCount_fraction_of_twice_periodDensity_tauSq
    (n a b : ℕ) (ha : 0 < a)
    (hdensity : 2 * b * divisorPeriodCount n ≤ a * divisorPeriod n) :
    ∃ Y : ℕ, ∀ y : ℕ, Y ≤ y → ∀ x : ℕ,
      b * localCount n x y ≤ a * y := by
  refine ⟨2 * b * ((divisorPeriod n).divisors.card ^ 2), ?_⟩
  intro y hy x
  apply localCount_fraction_of_twice_periodDensity n a b y x ha hdensity
  calc
    2 * b * mobiusCoeffNorm n ≤
        2 * b * ((divisorPeriod n).divisors.card ^ 2) :=
      Nat.mul_le_mul_left (2 * b) (mobiusCoeffNorm_le_card_divisors_sq n)
    _ ≤ y := hy

end Erdos450
