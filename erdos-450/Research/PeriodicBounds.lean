import Research.Basic
import Mathlib.Data.Nat.Periodic

namespace Erdos450

/-- A convenient common period for all divisibility classes in `(n,2n)`. -/
def commonPeriod (n : ℕ) : ℕ := Nat.factorial (2 * n)

/-- The common period is always positive. -/
theorem commonPeriod_pos (n : ℕ) : 0 < commonPeriod n := by
  exact Nat.factorial_pos _

/-- Having a divisor in `(n,2n)` is periodic with period `(2n)!`. -/
theorem hasMediumDivisor_periodic (n : ℕ) :
    Function.Periodic (HasMediumDivisor n) (commonPeriod n) := by
  intro m
  apply propext
  constructor
  · rintro ⟨d, hnd, hd2, hdiv⟩
    have hdpos : 0 < d := lt_of_le_of_lt (Nat.zero_le n) hnd
    have hdP : d ∣ commonPeriod n :=
      Nat.dvd_factorial hdpos (le_of_lt hd2)
    refine ⟨d, hnd, hd2, ?_⟩
    have hs := Nat.dvd_sub hdiv hdP
    simpa [commonPeriod] using hs
  · rintro ⟨d, hnd, hd2, hdiv⟩
    have hdpos : 0 < d := lt_of_le_of_lt (Nat.zero_le n) hnd
    have hdP : d ∣ commonPeriod n :=
      Nat.dvd_factorial hdpos (le_of_lt hd2)
    exact ⟨d, hnd, hd2, dvd_add hdiv hdP⟩

/-- Exact number of bad residue classes in one common period. -/
noncomputable def periodCount (n : ℕ) : ℕ := by
  classical
  exact Nat.count (HasMediumDivisor n) (commonPeriod n)

/-- A general periodic predicate has exactly `q` times its one-period count in
any half-open interval of length `q*a`. -/
theorem periodic_filter_Ico_mul (p : ℕ → Prop) [DecidablePred p]
    {a : ℕ} (hp : Function.Periodic p a) (q x : ℕ) :
    ((Finset.Ico x (x + q * a)).filter p).card = q * Nat.count p a := by
  induction q with
  | zero => simp
  | succ q ih =>
      let b := x + q * a
      let c := x + (q + 1) * a
      have hxb : x ≤ b := by
        dsimp [b]
        exact Nat.le_add_right x (q * a)
      have hc : c = b + a := by
        dsimp [b, c]
        ring
      have hbc : b ≤ c := by
        rw [hc]
        exact Nat.le_add_right b a
      have hu : Finset.Ico x b ∪ Finset.Ico b c = Finset.Ico x c :=
        Finset.Ico_union_Ico_eq_Ico hxb hbc
      have hd : Disjoint ((Finset.Ico x b).filter p) ((Finset.Ico b c).filter p) :=
        Finset.disjoint_filter_filter (Finset.Ico_disjoint_Ico_consecutive x b c)
      change ((Finset.Ico x c).filter p).card = (q + 1) * Nat.count p a
      rw [← hu, Finset.filter_union, Finset.card_union_of_disjoint hd]
      have hfirst : ((Finset.Ico x b).filter p).card = q * Nat.count p a := by
        simpa [b] using ih
      have hsecond : ((Finset.Ico b c).filter p).card = Nat.count p a := by
        rw [hc]
        exact Nat.filter_Ico_card_eq_of_periodic b a p hp
      rw [hfirst, hsecond]
      simp [Nat.add_mul]

/-- Crude but exact transference bound for any periodic predicate: a length-`l`
block is contained in at most `l/a+1` complete periods. -/
theorem periodic_filter_Ico_le (p : ℕ → Prop) [DecidablePred p]
    {a : ℕ} (ha : 0 < a) (hp : Function.Periodic p a) (x l : ℕ) :
    ((Finset.Ico x (x + l)).filter p).card ≤
      (l / a + 1) * Nat.count p a := by
  let q := l / a + 1
  have hl : l ≤ q * a := by
    have hmod : l % a < a := Nat.mod_lt l ha
    have hdecomp : a * (l / a) + l % a = l := Nat.div_add_mod l a
    have hlt : l < (l / a + 1) * a := by
      calc
        l = a * (l / a) + l % a := hdecomp.symm
        _ < a * (l / a) + a := Nat.add_lt_add_left hmod _
        _ = (l / a + 1) * a := by ring
    dsimp [q]
    exact le_of_lt hlt
  have hsub : Finset.Ico x (x + l) ⊆ Finset.Ico x (x + q * a) := by
    intro z hz
    simp only [Finset.mem_Ico] at hz ⊢
    omega
  have hfsub : (Finset.Ico x (x + l)).filter p ⊆
      (Finset.Ico x (x + q * a)).filter p := by
    intro z hz
    simp only [Finset.mem_filter] at hz ⊢
    exact ⟨hsub hz.1, hz.2⟩
  calc
    ((Finset.Ico x (x + l)).filter p).card
        ≤ ((Finset.Ico x (x + q * a)).filter p).card := Finset.card_le_card hfsub
    _ = q * Nat.count p a := periodic_filter_Ico_mul p hp q x
    _ = (l / a + 1) * Nat.count p a := rfl

/-- Specialized local-count upper bound.  The open interval has `y-1`
interior integral offsets, so it is covered by at most
`(y-1)/(2n)! + 1` complete periods. -/
theorem localCount_le_period_blocks (n x y : ℕ) :
    localCount n x y ≤
      ((y - 1) / commonPeriod n + 1) * periodCount n := by
  classical
  rcases y with _ | y
  · simp [localCount, badIntegers]
  · have heq : Finset.Ioo x (x + (y + 1)) = Finset.Ico (x + 1) (x + 1 + y) := by
      ext z
      simp only [Finset.mem_Ioo, Finset.mem_Ico]
      omega
    unfold localCount badIntegers
    rw [heq]
    simpa [periodCount] using
      periodic_filter_Ico_le (HasMediumDivisor n) (commonPeriod_pos n)
        (hasMediumDivisor_periodic n) (x + 1) y

/-- At the aligned lengths `q*(2n)!+1`, the open interval starting at zero
contains exactly `q` complete periods. -/
theorem localCount_period_aligned (n q : ℕ) :
    localCount n 0 (q * commonPeriod n + 1) = q * periodCount n := by
  classical
  have heq : Finset.Ioo 0 (q * commonPeriod n + 1) =
      Finset.Ico 1 (1 + q * commonPeriod n) := by
    ext z
    simp only [Finset.mem_Ioo, Finset.mem_Ico]
    omega
  unfold localCount badIntegers
  simp only [zero_add]
  rw [heq]
  simpa [periodCount] using
    periodic_filter_Ico_mul (HasMediumDivisor n)
      (hasMediumDivisor_periodic n) q 1

/-- Purely integral eventual upper bound for a rational target `a/b`: if the
period density is strictly below `a/b`, then all lengths beyond the explicit
(very large) threshold `b*A*P` work uniformly. -/
theorem eventually_localCount_fraction_of_periodCount_lt
    (n a b : ℕ)
    (hdensity : b * periodCount n < a * commonPeriod n) :
    ∃ Y : ℕ, ∀ y : ℕ, Y ≤ y → ∀ x : ℕ,
      b * localCount n x y ≤ a * y := by
  let P := commonPeriod n
  let A := periodCount n
  refine ⟨b * A * P, ?_⟩
  intro y hy x
  let Q := (y - 1) / P + 1
  have hcount : localCount n x y ≤ Q * A := by
    simpa [P, A, Q] using localCount_le_period_blocks n x y
  have hQP : P * Q ≤ y + P := by
    have hdiv : ((y - 1) / P) * P ≤ y - 1 := Nat.div_mul_le_self _ _
    calc
      P * Q = ((y - 1) / P) * P + P := by dsimp [Q]; ring
      _ ≤ (y - 1) + P := Nat.add_le_add_right hdiv P
      _ ≤ y + P := Nat.add_le_add_right (Nat.sub_le y 1) P
  have hgap : b * A + 1 ≤ a * P := by
    simpa [A, P] using hdensity
  have htail : b * A * (y + P) ≤ a * P * y := by
    calc
      b * A * (y + P) = b * A * y + b * A * P := by ring
      _ ≤ b * A * y + y := Nat.add_le_add_left hy (b * A * y)
      _ = (b * A + 1) * y := by ring
      _ ≤ (a * P) * y := Nat.mul_le_mul_right y hgap
      _ = a * P * y := rfl
  have hscaled : P * (b * localCount n x y) ≤ P * (a * y) := by
    calc
      P * (b * localCount n x y) = (P * b) * localCount n x y := by ring
      _ ≤ (P * b) * (Q * A) := Nat.mul_le_mul_left (P * b) hcount
      _ = (b * A) * (P * Q) := by ring
      _ ≤ (b * A) * (y + P) := Nat.mul_le_mul_left (b * A) hQP
      _ ≤ a * P * y := htail
      _ = P * (a * y) := by ring
  exact Nat.le_of_mul_le_mul_left hscaled (by simpa [P] using commonPeriod_pos n)

/-- Exact cast bridge for the rational targets used in the dichotomy. -/
theorem natCast_le_rational_mul_iff (a b c y : ℕ) (hb : 0 < b) :
    ((c : ℝ) ≤ (a : ℝ) / (b : ℝ) * (y : ℝ)) ↔ b * c ≤ a * y := by
  have hbR : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb
  rw [div_mul_eq_mul_div, le_div_iff₀ hbR]
  norm_cast
  simp [Nat.mul_comm]

/-- Real-valued form of the eventual upper bound: every rational target above
the exact period density eventually works at all larger lengths. -/
theorem eventually_uniformlySparse_rational_of_periodCount_lt
    (n a b : ℕ) (hb : 0 < b)
    (hdensity : b * periodCount n < a * commonPeriod n) :
    ∃ Y : ℕ, ∀ y : ℕ, Y ≤ y →
      UniformlySparse ((a : ℝ) / (b : ℝ)) n y := by
  obtain ⟨Y, hY⟩ :=
    eventually_localCount_fraction_of_periodCount_lt n a b hdensity
  refine ⟨Y, ?_⟩
  intro y hy x
  exact (natCast_le_rational_mul_iff a b (localCount n x y) y hb).2
    (hY y hy x)

/-- If a rational target lies below the exact period density, arbitrarily large
lengths violate its corresponding integral count inequality. -/
theorem arbitrarily_large_fraction_violation_of_lt_periodCount
    (n a b : ℕ)
    (hdensity : a * commonPeriod n < b * periodCount n) :
    ∀ Y : ℕ, ∃ y : ℕ, Y ≤ y ∧
      a * y < b * localCount n 0 y := by
  intro Y
  let P := commonPeriod n
  let A := periodCount n
  let q := Y + a + 1
  let y := q * P + 1
  have hPpos : 0 < P := by simpa [P] using commonPeriod_pos n
  have hPone : 1 ≤ P := by omega
  have hy : Y ≤ y := by
    calc
      Y ≤ q := by dsimp [q]; omega
      _ ≤ q * P := le_mul_of_one_le_right' hPone
      _ ≤ q * P + 1 := Nat.le_add_right _ _
      _ = y := rfl
  have hgap : a * P + 1 ≤ b * A := by
    simpa [P, A] using hdensity
  have hqa : a < q := by dsimp [q]; omega
  have hstrict : a * y < b * (q * A) := by
    calc
      a * y = q * (a * P) + a := by dsimp [y]; ring
      _ < q * (a * P) + q := Nat.add_lt_add_left hqa _
      _ = q * (a * P + 1) := by ring
      _ ≤ q * (b * A) := Nat.mul_le_mul_left q hgap
      _ = b * (q * A) := by ring
  refine ⟨y, hy, ?_⟩
  rw [localCount_period_aligned n q]
  exact hstrict

/-- Real-valued obstruction: every rational target below the exact period
density fails at arbitrarily large lengths, so no sufficient threshold exists. -/
theorem arbitrarily_large_not_uniformlySparse_rational_of_lt_periodCount
    (n a b : ℕ) (hb : 0 < b)
    (hdensity : a * commonPeriod n < b * periodCount n) :
    ∀ Y : ℕ, ∃ y : ℕ, Y ≤ y ∧
      ¬ UniformlySparse ((a : ℝ) / (b : ℝ)) n y := by
  intro Y
  obtain ⟨y, hy, hbad⟩ :=
    arbitrarily_large_fraction_violation_of_lt_periodCount n a b hdensity Y
  refine ⟨y, hy, ?_⟩
  intro huniform
  have hle : b * localCount n 0 y ≤ a * y :=
    (natCast_le_rational_mul_iff a b (localCount n 0 y) y hb).1
      (huniform 0)
  exact (not_lt_of_ge hle) hbad

end Erdos450
