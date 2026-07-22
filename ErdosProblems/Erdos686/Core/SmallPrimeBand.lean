/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import ErdosProblems.Erdos686.Core.LargeKWedge
import ErdosProblems.Erdos686.Core.PadicLift

/-!
# Erdős 686: prime-power lower-term obstructions

The exact small-prime valuation system already excludes an unbounded family
from the remaining `k ≥ 16`, `d ≥ k` target.  If the lower block ends at a
prime power `p^A`, then its `p`-adic valuation contains both the endpoint
exponent and the full factorial baseline `vₚ((k-1)!)`.  The upper block lies
strictly between `p^A` and `2p^A`, so valuation concentration bounds its
`p`-adic valuation by one less than the same baseline.  Multiplication by four
can only preserve or increase a prime valuation, giving a contradiction.

For an arbitrary lower position the factorial baseline splits at that
position, so the all-prime endpoint argument does not extend verbatim.  A
second theorem nevertheless excludes every position when the prime base is
larger than the block length.  No floating-point approximation or finite
computation enters either theorem.
-/

namespace Erdos686

namespace Erdos686Variant

private lemma blockProduct_eq_ascFactorial (k x : ℕ) :
    blockProduct k x = (x + 1).ascFactorial k := by
  have hs : Finset.Icc 1 k = Finset.Ico 1 (k + 1) := by
    ext i
    simp
  rw [Nat.ascFactorial_eq_prod_range]
  unfold blockProduct
  rw [hs, Finset.prod_Ico_eq_prod_range]
  simp only [Nat.add_sub_cancel]
  apply Finset.prod_congr rfl
  intro i hi
  omega

private lemma blockProduct_sub_eq_descFactorial {k t : ℕ} (hkt : k ≤ t) :
    blockProduct k (t - k) = t.descFactorial k := by
  rw [blockProduct_eq_ascFactorial]
  have h := Nat.add_descFactorial_eq_ascFactorial (t - k) k
  rw [Nat.sub_add_cancel hkt] at h
  exact h.symm

private lemma localBlockCoefficientNat_dvd_localBlockCofactorNat
    {k i n : ℕ} (hi : i ∈ Finset.Icc 1 k) :
    localBlockCoefficientNat k i ∣ localBlockCofactorNat k i n := by
  have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
  have hik : i ≤ k := (Finset.mem_Icc.mp hi).2
  have herase :
      (Finset.Icc 1 k).erase i =
        Finset.Icc 1 (i - 1) ∪ Finset.Icc (i + 1) k := by
    ext j
    simp only [Finset.mem_erase, Finset.mem_Icc, Finset.mem_union]
    omega
  have hdisjoint :
      Disjoint (Finset.Icc 1 (i - 1)) (Finset.Icc (i + 1) k) := by
    refine Finset.disjoint_left.mpr ?_
    intro j hjleft hjright
    simp only [Finset.mem_Icc] at hjleft hjright
    omega
  have hleft :
      (i - 1).factorial ∣ ∏ j ∈ Finset.Icc 1 (i - 1), (n + j) := by
    change (i - 1).factorial ∣ blockProduct (i - 1) n
    rw [blockProduct_eq_ascFactorial]
    exact Nat.factorial_dvd_ascFactorial (n + 1) (i - 1)
  have hrightEq :
      (∏ j ∈ Finset.Icc (i + 1) k, (n + j)) =
        blockProduct (k - i) (n + i) := by
    unfold blockProduct
    refine Finset.prod_bij'
      (fun j _hj => j - i) (fun a _ha => i + a) ?_ ?_ ?_ ?_ ?_
    · intro j hj
      simp only [Finset.mem_Icc] at hj ⊢
      constructor <;> omega
    · intro a ha
      simp only [Finset.mem_Icc] at ha ⊢
      constructor <;> omega
    · intro j hj
      have hij : i ≤ j := by
        have := (Finset.mem_Icc.mp hj).1
        omega
      change i + (j - i) = j
      rw [Nat.add_comm, Nat.sub_add_cancel hij]
    · intro a ha
      change i + a - i = a
      omega
    · intro j hj
      have hij : i ≤ j := by
        have := (Finset.mem_Icc.mp hj).1
        omega
      change n + j = n + i + (j - i)
      omega
  have hright :
      (k - i).factorial ∣ ∏ j ∈ Finset.Icc (i + 1) k, (n + j) := by
    rw [hrightEq, blockProduct_eq_ascFactorial]
    exact Nat.factorial_dvd_ascFactorial (n + i + 1) (k - i)
  unfold localBlockCoefficientNat localBlockCofactorNat
  rw [herase, Finset.prod_union hdisjoint]
  exact mul_dvd_mul hleft hright

private lemma endpoint_mul_factorial_pred_dvd_blockProduct
    {k t : ℕ} (hk : 1 ≤ k) (hkt : k ≤ t) :
    t * (k - 1).factorial ∣ blockProduct k (t - k) := by
  have ht : 1 ≤ t := hk.trans hkt
  have hfac : (k - 1).factorial ∣ (t - 1).descFactorial (k - 1) :=
    Nat.factorial_dvd_descFactorial (t - 1) (k - 1)
  rw [blockProduct_sub_eq_descFactorial hkt]
  have hdesc :
      t.descFactorial k = t * (t - 1).descFactorial (k - 1) := by
    simpa [Nat.sub_add_cancel ht, Nat.sub_add_cancel hk] using
      Nat.succ_descFactorial_succ (t - 1) (k - 1)
  rw [hdesc]
  exact Nat.mul_dvd_mul_left t hfac

private lemma factorization_lt_of_between_prime_powers
    {p A u : ℕ} (hp : p.Prime)
    (hlo : p ^ A < u) (hhi : u < 2 * p ^ A) :
    u.factorization p < A := by
  by_contra hnot
  have hpow : p ^ A ∣ u :=
    (hp.pow_dvd_iff_le_factorization (by omega : u ≠ 0)).mpr
      (Nat.le_of_not_gt hnot)
  obtain ⟨c, rfl⟩ := hpow
  have ht : 0 < p ^ A := Nat.pow_pos hp.pos
  have hc : 1 < c := (Nat.lt_mul_iff_one_lt_right ht).mp hlo
  have htwo : 2 * p ^ A ≤ p ^ A * c := by
    have := Nat.mul_le_mul_left (p ^ A) (by omega : 2 ≤ c)
    simpa [mul_comm] using this
  omega

/-- General any-position core with the exact split-factorial correction.  The
local coefficient is `(i-1)!*(k-i)!`; the premise says that the universal
upper concentration loss `v_p((k-1)!)` exceeds this lower baseline by at most
the multiplier valuation `v_p(4)`.

The explicit interval hypotheses separate the local valuation argument from
the ratio-window estimate used by the target-facing corollary below.
-/
theorem no_four_solution_lower_prime_power_of_upper_between_of_factorial_loss_le
    {p k n d i A : ℕ}
    (hp : p.Prime) (hi : i ∈ Finset.Icc 1 k)
    (howner : n + i = p ^ A)
    (hupperLo : p ^ A < n + d + 1)
    (hupperHi : n + d + k < 2 * p ^ A)
    (hfactorialLoss :
      (k - 1).factorial.factorization p ≤
        (4 : ℕ).factorization p +
          (localBlockCoefficientNat k i).factorization p) :
    blockProduct k (n + d) ≠ 4 * blockProduct k n := by
  intro heq
  have hk1 : 1 ≤ k := by
    have hi1 := (Finset.mem_Icc.mp hi).1
    have hik := (Finset.mem_Icc.mp hi).2
    omega
  have hlower0 : blockProduct k n ≠ 0 :=
    ne_of_gt (blockProduct_pos k n)
  have hcoeff0 : localBlockCoefficientNat k i ≠ 0 := by
    unfold localBlockCoefficientNat
    exact mul_ne_zero (Nat.factorial_ne_zero _) (Nat.factorial_ne_zero _)
  have hpowCoeff :
      p ^ (localBlockCoefficientNat k i).factorization p ∣
        localBlockCoefficientNat k i :=
    (hp.pow_dvd_iff_le_factorization hcoeff0).mpr le_rfl
  have hpowCofactor :
      p ^ (localBlockCoefficientNat k i).factorization p ∣
        localBlockCofactorNat k i n :=
    dvd_trans hpowCoeff (localBlockCoefficientNat_dvd_localBlockCofactorNat hi)
  have hpowOwner : p ^ A ∣ n + i := by rw [howner]
  have hpowLower :
      p ^ (A + (localBlockCoefficientNat k i).factorization p) ∣
        blockProduct k n := by
    rw [blockProduct_eq_factor_mul_localBlockCofactorNat hi, pow_add]
    exact mul_dvd_mul hpowOwner hpowCofactor
  have hlowerVal :
      A + (localBlockCoefficientNat k i).factorization p ≤
        (blockProduct k n).factorization p :=
    (hp.pow_dvd_iff_le_factorization hlower0).mp hpowLower
  obtain ⟨j, hj, hupperConcentration⟩ :=
    exists_blockProduct_factorization_concentration hp hk1 (n := n + d)
  have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
  have hjk : j ≤ k := (Finset.mem_Icc.mp hj).2
  have hownerLo : p ^ A < n + d + j := by omega
  have hownerHi : n + d + j < 2 * p ^ A := by omega
  have hownerVal : (n + d + j).factorization p < A :=
    factorization_lt_of_between_prime_powers hp hownerLo hownerHi
  have hupperVal :
      (blockProduct k (n + d)).factorization p <
        A + (k - 1).factorial.factorization p := by
    omega
  have hvalEq := congrArg (fun z : ℕ => z.factorization p) heq
  change (blockProduct k (n + d)).factorization p =
    (4 * blockProduct k n).factorization p at hvalEq
  rw [Nat.factorization_mul (by norm_num : (4 : ℕ) ≠ 0) hlower0,
    Finsupp.add_apply] at hvalEq
  omega

/-- Reusable unconditional specialization: when `p>k`, the factorial loss in
the general core is zero, so every lower-block position is excluded. -/
theorem no_four_solution_lower_prime_power_of_upper_between
    {p k n d i A : ℕ}
    (hp : p.Prime) (hpk : k < p) (hi : i ∈ Finset.Icc 1 k)
    (howner : n + i = p ^ A)
    (hupperLo : p ^ A < n + d + 1)
    (hupperHi : n + d + k < 2 * p ^ A) :
    blockProduct k (n + d) ≠ 4 * blockProduct k n := by
  apply no_four_solution_lower_prime_power_of_upper_between_of_factorial_loss_le
    hp hi howner hupperLo hupperHi
  have hpNotDvdFac : ¬ p ∣ (k - 1).factorial := by
    rw [hp.dvd_factorial]
    omega
  rw [Nat.factorization_eq_zero_of_not_dvd hpNotDvdFac]
  omega

/-- Target-facing form of the exact split-factorial criterion.  The banked
`9d<n` estimate supplies the explicit upper interval needed by the local core. -/
theorem no_gap_solution_lower_term_prime_power_of_factorial_loss_le
    {p k n d i A : ℕ}
    (hp : p.Prime) (hk : 16 ≤ k) (hd : k ≤ d)
    (hi : i ∈ Finset.Icc 1 k) (howner : n + i = p ^ A)
    (hfactorialLoss :
      (k - 1).factorial.factorization p ≤
        (4 : ℕ).factorization p +
          (localBlockCoefficientNat k i).factorization p) :
    blockProduct k (n + d) ≠ 4 * blockProduct k n := by
  intro heq
  have hgap : 9 * d < n :=
    nine_mul_gap_lt_n_of_four_solution hk hd heq
  have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
  have hik : i ≤ k := (Finset.mem_Icc.mp hi).2
  have hupperLo : p ^ A < n + d + 1 := by
    rw [← howner]
    omega
  have hupperHi : n + d + k < 2 * p ^ A := by
    rw [← howner]
    omega
  exact no_four_solution_lower_prime_power_of_upper_between_of_factorial_loss_le
    hp hi howner hupperLo hupperHi hfactorialLoss heq

/-- All-prime first-position specialization.  If the lower block starts at a
prime power, the split local coefficient is the full `(k-1)!` baseline. -/
theorem no_gap_solution_lower_block_starts_at_prime_power
    {p k n d A : ℕ}
    (hp : p.Prime) (hk : 16 ≤ k) (hd : k ≤ d)
    (howner : n + 1 = p ^ A) :
    blockProduct k (n + d) ≠ 4 * blockProduct k n := by
  apply no_gap_solution_lower_term_prime_power_of_factorial_loss_le
    hp hk hd (by simp; omega) howner
  simp [localBlockCoefficientNat]

/-- Unconditional any-position corollary.  In a remaining large-row solution,
no lower-block term can be a power of a prime larger than the block length. -/
theorem no_gap_solution_lower_term_prime_power_base_gt_length
    {p k n d i A : ℕ}
    (hp : p.Prime) (hk : 16 ≤ k) (hd : k ≤ d) (hpk : k < p)
    (hi : i ∈ Finset.Icc 1 k) (howner : n + i = p ^ A) :
    blockProduct k (n + d) ≠ 4 * blockProduct k n := by
  apply no_gap_solution_lower_term_prime_power_of_factorial_loss_le
    hp hk hd hi howner
  have hpNotDvdFac : ¬ p ∣ (k - 1).factorial := by
    rw [hp.dvd_factorial]
    omega
  rw [Nat.factorization_eq_zero_of_not_dvd hpNotDvdFac]
  omega

/-- Reusable large-base owner-transfer obstruction.  The equation transfers
`p^A` from the lower owner `a*p^A` to one upper owner, forcing
`p^A≤d+k-1`.  Any external size estimate making `a*(d+k-1)<n+i` then closes
the configuration. -/
theorem no_four_solution_lower_term_cofactor_prime_power_base_gt_length_of_size
    {p k n d i A a : ℕ}
    (hp : p.Prime) (hd : k ≤ d) (hpk : k < p)
    (hi : i ∈ Finset.Icc 1 k) (hA : 1 ≤ A)
    (howner : n + i = a * p ^ A)
    (hsize : a * (d + k - 1) < n + i) :
    blockProduct k (n + d) ≠ 4 * blockProduct k n := by
  intro heq
  have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
  have hik : i ≤ k := (Finset.mem_Icc.mp hi).2
  have hpowLowerTerm : p ^ A ∣ n + i := by
    refine ⟨a, ?_⟩
    rw [howner]
    ring
  have hpowLower : p ^ A ∣ blockProduct k n := by
    rw [blockProduct_eq_factor_mul_localBlockCofactorNat hi]
    obtain ⟨c, hc⟩ := hpowLowerTerm
    refine ⟨c * localBlockCofactorNat k i n, ?_⟩
    rw [hc]
    ring
  have hpowUpper : p ^ A ∣ blockProduct k (n + d) := by
    rw [heq]
    obtain ⟨c, hc⟩ := hpowLower
    refine ⟨4 * c, ?_⟩
    rw [hc]
    ring
  obtain ⟨j, ⟨hj, hpowUpperTerm⟩, _hunique⟩ :=
    primePower_dvd_blockProduct_existsUnique hp (by omega : 0 < A)
      (by omega : k ≤ p) hpowUpper
  have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
  have hjk : j ≤ k := (Finset.mem_Icc.mp hj).2
  have htermOrder : n + i ≤ n + d + j := by omega
  have hpowDiff : p ^ A ∣ (n + d + j) - (n + i) :=
    Nat.dvd_sub hpowUpperTerm hpowLowerTerm
  have hdiffEq : (n + d + j) - (n + i) = d + j - i := by omega
  rw [hdiffEq] at hpowDiff
  have hdiffPos : 0 < d + j - i := by omega
  have hpAle : p ^ A ≤ d + j - i := Nat.le_of_dvd hdiffPos hpowDiff
  have hdiffBound : d + j - i ≤ d + k - 1 := by omega
  have hownerBound : n + i ≤ a * (d + k - 1) := by
    calc
      n + i = a * p ^ A := howner
      _ ≤ a * (d + k - 1) :=
        Nat.mul_le_mul_left a (hpAle.trans hdiffBound)
  omega

/-- Stronger large-base owner exclusion.  A lower term cannot be `a*p^A`
with `a≤4`, positive exponent, and `p>k`.  The exact `9d<n` estimate supplies
the abstract size premise above. -/
theorem no_gap_solution_lower_term_small_cofactor_prime_power_base_gt_length
    {p k n d i A a : ℕ}
    (hp : p.Prime) (hk : 16 ≤ k) (hd : k ≤ d) (hpk : k < p)
    (hi : i ∈ Finset.Icc 1 k) (hA : 1 ≤ A)
    (ha4 : a ≤ 4) (howner : n + i = a * p ^ A) :
    blockProduct k (n + d) ≠ 4 * blockProduct k n := by
  intro heq
  have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
  have hgap : 9 * d < n :=
    nine_mul_gap_lt_n_of_four_solution hk hd heq
  have hsize : a * (d + k - 1) < n + i := by
    have haBound : a * (d + k - 1) ≤ 4 * (d + k - 1) :=
      Nat.mul_le_mul_right (d + k - 1) ha4
    have hfourBound : 4 * (d + k - 1) < n := by omega
    omega
  exact no_four_solution_lower_term_cofactor_prime_power_base_gt_length_of_size
    hp hd hpk hi hA howner hsize heq

/-- Core valuation obstruction.  If the lower block ends at `p^A`, the gap
starts the upper block after `p^A`, but is still small enough that the upper
block ends before `2p^A`; the quotient-four equation is then impossible.

This statement uses only `1 ≤ k ≤ d < p^A`.  In particular, it is independent
of the large-row ratio-window estimate used by the corollary below.
-/
theorem no_four_solution_prime_power_endpoint_of_gap_lt_endpoint
    {p k A d : ℕ} (hp : p.Prime)
    (hk : 1 ≤ k) (hkd : k ≤ d) (hdt : d < p ^ A) :
    blockProduct k ((p ^ A - k) + d) ≠
      4 * blockProduct k (p ^ A - k) := by
  intro heq
  let t := p ^ A
  let n := t - k
  have hkt : k ≤ t := by dsimp [t]; omega
  have heq' : blockProduct k (n + d) = 4 * blockProduct k n := by
    simpa [n, t] using heq
  have hlower0 : blockProduct k n ≠ 0 :=
    ne_of_gt (blockProduct_pos k n)
  let f := (k - 1).factorial.factorization p
  have hpowFac : p ^ f ∣ (k - 1).factorial := by
    exact (hp.pow_dvd_iff_le_factorization
      (Nat.factorial_ne_zero (k - 1))).mpr le_rfl
  have hendpoint : t * (k - 1).factorial ∣ blockProduct k n := by
    dsimp [n]
    exact endpoint_mul_factorial_pred_dvd_blockProduct hk hkt
  have hpowLower : p ^ (A + f) ∣ blockProduct k n := by
    have hmul : p ^ A * p ^ f ∣ t * (k - 1).factorial := by
      dsimp [t]
      exact Nat.mul_dvd_mul_left (p ^ A) hpowFac
    rw [pow_add]
    exact dvd_trans hmul hendpoint
  have hlowerVal : A + f ≤ (blockProduct k n).factorization p :=
    (hp.pow_dvd_iff_le_factorization hlower0).mp hpowLower
  obtain ⟨i, hi, hupperConcentration⟩ :=
    exists_blockProduct_factorization_concentration hp hk (n := n + d)
  have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
  have hik : i ≤ k := (Finset.mem_Icc.mp hi).2
  have hownerLo : t < n + d + i := by
    dsimp [n]
    omega
  have hownerHi : n + d + i < 2 * t := by
    dsimp [n, t] at hownerLo ⊢
    omega
  have hownerVal : (n + d + i).factorization p < A :=
    factorization_lt_of_between_prime_powers hp hownerLo hownerHi
  have hupperVal :
      (blockProduct k (n + d)).factorization p ≤ (A - 1) + f := by
    dsimp [f]
    omega
  have hvalEq := congrArg (fun z : ℕ => z.factorization p) heq'
  change (blockProduct k (n + d)).factorization p =
    (4 * blockProduct k n).factorization p at hvalEq
  rw [Nat.factorization_mul (by norm_num : (4 : ℕ) ≠ 0) hlower0,
    Finsupp.add_apply] at hvalEq
  omega

/-- In the large-`k`, non-overlap range, a quotient-four solution cannot have
its lower consecutive block end at a prime power.  This excludes every triple

`(k, n, d) = (k, p^A-k, d)`

with prime `p`, `16 ≤ k < p^A`, and `k ≤ d`; hence it is unbounded in all
parameters.
-/
theorem no_gap_solution_lower_block_ends_at_prime_power
    {p k A d : ℕ} (hp : p.Prime)
    (hk : 16 ≤ k) (hkt : k < p ^ A) (hd : k ≤ d) :
    blockProduct k ((p ^ A - k) + d) ≠
      4 * blockProduct k (p ^ A - k) := by
  intro heq
  have hgap : 9 * d < p ^ A - k :=
    nine_mul_gap_lt_n_of_four_solution hk hd heq
  have hdt : d < p ^ A := by
    omega
  exact no_four_solution_prime_power_endpoint_of_gap_lt_endpoint
    hp (by omega) hd hdt heq

/-- The power-of-two specialization, retained as the exact small-prime-system
corollary (`v₂(4)=2`). -/
theorem no_gap_solution_lower_block_ends_at_two_power
    {k A d : ℕ} (hk : 16 ≤ k) (hkt : k < 2 ^ A) (hd : k ≤ d) :
    blockProduct k ((2 ^ A - k) + d) ≠
      4 * blockProduct k (2 ^ A - k) :=
  no_gap_solution_lower_block_ends_at_prime_power Nat.prime_two hk hkt hd

#print axioms no_gap_solution_lower_block_ends_at_prime_power
#print axioms no_gap_solution_lower_block_ends_at_two_power
#print axioms no_four_solution_prime_power_endpoint_of_gap_lt_endpoint
#print axioms no_four_solution_lower_prime_power_of_upper_between_of_factorial_loss_le
#print axioms no_four_solution_lower_prime_power_of_upper_between
#print axioms no_gap_solution_lower_term_prime_power_of_factorial_loss_le
#print axioms no_gap_solution_lower_block_starts_at_prime_power
#print axioms no_gap_solution_lower_term_prime_power_base_gt_length
#print axioms no_four_solution_lower_term_cofactor_prime_power_base_gt_length_of_size
#print axioms no_gap_solution_lower_term_small_cofactor_prime_power_base_gt_length

end Erdos686Variant

end Erdos686
