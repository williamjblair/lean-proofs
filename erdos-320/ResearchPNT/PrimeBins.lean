import PrimeNumberTheoremAnd.IEANTN.RosserSchoenfeld.RosserSchoenfeldPrime

/-!
# Quantitative prime-bin input

Only the kernel-clean theorem `RS_prime.pntBigO`, ultimately proved from the
kernel-clean `MediumPNT`, is used here. Unrelated numerical statements in the
upstream project are not dependencies of these results.
-/

open Filter Asymptotics Real Chebyshev

namespace ResearchPNT

/-- An explicit-quantifier form of the medium-strength PNT estimate for
Chebyshev's theta function. -/
theorem exists_theta_error_bound :
    ∃ C : ℝ, 0 < C ∧ ∃ X : ℝ, 2 ≤ X ∧
      ∀ x : ℝ, X ≤ x →
        |Chebyshev.theta x - x| ≤ C * (x / (Real.log x) ^ 2) := by
  have hpnt := RS_prime.pntBigO
  rw [Asymptotics.isBigO_iff'] at hpnt
  obtain ⟨C, hC, hEventually⟩ := hpnt
  rw [Filter.eventually_atTop] at hEventually
  obtain ⟨X₀, hX₀⟩ := hEventually
  refine ⟨C, hC, max X₀ 2, le_max_right _ _, ?_⟩
  intro x hx
  have hx0 : X₀ ≤ x := le_trans (le_max_left _ _) hx
  have hx2 : 2 ≤ x := le_trans (le_max_right _ _) hx
  have h := hX₀ x hx0
  simp only [Pi.sub_apply, id_eq, Real.norm_eq_abs] at h
  have hxpos : 0 < x := lt_of_lt_of_le (by norm_num) hx2
  have hlogpos : 0 < Real.log x := Real.log_pos (by linarith)
  have hquotpos : 0 < x / Real.log x ^ 2 := div_pos hxpos (sq_pos_of_pos hlogpos)
  rw [abs_of_pos hquotpos] at h
  exact h

/-- Number of primes in a natural interval, expressed by prime-counting
functions. -/
theorem card_prime_Ioc (u v : ℕ) (huv : u ≤ v) :
    ((Finset.Ioc u v).filter Nat.Prime).card =
      Nat.primeCounting v - Nat.primeCounting u := by
  let A := (Finset.range (u + 1)).filter Nat.Prime
  let B := (Finset.range (v + 1)).filter Nat.Prime
  have hsub : A ⊆ B := by
    apply Finset.filter_subset_filter
    intro x hx
    simp only [Finset.mem_range] at hx ⊢
    omega
  have heq : (Finset.Ioc u v).filter Nat.Prime = B \ A := by
    ext p
    by_cases hp : Nat.Prime p <;> simp [A, B, hp]
    omega
  rw [heq, Finset.card_sdiff, Finset.inter_eq_left.mpr hsub]
  simp [A, B, Nat.primeCounting, Nat.primeCounting',
    Nat.count_eq_card_filter_range]

/-- The theta increment over a natural interval is exactly the sum of prime
logarithms in that interval. -/
theorem theta_sub_theta_eq_sum_Ioc (u v : ℕ) (huv : u ≤ v) :
    Chebyshev.theta v - Chebyshev.theta u =
      ∑ p ∈ (Finset.Ioc u v).filter Nat.Prime, Real.log p := by
  rw [Chebyshev.theta_eq_sum_Icc, Chebyshev.theta_eq_sum_Icc]
  norm_num
  let A := (Finset.Icc 0 u).filter Nat.Prime
  let B := (Finset.Icc 0 v).filter Nat.Prime
  have hsub : A ⊆ B := by
    apply Finset.filter_subset_filter
    intro x hx
    simp only [Finset.mem_Icc] at hx ⊢
    omega
  have heq : (Finset.Ioc u v).filter Nat.Prime = B \ A := by
    ext p
    by_cases hp : Nat.Prime p <;> simp [A, B, hp]
    omega
  rw [heq]
  change (∑ p ∈ B, Real.log p) - (∑ p ∈ A, Real.log p) = _
  rw [Finset.sum_sdiff_eq_sub hsub]

/-- A prime-bin upper bound from endpoint errors for theta. -/
theorem card_prime_Ioc_le_of_theta_error (u v : ℕ) (Eu Ev : ℝ)
    (hu : 2 ≤ u) (huv : u ≤ v)
    (hEu : |Chebyshev.theta u - u| ≤ Eu)
    (hEv : |Chebyshev.theta v - v| ≤ Ev) :
    (((Finset.Ioc u v).filter Nat.Prime).card : ℝ) ≤
      ((v : ℝ) - u + Eu + Ev) / Real.log u := by
  have hupos : (0 : ℝ) < u := by positivity
  have hlogpos : 0 < Real.log (u : ℝ) := Real.log_pos (by exact_mod_cast hu)
  rw [le_div_iff₀ hlogpos]
  calc
    (((Finset.Ioc u v).filter Nat.Prime).card : ℝ) * Real.log u =
        ∑ _p ∈ (Finset.Ioc u v).filter Nat.Prime, Real.log u := by
      simp
    _ ≤ ∑ p ∈ (Finset.Ioc u v).filter Nat.Prime, Real.log p := by
      apply Finset.sum_le_sum
      intro p hp
      rw [Finset.mem_filter, Finset.mem_Ioc] at hp
      exact Real.log_le_log hupos (by exact_mod_cast hp.1.1.le)
    _ = Chebyshev.theta v - Chebyshev.theta u :=
      (theta_sub_theta_eq_sum_Ioc u v huv).symm
    _ ≤ (v : ℝ) - u + Eu + Ev := by
      rw [abs_le] at hEu hEv
      linarith

/-- Uniform prime-bin estimate for the quotient bins
`floor(N/p)=m`, obtained from the quantitative theta PNT. -/
theorem exists_prime_quotient_bin_bound :
    ∃ C : ℝ, 0 < C ∧ ∃ X : ℝ, 2 ≤ X ∧
      ∀ (N m : ℕ), 0 < m → X ≤ (N / (m + 1) : ℕ) →
        (((Finset.Ioc (N / (m + 1)) (N / m)).filter Nat.Prime).card : ℝ) ≤
          (((N / m : ℕ) : ℝ) - (N / (m + 1) : ℕ) +
            C * ((N / (m + 1) : ℕ) / Real.log (N / (m + 1) : ℕ) ^ 2) +
            C * ((N / m : ℕ) / Real.log (N / m : ℕ) ^ 2)) /
              Real.log (N / (m + 1) : ℕ) := by
  obtain ⟨C, hC, X, hX, htheta⟩ := exists_theta_error_bound
  refine ⟨C, hC, X, hX, ?_⟩
  intro N m hm hsmall
  let u := N / (m + 1)
  let v := N / m
  have huv : u ≤ v := Nat.div_le_div_left (Nat.le_succ m) hm
  have hu2 : 2 ≤ u := by exact_mod_cast (le_trans hX hsmall)
  have hvX : X ≤ (v : ℝ) := le_trans hsmall (by exact_mod_cast huv)
  exact card_prime_Ioc_le_of_theta_error u v
    (C * ((u : ℝ) / Real.log u ^ 2))
    (C * ((v : ℝ) / Real.log v ^ 2)) hu2 huv
    (htheta u hsmall) (htheta v hvX)

#print axioms exists_theta_error_bound
#print axioms card_prime_Ioc_le_of_theta_error
#print axioms exists_prime_quotient_bin_bound

end ResearchPNT
